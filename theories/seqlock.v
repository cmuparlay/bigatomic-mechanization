From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap list lib.mono_nat.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
Import derived_laws.bi.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(* Begin hooks to make `lia` work witrefines_right_CG_dequeueh Nat.modulo and Nat.div *)
Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.

Global Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

Require Import stdpp.sorting.

Definition write : val :=
  rec: "write" "version" "dst" "src" "n" :=
    let: "ver" := !"version" in
    if: "ver" `rem` #2 = #1 then
      (* Loop if locked *)
      "write" "version" "dst" "src" "n"
    else
      if: CAS "version" "ver" (#1 + "ver") then
        (* Lock was successful *)
        (* Perform update *)
        array_copy_to "dst" "src" "n";;
        (* Unlock *)
        "version" <- #2 + "ver"
      else
        (* Loop if CAS failed, meaning we tried and failed to lock *)
        "write" "version" "dst" "src" "n".

Definition read : val :=
  rec: "read" "version" "src" "n" :=
    let: "ver" := !"version" in
    if: "ver" `rem` #2 = #1 then
      (* If locked, retry *)
      "read" "version" "src" "n"
    else
      (* Unlocked *)
      let: "data" := array_clone "src" "n" in
      if: !"version" = "ver" then
        (* Data was not changed, so our read was valid *)
        "data"
      else
        (* Data was locked and updated since we loaded *)
        (* Retry *)
        "read" "version" "src" "n".


Definition history := gmap nat (agree (list val)).

Definition historyUR := authUR $ gmapUR nat (agreeR (listO valO)).

Class seqlockG (Σ : gFunctors) := {
  seqlock_heapGS :: heapGS Σ;
  seqlock_historyUR :: inG Σ historyUR;
  seqlock_mono_natG :: mono_natG Σ;
}.

Section seqlock.
  Context `{!seqlockG Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition seqlockN := N .@ "seqlock".

  Definition history_auth_own γ (q : Qp) history := own γ (●{#q} map_seq 0 (to_agree <$> history)).

  Definition value γ (vs : list val) : iProp Σ :=
    ∃ history,
      history_auth_own γ (1/2) history ∗ ⌜last history = Some vs⌝.

  Definition history_frag_own γₕ i value := own γₕ (◯ {[i := to_agree value]}).

  Lemma history_auth_update value γₕ history :
    history_auth_own γₕ 1 history ==∗
      history_auth_own γₕ 1 (history ++ [value]) ∗ history_frag_own γₕ (length history) value.
  Proof.
    iIntros "H●".
    rewrite /history_auth_own /history_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length history)
          (x := to_agree value).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length history) with (O + length (to_agree <$> history)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma history_frag_alloc i value γₕ history q :
    history !! i = Some value →
      history_auth_own γₕ q history ==∗
        history_auth_own γₕ q history ∗ history_frag_own γₕ i value.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree value]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree value). split; last done.
      by rewrite lookup_map_seq_0 list_lookup_fmap Hlookup. }
    by iFrame.
  Qed.

  (* Definition AU_write (Φ : val → iProp Σ) γ (q : Z) : iProp Σ := *)
    (* AU <{ ∃∃ p : Z, value γ p }> @ ⊤ ∖ ↑N, ∅ <{ value γ q, COMM Φ #() }>. *)
    
  Definition AU_read γ Φ : iProp Σ :=
    AU <{ ∃∃ (vs : list val), value γ vs }> @ ⊤ ∖ ↑N, ∅ 
       <{ ∃ l : loc, value γ vs, COMM Φ #() }>.

  Definition seqlock_inv (γ γₕ : gname) (version l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (history : list (list val)) (vs : list val),
      (* Physical state of version *)
      version ↦ #ver ∗
      (* Big atomic is of fixed size *)
      ⌜length vs = len⌝ ∗
      (* The version number is twice (or one greater than twice) than number of versions*)
      ⌜length history = S (Nat.div2 ver)⌝ ∗
      if Nat.even ver then 
        (* If sequence number is even, then unlocked *)
        (* Full ownership of points-to pred in invariant *)
        (* And the logical state consistent with physical state *)
        history_auth_own γₕ (1/2) history ∗ mono_nat_auth_own γ 1 ver ∗ l ↦∗ vs ∗ ⌜last history = Some vs⌝
      else 
        (* If locked, have only read-only access to ensure one updater *)
        history_auth_own γₕ (1/4) history ∗ mono_nat_auth_own γ (1/2) ver ∗ l ↦∗{# 1/2} vs.

  Lemma wp_array_copy_to' γ γₕ (version dst src : loc) (n i : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    i ≤ n → length vdst = n - i →
      inv seqlockN (seqlock_inv γ γₕ version src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ i) #(n - i)
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      history_frag_own γₕ (Nat.div2 ver') vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! (i + j)%nat = Some v⌝)) }}}.
  Proof.
    iIntros "%Hle %Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
    iLöb as "IH" forall (i vdst ver Hle Hvdst) "Hlb".
    wp_rec.
    wp_pures.
    case_bool_decide as Hdone.
    - wp_pures.
      assert (i = n)%Z as -> by lia. clear Hdone. simplify_eq/=.
      rewrite Nat.sub_diag length_zero_iff_nil in Hvdst.
      clear Hle. subst.
      iApply ("HΦ" $! [] []). iFrame.
      iModIntro.
      iSplit; first by rewrite Nat.sub_diag.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { assert (@List.length val [] > 0) as Hlen by lia. inv Hlen.  }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E.
      iInv seqlockN as "(%ver' & %history & %vs & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl". simplify_eq.
      destruct (Nat.even ver') eqn:Hparity.
      + iDestruct "Hlock" as ">(Hγₕ & Hγ & Hsrc & %Hcons)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iMod (history_frag_alloc with "Hγₕ") as "[H● #H◯]".
        { by rewrite last_lookup in Hcons. }
        rewrite Hhistory /=.
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists ver', history, vs. rewrite Hparity. by iFrame "∗ %".  }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        rewrite -{1}Nat.add_1_r.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iCombine "Hhd Hdst" as "Hdst".
        rewrite -array_cons.
        iFrame. repeat iSplit.
        { iIntros "!% /=". lia. }
        { iPureIntro. by eapply SSorted_cons. }
        { iPureIntro. constructor; first done.
          eapply Forall_impl; eauto. lia. }
        { simpl. iSplitR "Hcons".
          - iSplitR; first done. 
            iIntros "%Heven".
            iExists vs. iFrame "#".
            rewrite Nat.add_0_r.
            by rewrite <- list_lookup_lookup_total_lt by lia.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
      + iDestruct "Hlock" as ">(Hγₕ & Hγ & Hsrc)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists _, _, _. iFrame. 
          repeat iSplit; try done.
          rewrite Hparity. by iFrame. }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        rewrite -{1}Nat.add_1_r.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iCombine "Hhd Hdst" as "Hdst".
        rewrite -array_cons.
        iFrame. repeat iSplit.
        { iIntros "!% /=". lia. }
        { iPureIntro. by eapply SSorted_cons. }
        { iPureIntro. constructor; first done.
          eapply Forall_impl; eauto. lia. }
        { simpl. iSplitR "Hcons".
          - rewrite -Nat.even_spec.
            iSplitR; first done.
            iIntros "%Heven". congruence.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
  Qed.

  Lemma map_seq_agree (vs vs' : list (list val))  :
    map_seq 0 (to_agree <$> vs) ≡@{gmap _ _} map_seq 0 (to_agree <$> vs') → vs = vs'.
  Proof.
    intros Heq.
    apply list_eq.
    intros i.
    apply leibniz_equiv.
    apply (inj (fmap to_agree)).
    repeat rewrite -list_lookup_fmap.
    by do 2 rewrite -lookup_map_seq_0.
  Qed.

  Lemma wp_array_copy_to γ γₕ (version dst src : loc) (n : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    length vdst = n →
      inv seqlockN (seqlock_inv γ γₕ version src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #src #n
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     replace dst with (dst +ₗ 0) by apply Loc.add_0.
     replace src with (src +ₗ 0) at 2 by apply Loc.add_0.
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' γ γₕ version dst src n 0 vdst ver with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     by rewrite Nat.sub_0_r.
  Qed.

  Lemma wp_array_clone γ γₕ (version src : loc) (n : nat) ver :
    n > 0 →
      inv seqlockN (seqlock_inv γ γₕ version src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γ ver -∗
          {{{ True }}}
            array_clone #src #n
          {{{ vers vdst (dst : loc), RET #dst; 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst, 
                  mono_nat_lb_own γ ver' ∗
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
    iIntros "%Hpos #Hinv #Hlb %Φ !# _ HΦ".
    rewrite /array_clone.
    wp_pures.
    wp_alloc dst as "Hdst".
    { lia. }
    wp_pures.
    wp_apply (wp_array_copy_to with "[//] [//] [$]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma Even_inj n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma Odd_inj n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.


  Lemma even_inj n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec Even_inj in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec Even_inj in H.
      rewrite -bool_decide_not in H'.
  Qed.

  Lemma wp_array_copy_to_half' γ γₕ version dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv seqlockN (seqlock_inv γ γₕ version dst n) -∗
          {{{ (dst +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ i) #(n - i)%nat
          {{{ RET #(); (dst +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
  Proof.
    iIntros (Hle Hlen Hmatch) "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    iLöb as "IH" forall (i vs vs' Hlen Hle Hmatch).
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      simpl in *.
      assert (i = n) as -> by lia.
      rewrite Nat.sub_diag in Hlen.
      rewrite Hlen in Hmatch.
      symmetry in Hmatch.
      rewrite length_zero_iff_nil in Hlen.
      rewrite length_zero_iff_nil in Hmatch.
      subst.
      repeat rewrite array_nil.
      by iApply "HΦ".
    - wp_pures.
      assert (length vs > 0) by lia.
      destruct vs as [| v vs].
      { simplify_list_eq. lia. }
      destruct vs' as [| v' vs']; first simplify_list_eq.
      do 2 rewrite array_cons.
      iDestruct "Hdst" as "[Hdst Hdst']".
      iDestruct "Hsrc" as "[Hsrc Hsrc']".
      wp_load.
      wp_bind (_ <- _)%E.
      iInv seqlockN as "(%ver & %history & %vs'' & >Hversion & >%Hlen' & >%Hhistory & Hlock)" "Hcl".
      assert (i < length vs'') as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγₕ & Hγ & Hdst'' & %Hcons') /=".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' _]".
        { done. }
        by iCombine "Hdst Hdst''" gives %[Hfrac%dfrac_valid_own_r <-].
      + iMod "Hlock" as "(Hγₕ & Hγ & Hdst'')".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' Hacc]".
        { done. }
        iCombine "Hdst Hdst''" as "Hdst".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hdst" as "[Hdst Hdst'']".
        iPoseProof ("Hacc" with "Hdst''") as "Hdst''".
        iMod ("Hcl" with "[$Hversion Hγₕ Hγ Hdst'']") as "_".
        { iExists history, (<[i:=v']> vs''). rewrite Heven. iFrame "∗ %".
          iPureIntro. by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm /=.
        rewrite <- Nat2Z.inj_sub by lia.
        simplify_list_eq.
        wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
        * iPureIntro. lia.
        * iPureIntro. lia.
        * iIntros "[Hdst' Hsrc']".
          iApply "HΦ". iFrame.
          rewrite Loc.add_assoc /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma wp_array_copy_to_half γ γₕ version dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv seqlockN (seqlock_inv γ γₕ version dst n) -∗
          {{{ dst ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #dst #src #n
          {{{ RET #(); dst ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    replace dst with (dst +ₗ O) by now rewrite Loc.add_0.
    replace src with (src +ₗ O) by now rewrite Loc.add_0.
    replace n with (n - O) at 2 by lia.
    wp_apply (wp_array_copy_to_half' _ _ _ _ _ vs vs' with "[#] [$] [$]").
    - lia.
    - lia.
    - done.
    - by rewrite Loc.add_0.
  Qed.

  Lemma even_iff_not_odd n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma odd_iff_not_even n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma div2_def n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  Require Import iris.bi.lib.fractional.

  Lemma array_frac_add l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
  Proof.
    iIntros (Hlen) "Hl Hl'".
    iInduction vs as [|v vs] "IH" forall (l vs' Hlen).
    - symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. simplify_list_eq. by iSplit.
    - destruct vs' as [|v' vs']; simplify_list_eq.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hls]".
      iDestruct "Hl'" as "[Hl' Hls']".
      iCombine "Hl Hl'" as "Hl" gives %[_ <-].
      iFrame.
      iPoseProof ("IH" with "[//] [$] [$]") as "[Hl <-]".
      by iFrame.
  Qed.

  Lemma write_spec (γ γₕ : gname) (version dst src : loc) dq (vs' : list val) :
    inv seqlockN (seqlock_inv γ γₕ version dst (length vs')) -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, value γₕ vs  }>> 
          write #version #dst #src #(length vs') @ ↑N
        <<{ value γₕ vs' | RET #(); src ↦∗{dq} vs' }>>.
  Proof.
    iIntros "#Hinv Hsrc %Φ AU".
    iLöb as "IH".
    wp_rec.
    wp_pures.
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver & %history & %vs & >Hγ & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    destruct (Nat.even ver) eqn:Heven.
    - iMod "Hlock" as "(Hγₕ & Hver & Hdst & %Hcons)".
      wp_load.
      iMod ("Hcl" with "[-AU Hsrc]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. rewrite Heven. by iFrame. }
      iModIntro.
      wp_pures.
      case_bool_decide as Hparity.
      + simplify_eq.
        wp_pures.
        iApply ("IH" with "Hsrc AU").
      + wp_pures.
        wp_bind (CmpXchg _ _ _)%E.
        iInv seqlockN as "(%ver' & %history' & %vs'' & >Hver & >%Hlen' & >%Hhistory' & Hlock)" "Hcl".
        destruct (decide (ver = ver')) as [<- | Hne].
        * rewrite Heven.
          iMod "Hlock" as "(Hγₕ & Hγ & Hdst & %Hcons')".
          wp_cmpxchg_suc.
          iDestruct "Hγₕ" as "[Hγₕ Hγₕ']".
          iDestruct "Hdst" as "[Hdst Hdst']".
          replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
          iMod (mono_nat_own_update (S ver) with "Hγ") as "[[Hγ Hγ'] #Hlb]".
          { lia. }
          iMod ("Hcl" with "[Hver Hγₕ' Hdst' Hγ']") as "_".
          { rewrite /seqlock_inv. iExists (S ver), history', vs''.
            destruct (Nat.even (S ver)) eqn:Heven''.
            { exfalso. eapply Nat.Even_Odd_False.
              - by rewrite -Nat.even_spec.
              - by rewrite Nat.Odd_succ -Nat.even_spec. }
            rewrite -> Nat.Odd_div2 by now rewrite Nat.Odd_succ -Nat.even_spec.
            change 1%Z with (Z.of_nat 1).
            rewrite -Nat2Z.inj_add /=.
            iFrame "∗ %". }
          iModIntro.
          wp_pures.
          wp_apply (wp_array_copy_to_half _ _ _ _ _ vs'' vs' with "[//] [$] [-]"); try done.
          iIntros "!> [Hdst Hsrc]".
          wp_pures.
          iInv seqlockN as "(%ver' & %history'' & %vs''' & >Hver & >%Hlen'' & >%Hhistory'' & Hlock)" "Hcl".
          destruct (Nat.even ver') eqn:Heven''.
          { iMod "Hlock" as "(_ & Hγ' & _)". by iDestruct (mono_nat_auth_own_agree with "Hγ Hγ'") as %[Hq _]. }
          iMod "Hlock" as "(Hγₕ' & Hγ' & Hdst')".
          iPoseProof (array_frac_add with "Hdst Hdst'") as "[Hdst <-]".
          { done. }
          rewrite dfrac_op_own Qp.half_half.
          wp_store.
          change 2%Z with (Z.of_nat 2). simplify_eq.
          iDestruct (mono_nat_auth_own_agree with "Hγ Hγ'") as %[_ <-].
          iCombine "Hγ Hγ'" as "Hγ".
          iMod (mono_nat_own_update (S (S ver)) with "Hγ") as "[Hγ #Hlb']".
          { lia. }
          iCombine "Hγₕ Hγₕ'" gives %<-%auth_auth_dfrac_op_inv%map_seq_agree.
          iCombine "Hγₕ Hγₕ'" as "Hγₕ".
          rewrite Qp.quarter_quarter.
          iMod "AU" as (vs''') "[(%history'' & Hγₕ' & %Hagree) [_ Hconsume]]".
          iCombine "Hγₕ Hγₕ'" gives %<-%auth_auth_dfrac_op_inv%map_seq_agree.
          iCombine "Hγₕ Hγₕ'" as "Hγₕ".
          assert (Some vs'' = Some vs''') as [=<-] by (transitivity (last history'); eauto).
          iMod (history_auth_update vs' with "Hγₕ") as "[[●Hγₕ ●Hγₕ'] #◯Hγₕ]".
          iMod ("Hconsume" with "[$●Hγₕ']") as "HΦ".
          { by rewrite last_snoc. }
          rewrite -Nat2Z.inj_add /=.
          simplify_eq.
          iMod ("Hcl" with "[-HΦ Hsrc]") as "_".
          { rewrite /seqlock_inv. iFrame. iExists (history' ++ [vs']), vs'.
            iSplit; first done. simpl. rewrite Heven. iSplit.
            { rewrite last_length. auto. }
            iFrame. by rewrite last_snoc. }
          iModIntro.
          by iApply "HΦ".
        * wp_cmpxchg_fail.
          { intros Heq. simplify_eq. }
          iMod ("Hcl" with "[-Hsrc AU]") as "_".
          { iFrame "∗ %". }
          iModIntro.
          wp_pures.
          by wp_apply ("IH" with "[$]").
      - wp_load.
        iMod ("Hcl" with "[-Hsrc AU]") as "_".
        { iFrame "∗ %". rewrite Heven. iFrame. }
        iModIntro.
        wp_pures.
        case_bool_decide as H.
        { wp_pures. by wp_apply ("IH" with "[$]"). }
        replace (ver `rem` 2)%Z with (ver `mod` 2)%Z in H by lia.
        rewrite Zmod_even -Even_inj in H. rewrite 
        assert (ver `rem` 2 ≠ 1)%Z.
        { intros Hne. apply H. by repeat f_equal. }
        replace (ver `rem` 2)%Z with (ver `mod` 2)%Z in H by lia.
        { lia. }
        
        by wp_apply ("IH" with "[$]").
    
    
          -- wp_cmpxchg_fail.
             { intros Heq. simplify_eq. }
             iMod ("Hcl" with "[-Hsrc AU]") as "_".
             { iFrame. rewrite Heven'. iExists history', vs''. iFrame "∗ %". }
             iModIntro.
             wp_pures.
             by wp_apply ("IH" with "[$]").
        *

            

             specialize (H 1).
             rewrite /equiv /ofe_equiv in H.
             apply (inj map_seq) in H.

             rewrite -Nat2Z.inj_add /=.
             

             iPoseProof (map_seq_agree with "Hγₕ ◯Hγₕ'") as "->".
             { by rewrite Hhistory'' last_length Hhistory'. }
             iPoseProof (array_frac_add with "Hdst Hdst''") as "[Hdst <-]".
             { done. }
             rewrite dfrac_op_own Qp.half_half.
             iMod ("Hcl" with "[-]") as "_".
             { rewrite /seqlock_inv. iExists (S (S ver)), (history' ++ [vs']), vs'.
               rewrite Hhistory''.
               rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec.
               simpl. rewrite Heven last_snoc. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl.
               change 2%Z with (Z.of_nat 2). rewrite -Nat2Z.inj_add /=. iFrame "∗ %".
               iSplitR; first done.
 
               - done.
               iFrame "∗ %". iNext. change 2%Z with (Z.of_nat 2). rewrite -Nat2Z.inj_add /=. repeat iSplit; try done.
               rewrite Heven'. rewrite last_snoc. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. iFrame "∗ %". simpl. 
               rewrite Hhistory''. iFrame "∗ %". simpl. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl. iSplitL; try done. iFrame "∗ %".
               { admit. }
               iNext. iSplit.
               * iPureIntro. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl. rewrite /Nat.div2. done.
               rewrite last
               simpl.

             

               iMod (mono_nat_own_update (S ver) with "Hγ") as "[(Hauth & Hauth' & Hauth'') #Hlb]".
               Check mono_nat_own_update.
               iMod mono_nat_auth_own_update.
               
               iFrame "∗ %".
                first last. 
               { by rewrite Nat.Odd_succ -Nat.even_spec.
               rewrite 
                
               assert 
               Set Printing Coercions.
               change 1%Z with (Z.of_nat 1).
               rewrite -Nat2Z.inj_add /=.
               iFrame.
               rewrite 
               iFrame. }
             rewrite /value.
             iMod "AU" as (vs''') "[(%ver'' & Hγ' & #Hfrag) [_ Hconsume]]".
            iDestruct (mono_nat_auth_own_agree with "Hγ Hγ'") as %[_ <-].
            iCombine "Hγ Hγ'" as "Hγ".
            iMod (mono_nat_own_update (S ver) with "Hγ") as "[(Hauth & Hauth' & Hauth'') #Hlb]".
            { lia. }
            replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
            iMod (history_auth_update vs' with "Hγₕ") as "[●Hγₕ #◯Hγₕ]".
            rewrite Hhistory'.
            rewrite <- Nat.Even_div2 by (now rewrite -Nat.even_spec).
            rewrite <- Nat.Even_div2 in Hhistory, Hhistory' by (now rewrite -Nat.even_spec).
            iMod ("Hconsume" with "[$]") as "HΦ".
            change 1%Z with (Z.of_nat 1).
            rewrite -Nat2Z.inj_add /=.
            iDestruct "Hdst" as "[Hdst Hdst']".
            iMod (own_update with "●Hγₕ") as "[●Hγₕ ◯Hγₕ']".
            { apply auth_update_alloc. 
              eapply core_id_local_update; last reflexivity.
              apply _. }
            iPoseProof "◯Hγₕ'" as "#◯Hγₕ'".
            rewrite left_id.
            iMod ("Hcl" with "[-Hsrc Hdst Hauth' HΦ]") as "_".
            { rewrite /seqlock_inv.
              destruct (Nat.even (S ver)) eqn:Heven''.
              { exfalso. eapply Nat.Even_Odd_False.
                - by rewrite -Nat.even_spec.
                - by rewrite Nat.Odd_succ -Nat.even_spec. }
              iExists (S ver), (history' ++ [vs']), vs''.
              rewrite Heven'' last_length.
              iFrame "∗ %". auto. }
            iModIntro.
            wp_pures.
            wp_apply (wp_array_copy_to_half _ _ _ _ _ vs'' vs' with "[//] [$] [-]"); try done.
            iIntros "!> [Hdst Hsrc]".
            wp_pures.
            iInv seqlockN as "(%ver' & %history''' & %vs'''' & >Hver' & >%Hlen'' & >Hγₕ & >%Hhistory'' & Hlock)" "Hcl".
            destruct (Nat.even ver') eqn:Heven''.
            { iMod "Hlock" as "[Hγ _]".
              iDestruct (mono_nat_auth_own_agree with "Hγ Hauth'") as %[_ Heq].
              exfalso. apply Nat.Even_Odd_False with (x := ver).
              - by rewrite -Nat.even_spec.
              - rewrite -Nat.Even_succ -Nat.even_spec. congruence. }
            iMod "Hlock" as "[Hγ Hdst'']".
            iDestruct (mono_nat_auth_own_agree with "Hγ Hauth'") as %[_ ->].
            wp_store.
            iPoseProof (map_seq_agree with "Hγₕ ◯Hγₕ'") as "->".
            { by rewrite Hhistory'' last_length Hhistory'. }
            iPoseProof (array_frac_add with "Hdst Hdst''") as "[Hdst <-]".
            { done. }
            rewrite dfrac_op_own Qp.half_half.
            iMod ("Hcl" with "[-]") as "_".
            { rewrite /seqlock_inv. iExists (S (S ver)), (history' ++ [vs']), vs'.
              rewrite Hhistory''.
              rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec.
              simpl. rewrite Heven last_snoc. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl.
              change 2%Z with (Z.of_nat 2). rewrite -Nat2Z.inj_add /=. iFrame "∗ %".
              iSplitR; first done.

              - done.
              iFrame "∗ %". iNext. change 2%Z with (Z.of_nat 2). rewrite -Nat2Z.inj_add /=. repeat iSplit; try done.
              rewrite Heven'. rewrite last_snoc. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. iFrame "∗ %". simpl. 
              rewrite Hhistory''. iFrame "∗ %". simpl. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl. iSplitL; try done. iFrame "∗ %".
              { admit. }
              iNext. iSplit.
              * iPureIntro. rewrite -> Nat.Even_div2 by now rewrite -Nat.even_spec. simpl. rewrite /Nat.div2. done.
              rewrite last
              simpl.
            cbn beta delta iota in *.

              change (Nat.div2 (S (S _))) with (S (Nat.div2 _)).
              cbn. rewrite Heven. iFrame. by iFrame. }
               
               
               
            ++ iFrame.

            
              iPureIntro. intuition. simpl
              rewrite Heven'' last_length.
              iFrame "∗ %".
              replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
              
              destruct (Nat)
                iExists (S ver).
              iExists
            
            
              
              iExists (S ver), (history' ++ [vs']), vs'. iFrame "∗ %". simpl. rewrite Heven. by iFrame. }
            
            



            Check mono_nat_auth_own_update.
        wp_cmpxchg.
        { apply _. done. }
        
        wp_cmpxchg_suc.

    wp_load.

    rewrite /write.
    wp_pures.
  Admitted.


  Check list.list_eq.

  Search (?m' ≼ ?m → (?m, ε) ~l~> (?m, ?m')).

  Check inj_iff.

  Search (?f ?x ≠ ?f ?y ↔ ?x ≠ ?y).

  Lemma neq_inv {A B} (f : A → B) x y : f x ≠ f y → x ≠ y.
  Proof.
    intros Hne Heq. simplify_eq.
  Qed.

  Lemma read_spec (γ γₕ : gname) (version src : loc) (n : nat) :
  n > 0 →
    inv seqlockN (seqlock_inv γ γₕ version src n) -∗
      <<{ ∀∀ vs, value γ γₕ vs ∗ ⌜length vs = n⌝ }>> 
        read #version #src #n @ ↑N
      <<{ ∃∃ copy : loc, value γ γₕ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
    iIntros "%Hpos #Hinv %Φ AU".
    iLöb as "IH".
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver & %history & %vs & >Hγ & >%Hlen & >Hγₕ & >%Hhistory & Hlock)" "Hcl".
    simplify_eq.
    destruct (Nat.even ver) eqn:Hparity.
    - iDestruct "Hlock" as "(>Hver & >Hsrc & >%Hcons)".
      wp_load.
      iPoseProof (mono_nat_lb_own_get with "Hγ") as "#Hlb'".
      iMod (own_update with "Hγₕ") as "[H● H◯]".
      { apply auth_update_alloc. apply (core_id_local_update _ {[Nat.div2 ver := to_agree vs]}).
        - apply _.
        - rewrite singleton_included_l.
          exists (to_agree vs). split.
          + rewrite last_lookup Hhistory /= in Hcons.
            rewrite lookup_map_seq_0. rewrite list_lookup_fmap.
            by rewrite Hcons.
          + reflexivity. }
      iPoseProof "H◯" as "#H◯".
      rewrite left_id.
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. rewrite Hparity. by iFrame. }
      iModIntro.
      wp_pures.
      case_bool_decide as Hparity'.
      { exfalso. rewrite Nat.even_spec -Even_inj -Z.even_spec in Hparity.
        simplify_eq.
        pose proof (Zmod_even ver) as Heven.
        rewrite Hparity in Heven. lia. }
      wp_pures.
      wp_smart_apply (wp_array_clone with "[//] [//] [//]").
      { done. }
      iIntros (vers vdst dst) "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
      wp_pures.
      wp_bind (! _)%E.
      iInv seqlockN as "(%ver' & %history' & %vs' & >Hγ & >%Hlen' & >Hγₕ & >%Hhistory' & Hlock)" "Hcl".
      destruct (decide (ver = ver')) as [<- | Hne].
      + rewrite Hparity.
        iDestruct "Hlock" as "(>Hver & >Hsrc & >%Hcons')".
        iCombine "Hγₕ H◯" gives %[Hincl _]%auth_both_valid_discrete.
        apply dom_included in Hincl as Hdom.
        rewrite dom_singleton_L singleton_subseteq_l in Hdom.
        rewrite lookup_included in Hincl.
        specialize Hincl with (Nat.div2 ver).
        rewrite option_included_total in Hincl.
        destruct Hincl as [Hnone | (a & b & H & H' & Heq)].
        { by rewrite lookup_insert in Hnone. }
        rewrite lookup_insert in H. simplify_eq.
        rewrite lookup_map_seq_0 list_lookup_fmap_Some in H'.
        destruct H' as (vs'' & Hlookup & ->).
        rewrite to_agree_included_L in Heq.
        destruct Heq.
        clear Hdom.
        rewrite last_lookup Hhistory' /= in Hcons'.
        simplify_eq.
        iAssert (⌜vs = vdst⌝)%I with "[Hcons Hγ]" as "<-".
        { iClear "IH".
          iApply pure_mono.
          { by apply list_eq_same_length. }
          rewrite big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver' Hver']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb #Hfrag]".
          assert (ver ≤ ver') as Hle by (by eapply Forall_lookup).
          iPoseProof (mono_nat_lb_own_valid with "Hγ Hlb") as "[%Hq %Hge]".
          assert (ver = ver') as <- by lia.
          clear Hle Hge.
          iPoseProof ("Hfrag" with "[]") as "(%vs' & #Hvs' & %Hlookup')".
          { by rewrite -Nat.even_spec. }
          iCombine "H◯ Hvs'" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as <-.
          iPureIntro.
          apply (inj Some).
          by etransitivity. }
          wp_load.
          iMod "AU" as (vs') "[[(%ver' & Hγ' & #Hfrag) %Hlen'] [_ Hclose']]".
          iDestruct (mono_nat_auth_own_agree with "Hγ Hγ'") as %[_ <-].
          clear Hq.
          iCombine "H◯ Hfrag" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as <-.
          iClear "Hfrag".
          iMod ("Hclose'" $! dst with "[$]") as "HΦ".
          iMod ("Hcl" with "[-HΦ Hdst]") as "_".
          { rewrite /seqlock_inv.
            iExists ver, history', vs. rewrite Hparity. iFrame. iFrame "%".
            iPureIntro. rewrite last_lookup. by rewrite Hhistory'. }
          iModIntro. wp_pures. case_bool_decide; simplify_eq.
          wp_pures. iModIntro. by iApply "HΦ".
      + destruct (Nat.even ver') eqn:Hparity'''.
        * iDestruct "Hlock" as "(Hversion & Hsrc & History)".
          (* iCombine "Hγₕ H◯" gives 
            %[(vs'' & H' & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l G]%auth_both_valid_discrete.
          rewrite lookup_map_seq_0 in H'. apply leibniz_equiv in H'. list_lookup_fmap_Some in H.
          rewrite singleton_included_l in H. *)
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /seqlock_inv.
            iExists ver', history', vs'. rewrite Hparity'''. iFrame. by iFrame "%". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
        * iDestruct "Hlock" as "(Hversion & Hsrc)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /seqlock_inv.
            iExists ver', history', vs'. rewrite Hparity'''. iFrame. by iFrame "%". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
    - iDestruct "Hlock" as "(Hversion & Hsrc)".
      wp_load.
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. rewrite Hparity. iFrame. by iFrame "%". }
      iModIntro.
      wp_pures.
      case_bool_decide as Hparity'; first last.
      { exfalso.
        do 2 apply neq_inv in Hparity'.
        assert (ver `mod` 2 = 0)%Z as Hparity''.
        { lia. }
        rewrite Zmod_even in Hparity''.
        destruct (Z.even ver) eqn:Heven.
        { rewrite Z.even_spec Even_inj -Nat.even_spec in Heven. congruence. }
        done. }
      wp_pures.
      iApply ("IH" with "AU").
  Qed.
        
        assert (ver `rem` 2 = 0).
        assert (Nat.odd ver = )
        rewrite Nat.odd_spec -Even_inj -Zmod_even in Hparity.  }
  Qed.
          destruct (decide (ver'))
          wp_pures.
          iMod ("Hcl" with "[$]") as "_".
          { rewrite /value. iExists ver. iFrame. }

          congruence.
          done.
          erewrite merge_singleton in Hvalid.
          assert (merge op _ _ = {[Nat.div2 ver := to_agree vs ⋅ to_agree vs']}).
          rewrite 
          assert (✓ )
          erewrite merge_singleton in Hvalid.
          iPoseProof ("Hfrag" with "[]") as "Hfrag".
          { by rewrite -Nat.even_spec. }
          rewrite Nat.even_spec in Hparity.
          Check Nat.even_spec.
          assert (Nat.even ver).
          assert (((Z.of_nat ver) mod 2)%Z ≠ 1) as Hmod.
        { intuition. apply Hparity. repeat f_equal. lia. }
        rewrite Odd_inj -Z.odd_spec in Hlocked.
        by rewrite Zmod_odd Hlocked in Hmod. }
          Check auth_frag_valid.


          pose proof (elem_of_list_lookup_2 _ _ _ Hver') as "Hin".
          Search (?l !! ?i = Some ?x → ?x ∈ ?l).
          { }
          iInduction i as [ | k] "IH'" forall (vdst Hlen Heq).
          - iIntros (x y Hlt).
            inv Hlt.
            iDestruct "Hcons" as "->".
            by rewrite -length_zero_iff_nil.
          - rewrite big_sepL2_cons_inv_l.
            iDestruct "Hcons" as "(%v & %vdst' & -> & Hlb & Hcons)".
            simplify_list_eq.

             }


        (* iCombine "Hγₕ H◯" gives 
          %[(vs'' & H' & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l G]%auth_both_valid_discrete.
        rewrite lookup_map_seq_0 in H'. apply leibniz_equiv in H'. list_lookup_fmap_Some in H.
        rewrite singleton_included_l in H. *)
        rewrite 
        iAssert ()
        wp_load.
        iMod 
        

      { }
      
      assert (((Z.of_nat ver) mod 2)%Z ≠ 1) as Hmod.
        { intuition. apply Hparity. repeat f_equal. lia. }
        rewrite Odd_inj -Z.odd_spec in Hlocked.
        by rewrite Zmod_odd Hlocked in Hmod. }
      by wp_smart_apply "IH".
    - wp_load.
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. iFrame. auto. }
      iModIntro.
      wp_pures.
      case_bool_decide as Hparity.
      { by wp_smart_apply "IH". }
      wp_pures.
      +  by wp_smart_apply "IH".
      { assert (((Z.of_nat ver) mod 2)%Z = 1) as Hmod.
        { intuition. apply Hparity. repeat f_equal. lia. }
        rewrite Odd_inj -Z.odd_spec in Hlocked.
        by rewrite Zmod_odd Hlocked in Hmod. }
      by wp_smart_apply "IH".
  Qed.
  
  Check mono_nat_auth_own.
End seqlock.