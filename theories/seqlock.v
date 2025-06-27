From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap list lib.mono_nat.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.

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
      if: CAS "l" "ver" (#1 + "ver") then
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

  Definition value γ γₕ (vs : list val) : iProp Σ :=
    ∃ ver,
      mono_nat_auth_own γ (1/2) ver ∗
      own γₕ (◯ {[Nat.div2 ver := to_agree vs]}).

  (* Definition AU_write (Φ : val → iProp Σ) γ (q : Z) : iProp Σ := *)
    (* AU <{ ∃∃ p : Z, value γ p }> @ ⊤ ∖ ↑N, ∅ <{ value γ q, COMM Φ #() }>. *)
    
  Definition AU_read γ γₕ Φ : iProp Σ :=
    AU <{ ∃∃ (vs : list val), value γ γₕ vs }> @ ⊤ ∖ ↑N, ∅ 
       <{ ∃ l : loc, value γ γₕ vs, COMM Φ #() }>.

  Definition seqlock_inv (γ γₕ : gname) (version l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (history : list (list val)) (vs : list val),
      (* Logical state of version (monotonically increasing natural) *)
      mono_nat_auth_own γ (1/2) ver ∗
      (* Big atomic is of fixed size *)
      ⌜length vs = len⌝ ∗
      (* Version history *)
      own γₕ (● map_seq O (to_agree <$> history)) ∗
      (* The version number is twice (or one greater than twice) than number of versions*)
      ⌜length history = S (Nat.div2 ver)⌝ ∗
      if Nat.even ver then 
        (* If sequence number is even, then unlocked *)
        (* Full ownership of points-to pred in invariant *)
        (* And the logical state consistent with physical state *)
        version ↦ #ver ∗ l ↦∗ vs ∗ ⌜last history = Some vs⌝
      else 
        (* If locked, have only read-only access to ensure one updater *)
        version ↦{#(1/2)} #ver ∗ l ↦∗{#(1/2)} vs.

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
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  ⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! (i + j)%nat = Some v⌝) }}}.
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
      iInv seqlockN as "(%ver' & %history & %vs & >Hγ & >%Hlen & >Hγₕ & >%Hhistory & Hlock)" "Hcl". simplify_eq.
      destruct (Nat.even ver') eqn:Hparity.
      + iDestruct "Hlock" as "(>Hver' & >Hsrc & >%Hcons)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iMod (own_update with "Hγₕ") as "[H● H◯]".
        { apply auth_update_alloc. apply (core_id_local_update _ {[Nat.div2 ver' := to_agree vs]}).
          - apply _.
          - rewrite singleton_included_l.
            exists (to_agree vs). split.
            + rewrite last_lookup Hhistory /= in Hcons.
              rewrite lookup_map_seq_0. rewrite list_lookup_fmap.
              by rewrite Hcons.
            + reflexivity. }
        iPoseProof "H◯" as "#H◯".
        rewrite left_id.
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
          - iIntros "%Heven".
            iExists vs. iFrame.
            iSplitL; first done.
            iPureIntro.
            rewrite Nat.add_0_r.
            by rewrite <- list_lookup_lookup_total_lt by lia.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
      + iDestruct "Hlock" as "(>Hver' & >Hsrc)".
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
            iIntros "%Heven". congruence.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
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
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  ⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝) }}}.
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
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  ⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝) }}}.
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

  Lemma even_inj n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma odd_inj n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  Lemma write_spec (γ γₕ : gname) (version dst src : loc) (vs' : list val) n :
    inv seqlockN (seqlock_inv γ γₕ version dst n) -∗
      src ↦∗ vs' -∗
        <<{ ∀∀ vs, value γ γₕ vs ∗ ⌜length vs = length vs'⌝ }>> 
          write #version #dst #src #(length vs') @ ↑N
        <<{ value γ γₕ vs' | RET #() }>>.

  Lemma read_spec (γ γₕ : gname) (version src : loc) (n : nat) :
    inv seqlockN (seqlock_inv γ γₕ version src n) -∗
      <<{ ∀∀ vs, value γ γₕ vs ∗ ⌜length vs = n⌝ }>> 
        read #version #src #n @ ↑N
      <<{ ∃∃ copy : loc, value γ γₕ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
    iIntros "#Hinv %Φ AU".
    iLöb as "IH".
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver & %history & %vs & Hversion & Hγ & Hsrc & >% & Hγₕ & >%Hlen & >[%Hlocked | %Hunlocked])" "Hcl".
    - wp_load.
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. iFrame. auto. }
      iModIntro.
      wp_pures.
      case_bool_decide as Hparity; first last.
      { assert (((Z.of_nat ver) mod 2)%Z ≠ 1) as Hmod.
        { intuition. apply Hparity. repeat f_equal. lia. }
        rewrite odd_inj -Z.odd_spec in Hlocked.
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
        rewrite odd_inj -Z.odd_spec in Hlocked.
        by rewrite Zmod_odd Hlocked in Hmod. }
      by wp_smart_apply "IH".
  Qed.
  
  Check mono_nat_auth_own.
End seqlock.