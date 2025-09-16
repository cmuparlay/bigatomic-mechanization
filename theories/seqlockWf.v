From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap list lib.mono_nat.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
Import derived_laws.bi.
Require Import  Coq.ZArith.Zquot.

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

Definition new_big_atomic (n : nat) : val :=
  λ: "src",
    let: "dst" := AllocN #(S n) #0 in
    array_copy_to ("dst" +ₗ #1) "src" #n;;
    "dst".

Definition loop_while : val :=
  rec: "loop" "l" "v" :=
    if: !"l" = "v" then "loop" "l" "v"
    else #().

Definition write (n : nat) : val :=
  λ: "l" "src",
    let: "ver" := !"l" in
    if: "ver" `rem` #2 = #1 then
      (* If locked, spin until unlocked and return *)
      loop_while "l" "ver"
    else
      let: "res" := CmpXchg "l" "ver" (#1 + "ver") in
      if: Snd "res" then
        (* Lock was successful *)
        (* Perform update *)
        array_copy_to ("l" +ₗ #1) "src" #n;;
        (* Unlock *)
        "l" <- #2 + "ver"
      else
        (* Failed to take lock *)
        let: "ver'" := Fst "res" in
        if: "ver'" = #1 + "ver" then
          (* If another writer is updating this version, wait until it is done *)
          loop_while "l" "ver'"
        else
          (* Otherwise, we have already been linearized by someone else *)
          #().

Definition read (n : nat) : val :=
  rec: "read" "l" :=
    let: "ver" := !"l" in
    if: "ver" `rem` #2 = #1 then
      (* If locked, retry *)
      "read" "l"
    else
      (* Unlocked *)
      let: "data" := array_clone ("l" +ₗ #1) #n in
      if: !"l" = "ver" then
        (* Data was not changed, so our read was valid *)
        "data"
      else
        (* Data was locked and updated since we loaded *)
        (* Retry *)
        "read" "l".

Definition history := gmap nat $ agree $ list val.

Definition historyUR := authUR $ gmapUR nat $ agreeR $ listO valO.

Definition requestReg := gmap nat $ agree (gname * nat).
Definition requestRegUR := authUR $ gmapUR nat $ agreeR $ prodO gnameO natO.

Class seqlockG (Σ : gFunctors) := {
  seqlock_heapGS :: heapGS Σ;
  seqlock_historyUR :: inG Σ historyUR;
  seqlock_requestRegUR :: inG Σ requestRegUR;
  seqlock_mono_natG :: mono_natG Σ;
  seqlock_ghost_varG_vals :: ghost_varG Σ (list val);
  seqlock_ghost_varG_bool :: ghost_varG Σ bool;
  seqlock_tokenG :: tokenG Σ;
}.

Section seqlock.
  Context `{!seqlockG Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition seqlockN := N .@ "seqlock".

  Definition writeN := N .@ "write".

  Definition history_auth_own γᵥ (q : Qp) (history : list (list val)) := own γᵥ (●{#q} map_seq 0 (to_agree <$> history)).

  Definition value γᵥ (vs : list val) : iProp Σ := ghost_var γᵥ (1/2) vs.

  Definition history_frag_own γₕ i (value : list val) := own γₕ (◯ {[i := to_agree value]}).

  Lemma history_auth_update (value : list val) γₕ (history : list (list val)) :
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
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma history_auth_frag_agree γₕ q history i value : 
    history_auth_own γₕ q history -∗
      history_frag_own γₕ i value -∗
        ⌜history !! i = Some value⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition registry γᵣ (requests : list (gname * nat)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γᵣ i (γₗ : gname) (ver : nat) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, ver)]})).

  Lemma registry_update γₗ ver γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(γₗ, ver)]) ∗ registered γ (length requests) γₗ ver.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (γₗ, ver)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree γᵣ (requests : list (gname * nat)) (i : nat) γₗ ver :
    registry γᵣ requests -∗
      registered γᵣ i γₗ ver -∗
        ⌜requests !! i = Some (γₗ, ver)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition AU_write (Φ : val → iProp Σ) γ (vs' : list val) (src : loc) dq : iProp Σ :=
       AU <{ ∃∃ vs : list val, value γ vs }>
            @ ⊤ ∖ ↑N, ∅
          <{ value γ vs', COMM src ↦∗{dq} vs' -∗ Φ #() }>.

  Definition write_inv (Φ : val → iProp Σ) (γ γₗ γₜ : gname) (src : loc) (dq : dfrac) (vs' : list val) : iProp Σ :=
      ((src ↦∗{dq} vs' -∗ Φ #()) ∗ ghost_var γₗ (1/2) false) (* The failing write has already been linearized and its atomic update has been consumed *)
    ∨ (£ 1 ∗ AU_write Φ γ vs' src dq ∗ ghost_var γₗ (1/2) true)
    ∨ (token γₜ ∗ ∃ b : bool, ghost_var γₗ (1/2) b). (* The failing write has linearized and returned *)

  Definition request_inv γ γₗ ver ver' : iProp Σ :=
    ghost_var γₗ (1/2) (bool_decide (ver < ver')) ∗
    ∃ (Φ : val → iProp Σ) (γₜ : gname) (src : loc) (dq : dfrac) (vs : list val),
      inv writeN (write_inv Φ γ γₗ γₜ src dq vs).

  Definition registry_inv γ ver (requests : list (gname * nat)) : iProp Σ :=
    [∗ list] '(γₗ, ver') ∈ requests, request_inv γ γₗ ver ver'.

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
  Lemma linearize_writes γ (ver : nat) (vs : list val) requests :
    ghost_var γ (1/2) vs -∗
      registry_inv γ ver requests ={⊤ ∖ ↑seqlockN}=∗ 
        registry_inv γ (S ver) requests ∗ ∃ vs' : list val, ghost_var γ (1/2) vs'.
  Proof.
    iIntros "Hγ Hreqs".
    iInduction requests as [|[γₗ ver'] reqs'] "IH" forall (vs).
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(Hlin & %Φ & %γₜ & %src & %dq & %vs' & #Hwinv) Hreqs']";
      iMod ("IH" with "Hγ Hreqs'") as "(Hreqs' & %vs'' & Hγ)".
      iInv writeN as "[[HΦ >Hlin'] | [(>Hcredit & AU & >Hlin') | (>Htok & %b & >Hlin')]]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ Hless].
        iMod ("Hclose" with "[HΦ Hlin]") as "_".
        { iLeft. rewrite Hless. iFrame. }
        rewrite bool_decide_eq_false in Hless.
        assert (ver ≥ ver') as Hge by lia.
        iFrame "∗ #".
        by case_bool_decide; first lia.
      + iCombine "Hlin Hlin'" gives %[_ Hless].
        destruct (decide (ver' = S ver)) as [-> | Hne].
        * iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
          iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
          iMod "AU" as (n') "[Hγ' [_ Hconsume]]".
          iMod (ghost_var_update_halves vs' with "Hγ Hγ'") as "[Hγ Hγ']".
          iFrame.
          rewrite /request_inv.
          rewrite -> bool_decide_eq_false_2 by lia.
          iFrame "∗ #".
          iMod ("Hconsume" with "Hγ") as "HΦ".
          iMod ("Hclose" with "[-]") as "_".
          { iLeft. iFrame. }
          done.
        * iMod ("Hclose" with "[Hcredit AU Hlin']") as "_".
          { iRight. iLeft. iFrame. }
          iFrame.
          rewrite Hless.
          rewrite bool_decide_eq_true in Hless.
          rewrite /request_inv.
          rewrite -> bool_decide_eq_true_2 by lia.
          by iFrame "∗ #".
      + iCombine "Hlin Hlin'" gives %[_ <-].
        iMod (ghost_var_update_halves (bool_decide (S ver < ver')) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[Htok Hlin]") as "_".
        { do 2 iRight. iFrame. }
        by iFrame "∗ #".
  Qed.

  Definition seqlock_inv (γ γᵥ γₕ γᵣ : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (history : list (list val)) (vs : list val) requests,
      registry γᵣ requests ∗
      (* State of request registry *)
      registry_inv γ (Nat.div2 ver) requests ∗
      (* Physical state of version *)
      l ↦ #ver ∗
      (* Big atomic is of fixed size *)
      ⌜length vs = len⌝ ∗
      (* The version number is twice (or one greater than twice) than number of versions*)
      ⌜length history = S (Nat.div2 ver)⌝ ∗
      if Nat.even ver then 
        (* If sequence number is even, then unlocked *)
        (* Full ownership of points-to pred in invariant *)
        (* And the logical state consistent with physical state *)
        ghost_var γ (1/2) vs ∗ history_auth_own γₕ 1 history ∗ mono_nat_auth_own γᵥ 1 ver ∗ (l +ₗ 1) ↦∗ vs ∗ ⌜last history = Some vs⌝
      else 
        (* If locked, have only read-only access to ensure one updater *)
        history_auth_own γₕ (1/2) history ∗ mono_nat_auth_own γᵥ (1/2) ver ∗ (l +ₗ 1) ↦∗{# 1/2} vs.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵣ (dst src : loc) (n i : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    i ≤ n → length vdst = n - i →
      inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ 1 +ₗ i) #(n - i)
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
                  mono_nat_lb_own γᵥ ver' ∗ 
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
      iSplit; first rewrite Nat.sub_diag //.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { assert (@List.length val [] > 0) as Hlen by lia. inv Hlen.  }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E.
      iInv seqlockN as "(%ver' & %history & %vs & %registry & Hreg & Hreginv & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl". simplify_eq.
      destruct (Nat.even ver') eqn:Hparity.
      + iDestruct "Hlock" as ">(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iMod (history_frag_alloc with "Hγₕ") as "[H● #H◯]".
        { by rewrite last_lookup in Hcons. }
        rewrite Hhistory /=.
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists ver', history, vs. rewrite Hparity. by iFrame "∗ %".  }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        do 2 rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        replace (S i) with (i + 1) by lia.
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
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
      + iDestruct "Hlock" as ">(Hγₕ & Hγᵥ & Hsrc)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists _, _, _. iFrame. 
          repeat iSplit; try done.
          rewrite Hparity. by iFrame. }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        do 2 rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        replace (S i) with (i + 1) by lia.
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
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma history_auth_auth_agree γₕ p q history history' :
    history_auth_own γₕ p history -∗
      history_auth_own γₕ q history'  -∗
        ⌜history = history'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply list_eq.
    intros i.
    apply leibniz_equiv.
    apply (inj (fmap to_agree)).
    repeat rewrite -list_lookup_fmap.
    by do 2 rewrite -lookup_map_seq_0.
  Qed.

  Lemma wp_array_copy_to_wk γ γᵥ γₕ γᵣ (dst src : loc) (n : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    length vdst = n →
      inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ 1) #n
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
                  mono_nat_lb_own γᵥ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ 1)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.

  Lemma wp_array_clone_wk γ γᵥ γₕ γᵣ (src : loc) (n : nat) ver :
    n > 0 →
      inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ 1) #n
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
                  mono_nat_lb_own γᵥ ver' ∗
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
    wp_apply (wp_array_copy_to_wk with "[//] [//] [$]").
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

  Lemma wp_array_copy_to_half' γ γᵥ γₕ γᵣ dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ dst n) -∗
          {{{ (dst +ₗ 1 +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 1 +ₗ i) #(src +ₗ i) #(n - i)%nat
          {{{ RET #(); (dst +ₗ 1 +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
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
      iInv seqlockN as "(%ver & %history & %vs'' & %registry & Hreg & Hreginv & >Hversion & >%Hlen' & >%Hhistory & Hlock)" "Hcl".
      assert (i < length vs'') as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst'' & %Hcons') /=".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' _]".
        { done. }
        by iCombine "Hdst Hdst''" gives %[Hfrac%dfrac_valid_own_r <-].
      + iMod "Hlock" as "(Hγₕ & Hγᵥ & Hdst'')".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' Hacc]".
        { done. }
        iCombine "Hdst Hdst''" as "Hdst".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hdst" as "[Hdst Hdst'']".
        iPoseProof ("Hacc" with "Hdst''") as "Hdst''".
        iMod ("Hcl" with "[$Hreg $Hreginv $Hversion Hγₕ Hγᵥ Hdst'']") as "_".
        { iExists history, (<[i:=v']> vs''). rewrite Heven. iFrame "∗ %".
          iPureIntro. by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        rewrite Loc.add_assoc /=.
        rewrite (Loc.add_assoc src) /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm /=.
        rewrite <- Nat2Z.inj_sub by lia.
        simplify_list_eq.
        wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
        * iPureIntro. lia.
        * iPureIntro. lia.
        * iIntros "[Hdst' Hsrc']".
          iApply "HΦ". iFrame.
          rewrite (Loc.add_assoc (dst +ₗ 1)) /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma wp_array_copy_to_half γ γᵥ γₕ γᵣ dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ dst n) -∗
          {{{ (dst +ₗ 1) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 1) #src #n
          {{{ RET #(); (dst +ₗ 1) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ 1)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (wp_array_copy_to_half' _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
    - lia.
    - lia.
    - done.
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

  Definition is_seqlock (v : val) (γ : gname) (n : nat) : iProp Σ :=
    ∃ (dst : loc) (γₕ γᵥ γᵣ : gname),
      ⌜v = #dst⌝ ∗ inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ dst n).

  Lemma new_big_atomic_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        new_big_atomic n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ is_seqlock v γ n ∗ value γ vs  }}}.
  Proof.
    iIntros "%Hlen %Hpos %Φ Hsrc HΦ".
    wp_rec.
    wp_pures.
    wp_alloc l as "Hl".
    { done. }
    wp_pures.
    rewrite Nat2Z.id /= array_cons.
    iDestruct "Hl" as "[Hversion Hl]".
    wp_apply (wp_array_copy_to with "[$Hl $Hsrc]").
    { by rewrite length_replicate. }
    { auto. }
    iIntros "[Hl Hsrc]".
    wp_pures.
    iMod (ghost_var_alloc vs) as "(%γ & Hγ & Hγ')".
    iMod (mono_nat_own_alloc 0) as "(%γᵥ & Hγᵥ & _)".
    iMod (own_alloc (● map_seq O (to_agree <$> [vs]))) as "[%γₕ Hγₕ]".
    { by apply auth_auth_valid, singleton_valid. }
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γᵣ Hγᵣ]".
    { by apply auth_auth_valid. }
    iMod (inv_alloc seqlockN _ (seqlock_inv γ γᵥ γₕ γᵣ l n) with "[Hl Hversion Hγ' Hγᵥ Hγₕ Hγᵣ]") as "H".
    { rewrite /seqlock_inv /registry_inv. iExists O, [vs], vs, [].
      simpl. by iFrame "∗ %". }
    iModIntro.
    iApply ("HΦ" $! #l γ).
    by iFrame.
  Qed.

  Lemma wp_loop_while γ γᵥ γₕ γᵣ (l : loc) (n ver : nat) :
    inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ l n) -∗
      {{{ mono_nat_lb_own γᵥ ver }}}
        loop_while #l #ver
      {{{ ver', RET #(); ⌜ver < ver'⌝ ∗ mono_nat_lb_own γᵥ ver' }}}.
  Proof.
    iIntros "#Hinv %Φ !# #Hlb HΦ".
    iLöb as "IH".
    wp_rec.
    wp_pures.
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver' & %history & %vs & %registry & Hreg & Hreginv & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    wp_load.
    destruct (Nat.even ver') eqn:Heven.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hl & %Hcons)".
      iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
      iClear "Hlb".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iFrame. rewrite Heven. by iFrame. }
      iModIntro.
      wp_pures.
      destruct (decide (ver = ver')) as [-> | Hne].
      + rewrite -> bool_decide_eq_true_2 by congruence.
        wp_pures.
        iApply ("IH" with "[$]").
      + rewrite -> bool_decide_eq_false_2 by (intros Heq; simplify_eq).
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hlb]").
        iPureIntro. lia.
    - iDestruct "Hlock" as "(Hγₕ & Hγᵥ & Hl)".
      iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
      iClear "Hlb".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iFrame. rewrite Heven. by iFrame. }
      iModIntro.
      wp_pures.
      destruct (decide (ver = ver')) as [-> | Hne].
      + rewrite -> bool_decide_eq_true_2 by congruence.
        wp_pures.
        iApply ("IH" with "[$]").
      + rewrite -> bool_decide_eq_false_2 by (intros Heq; simplify_eq).
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hlb]").
        iPureIntro. lia.
  Qed.

  Lemma div2_mono x y : x ≤ y → Nat.div2 x ≤ Nat.div2 y.
  Proof.
    intros Hle. induction Hle as [| y Hle IH].
    - done.
    - destruct (Nat.Even_Odd_dec y).
      + by rewrite -Nat.Even_div2.
      + rewrite <- Nat.Odd_div2 by done. by constructor.
  Qed.

  Lemma even_odd_negb n b : Nat.even n = b ↔ Nat.odd n = negb b.
  Proof.
    split; destruct b; simpl.
    - intros Heven%Nat.even_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Hodd%Nat.odd_spec.
      by eapply Nat.Even_Odd_False.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + contradiction.
      + done.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + done.
      + contradiction.
    - intros Hodd%Nat.odd_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Heven%Nat.even_spec.
      by eapply Nat.Even_Odd_False.
  Qed.

  Lemma odd_even_negb n b : Nat.odd n = b ↔ Nat.even n = negb b.
  Proof.
    rewrite even_odd_negb negb_involutive //.
  Qed.

  Lemma even_inj n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec Even_inj in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec Even_inj in H.
  Qed.

  Lemma odd_inj n : Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    destruct (Z.odd n) eqn:H, (Nat.odd n) eqn:H'; auto.
    - rewrite Z.odd_spec -Odd_inj in H.
      by rewrite -not_true_iff_false Nat.odd_spec in H'.
    - rewrite Nat.odd_spec in H'.
      by rewrite -not_true_iff_false Z.odd_spec -Odd_inj in H.
  Qed.

  Lemma already_linearized Φ γ γₗ γᵥ γᵣ γₕ γₜ l n src dq vs' ver i :
    inv seqlockN (seqlock_inv γ γᵥ γₕ γᵣ l n) -∗
      inv writeN (write_inv Φ γ γₗ γₜ src dq vs') -∗
        registered γᵣ i γₗ (S (Nat.div2 ver)) -∗
          mono_nat_lb_own γᵥ (S (S ver)) -∗ 
            token γₜ -∗ 
              £ 2 -∗ 
                src ↦∗{dq} vs' 
                  ={⊤}=∗ Φ #().
  Proof.
    iIntros "#Hinv #Hwinv #◯Hreg #Hlb Hγₜ [Hcredit Hcredit'] Hsrc".
    iInv seqlockN as "(%ver' & %history & %vs'' & %registry & >Hreg & Hreginv & >Hver & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    iMod (lc_fupd_elim_later with "Hcredit Hreginv") as "Hreginv".
    iPoseProof (registry_agree with "Hreg ◯Hreg") as "%Hagree".
    (* Consider which state our helping request is in*)
    iPoseProof (big_sepL_lookup_acc _ _ _ _ Hagree with "Hreginv") as "[[Hlin _] Hrest]".
    iInv writeN as "[[HΦ >Hlin'] | [(>Hcredit & AU & >Hlin') | (>Htok & >Hlin')]]" "Hclose".
    { iMod ("Hclose" with "[Hγₜ Hlin']") as "_".
      { do 2 iRight. iFrame. }
      iMod ("Hcl" with "[-HΦ Hsrc Hcredit']") as "_".
      { iFrame. iSplit; last done. iApply "Hrest". iFrame "∗ #". }
      iMod (lc_fupd_elim_later with "Hcredit' HΦ") as "HΦ".
      iModIntro.
      iApply ("HΦ" with "Hsrc"). }
    { destruct (Nat.even ver') eqn:Heven''.
      - iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst & %Hcons')".
        iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hless].
        (* Our request is still pending *)
        (* This is impossible, as the value stored in the cell is what was prophecized *)
        iCombine "Hlin Hlin'" gives %[_ Heq%bool_decide_eq_true].
        assert (S (S ver) ≤ ver') as Htight%div2_mono by lia. simpl in Htight. lia.
      - iMod "Hlock" as "(Hγₕ & Hγᵥ & Hdst)".
        iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hless''].
        (* Our request is still pending *)
        (* This is impossible, as the value stored in the cell is what was prophecized *)
        iCombine "Hlin Hlin'" gives %[_ Heq%bool_decide_eq_true].
        assert (S (S ver) ≤ ver') as Htight%div2_mono by lia.
        simpl in Htight. lia. }
    { (* We have returned *)
      (* This is impossible, as we still own the token. There cannot be another copy in the invariant *)
      iCombine "Hγₜ Htok" gives %[]. }
  Qed.

  Lemma write_spec (γ : gname) (v : val) (src : loc) dq (vs' : list val) :
    is_seqlock v γ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, value γ vs  }>> 
          write (length vs') v #src @ ∅
        <<{ value γ vs' | RET #(); src ↦∗{dq} vs' }>>.
  Proof.
    iIntros "(%dst & %γₕ & %γᵥ & %γᵣ & -> & #Hinv) Hsrc %Φ AU".
    wp_rec.
    wp_pure credit:"Hcredit".
    wp_pure credit:"Hcredit'".
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver & %history & %vs & %registry & Hreg & Hreginv & >Hver & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    iMod (ghost_var_alloc true) as "(%γₗ & Hγₗ & Hγₗ')".
    iMod token_alloc as "[%γₜ Hγₜ]".
    iMod (inv_alloc writeN _ (write_inv Φ γ γₗ γₜ src dq vs') with "[Hcredit' AU Hγₗ']") as "#Hwinv".
    { iRight. iLeft. iFrame. }
    wp_load.
    iMod (registry_update γₗ (S (Nat.div2 ver)) with "[$]") as "[●Hreg #◯Hreg]".
    destruct (Nat.even ver) eqn:Heven.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst & %Hcons)".
      iDestruct (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-Hsrc Hγₜ Hcredit]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs, (registry ++ [(γₗ, S (Nat.div2 ver))]). rewrite Heven. iFrame "∗ #".
        rewrite bool_decide_eq_true_2.
        - simpl. by iFrame.
        - lia. }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_false_2; first last.
      { intros [=Heq]. by rewrite Zrem_even even_inj Heven in Heq. }
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iInv seqlockN as "(%ver' & %history' & %vs'' & %registry' & Hreg & Hreginv & >Hver & >%Hlen' & >%Hhistory' & Hlock)" "Hcl".
      destruct (decide (ver = ver')) as [<- | Hne].
      + rewrite Heven.
        wp_cmpxchg_suc.
        iDestruct "Hlock" as "([Hγ Hγ'] & [Hγₕ Hγₕ'] & Hγᵥ & [Hdst Hdst'] & %Hcons')".
        replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
        iMod (mono_nat_own_update (S ver) with "Hγᵥ") as "[[Hγᵥ Hγᵥ'] #Hlb']".
        { lia. }
        iMod ("Hcl" with "[Hver Hreg Hreginv Hγₕ' Hdst' Hγᵥ']") as "_".
        { rewrite /seqlock_inv. iExists (S ver), history', vs'', registry'.
          rewrite <- (Nat.Even_div2 ver) by now rewrite -Nat.even_spec.
          rewrite Nat.even_spec -Nat.Odd_succ -Nat.odd_spec odd_even_negb in Heven.
          rewrite Heven /=.
          iFrame "∗ #".
          change 1%Z with (Z.of_nat 1).
          rewrite -Nat2Z.inj_add /=.
          iFrame "∗ %". }
        iModIntro.
        wp_pures.
        wp_apply (wp_array_copy_to_half _ _ _ _ _ _ vs'' vs' with "[//] [$] [-]"); try done.
        iIntros "!> [Hdst Hsrc]".
        wp_pures.
        iInv seqlockN as "(%ver' & %history'' & %vs''' & %registry'' & Hreg & Hreginv & >Hver & >%Hlen'' & >%Hhistory'' & Hlock)" "Hcl".
        destruct (Nat.even ver') eqn:Heven''.
        { iMod "Hlock" as "(_ & _ & Hγᵥ' & _ & _)". by iDestruct (mono_nat_auth_own_agree with "Hγᵥ Hγᵥ'") as %[Hq _]. }
        iMod "Hlock" as "(Hγₕ' & Hγᵥ' & Hdst')".
        iPoseProof (array_frac_add with "Hdst Hdst'") as "[Hdst <-]".
        { done. }
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        change 2%Z with (Z.of_nat 2). simplify_eq.
        iDestruct (mono_nat_auth_own_agree with "Hγᵥ Hγᵥ'") as %[_ <-].
        iCombine "Hγᵥ Hγᵥ'" as "Hγᵥ".
        iMod (mono_nat_own_update (S (S ver)) with "Hγᵥ") as "[Hγᵥ #Hlb'']".
        { lia. }
        iPoseProof (history_auth_auth_agree with "Hγₕ Hγₕ'") as "<-".
        iCombine "Hγₕ Hγₕ'" as "Hγₕ".
        iCombine "Hγ Hγ'" as "Hγ".
        rewrite Qp.quarter_quarter.
        iPoseProof (registry_agree with "Hreg ◯Hreg") as "%Hagree".
        rewrite -(take_drop_middle _ _ _ Hagree).
        rewrite /registry_inv.
        rewrite big_sepL_app big_sepL_cons.
        iDestruct "Hreginv" as "(Hlft & [Hγₗ _] & Hrht)".
        rewrite -> bool_decide_eq_true_2 by lia.
        iMod (linearize_writes with "Hγ Hlft") as "(Hlft & %vs₁ & Hγ)".
        iMod (linearize_writes with "Hγ Hrht") as "(Hrht & %vs₂ & Hγ)".
        iMod (history_auth_update vs' with "Hγₕ") as "[●Hγₕ #◯Hγₕ]".
        iInv writeN as "[[HΦ >Hγₗ'] | [(>_ & AU & >Hγₗ') | (>Htok & >Hlin')]]" "Hclose".
        { by iCombine "Hγₗ Hγₗ'" gives %[]. }
        { iMod (ghost_var_update_halves false with "Hγₗ Hγₗ'") as "[Hlin Hlin']".
          iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
          iMod "AU" as (n') "[Hγ' [_ Hconsume]]".
          iMod (ghost_var_update_halves vs' with "Hγ Hγ'") as "[Hγ Hγ']".
          iMod ("Hconsume" with "Hγ") as "HΦ".
          iMod ("Hclose" with "[Hγₜ Hlin']") as "_".
          { do 2 iRight. iFrame. }
          iMod ("Hcl" with "[-HΦ Hsrc]") as "_".
          { iExists (S (S ver)), (history' ++ [vs']), vs', registry''.
            rewrite <- Nat.Even_div2 by now rewrite -Nat.even_spec.
            rewrite (take_drop_middle _ _ _ Hagree).
            rewrite /= Heven. change 2%Z with (Z.of_nat 2).
            rewrite -Nat2Z.inj_add /=.
            rewrite last_snoc last_length Hhistory'. iFrame.
            iNext. iSplit; last done.
            rewrite -{3}(take_drop_middle _ _ _ Hagree) /registry_inv big_sepL_app big_sepL_cons.
            iFrame "∗ #".
            rewrite bool_decide_eq_false_2; first done.
            lia. }
          iModIntro.
          by iApply "HΦ". }
        { (* We have returned *)
          (* This is impossible, as we still own the token. There cannot be another copy in the invariant *)
          iCombine "Hγₜ Htok" gives %[]. }
      + wp_cmpxchg_fail.
        { intros Heq. simplify_eq. }
        destruct (Nat.even ver') eqn:Heven'.
        * iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst & %Hcons')".
          iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
          iClear "Hlb".
          iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
          iMod ("Hcl" with "[-Hsrc Hγₜ Hcredit]") as "_".
          { iFrame. rewrite Heven'. iFrame "∗ %". }
          iModIntro.
          wp_pure credit:"Hcredit'".
          wp_pures.
          change 1%Z with (Z.of_nat 1).
          rewrite -Nat2Z.inj_add /=.
          assert (ver' ≠ S ver) as Hne'.
          { intros ->. apply (Nat.Even_Odd_False ver).
            - rewrite -Nat.even_spec //.
            - rewrite -Nat.Even_succ -Nat.even_spec //. }
          rewrite bool_decide_eq_false_2; first last.
          { intros [=->%(inj Z.of_nat)]. lia. }
          wp_pures.
          iApply (already_linearized with "[$] [$] [$] [] [$] [Hcredit Hcredit'] [$]").
          { iApply (mono_nat_lb_own_le (S (S ver)) with "Hlb"). lia. }
          by iCombine "Hcredit Hcredit'" as "?".
        * iDestruct "Hlock" as "(Hγ & Hγᵥ & Hdst)".
          iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
          iClear "Hlb".
          iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
          iMod ("Hcl" with "[-Hsrc Hγₜ Hcredit]") as "_".
          { iFrame. rewrite Heven'. iFrame "∗ %". }
          iModIntro.
          wp_pure credit:"Hcredit'".
          wp_pures.
          destruct (decide (ver' = S ver)) as [-> | Hne'].
          { rewrite bool_decide_eq_true_2; first last.
            { f_equal. change 1%Z with (Z.of_nat 1). rewrite -Nat2Z.inj_add //. }
            wp_pures.
            wp_apply wp_fupd.
            wp_apply (wp_loop_while with "[$] [$]").
            iClear "Hlb".
            iIntros (ver') "[%Hless #Hlb]".
            iApply (already_linearized with "[$] [$] [$] [] [$] [Hcredit Hcredit'] [$]").
            { iApply (mono_nat_lb_own_le (S (S ver)) with "Hlb"). lia. }
            by iCombine "Hcredit Hcredit'" as "?". }
          { rewrite bool_decide_eq_false_2; first last.
            { change 1%Z with (Z.of_nat 1). intros [=Heq]. rewrite -Nat2Z.inj_add in Heq. simplify_eq. }
            wp_pures.
            iApply (already_linearized with "[$] [$] [$] [] [$] [Hcredit Hcredit'] [$]").
            { iApply (mono_nat_lb_own_le (S (S ver)) with "Hlb"). lia. }
            by iCombine "Hcredit Hcredit'" as "?". }
    - iDestruct "Hlock" as "(Hγ & Hγᵥ & Hdst)".
      iDestruct (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-Hsrc Hγₜ Hcredit]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs, (registry ++ [(γₗ, S (Nat.div2 ver))]). rewrite Heven. iFrame "∗ #".
        rewrite bool_decide_eq_true_2.
        - simpl. by iFrame.
        - lia. }
      iModIntro.
      wp_pure credit:"Hcredit'".
      wp_pures.
      rewrite bool_decide_eq_true_2; first last.
      { repeat f_equal. rewrite Zrem_odd odd_inj. rewrite Z.sgn_pos.
        - rewrite even_odd_negb /= in Heven. rewrite Heven //.
        - by destruct ver. }
      wp_pures.
      wp_apply wp_fupd.
      wp_apply (wp_loop_while with "[$] [$]").
      iClear "Hlb".
      iIntros (ver') "[%Hless #Hlb]".
      destruct ver as [| ver].
      { discriminate. }
      rewrite -Nat.Even_div2; first last.
      { rewrite -Nat.Odd_succ -Nat.odd_spec odd_even_negb //. }
      iApply (already_linearized with "[$] [$] [$] [] [$] [Hcredit Hcredit'] [$]").
      { iApply (mono_nat_lb_own_le (S (S ver)) with "Hlb"). lia. }
      by iCombine "Hcredit Hcredit'" as "?".
  Qed.

  Lemma read_spec (γ : gname) (v : val) (n : nat) :
    n > 0 →
      is_seqlock v γ n -∗
        <<{ ∀∀ vs, value γ vs  }>> 
          read n v @ ↑N
        <<{ ∃∃ copy : loc, value γ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
    iIntros "%Hpos (%src & %γₕ & %γᵥ & %γᵣ & -> & #Hinv) %Φ AU".
    iLöb as "IH".
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv seqlockN as "(%ver & %history & %vs & %registry & Hreg & Hreginv & >Hver & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    wp_load.
    destruct (Nat.even ver) eqn:Hparity.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons)".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod (history_frag_alloc with "Hγₕ") as "[H● #H◯]".
      { by rewrite last_lookup in Hcons. }
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. rewrite Hparity. by iFrame. }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_false_2; first last.
      { rewrite Zrem_even even_inj Hparity //. }
      wp_pures.
      wp_smart_apply (wp_array_clone_wk with "[//] [//] [//]").
      { done. }
      iIntros (vers vdst dst) "(Hdst & %Hlen' & %Hsorted & %Hbound & Hcons)".
      wp_pures.
      wp_bind (! _)%E.
      iInv seqlockN as "(%ver' & %history' & %vs' & %registry' & Hreg & Hreginv & >Hver & >%Hlen'' & >%Hhistory' & Hlock)" "Hcl".
      destruct (decide (ver = ver')) as [<- | Hne].
      + rewrite Hparity.
        iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons')".
        rewrite /history_frag_own.
        iPoseProof (history_auth_frag_agree with "Hγₕ H◯") as "%Hlookup".
        rewrite last_lookup Hhistory' /= in Hcons'.
        rewrite Hhistory /=.
        rewrite Hhistory /= in Hlookup.
        assert (Some vs = Some vs') as [=<-].
        { by rewrite -Hlookup -Hcons'. }
        clear Hcons'. simplify_eq.
        iAssert (⌜vs = vdst⌝)%I with "[Hcons Hγᵥ]" as "<-".
        { iClear "IH".
          iApply pure_mono.
          { by apply list_eq_same_length. }
          rewrite big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver' Hver']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb' #Hfrag]".
          assert (ver ≤ ver') as Hle by (by eapply Forall_lookup).
          iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb'") as "[%Hq %Hge]".
          assert (ver = ver') as <- by lia.
          clear Hle Hge.
          iPoseProof ("Hfrag" with "[]") as "(%vs' & #Hvs' & %Hlookup')".
          { by rewrite -Nat.even_spec. }
          iCombine "H◯ Hvs'" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as <-.
          iPureIntro. apply (inj Some). by rewrite -Hv -Hlookup'. }
        wp_load.
        iMod "AU" as (vs') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ <-].
        iMod ("Hconsume" $! dst with "[$Hγ']") as "HΦ".
        iMod ("Hcl" with "[-HΦ Hdst]") as "_".
        { rewrite /seqlock_inv.
          iExists ver, history', vs. rewrite Hparity. iFrame "∗ %".
          iPureIntro. rewrite last_lookup. by rewrite Hhistory'. }
        iModIntro. wp_pures. rewrite bool_decide_eq_true_2; last done.
        wp_pures. iModIntro. by iApply "HΦ".
      + destruct (Nat.even ver') eqn:Hparity'''.
        * iMod "Hlock" as "(Hversion & Hsrc & History)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /seqlock_inv.
            iExists ver', history', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
        * iDestruct "Hlock" as "(Hversion & Hsrc)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /seqlock_inv.
            iExists ver', history', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
    - iDestruct "Hlock" as "(Hγₕ & Hγᵥ & Hsrc)".
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /seqlock_inv.
        iExists ver, history, vs. rewrite Hparity. by iFrame "∗ %". }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_true_2; first last.
      { rewrite Zrem_even even_inj Hparity. by destruct ver. }
      wp_pures.
      iApply ("IH" with "AU").
  Qed.

End seqlock.
