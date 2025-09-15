From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap gset list lib.mono_nat.
From iris.heap_lang Require Import lang proofmode notation lib.array.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
Import derived_laws.bi.
Require Import  Coq.ZArith.Zquot.
Require Import stdpp.gmap.
Require Import iris.bi.interface.

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
    let: "dst" := AllocN #(S (S n)) #0 in
    "dst" +ₗ #1 <- (#true, array_clone "src" #n);;
    array_copy_to ("dst" +ₗ #2) "src" #n;;
    "dst".

Definition read' (n : nat) : val :=
  λ: "l",
    let: "ver" := !"l" in
    let: "data" := array_clone ("l" +ₗ #2) #n in
    let: "p" := NewProph in
    let: "backup" := !("l" +ₗ #1) in
    if: (Fst "backup") && Resolve (!"l" = "ver") "p" #() then
      ("data", "backup", "ver")
    else
      (array_clone (Snd "backup") #n, "backup", "ver").

Definition read (n : nat) : val := λ: "l", Fst (Fst (read' n "l")).

Definition array_equal : val :=
  rec: "array_equal" "l" "l'" "n" :=
    if: "n" ≤ #0 then #true
    else
      (!"l" = !"l'") && ("array_equal" ("l" +ₗ #1) ("l'" +ₗ #1) ("n" - #1)).

Definition cas (n : nat) : val :=
  λ: "l" "expected" "desired",
    let: "old" := read' n "l" in
    if: array_equal (Fst (Fst "old")) "expected" then 
      if: array_equal "expected" "desired" then #true
      else
        let: "backup'" := (#false, array_clone "desired" #n) in
        let: "backup" := (Snd (Fst "old")) in
        if: CAS ("l" +ₗ #1) "backup" "backup'" || CAS ("l" +ₗ #1) (#true, Snd "backup") "backup'" then
          let: "ver" := Snd "old" in
          if: "ver" `rem` #2 = #0 && CAS "l" "ver" (#1 + "ver") then
            (* Lock was successful *)
            (* Perform update *)
            array_copy_to ("l" +ₗ #2) "desired" #n;;
            (* Unlock *)
            "l" <- #2 + "ver";;
            CmpXchg ("l" +ₗ #1) "backup'" (#true, Snd "backup'");;
            #true
          else #true
        else #false
    else #false.

Definition log := gmap nat $ agree $ (loc * list val)%type.

Definition index := gmap nat $ agree nat.

Definition indexUR := authUR $ gmapUR nat (agreeR locO).

Definition logUR := authUR $ gmapUR loc $ agreeR $ (prodO gnameO (listO valO)).

Definition requestReg := gmap nat $ agree (gname * gname * loc).
Definition requestRegUR := authUR $ gmapUR nat $ agreeR $ prodO (prodO gnameO gnameO) locO.

Definition usedUR := authUR $ gsetUR $ locO.

Class cached_wfG (Σ : gFunctors) := {
  cached_wf_heapGS :: heapGS Σ;
  cached_wf_logUR :: inG Σ logUR;
  cached_wf_indexUR :: inG Σ indexUR;
  cached_wf_usedUR :: inG Σ usedUR;
  cached_wf_requestRegUR :: inG Σ requestRegUR;
  cached_wf_mono_natG :: mono_natG Σ;
  cached_wf_ghost_varG_vals :: ghost_varG Σ (list val);
  cached_wf_ghost_varG_bool :: ghost_varG Σ bool;
  cached_wf_tokenG :: tokenG Σ;
}.

Section cached_wf.
  Context `{!cached_wfG Σ, !heapGS Σ}.

  Lemma wp_array_equal (l l' : loc) (dq dq' : dfrac) (vs vs' : list val) :
    length vs = length vs' → Forall2 vals_compare_safe vs vs' →
    {{{ l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}
      array_equal #l #l' #(length vs)
    {{{ RET #(bool_decide (vs = vs')); l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}.
  Proof.
    iIntros (Hlen Hsafe Φ) "[Hl Hl'] HΦ".
    iInduction vs as [|v vs] "IH" forall (l l' vs' Hsafe Hlen) "HΦ".
    - wp_rec. wp_pures.
      apply symmetry, length_zero_iff_nil in Hlen as ->.
      iModIntro.
      rewrite bool_decide_eq_true_2; last done.
      iApply "HΦ". iFrame.
    - wp_rec. wp_pures.
      destruct vs' as [| v' vs']; first discriminate.
      inv Hlen. inv Hsafe.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hlrest]".
      iDestruct "Hl'" as "[Hl' Hlrest']".
      do 2 wp_load.
      wp_pures.
      destruct (decide (v = v')) as [-> | Hne].
      + rewrite (bool_decide_eq_true_2 (v' = v')); last done.
        wp_pures.
        rewrite Z.sub_1_r.
        rewrite -Nat2Z.inj_pred /=; last lia.
        iApply ("IH" $! _ _ vs' with "[//] [//] [$] [$]").
        iIntros "!> [Hlrest Hlrest']".
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne].
        * rewrite bool_decide_eq_true_2; last done.
          by rewrite bool_decide_eq_true_2.
        * rewrite bool_decide_eq_false_2.
          -- by rewrite bool_decide_eq_false_2.
          -- by intros [=].
      + rewrite (bool_decide_eq_false_2 (v = v')); last done.
        wp_pures.
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne'];
        rewrite bool_decide_eq_false_2; auto; by intros [=].
  Qed.

  Context (N : namespace).

  Definition cached_wfN := N .@ "cached_wf".

  Definition casN := N .@ "write".

  Definition index_auth_own γᵢ (q : Qp) (index : list loc) := own γᵢ (●{#q} map_seq 0 (to_agree <$> index)).

  Definition log_auth_own γᵥ (q : Qp) (log : gmap loc (gname * list val)) := own γᵥ (●{#q} (@fmap _ gmap_fmap _ _ to_agree log)).

  Definition value γᵥ (vs : list val) : iProp Σ := ghost_var γᵥ (1/2) vs.

  Definition log_frag_own γₕ l γ (value : list val) := own γₕ (◯ {[l := to_agree (γ, value)]}).

  Definition index_frag_own γᵢ (i : nat) (l : loc) := own γᵢ (◯ {[i := to_agree l]}).

  Lemma index_auth_update (l : loc) γ (index : list loc) :
    index_auth_own γ 1 index ==∗
      index_auth_own γ 1 (index ++ [l]) ∗ index_frag_own γ (length index) l.
  Proof.
    iIntros "H●".
    rewrite /index_auth_own /index_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length index)
          (x := to_agree l).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length index) with (O + length (to_agree <$> index)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma index_frag_alloc i l γ index q :
    index !! i = Some l →
      index_auth_own γ q index ==∗
        index_auth_own γ q index ∗ index_frag_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma log_auth_update (l : loc) (value : list val) (γ γₕ : gname) (log : gmap loc (gname * list val)) :
    log !! l = None →
      log_auth_own γₕ 1 log ==∗
        log_auth_own γₕ 1 (<[l := (γ, value)]>log) ∗ log_frag_own γₕ l γ value.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := l)
          (x := to_agree (γ, value)).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite fmap_insert.
    by iFrame.
  Qed.

  Lemma log_frag_alloc i γ value γₕ log q :
    log !! i = Some (γ, value) →
      log_auth_own γₕ q log ==∗
        log_auth_own γₕ q log ∗ log_frag_own γₕ i γ value.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree (γ, value)]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree (γ, value)). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma log_auth_frag_agree γₕ q log i γ value : 
    log_auth_own γₕ q log -∗
      log_frag_own γₕ i γ value -∗
        ⌜log !! i = Some (γ, value)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

Lemma index_auth_frag_agree (γ : gname) (i : nat) (l : loc) (index : list loc) : 
    index_auth_own γ 1 index -∗
      index_frag_own γ i l -∗
        ⌜index !! i = Some l⌝.
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

  Definition registry γᵣ (requests : list (gname * gname * loc)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γᵣ i (γₗ γₑ : gname) (l : loc) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, γₑ, l)]})).

  Lemma registry_update γₗ γₑ l γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(γₗ, γₑ, l)]) ∗ registered γ (length requests) γₗ γₑ l.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (γₗ, γₑ, l)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree γᵣ (requests : list (gname * gname * loc)) (i : nat) γₗ γₑ ver :
    registry γᵣ requests -∗
      registered γᵣ i γₗ γₑ ver -∗
        ⌜requests !! i = Some (γₗ, γₑ, ver)⌝.
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

  Definition AU_cas (Φ : val → iProp Σ) γ (expected desired : list val) (lexp ldes : loc) dq dq' : iProp Σ :=
       AU <{ ∃∃ actual : list val, value γ actual }>
            @ ⊤ ∖ ↑N, ∅
          <{ if bool_decide (actual = expected) then value γ desired else value γ actual,
             COMM lexp ↦∗{dq} expected -∗ ldes ↦∗{dq'} desired -∗ Φ #(bool_decide (actual = expected)) }>.

  Definition cas_inv (Φ : val → iProp Σ) (γ γₑ γₗ γₜ : gname) (lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) : iProp Σ :=
      ((lexp ↦∗{dq} expected -∗ ldes ↦∗{dq'} desired -∗ Φ #false) ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ghost_var γₗ (1/2) false) (* The failing write has already been linearized and its atomic update has been consumed *)
    ∨ (£ 1 ∗ AU_cas Φ γ expected desired lexp ldes dq dq' ∗ ghost_var γₑ (1/2) true ∗ ghost_var γₗ (1/2) true)
    ∨ (token γₜ ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ∃ b : bool, ghost_var γₗ (1/2) b).  (* The failing write has linearized and returned *)

  Definition log_points_to (n : nat) (log : gmap loc (gname * list val)) : iProp Σ :=
    ([∗ map] _ ↦ '(γ, value) ∈ log, token γ ∗ ⌜length value = n⌝)%I.

  Lemma log_points_to_impl log l γ value n :
    log !! l = Some (γ, value) →
    log_points_to n log -∗
    token γ ∗ ⌜length value = n⌝.
  Proof.
    iIntros (Hbound) "Hlog".
    iPoseProof (big_sepM_lookup with "Hlog") as "H /=".
    { done. }
    done. 
  Qed.

  Lemma log_points_to_singleton l γ value n :
    log_points_to n {[ l := (γ, value) ]} ⊣⊢ token γ ∗ ⌜length value = n⌝.
  Proof.
    iSplit.
    - iIntros "Hlog". iApply (@big_sepM_singleton (iProp Σ) _ _ _ _ (λ _ '(γ, value), token γ ∗ ⌜length value = n⌝)%I l (γ, value) with "Hlog").
    - iIntros "[Htok %Hlen]". iApply (@big_sepM_singleton (iProp Σ) _ _ _ _ (λ _ '(γ, value), token γ ∗ ⌜length value = n⌝)%I l (γ, value) with "[-]").
      { iFrame "% ∗". }
  Qed.

  Definition request_inv γ γₗ γₑ (lactual lexp : loc) (actual : list val) (used : gset loc) : iProp Σ :=
    ⌜lexp ∈ used⌝ ∗
    ghost_var γₗ (1/2) (bool_decide (lactual = lexp)) ∗
    ∃ (Φ : val → iProp Σ) (γₜ : gname) (ldes : loc) (dq dq' : dfrac) (expected desired : list val),
      ghost_var γₑ (1/2) (bool_decide (actual = expected)) ∗
      inv casN (cas_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired).

  Definition registry_inv γ lactual actual (requests : list (gname * gname * loc)) (used : gset loc) : iProp Σ :=
    [∗ list] '(γₗ, γₑ, lexp) ∈ requests,
    
    request_inv γ γₗ γₑ lactual lexp actual used.
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

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
  Lemma linearize_cas γ (ver : nat) (lactual lactual' : loc) (actual actual' : list val) requests (log : gmap loc (gname * list val)) (γₜ : gname) :
    length actual > 0 →
    (* The current and previous logical state should be distinct if swapping backup pointer *)
    actual ≠ actual' →
    (* Both the current and new logical state are comprised of the same number of bytes *)
    length actual = length actual' → 
    (* The current backup pointer has been logged *)
    fst <$> log !! lactual' = Some γₜ →
    (* Points-to predicate of every previously logged backup *)
    log_points_to (length actual) log -∗
    (* Physical state of backup *)
    token γₜ -∗
    (* The logical state has not yet been updated to the new state *)
    ghost_var γ (1/2) actual' -∗
    (* The registry invariant is satisfied for the current logical state *)
    registry_inv γ lactual actual requests (dom log)
    (* We can take frame-preserving updated that linearize the successful CAS,
       alongside all of the other failing CAS's *)
    ={⊤ ∖ ↑cached_wfN}=∗
      (* Points-to predicate of every previously logged backup *)
      log_points_to (length actual) log ∗
      (* Return ownership of token *)
      token γₜ ∗
      (* Update new logical state to correspond to logical CAS *)
      ghost_var γ (1/2) actual' ∗
      (* Invariant corresponding to new logical state *)
      registry_inv γ lactual' actual' requests (dom log).
  Proof.
    iIntros (Hpos Hne Hlen Hlogged) "Hlog Hγₜ Hγ Hreqs".
    iInduction requests as [|[[γₗ γₑ] lexp] reqs'] "IH".
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(%Hfresh & Hlin & %Φ & %γₜ' & %ldes & %dq & %dq' & %expected & %desired & Hγₑ & #Hwinv) Hreqs']".
      iMod ("IH" with "Hlog Hγₜ Hγ Hreqs'") as "(Hlog & Hactual & Hγ & Hreqinv)".
      iInv casN as "[(HΦ & [%b >Hγₑ'] & >Hlin') | [(>Hcredit & AU & >Hγₑ' & >Hlin') | (>Htok & [%b >Hγₑ'] & [%b' >Hlin'])]]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ ->].
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']". 
        (* rewrite bool_decide_eq_false in Hneq. *)
        iMod ("Hclose" with "[HΦ Hγₑ Hlin]") as "_".
        { iLeft. iFrame. }
        destruct (decide (lactual' = lexp)) as [-> | Hneq].
        * apply elem_of_dom in Hfresh as [[γₜ'' value] Hvalue].
          iPoseProof (log_points_to_impl with "Hlog") as "[Hactual' %Hlen']".
          { done. }
          rewrite -lookup_fmap lookup_fmap_Some in Hlogged.
          destruct Hlogged as ([γₜ''' vs] & Heq & Hlookup).
          simplify_eq. simpl. iCombine "Hactual Hactual'" gives %[].
        * iFrame "∗ # %".
          rewrite /request_inv.
          replace (bool_decide (lactual' = lexp)) with false.
          { by iFrame. }
          { by rewrite bool_decide_eq_false_2. }
      + iCombine "Hlin Hlin'" gives %[_ ->%bool_decide_eq_true].
        iCombine "Hγₑ Hγₑ'" gives %[_ ->%bool_decide_eq_true].
        iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (actual'') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ <-].
        rewrite (bool_decide_eq_false_2 (actual' = expected)); last done.
        destruct (decide (lactual' = lexp)) as [-> | Hdiff].
        * apply elem_of_dom in Hfresh as [[γₜ'' value] Hvalue].
          iPoseProof (log_points_to_impl with "Hlog") as "[Hactual' %Hlen']".
          { done. }
          rewrite -lookup_fmap lookup_fmap_Some in Hlogged.
          destruct Hlogged as ([γₜ''' vs] & Heq & Hlookup).
          simplify_eq. simpl. iCombine "Hactual Hactual'" gives %[].
        * iFrame "∗ # %".
          rewrite (bool_decide_eq_false_2 (lactual' = lexp)); last done.
          iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
          iMod ("Hconsume" with "[$]") as "HΦ".
          iFrame.
          iMod ("Hclose" with "[-]") as "_".
          { iLeft. iFrame. }
          done.
      + iMod (ghost_var_update_halves (bool_decide (lactual' = lexp)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        iFrame "∗ # %".
        iMod ("Hclose" with "[-]") as "_".
        { do 2 iRight. iFrame. }
        done.
  Qed.

  Definition cached_wf_inv (γ γᵥ γₕ γᵣ γᵢ : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (log : gmap loc (gname * list val)) (actual cache : list val) (valid : bool) (backup backup' : loc) requests (index : list loc),
      (* Physical state of version *)
      l ↦ #ver ∗
      (* backup, consisting of boolean to indicate whether cache is valid, and the backup pointer itself *)
      (l +ₗ 1) ↦ (#valid, #backup)%V ∗
      (* Half ownership of logical state *)
      ghost_var γ (1/2) actual ∗
      (* Shared read ownerhip of backup *)
      backup ↦∗□ actual ∗
      (* The most recent version is associated with some other backup pointer *)
      ⌜last index = Some backup'⌝ ∗
      (* If the backup is validated, then the cache is unlocked, the logical state is equal to the cache,
         and the backup pointer corresponding to the most recent version is up to date *)
      ⌜if valid then Nat.Even ver ∧ actual = cache ∧ backup = backup' else True⌝ ∗
      registry γᵣ requests ∗
      (* State of request registry *)
      registry_inv γ (l +ₗ 1) actual requests (dom log) ∗
      (* Big atomic is of fixed size *)
      ⌜length actual = len⌝ ∗ 
      ⌜length cache = len⌝ ∗
      (* The version number is twice (or one greater than twice) than number of versions *)
      (* For every pair of (backup', cache') in the log, we have ownership of the corresponding points-to *)
      log_points_to (length actual) log ∗
      (* The last item in the log corresponds to the currently installed backup pointer *)
      ⌜snd <$> log !! backup = Some actual⌝ ∗
      (* Store full authoritative ownership of the log in the invariant *)
      log_auth_own γₕ 1 log ∗
      (* The is a mapping in the index for every version *)
      ⌜length index = S (Nat.div2 ver)⌝ ∗
      (* Because the mapping from versions to log entries is injective, the index should not contain duplicates *)
      ⌜NoDup index⌝ ∗
      (* Moreover, every index should be less than the length of the log (to ensure every version
         corresponds to a valid entry) *)
      ⌜Forall (λ l, l ∈ dom log) index⌝ ∗
      if Nat.even ver then 
        (* If sequence number is even, then unlocked *)
        (* Full ownership of points-to pred in invariant *)
        (* And the logical state consistent with physical state *)
        index_auth_own γᵢ 1 index ∗ mono_nat_auth_own γᵥ 1 ver ∗ ⌜snd <$> log !! backup' = Some cache⌝ ∗ (l +ₗ 2) ↦∗ cache
      else 
        (* If locked, have only read-only access to ensure one updater *)
        index_auth_own γᵢ (1/2) index ∗ mono_nat_auth_own γᵥ (1/2) ver ∗ (l +ₗ 2) ↦∗{# 1/2} cache ∗ ⌜valid = false⌝.

  Global Instance pointsto_array_persistent l vs : Persistent (l ↦∗□ vs).
  Proof.
    rewrite /Persistent.
    iIntros "P".
    iInduction vs as [|v vs] "IH" forall (l).
    - rewrite array_nil. by iModIntro.
    - rewrite array_cons.
      iDestruct "P" as "[#Hl Hrest]".
      iPoseProof ("IH" with "Hrest") as "Hvs".
      by iFrame "#".
  Qed.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵣ γᵢ (dst src : loc) (n i : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    i ≤ n → length vdst = n - i →
      inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ 2 +ₗ i) #(n - i)
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
                    ∃ l γₜ vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ l γₜ vs ∗
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
      iInv cached_wfN as "(%ver' & %log & %actual & %cache & %valid & %backup & %backup' & %requests & %index & >Hver & >Hbackup & >Hγ & >#□Hbackup & >%Hindex & >%Hvalidated & >Hregistry & Hreginv & >%Hlenactual & >%Hlencache & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & Hlock)" "Hcl".
      destruct (Nat.even ver') eqn:Heven.
      + iMod "Hlock" as "(Hγᵢ & Hγᵥ & %Hbackup & Hcache)".
        wp_apply (wp_load_offset with "Hcache").
        { apply list_lookup_lookup_total_lt. lia. }
        iMod (index_frag_alloc with "Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
        { by rewrite last_lookup Hlenᵢ /= in Hindex. }
        (* apply Forall_lookup_1 with (i := Nat.div2 ver') (x := l) in Hrange as Hldom; last done. *)
        (* apply elem_of_dom in Hldom as [value Hvalue]. *)
        rewrite -lookup_fmap lookup_fmap_Some in Hbackup.
        destruct Hbackup as ([γₜ vs] & <- & Hlookup).
        iMod (log_frag_alloc backup' γₜ vs with "●Hlog") as "[●Hlog #◯Hlog]".
        { done. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { rewrite /cached_wf_inv. simpl in *.
          iExists ver', log, actual, vs, valid, backup, backup', requests, index.
          iFrame "∗ # %". rewrite Heven. iFrame "∗ %". iIntros "!> !%".
          rewrite -lookup_fmap lookup_fmap_Some. by exists (γₜ, vs). }
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
            iIntros "%Heven'".
            iExists backup', _.
            iFrame "∗ # %".
            rewrite Nat.add_0_r.
            rewrite list_lookup_lookup_total_lt; first done.
            simpl in *. lia.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
      + iDestruct "Hlock" as ">(Hγₕ & Hγᵥ & Hsrc & Hinvalid)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists ver', log, actual, cache, valid, backup, backup', requests, index. iFrame "∗ # %".
          rewrite Heven. iFrame "∗ # %". }
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
            iIntros "%Heven'". congruence.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma log_auth_auth_agree γₕ p q (log log' : gmap loc (gname * list val)) :
    log_auth_own γₕ p log -∗
      log_auth_own γₕ q log'  -∗
        ⌜log = log'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma wp_array_copy_to_wk γ γᵥ γₕ γᵣ γᵢ (dst src : loc) (n : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    length vdst = n →
      inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ 2) #n
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
                    ∃ l γₜ vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ l γₜ vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝ ))}}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ 2)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.

  Lemma wp_array_clone_wk γ γᵥ γₕ γᵣ γᵢ (src : loc) (n : nat) ver :
    n > 0 →
      inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ 2) #n
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
                    ∃ l γₜ vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ l γₜ vs ∗
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

  Lemma wp_array_copy_to_half' γ γᵥ γₕ γᵣ γᵢ dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ dst n) -∗
          {{{ (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 2 +ₗ i) #(src +ₗ i) #(n - i)%nat
          {{{ RET #(); (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
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
      iInv cached_wfN as "(%ver & %log & %actual & %cache & %valid & %backup & %backup' & %requests & %index & >Hver & >Hbackup & >Hγ & □Hbackup & >%Hindex & >%Hvalidated & >Hregistry & Hreginv & >%Hlenactual & >%Hlencache & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & Hlock)" "Hcl".
      assert (i < length cache) as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγᵢ & Hγᵥ & %Hbackup & Hcache) /=".
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache _]".
        { done. }
        by iCombine "Hdst Hcache" gives %[Hfrac%dfrac_valid_own_r <-].
      + iMod "Hlock" as "(Hγᵢ & Hγᵥ & Hcache & ->)".
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache Hacc]".
        { done. }
        iCombine "Hdst Hcache" as "Hcache".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hcache" as "[Hcache Hcache']".
        iPoseProof ("Hacc" with "Hcache") as "Hcache".
        (* $Hregistry $Hreginv $Hver Hγᵢ Hγᵥ Hcache *)
        iMod ("Hcl" with "[-Hcache' Hdst' Hsrc Hsrc' HΦ]") as "_".
        { iExists ver, log, actual, (<[i:=v']> cache), false, backup, backup', requests, index.
          iFrame "∗ # %".
          rewrite Heven. iFrame.
          iNext. iSplit; last done.
          by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
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
          rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma wp_array_copy_to_half γ γᵥ γₕ γᵣ γᵢ dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ dst n) -∗
          {{{ (dst +ₗ 2) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 2) #src #n
          {{{ RET #(); (dst +ₗ 2) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ 2)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (wp_array_copy_to_half' _ _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
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

  Definition is_cached_wf (v : val) (γ : gname) (n : nat) : iProp Σ :=
    ∃ (dst : loc) (γₕ γᵥ γᵣ γᵢ : gname),
      ⌜v = #dst⌝ ∗ inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ dst n).

  Lemma array_persist l vs : l ↦∗ vs ==∗ l ↦∗□ vs.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l).
    - by iIntros.
    - do 2 rewrite array_cons. iIntros "[Hl Hrest]".
      iSplitL "Hl".
      + iApply (pointsto_persist with "Hl").
      + iApply ("IH" with "Hrest").
  Qed.

  Lemma new_big_atomic_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        new_big_atomic n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ is_cached_wf v γ n ∗ value γ vs  }}}.
  Proof.
    iIntros "%Hlen %Hpos %Φ Hsrc HΦ".
    wp_rec.
    wp_pures.
    wp_alloc l as "Hl".
    { done. }
    wp_pures.
    rewrite Nat2Z.id /= array_cons array_cons.
    iDestruct "Hl" as "(Hversion & Hvalidated & Hcache)".
    rewrite Loc.add_assoc /=.
    change (1 + 1)%Z with 2%Z.
    wp_apply (wp_array_clone with "Hsrc").
    { auto. }
    { lia. }
    iIntros (backup) "[Hbackup Hsrc]".
    wp_store.
    wp_smart_apply (wp_array_copy_to _ _ _ _ (replicate n #0) vs with "[$]").
    { by rewrite length_replicate. }
    { auto. }
    iIntros "[Hcache Hsrc]". wp_pures.
    iMod (ghost_var_alloc vs) as "(%γ & Hγ & Hγ')".
    iMod (mono_nat_own_alloc 0) as "(%γᵥ & Hγᵥ & _)".
    iMod (own_alloc (● map_seq O (to_agree <$> [backup]))) as "[%γᵢ Hγᵢ]".
    { by apply auth_auth_valid, singleton_valid. }
    iMod token_alloc as "[%γₜ Hγₜ]".
    iMod (own_alloc (● {[ backup := to_agree (γₜ, vs) ]})) as "[%γₕ Hγₕ]".
    { by apply auth_auth_valid, singleton_valid. }
    rewrite -map_fmap_singleton.
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γᵣ Hγᵣ]".
    { by apply auth_auth_valid. }
    iMod (array_persist with "Hbackup") as "Hbackup".
    iMod (inv_alloc cached_wfN _ (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ l n) with "[Hbackup $Hvalidated Hversion $Hγ' Hγᵥ Hγₕ $Hγᵣ Hγᵢ Hcache Hγₜ]") as "#Hinv".
    { rewrite /cached_wf_inv /registry_inv.
      iExists O, ({[backup := (γₜ, vs) ]}), vs, backup, [backup]. simpl. iFrame "∗ # %".
      iSplit; first done.
      iNext. iSplit.
      { iPureIntro. split.
        { rewrite -Nat.even_spec /= //. }
        { auto. } }
      iSplitL "Hγₜ".
      { rewrite log_points_to_singleton. by iFrame. }
      iSplit.
      { by rewrite lookup_singleton. }
      iSplit.
      { done. }
      iSplit.
      { iPureIntro. apply NoDup_singleton. }
      iSplit.
      { iPureIntro. rewrite Forall_singleton. set_solver. }
      by rewrite lookup_singleton. }
    iModIntro.
    iApply "HΦ".
    iFrame.
    rewrite /is_cached_wf.
    iExists _, _, _, _, _. by iFrame "#".
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

  Lemma twp_array_copy_to_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
      [[{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }]]
        array_copy_to #dst #src #n @ stk; E
      [[{ RET #(); dst ↦∗ vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". auto with iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 #Hsrc]".
    wp_load; wp_store.
    wp_smart_apply ("IH" with "[%] [%] Hdst Hsrc") as "Hvdst"; [ lia .. | ].
    iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_array_copy_to_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_copy_to_persistent with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_array_clone_persistent stk E l vl n :
    Z.of_nat (length vl) = n → (0 < n)%Z →
      [[{ l ↦∗□ vl }]]
        array_clone #l #n @ stk; E
      [[{ l', RET #l'; l' ↦∗ vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_smart_apply (twp_array_copy_to_persistent with "[$Hdst $Hvl]") as "Hdst".
    - rewrite length_replicate Z2Nat.id; lia.
    - auto.
    - wp_pures.
      iApply "HΦ". by iFrame.
  Qed.

  Definition extract_result (vs : list (val * val)) : option bool :=
    match vs with
    | (LitV (LitBool b), _) :: _ => Some b
    | _ => None
    end.

  Lemma wp_array_clone_persistent stk E l vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    {{{ l ↦∗□ vl }}}
      array_clone #l #n @ stk; E
    {{{ l', RET #l'; l' ↦∗ vl }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_clone_persistent with "H"); [auto..|]; iIntros (l') "H HΦ". by iApply "HΦ".
  Qed.

  Lemma read'_spec (γ γᵥ γₕ γᵣ γᵢ : gname) (l : loc) (n : nat) :
    n > 0 →
      inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵣ γᵢ l n) -∗
        <<{ ∀∀ vs, value γ vs  }>> 
          read' n #l @ ↑N
        <<{ ∃∃ (valid : bool) (copy backup : loc) (ver : nat) (γₜ : gname), value γ vs | 
            RET (#copy, (#valid, #backup), #ver)%V; 
            copy ↦∗ vs ∗ log_frag_own γₕ backup γₜ vs ∗ if valid then index_frag_own γᵢ (Nat.div2 ver) backup else True }>>.
  Proof.
    iIntros (Hpos) "#Hinv %Φ AU".
    wp_rec.
    wp_bind (! _)%E.
    iInv cached_wfN as "(%ver & %log & %actual & %cache & %valid & %backup & %backup' & %requests & %index & >Hver & >Hbackup & >Hγ & >#□Hbackup & >%Hindex & >%Hvalidated & >Hregistry & Hreginv & >%Hlenactual & >%Hlencache & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & Hlock)" "Hcl".
    wp_load.
    destruct (Nat.even ver) eqn:Heven.
    - iDestruct "Hlock" as "(Hγᵢ & Hγᵥ & %Hunlocked & Hcache)".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      pose proof Hunlocked as Hunlocked'.
      rewrite -lookup_fmap lookup_fmap_Some in Hunlocked'.
      destruct Hunlocked' as ([γₜ vs] & Hcons & Hbackup'logged).
      iMod (log_frag_alloc with "●Hlog") as "[●Hlog #◯Hlog]".
      { eauto. }
      iMod (index_frag_alloc with "Hγᵢ") as "[●Hindex #◯Hindex]".
      { by rewrite last_lookup Hlenᵢ /= in Hindex. }
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver, log, actual, cache, valid, backup, backup', requests, index.
        rewrite Heven. iFrame "∗ # %". }
      iModIntro.
      wp_pures.
      wp_smart_apply (wp_array_clone_wk with "[//] [//] [//]").
      { done. }
      iIntros (vers vdst dst) "(Hdst & %Hlen' & %Hsorted & %Hbound & Hcons)".
      wp_pures.
      wp_apply wp_new_proph.
      { done. }
      iIntros (pvs p) "Hproph".
      wp_pures.
      wp_bind (! _)%E.
      iInv cached_wfN as "(%ver' & %log' & %actual' & %cache' & %valid' & %backup₁ & %backup₁' & %requests' & %index' & >Hver & >Hbackup & >Hγ & >#□Hbackup₁ & >%Hindex' & >%Hvalidated' & >Hregistry & Hreginv & >%Hlenactual' & >%Hlencache' & Hlog & >%Hlogged' & >●Hlog & >%Hlenᵢ' & >%Hnodup' & >%Hrange' & Hlock)" "Hcl".
      wp_load.
      iMod "AU" as (vs') "[Hγ' [_ Hconsume]]".
      iCombine "Hγ Hγ'" gives %[_ <-].
      destruct (extract_result pvs) as [[|]|] eqn:Hres.
      + destruct valid'.
        { iMod ("Hconsume" $! true dst backup₁ ver γₜ with "Hγ'") as "HΦ".
          destruct (decide (ver = ver')) as [<- | Hne]. 
          - rewrite Heven.
            iDestruct "Hlock" as "(Hγᵢ & Hγᵥ & %Hunlocked' & Hcache)".
            rewrite /log_frag_own.
            iPoseProof (log_auth_frag_agree with "●Hlog ◯Hlog") as "%Hlookup".
            destruct Hvalidated' as (_ & <- & <-).
            rewrite last_lookup Hlenᵢ' /= in Hindex'.
            iAssert (⌜cache = vdst⌝)%I with "[Hcons Hγᵥ]" as "<-".
            { iApply pure_mono.
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
              iPoseProof ("Hfrag" with "[]") as "(%l' & %γₜ' & %vs' & #◯Hindex' & #◯Hlog' & %Hlookup')".
              { by rewrite -Nat.even_spec. }
              iCombine "◯Hindex ◯Hindex'" gives %Hvalid%auth_frag_op_valid_1.
              rewrite singleton_op singleton_valid in Hvalid.
              apply to_agree_op_inv_L in Hvalid as <-.
              iCombine "◯Hlog ◯Hlog'" gives %Hvalid%auth_frag_op_valid_1.
              rewrite singleton_op singleton_valid in Hvalid.
              apply to_agree_op_inv_L in Hvalid as [=<-<-].
              simplify_eq. iPureIntro. apply (inj Some). by rewrite -Hv -Hlookup'. }
            rewrite last_lookup Hlenᵢ /= in Hindex.
            iDestruct (index_auth_frag_agree with "Hγᵢ ◯Hindex") as "%H".
            simplify_eq.
            iMod ("Hcl" with "[-HΦ Hdst Hproph]") as "_".
            { iExists ver, log', actual', actual', true, backup₁, backup₁, requests', index'.
              iFrame "∗ # %". rewrite last_lookup Hlenᵢ' Heven /=. iFrame "∗ # %".
              iIntros "!> !%". split; last done. by rewrite -Nat.even_spec. }
            iModIntro.
            wp_pures.
            wp_bind (! _)%E.
            iInv cached_wfN as "(%ver' & %log'' & %actual'' & %cache' & %valid' & %backup₂ & %backup₂' & %requests'' & %index'' & >Hver & >Hbackup & >Hγ & >#□Hbackup₂ & >%Hindex'' & >%Hvalidated'' & >Hregistry & Hreginv & >%Hlenactual'' & >%Hlencache'' & Hlog & >%Hlogged'' & >●Hlog & >%Hlenᵢ'' & >%Hnodup'' & >%Hrange'' & Hlock)" "Hcl".
            wp_load.
            iMod ("Hcl" with "[-HΦ Hdst Hproph]") as "_".
            { iExists ver', log'', actual'', cache', valid', backup₂, backup₂', requests'', index''.
              iFrame "∗ # %". }
            iModIntro.
            wp_pures.
            destruct (decide (ver' = ver)) as [<- | Hne].
            { wp_pures.
              wp_apply (wp_resolve with "Hproph").
              { done. }
              wp_pures.
              iModIntro. 
              rewrite bool_decide_eq_true_2; last done.
              iIntros (pvs' ->) "Hproph".
              wp_pures. iModIntro. iApply "HΦ". simpl in *. iFrame "∗ #".
              rewrite -lookup_fmap lookup_fmap_Some in Hlogged'.
              destruct Hlogged' as ([γ' vs'] & ? & ?). simpl in *. simplify_eq.
              assert ((γ', actual') = (γₜ, vs)) as [=->->].
              { apply (inj Some). by etransitivity. }
              by iFrame "∗ %". }
            { wp_pures.
              wp_apply (wp_resolve with "Hproph").
              { done. }
              wp_pures.
              iModIntro.
              iIntros (pvs' ->) "Hproph".
              simpl in *.
              simplify_eq.
              rewrite bool_decide_eq_true in Hres.
              simplify_eq. }
          - iAssert (⌜ver < ver'⌝ ∗ mono_nat_lb_own γᵥ ver')%I as "[%Hless #Hlb']".
            { destruct (Nat.even ver') eqn:Heven';
              iDestruct "Hlock" as "(_ & Hγᵥ & _)";
              iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle]; iSplit.
              1, 3: (iPureIntro; lia).
              all: iApply (mono_nat_lb_own_get with "Hγᵥ"). }
            iMod ("Hcl" with "[-HΦ Hdst Hproph]") as "_".
            { iExists ver', log', actual', cache', true, backup₁, backup₁', requests', index'.
              iFrame "∗ # %". }
            iModIntro.
            wp_pures.
            wp_bind (! _)%E.
            iInv cached_wfN as "(%ver'' & %log'' & %actual'' & %cache'' & %valid' & %backup₂ & %backup₂' & %requests'' & %index'' & >Hver & >Hbackup & >Hγ & >#□Hbackup₂ & >%Hindex'' & >%Hvalidated'' & >Hregistry & Hreginv & >%Hlenactual'' & >%Hlencache'' & Hlog & >%Hlogged'' & >●Hlog & >%Hlenᵢ'' & >%Hnodup'' & >%Hrange'' & Hlock)" "Hcl".
            wp_load.
            iAssert (⌜ver < ver''⌝)%I as %Hless'.
            { destruct (Nat.even ver'');
              iDestruct "Hlock" as "(_ & Hγᵥ & _)";
              iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle'];
              iPureIntro; lia. }
            iMod ("Hcl" with "[-HΦ Hdst Hproph]") as "_".
            { iExists ver'', log'', actual'', cache'', valid', backup₂, backup₂', requests'', index''.
              iFrame "∗ # %". }
              iModIntro.
              wp_pures.
              wp_apply (wp_resolve with "Hproph").
              { done. }
              wp_pures.
              iModIntro.
              iIntros (pvs' ->) "Hproph".
              simpl in *.
              simplify_eq.
              rewrite bool_decide_eq_true in Hres.
              simplify_eq. lia.

              rewrite bool_decide_eq_false_2; first last.
              { intros [=]. lia. }
              wp_pures.
              wp_apply (wp_array_clone_persistent with "□Hbackup₁").
              { lia. }
              { lia. }

            
              

              rewrite bool_decide_eq_true_2; last done.
              iIntros (pvs' ->) "Hproph".
              
            
              rewrite bool_decide_eq_false_2; first last.
              { unfold not. intros. simplify_eq. }
              simpl. wp_pures.
              wp_bind (array_clone _ _).
              wp_apply (wp_array_clone with "□Hbackup₁").
              { lia. } 
              { lia. }
              iIntros (l') "Hl'".
              wp_pures.
              iModIntro.
              iApply "HΦ".

            wp_smart_apply (wp_array_clone with "Hdst").

             iApply "HΦ". }
          }
        { iMod ("Hconsume" with "Hγ'") as "HΦ". }
      
      destruct (decide (ver = ver')) as [<- | Hne]. 
      + rewrite Heven.
        iDestruct "Hlock" as "(Hγᵢ & Hγᵥ & %Hunlocked' & Hcache)".
        rewrite /log_frag_own.
        iPoseProof (log_auth_frag_agree with "●Hlog ◯Hlog") as "%Hlookup".
        destruct valid' eqn:Hvalid'.
        * destruct Hvalidated' as (_ & <- & <-).
          rewrite last_lookup Hlenᵢ' /= in Hindex'.
          iAssert (⌜cache = vdst⌝)%I with "[Hcons Hγᵥ]" as "<-".
          { iApply pure_mono.
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
            iPoseProof ("Hfrag" with "[]") as "(%l' & %γₜ' & %vs' & #◯Hindex' & #◯Hlog' & %Hlookup')".
            { by rewrite -Nat.even_spec. }
            iCombine "◯Hindex ◯Hindex'" gives %Hvalid%auth_frag_op_valid_1.
            rewrite singleton_op singleton_valid in Hvalid.
            apply to_agree_op_inv_L in Hvalid as <-.
            iCombine "◯Hlog ◯Hlog'" gives %Hvalid%auth_frag_op_valid_1.
            rewrite singleton_op singleton_valid in Hvalid.
            apply to_agree_op_inv_L in Hvalid as [=<-<-].
            simplify_eq. iPureIntro. apply (inj Some). by rewrite -Hv -Hlookup'. }
          rewrite last_lookup Hlenᵢ /= in Hindex.
          iDestruct (index_auth_frag_agree with "Hγᵢ ◯Hindex") as "%H".
          simplify_eq.
          iMod ("Hcl" with "[-HΦ Hdst]") as "_".
          { iExists ver, log', actual', actual', true, backup₁, backup₁, requests', index'.
            iFrame "∗ # %". rewrite last_lookup Hlenᵢ' Heven /=. iFrame "∗ # %".
            iIntros "!> !%". split; last done. by rewrite -Nat.even_spec. }
          iModIntro.
          wp_pures.
          wp_bind (! _)%E.
          iInv cached_wfN as "(%ver' & %log'' & %actual'' & %cache' & %valid' & %backup₂ & %backup₂' & %requests'' & %index'' & >Hver & >Hbackup & >Hγ & >#□Hbackup₂ & >%Hindex'' & >%Hvalidated'' & >Hregistry & Hreginv & >%Hlenactual'' & >%Hlencache'' & Hlog & >%Hlogged'' & >●Hlog & >%Hlenᵢ'' & >%Hnodup'' & >%Hrange'' & Hlock)" "Hcl".
          wp_load.
          iMod ("Hcl" with "[-HΦ Hdst]") as "_".
          { iExists ver', log'', actual'', cache', valid', backup₂, backup₂', requests'', index''.
            iFrame "∗ # %". }
          iModIntro.
          destruct (decide (ver' = ver)) as [<- | Hne].
          { wp_pures. rewrite bool_decide_eq_true_2; last done.
            wp_pures. iModIntro. iApply "HΦ". simpl in *. iFrame "∗ #".
            rewrite -lookup_fmap lookup_fmap_Some in Hlogged'.
            destruct Hlogged' as ([γ' vs'] & ? & ?). simpl in *. simplify_eq.
            assert ((γ', actual') = (γₜ, vs)) as [=->->].
            { apply (inj Some). by etransitivity. }
            by iFrame "∗ %". }
          { wp_pures. rewrite bool_decide_eq_false_2; first last.
            { unfold not. intros. simplify_eq. }
            simpl. wp_pures.
            wp_bind (array_clone _ _).
            wp_apply (wp_array_clone with "□Hbackup₁").
            { lia. } 
            { lia. }
            iIntros (l') "Hl'".
            wp_pures.
            iModIntro.
            iApply "HΦ".

            wp_smart_apply (wp_array_clone with "Hdst").

             iApply "HΦ". }

          
          iMod


            rewrite Heven.

            iExists ver', log', actual, cache, valid, backup, backup', requests, index.
            rewrite Heven. iFrame "∗ # %
            ". }
          
          
          
          
          
        (* rewrite Hlog /=.
        rewrite Hlog /= in Hlookup.
        assert (Some vs = Some vs') as [=<-].
        { by rewrite -Hlookup -Hcons'. }
        clear Hcons'. simplify_eq. *)
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
        { rewrite /cached_wf_inv.
          iExists ver, log', vs. rewrite Hparity. iFrame "∗ %".
          iPureIntro. rewrite last_lookup. by rewrite Hlog'. }
        iModIntro. wp_pures. rewrite bool_decide_eq_true_2; last done.
        wp_pures. iModIntro. by iApply "HΦ".
      + destruct (Nat.even ver') eqn:Hparity'''.
        * iMod "Hlock" as "(Hversion & Hsrc & log)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver', log', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
        * iDestruct "Hlock" as "(Hversion & Hsrc)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver', log', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
    - iDestruct "Hlock" as "(Hγₕ & Hγᵥ & Hsrc)".
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver, log, vs. rewrite Hparity. by iFrame "∗ %". }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_true_2; first last.
      { rewrite Zrem_even even_inj Hparity. by destruct ver. }
      wp_pures.
      iApply ("IH" with "AU").
  Qed.

  Lemma write_spec (γ : gname) (v : val) (src : loc) dq (vs' : list val) :
    is_cached_wf v γ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, value γ vs  }>> 
          write (length vs') v #src @ ↑N
        <<{ value γ vs' | RET #(); src ↦∗{dq} vs' }>>.
  Proof.
    iIntros "(%dst & %γₕ & %γᵥ & %γᵣ & -> & #Hinv) Hsrc %Φ AU".
    wp_rec.
    wp_pure credit:"Hcredit".
    wp_pure credit:"Hcredit'".
    wp_bind (! _)%E.
    iInv cached_wfN as "(%ver & %log & %vs & %registry & Hreg & Hreginv & >Hver & >%Hlen & >%Hlog & Hlock)" "Hcl".
    iMod (ghost_var_alloc true) as "(%γₗ & Hγₗ & Hγₗ')".
    iMod token_alloc as "[%γₜ Hγₜ]".
    iMod (inv_alloc casN _ (write_inv Φ γ γₗ γₜ src dq vs') with "[Hcredit' AU Hγₗ']") as "#Hwinv".
    { iRight. iLeft. iFrame. }
    wp_load.
    iMod (registry_update γₗ (S (Nat.div2 ver)) with "[$]") as "[●Hreg #◯Hreg]".
    destruct (Nat.even ver) eqn:Heven.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst & %Hcons)".
      iDestruct (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-Hsrc Hγₜ Hcredit]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver, log, vs, (registry ++ [(γₗ, S (Nat.div2 ver))]). rewrite Heven. iFrame "∗ #".
        rewrite bool_decide_eq_true_2.
        - simpl. by iFrame.
        - lia. }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_false_2; first last.
      { intros [=Heq]. by rewrite Zrem_even even_inj Heven in Heq. }
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iInv cached_wfN as "(%ver' & %log' & %vs'' & %registry' & Hreg & Hreginv & >Hver & >%Hlen' & >%Hlog' & Hlock)" "Hcl".
      destruct (decide (ver = ver')) as [<- | Hne].
      + rewrite Heven.
        wp_cmpxchg_suc.
        iDestruct "Hlock" as "([Hγ Hγ'] & [Hγₕ Hγₕ'] & Hγᵥ & [Hdst Hdst'] & %Hcons')".
        replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
        iMod (mono_nat_own_update (S ver) with "Hγᵥ") as "[[Hγᵥ Hγᵥ'] #Hlb']".
        { lia. }
        iMod ("Hcl" with "[Hver Hreg Hreginv Hγₕ' Hdst' Hγᵥ']") as "_".
        { rewrite /cached_wf_inv. iExists (S ver), log', vs'', registry'.
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
        iInv cached_wfN as "(%ver' & %log'' & %vs''' & %registry'' & Hreg & Hreginv & >Hver & >%Hlen'' & >%Hlog'' & Hlock)" "Hcl".
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
        iPoseProof (log_auth_auth_agree with "Hγₕ Hγₕ'") as "<-".
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
        iMod (log_auth_update vs' with "Hγₕ") as "[●Hγₕ #◯Hγₕ]".
        iInv casN as "[[HΦ >Hγₗ'] | [(>_ & AU & >Hγₗ') | (>Htok & >Hlin')]]" "Hclose".
        { by iCombine "Hγₗ Hγₗ'" gives %[]. }
        { iMod (ghost_var_update_halves false with "Hγₗ Hγₗ'") as "[Hlin Hlin']".
          iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
          iMod "AU" as (n') "[Hγ' [_ Hconsume]]".
          iMod (ghost_var_update_halves vs' with "Hγ Hγ'") as "[Hγ Hγ']".
          iMod ("Hconsume" with "Hγ") as "HΦ".
          iMod ("Hclose" with "[Hγₜ Hlin']") as "_".
          { do 2 iRight. iFrame. }
          iMod ("Hcl" with "[-HΦ Hsrc]") as "_".
          { iExists (S (S ver)), (log' ++ [vs']), vs', registry''.
            rewrite <- Nat.Even_div2 by now rewrite -Nat.even_spec.
            rewrite (take_drop_middle _ _ _ Hagree).
            rewrite /= Heven. change 2%Z with (Z.of_nat 2).
            rewrite -Nat2Z.inj_add /=.
            rewrite last_snoc last_length Hlog'. iFrame.
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
      { rewrite /cached_wf_inv.
        iExists ver, log, vs, (registry ++ [(γₗ, S (Nat.div2 ver))]). rewrite Heven. iFrame "∗ #".
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
      is_cached_wf v γ n -∗
        <<{ ∀∀ vs, value γ vs  }>> 
          read n v @ ↑N
        <<{ ∃∃ copy : loc, value γ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
    iIntros "%Hpos (%src & %γₕ & %γᵥ & %γᵣ & -> & #Hinv) %Φ AU".
    iLöb as "IH".
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv cached_wfN as "(%ver & %log & %vs & %registry & Hreg & Hreginv & >Hver & >%Hlen & >%Hlog & Hlock)" "Hcl".
    wp_load.
    destruct (Nat.even ver) eqn:Hparity.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons)".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod (log_frag_alloc with "Hγₕ") as "[H● #H◯]".
      { by rewrite last_lookup in Hcons. }
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver, log, vs. rewrite Hparity. by iFrame. }
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
      iInv cached_wfN as "(%ver' & %log' & %vs' & %registry' & Hreg & Hreginv & >Hver & >%Hlen'' & >%Hlog' & Hlock)" "Hcl".
      destruct (decide (ver = ver')) as [<- | Hne].
      + rewrite Hparity.
        iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons')".
        rewrite /log_frag_own.
        iPoseProof (log_auth_frag_agree with "Hγₕ H◯") as "%Hlookup".
        rewrite last_lookup Hlog' /= in Hcons'.
        rewrite Hlog /=.
        rewrite Hlog /= in Hlookup.
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
        { rewrite /cached_wf_inv.
          iExists ver, log', vs. rewrite Hparity. iFrame "∗ %".
          iPureIntro. rewrite last_lookup. by rewrite Hlog'. }
        iModIntro. wp_pures. rewrite bool_decide_eq_true_2; last done.
        wp_pures. iModIntro. by iApply "HΦ".
      + destruct (Nat.even ver') eqn:Hparity'''.
        * iMod "Hlock" as "(Hversion & Hsrc & log)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver', log', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
        * iDestruct "Hlock" as "(Hversion & Hsrc)".
          wp_load.
          iMod ("Hcl" with "[-AU]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver', log', vs'. rewrite Hparity'''. by iFrame "∗ %". }
          iModIntro.
          wp_pures.
          case_bool_decide; simplify_eq.
          wp_pures.
          iApply ("IH" with "AU").
    - iDestruct "Hlock" as "(Hγₕ & Hγᵥ & Hsrc)".
      iMod ("Hcl" with "[-AU]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver, log, vs. rewrite Hparity. by iFrame "∗ %". }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_true_2; first last.
      { rewrite Zrem_even even_inj Hparity. by destruct ver. }
      wp_pures.
      iApply ("IH" with "AU").
  Qed.

End cached_wf.
