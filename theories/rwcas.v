From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import token ghost_var invariants.
From iris.heap_lang Require Import lang proofmode notation.

(**
  * This example proves the correctness of a linearizable [read]/[write] cell
  * implemented using just [read] and [CmpXchg]. For a location [l] and value [v],
  * [write(l, v)] is implemented as [CmpXchg l !l v]. Obviously, if another thread
  * changes the value stored in [l] between the load and [CmpXchg], then the 
  * [CmpXchg] fails and the write has no physical effect. However, this means that
  * the failing write can linearize immediately before the succeeding conflicting write 
  * that caused the [CmpXchg] to fail. We prove that this implementation is logically
  * atomic.
  *
  * In the proof of the write spec, a prophecy is used by every writer to predict whether its
  * [CmpXchg] will succeed. If the prophecy predicts that the operation will fail, 
  * then its linearization point (LP) is external, as the conflicting successful write 
  * will have to carry out its LP on its behalf. Thus, the failing write will have to
  * store its atomic update in an invariant so that the
  * successful write can carry out its LP and consume the update. A successful
  * writer is obligated to consume every atomic update stored d in the invariant,
  * linearizing all writers prophesied to fail.
  *)

(* Initialize the cell *)
Definition new_rwcas : val := λ: "x", ref "x".

(** Can read the cell simply by derefencing it *)
Definition read : val := λ: "x", !"x".

(* A fine-grained wait-free implementation of [write] *)
Definition write : val :=
  λ: "l" "v",
    let: "p" := NewProph in
    Resolve (CmpXchg "l" !"l" "v") "p" #();;
    #().

(* LP stepping requests. *)
(* Map the process id of every failing write to a triple [(id, γₜ, v)]*)
Definition requestReg := gmap nat (agree (gname * Z)).
Definition requestRegUR := authUR $ gmapUR nat (agreeR (prodO (prodO gnameO gnameO) ZO)).

Class rwcasG Σ := {
  rwcas_requestUR :: inG Σ requestRegUR;
  rwcas_tokenG :: tokenG Σ;
  rwcas_ghost_varG_bool :: ghost_varG Σ bool;
  rwcas_ghost_varG_Z :: ghost_varG Σ Z;
  rwcas_heapGS :: heapGS Σ;
}.

Section rwcas.

  Context `{!rwcasG Σ}.

  Context (N : namespace).

  Definition rwcasN : namespace := N .@ "rwcas".

  Definition writeN : namespace := N .@ "write".

  Definition extract_result (vs : list (val * val)) : option (bool * Z) :=
    match vs with
    | (PairV (LitV (LitInt n)) (LitV (LitBool b)), _) :: _ => Some (b, n)
    | _ => None
    end.

  Definition value γ (n : Z) := ghost_var γ (1/2) n.

  Definition AU_write (Φ : val → iProp Σ) γ (q : Z) : iProp Σ :=
    AU <{ ∃∃ p : Z, value γ p }> @ ⊤ ∖ ↑N, ∅ <{ value γ q, COMM Φ #() }>.

  Definition AU_read (Φ : val → iProp Σ) γ : iProp Σ :=
    AU <{ ∃∃ n : Z, value γ n }> @ ⊤ ∖ ↑N, ∅ <{ value γ n, COMM Φ #n }>.

  Definition write_inv (Φ : val → iProp Σ) γ (γₗ γₜ : gname) : iProp Σ :=
      (Φ #() ∗ ∃ b : bool, ghost_var γₗ (1/2) b) (* The failing write has already been linearized and its atomic update has been consumed *)
    ∨ (£ 1 ∗ (∃ q : Z, AU_write Φ γ q) ∗ ghost_var γₗ (1/2) false)
    ∨ (token γₜ ∗ ∃ b : bool, ghost_var γₗ (1/2) b). (* The failing write has linearized and returned *)

  Definition registry_inv γ n (requests : list (gname * gname * Z)) : iProp Σ :=
    [∗ list] '(γₗ, γₜ, m) ∈ requests, (* For every thread/proph id *)
        ghost_var γₗ (1/2) (bool_decide (m = n)) ∗
        ∃ Φ : val → iProp Σ,
          inv writeN (write_inv Φ γ γₗ γₜ).

  (* Authoritative ownership over request registry *)
  Definition registry γᵣ (requests : list (gname * gname * Z)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γᵣ i (γₗ γₜ : gname) (m : Z) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, γₜ, m)]})).

  Definition rwcas_inv γᵣ l 'γ : iProp Σ :=
    (∃ (n : Z) (requests : list (gname * gname * Z)), 
      l ↦ #n ∗
      ghost_var γ (1/2) n ∗ (* implementation location *)
      registry γᵣ requests ∗ (* Authoritative ownership over request registry *)
      registry_inv γ n requests)%I.

      (* Frame-preserving updates permit allocation of a new request *)
  Lemma registry_update γₗ γₜ m γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(γₗ, γₜ, m)]) ∗ registered γ (length requests) γₗ γₜ m.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (γₗ, γₜ, m)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree (requests : list (gname * gname * Z)) i request : 
    ✓ (● map_seq O (to_agree <$> requests) ⋅ ◯ ({[i := to_agree request]})) →
        requests !! i = Some request.
  Proof.
    intros [Hincl _]%auth_both_valid_discrete.
    apply dom_included in Hincl as Hdom.
    rewrite dom_singleton_L singleton_subseteq_l in Hdom.
    rewrite lookup_included in Hincl.
    specialize Hincl with i.
    rewrite option_included in Hincl.
    destruct Hincl as [Hnone | (a & b & H & H' & Heq)].
    { by rewrite lookup_insert in Hnone. }
    rewrite lookup_insert in H. simplify_eq.
    rewrite lookup_map_seq_0 list_lookup_fmap_Some in H'.
    destruct H' as ([γₜ' m'] & Hlookup & ->).
    destruct Heq as [Heq | Hle].
    - apply (inj to_agree) in Heq.
      by simplify_eq.
    - rewrite to_agree_included in Hle.
      by simplify_eq.
  Qed.

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
  Lemma linearize_writes γ (m n p : Z) requests :
    ghost_var γ (1/2) m -∗
      registry_inv γ n requests ={⊤ ∖ ↑rwcasN}=∗ 
        registry_inv γ p requests ∗ ∃ q : Z, ghost_var γ (1/2) q.
  Proof.
    iIntros "Hγ Hreqs".
    iInduction requests as [|[[γₗ γₜ] m'] reqs'] "IH" forall (m).
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(Hlin & %Φ & #Hwinv) Hreqs']";
      iMod ("IH" with "Hγ Hreqs'") as "(Hreqs' & %q & Hγ)".
      iInv writeN as "[[HΦ >[%b Hlin']] | [(>Hcredit & [%q' AU] & >Hlin') | (>Htok & %b & >Hlin')]]" "Hclose".
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[HΦ Hlin]") as "_".
        { iLeft. iFrame. }
        iFrame. by iExists _.
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (n') "[Hγ' [_ Hclose']]".
        iMod (ghost_var_update_halves q' with "Hγ Hγ'") as "[Hγ Hγ']".
        iFrame. iExists Φ.
        iMod ("Hclose'" with "Hγ") as "HΦ".
        iMod ("Hclose" with "[-]") as "_".
        { iLeft. iFrame. }
        done.
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[Htok Hlin]") as "_".
        { do 2 iRight. iFrame. }
        iFrame. by iExists _.
  Qed.

  (* Predicate describing that a value is a RWCAS cell *)
  Definition is_rwcas (γ : gname) (v : val) : iProp Σ :=
    ∃ (l : loc) (γᵣ : gname), ⌜v = #l⌝ ∗ inv rwcasN (rwcas_inv γᵣ l γ).

  Lemma new_rwcas_spec (n : Z) :
    {{{ True }}}
      new_rwcas #n
    {{{ γ l, RET l; is_rwcas γ l ∗ value γ n }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /new_rwcas.
    wp_pures.
    wp_alloc l as "Hl".
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γᵣ H●]".
    { by apply auth_auth_valid. }
    iMod token_alloc as "[%γ_ex Hex]".
    iMod (ghost_var_alloc n) as "(%γ & Hγ & Hγ')".
    iMod (inv_alloc rwcasN _ (rwcas_inv γᵣ l γ) with "[-Hγ HΦ Hex]") as "#Hinv".
    { iNext. iFrame. by rewrite /registry_inv. }
    iModIntro.
    iApply "HΦ".
    iSplitR.
    - iExists _, _. by iSplit.
    - iFrame.
  Qed.

  Lemma read_spec (γ : gname) (v : val) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> read v @ ↑N <<{ value γ n | RET #n }>>.
  Proof.
    iIntros "(%l & %γᵣ & -> & #Hinv) %Φ AU".
    rewrite /read.
    wp_pures.
    iInv rwcasN as (n reqs) "(Hl & Hγ & H● & Hreqs)" "Hclose".
    wp_load.
    iMod "AU" as (n') "[Hγ' [_ Hclose']]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    iMod ("Hclose'" with "[$]") as "HΦ".
    by iMod ("Hclose" with "[$]") as "_".
  Qed.

  Lemma write_spec γ v (q : Z) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> write v #q @ ↑N <<{ value γ q | RET #() }>>.
  Proof.
    iIntros "(%l & %γᵣ & -> & #Hinv) %Φ AU".
    rewrite /write.
    wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_pure credit:"Hcredit".
    wp_pures.
    rewrite /rwcas_inv.
    wp_bind (! _)%E.
    iInv rwcasN as (n reqs) "(Hl & Hγ & H● & Hreqs)" "Hclose".
    wp_load.
    destruct (extract_result vs) as [[[|] m] | ] eqn:Hres.
    - iMod ("Hclose" with "[$Hl $Hγ $H● $Hreqs]") as "_".
      clear reqs.
      iModIntro.
      wp_apply (wp_resolve with "Hp"); first done.
      iInv rwcasN as (n' reqs) "(Hl & Hγ & H● & Hreqs)" "Hclose".
      destruct (decide (n' = n)) as [-> | Hne].
      + wp_cmpxchg_suc.
        iMod (linearize_writes _ _ _ q with "Hγ Hreqs") as "(Hreqs & %q' & Hγ)".
        iMod "AU" as (n') "[Hγ' [_ Hclose']]".
        iMod (ghost_var_update_halves q with "Hγ Hγ'") as "[Hγ Hγ']".
        iMod ("Hclose'" with "Hγ'") as "HΦ".
        iMod ("Hclose" with "[$]") as "_".
        iIntros "!> %vs' -> Hp".
        by wp_pures.
      + wp_cmpxchg_fail.
        iMod ("Hclose" with "[$]") as "_".
        iIntros "!> %vs' -> _ //".
    - destruct (decide (n = m)) as [-> | Hne].
      + iMod ("Hclose" with "[$Hl $Hγ $H● $Hreqs]") as "_".
        iModIntro.
        wp_bind (Resolve _ _ _)%E.
        clear reqs.
        iInv rwcasN as (n' reqs) "(Hl & Hγ & H● & Hreqs)" "Hclose".
        wp_apply (wp_resolve with "Hp"); first done.
        destruct (decide (n' = m)) as [-> | Hneq].
        * wp_cmpxchg_suc.
          iIntros "!> %vs' -> _ //".
        * wp_cmpxchg_fail.
          iIntros "!> %vs' -> _".
          inv Hres.
      + iMod token_alloc as "[%γₜ Hγₜ]".
        iMod (ghost_var_alloc false) as "(%γₗ & Hlin & Hlin')".
        iMod (registry_update γₗ γₜ m γᵣ reqs with "H●") as "[H● #H◯]".
        iMod (inv_alloc writeN _ (write_inv Φ γ γₗ γₜ) with "[AU Hcredit Hlin']") as "#Hwinv".
        { rewrite /write_inv. iRight. iLeft. iFrame. }
        iMod ("Hclose" with "[-Hp Hγₜ]") as "_".
        { iExists _, (reqs ++ [(γₗ, γₜ, m)]).
          iFrame.
          rewrite big_sepL_singleton.
          case_bool_decide; simplify_eq.
          iFrame.
          by iExists _. }
        iModIntro.
        wp_bind (Resolve _ _ _)%E.
        iInv rwcasN as (n' reqs') "(Hl & Hγ & H● & Hreqs')" "Hclose".
        wp_apply (wp_resolve with "Hp"); first done.
        destruct (decide (n' = n)) as [-> | Hneq].
        * wp_cmpxchg_suc.
          iIntros "!> %vs' -> _ //".
        * wp_cmpxchg_fail.
          iIntros "!> %vs' -> _".
          inv Hres.
          (* The registry must still contain out linearization request *)
          iCombine "H● H◯" gives %Hagree%registry_agree.
          (* Consider which state our helping request is in*)
          iPoseProof (big_sepL_lookup_acc _ _ _ _ Hagree with "Hreqs'") as "[(Hlin & %Φ' & HΦ') Hrest]".
          iInv writeN as "[[HΦ >[%b Hlin']] | [(>Hcredit & [%q' AU] & >Hlin') | (>Htok & %b & >Hlin')]]" "Hclose'".
          { iMod ("Hclose'" with "[Hγₜ Hlin']") as "_".
            { do 2 iRight. iFrame. }
            iMod ("Hclose" with "[-HΦ]") as "_".
            { iFrame. iApply "Hrest". iFrame. }
            iModIntro.
            by wp_pures. }
          { (* Our request is still pending *)
            (* This is impossible, as the value stored in the cell is what was prophecized *)
            case_bool_decide; simplify_eq.
            by iCombine "Hlin Hlin'" gives %[]. }
          { (* We have returned *)
            (* This is impossible, as we still own the token. There cannot be another copy in the invariant *)
            iCombine "Hγₜ Htok" gives %[]. }
    - iMod ("Hclose" with "[$Hl $Hγ $H● $Hreqs]") as "_".
      iModIntro.
      clear reqs.
      wp_bind (Resolve _ _ _)%E.
      iInv rwcasN as (n' reqs) "(Hl & Hγ & H● & Hreqs)" "Hclose".
      wp_apply (wp_resolve with "Hp"); first done.
      destruct (decide (n' = n)) as [-> | Hne].
      + wp_cmpxchg_suc.
        iIntros "!> %vs' -> _ //".
      + wp_cmpxchg_fail.
        iIntros "!> %vs' -> _ //".
  Qed.
      
End rwcas.
