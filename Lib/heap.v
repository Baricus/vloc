Require Import Vloc.Lib.core.
Require Import Vloc.Lib.pure.

Section heap.

Context `{ref_ctx: refines_ctx}.

(* Some helper lemmas *)
(* NOTE: what is the equivalent of cmra.included? *)
  Lemma tpool_singleton_included (tp : list iexp) (j : nat) (e : iexp) :
    join_sub {[j := Some e]} (to_tpool tp) → tp !! j = Some e.
  Proof.
    (*TODO*)
  Admitted.
    (*move=> /singleton_included_l [ex [/leibniz_equiv_iff]].*)
    (*rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.*)
  (*Qed.*)
  Lemma tpool_singleton_included' tp j e :
    join_sub {[j := Some e]} (to_tpool tp) → to_tpool tp !! j = (Some (Some e)).
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

(* Does this exist??? NOTE *)
Instance eq_dec_loc : EqDec loc.
Proof.
Admitted.


(* taken and modified from theories/logic/spec_rules.v *)
(* Questions:
    - Is (pos_to_Qp 1) equivalent to top?
    - 

   Notes:
    ref is notation for (AllocN (Val (LitV 1%Z)))

 *)
  Lemma step_alloc E j K e v :
    IntoVal e v →
    nclose nspace ⊆ E →
    spec_ctx ∗ tpool_mapsto j (fill K (AllocN (Val (LitV (LitInt 1%Z))) e)) ={E}=∗ ∃ l, spec_ctx ∗ tpool_mapsto j (fill K (Val (LitV (LitLoc l)))) ∗ (heapS_mapsto l v).
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hj" as (sh) "Hj".
    rewrite /spec_ctx /tpool_mapsto /=. 
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom].

    (* modification to use VST's update semantics *)
    iDestruct (ref_sub (P:= spec_ghost) with "[$Hown $Hj]") as "%Hghost_join".
    iCombine "Hj Hown" as "Hown".
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hown") as "Hown".
    (*NOTE: updating heap! *)
    iDestruct ((part_ref_update (P:= spec_ghost) _ _ _ _ 
      (({[j := Some (fill K (Val (LitV (LitLoc l))))]}), to_heap (heap σ)) 
      ((<[ j := Some (fill K (Val (LitV (LitLoc l)))) ]> (to_tpool tp)),  (<[l := (Val v) ]> (to_heap (heap σ)))))
        with "Hown") as ">Hown". 
      (* NOTE: This is nearly the same as pure, how do I generalize it? *)
    {
      intros Gframe Hjoin.
      split.
      - destruct Hjoin as [Htp Hheap].
        split; simpl in *.
        * iIntros (k).
          destruct (eq_dec k j).
          + subst.
            rewrite lookup_singleton.
            specialize (Htp j).
            rewrite lookup_singleton in Htp; rewrite lookup_insert.
            inv Htp; constructor.
            inv H4; constructor.
            inv H5.
          + rewrite ! lookup_insert_ne; auto.
            rewrite lookup_empty.
            pose proof Htp k as Htpk.
            rewrite lookup_singleton_ne in Htpk; auto.
        * intros index.
          destruct (eq_dec index l); subst.
          + specialize (Hheap l).
            rewrite lookup_fmap in Hheap. 
            rewrite lookup_fmap in Hheap. 
            rewrite Hl in Hheap.

            rewrite lookup_fmap. 
            rewrite Hl.
            simpl in *.
            inv Hheap; subst.
            {
              unfold to_heap.
              (*rewrite (lookup_insert _ l (Val v)).*)
              admit.
            }
            rewrite (lookup_insert _ l (Val v)).
      - intros Oldg.
        inv Oldg.
        rewrite insert_singleton.
        reflexivity.
    }
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "[$Hown]") as "[Hj Hown]".
    (*iDestruct (own_valid_2 with "Hown Hj")*)
      (*as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.*)
    (*iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".*)
    (*{ by eapply auth_update, prod_local_update_1,*)
        (*singleton_local_update, (exclusive_local_update _ (Excl (fill K (#l)%E))). }*)
    (*iMod (own_update with "Hown") as "[Hown Hl]".*)
    (*{ eapply auth_update_alloc, prod_local_update_2,*)
        (*(alloc_singleton_local_update _ l (1%Qp,to_agree (Some v : leibnizO _))); last done.*)
      (*by apply lookup_to_heap_None. }*)
    iExists l. 
    rewrite /UsrGhost /heapS_mapsto.
    (* why does this work? *)
    iApply fupd_frame_l.
    iSplitL "Hj"; auto.
    rewrite /heapS_mapsto /=.
    iExists sh.
    rewrite /UsrGhost.
    iExists sh.
    iApply "Hclose". iNext.
    iExists (<[j:=fill K (# l)]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros. assert (i = 0) as -> by lia. by rewrite loc_add_0.
  Qed.

  Lemma step_load E j K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ={E}=∗ spec_ctx ∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[? ?%heap_singleton_included]%prod_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ={E}=∗ spec_ctx ∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { by rewrite /to_heap lookup_fmap Hl. }
      apply: (exclusive_local_update _
        (1%Qp, to_agree (Some v : leibnizO (option val)))).
      apply: pair_exclusive_l. done. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.
