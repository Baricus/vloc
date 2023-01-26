Require Import Vloc.Lib.core.
Require Import Vloc.Lib.pure.

(* NOTE: I feel like this should exist somewhere? *)
Lemma share_split_nonempty sh:
  sh ≠ emptyshare -> fst (Share.split sh) ≠ emptyshare /\ snd (Share.split sh) ≠ emptyshare.
Proof.
  intros Hne.
  remember ((Share.split sh).1) as shl.
  remember ((Share.split sh).2) as shr.
    split.
    (* weirdly, connecting these via ; instead of 1,2: does not work *)
    1,2: intros Hfalse;
      specialize (Share.split_nontrivial) with shl shr sh; intros Hsnontriv;
      subst;
      specialize surjective_pairing with _ _ (Share.split sh); intros Hspliteq;
      apply Hsnontriv in Hspliteq; last auto;
      contradiction.
Qed.

Section heap.
  
Context `{ref_ctx: refines_ctx}.
(* Some helper lemmas *)
(* NOTE: what is the equivalent of cmra.included? *)
  Lemma tpool_singleton_included (tp : list iexp) (j : nat) (e : iexp) :
    join_sub {[j := Some e]} (to_tpool tp) → tp !! j = Some e.
  Proof.
    unfold join_sub.
    intros [g Hjoin].
    specialize (Hjoin j).
    rewrite lookup_singleton in Hjoin.
    inv Hjoin; auto.
    inv H2; auto.
    contradiction.
  Qed.
    (*move=> /singleton_included_l [ex [/leibniz_equiv_iff]].*)
    (*rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.*)
  (*Qed.*)
  Lemma tpool_singleton_included' tp j e :
    join_sub {[j := Some e]} (to_tpool tp) → to_tpool tp !! j = (Some (Some e)).
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

(* Does this exist??? NOTE *)
(*Instance eq_dec_loc : EqDec loc.*)
(*Proof.*)
(*Admitted.*)
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
    spec_ctx ∗ tpool_mapsto j (fill K (AllocN (Val (LitV (LitInt 1%Z))) e)) ={E}=∗ ∃ l, spec_ctx ∗ tpool_mapsto j (fill K (Val (LitV (LitLoc l)))) ∗ (heapS_mapsto fullshare l v).
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hj" as (sh) "[Hne Hj]".
    iPure "Hne" as shNE.
    rewrite /spec_ctx /tpool_mapsto /=. 
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom].

    (* modification to use VST's update semantics rather than iris *)
    iDestruct (ref_sub (P:= spec_ghost) with "[$Hown $Hj]") as "%Hghost_join".
    iCombine "Hj Hown" as "Hown".

    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hown") as "Hown".
    (*NOTE: updating heap! *)
    iDestruct ((part_ref_update (P:= spec_ghost) _ _ _ _
      (({[j := Some (fill K (Val (LitV (LitLoc l))))]}), {[ l := Some (fullshare, Some v) ]}) 
      ((<[ j := Some (fill K (Val (LitV (LitLoc l)))) ]> (to_tpool tp)),  
      (* NOTE: We need the "post-to-heap" version of the update here, not the original, so we include the share *)
      (<[l := Some (fullshare, Some v) ]> (to_heap (heap σ)))))
        with "Hown") as ">Hown". 
      (* NOTE: This is nearly the same as pure at the start, how do I generalize it? *)
    {
      intros (tp_frame, heap_frame) Hjoin.
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
          destruct (decide (index = l)); subst.
          + specialize (Hheap l).
            rewrite lookup_fmap in Hheap. 
            rewrite lookup_fmap in Hheap. 
            rewrite Hl in Hheap.
            rewrite lookup_singleton lookup_insert.
            (* NOTE: what is the difference here? *)
            inv Hheap; [rewrite H1|]; apply lower_None2.
          + rewrite lookup_singleton_ne.
            rewrite lookup_insert_ne; auto.
            (* This does so much work I didn't believe it *)
            specialize (Hheap index); auto.
            auto.
      - intros Oldg.
        inv Oldg.
        rewrite insert_singleton.
        unfold to_heap.
        setoid_rewrite fmap_empty.
        rewrite insert_empty.
        reflexivity.
    }
    (*NOTE: We may actually need this *)
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
    destruct (Share.split sh) as [shl shr] eqn:Hshplit.
    (* Split Hj into two pieces, one for the heap and one for the map *)
    (*remember ((Share.split sh).1) as shl.*)
    (*remember ((Share.split sh).2) as shr.*)
    (* prove that the shares can't be empty; we need this fact in multiple places *)
    specialize (share_split_nonempty sh shNE).
    rewrite Hshplit.
    simpl.
    intros HshrsNE; destruct HshrsNE as [HshlNE HshrNE].
    (* now we know the shares are not empty everywhere *)
    iDestruct (ghost_part_join (P:=spec_ghost) shl shr sh
      ({[j := Some (fill K (Val (LitV (LitLoc l))))]}, to_heap gmap_empty)
      (to_tpool [], {[l := Some (fullshare, Some v)]})
      ({[j := Some (fill K (Val (LitV (LitLoc l))))]}, {[l := Some (fullshare, Some v)]})
      gName
    ) as "[_ Himpl ]"; eauto.
    { 
      apply split_join.
      auto.
    }
    (* prove that the update joins properly *)
    { 
      split; intros index; 
      setoid_rewrite fmap_empty; rewrite lookup_empty; simpl.
      - apply lower_None2.
      - apply lower_None1.
    }

    (* Above gives us an implication to follow which we have to apply and break apart *)
    iDestruct ("Himpl" with "Hj") as "[Htp Hheap]".
    iClear "Himpl".

    iApply fupd_frame_l.
    iSplitL "Htp".
    (* not an empty share *)
    { iExists shl; iFrame; auto. }
    rewrite /heapS_mapsto /=.
    iExists shr.
    rewrite /UsrGhost.
    (* also not an empty share *)
    iApply fupd_frame_l; iSplitR; auto. 
    iFrame "Hheap".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K (Val (LitV (LitLoc l)))]> tp), (state_upd_heap <[l:=Some v]> σ).

    rewrite to_heap_insert. 
    eassert (to_tpool tp !! j = _).
    { 
      if_tac in Hghost_join. 
      - inv Hghost_join.
        rewrite lookup_singleton.
        auto.
      - destruct Hghost_join as [g Hghost_join].
        erewrite tpool_singleton_included'; auto.
        eexists.
        inv Hghost_join.
        eauto.
    }
    rewrite to_tpool_insert'; auto. 
     
    iFrame. iSplit; auto. iPureIntro.
  (*Admitted.*)
    (*TODO: figure out why rtc_r fails *)
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros. assert (i = 0) as -> by lia. by rewrite loc_add_0.
  Qed.

  Lemma step_load E j K l hSh v:
    nclose nspace ⊆ E →
    spec_ctx ∗ (tpool_mapsto j (fill K (Load (Val (LitV (LitLoc l)))))) ∗ (heapS_mapsto hSh l v)
    ={E}=∗ spec_ctx ∗ (tpool_mapsto j (fill K (of_val v))) ∗ (heapS_mapsto hSh l v).
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx /spec_inv /tpool_mapsto.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /heapS_mapsto /=.
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    (*TODO: update *)
  Admitted.
    (*iDestruct (own_valid_2 with "Hown Hj")*)
      (*as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.*)
    (*iDestruct (own_valid_2 with "Hown Hl")*)
      (*as %[[? ?%heap_singleton_included]%prod_included ?]%auth_both_valid_discrete.*)
    (*iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".*)
    (*{ by eapply auth_update, prod_local_update_1, singleton_local_update,*)
        (*(exclusive_local_update _ (Excl (fill K (of_val v)))). }*)
    (*iFrame "Hj Hl". iApply "Hclose". iNext.*)
    (*iExists (<[j:=fill K (of_val v)]> tp), σ.*)
    (*rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.*)
    (*eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.*)
  (*Qed.*)

  Lemma step_store E j K l v' e v:
    IntoVal e v →
    nclose nspace ⊆ E →
    spec_ctx ∗ (tpool_mapsto j (fill K (Store (Val (LitV (LitLoc l))) e))) ∗ (heapS_mapsto fullshare l v')
    ={E}=∗ spec_ctx ∗ (tpool_mapsto j (fill K (Val (LitV LitUnit)))) ∗ (heapS_mapsto fullshare l v).
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx /tpool_mapsto.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /heapS_mapsto /=.
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    (* TODO: update *)
  Admitted.
    (*iDestruct (own_valid_2 with "Hown Hj")*)
      (*as %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.*)
    (*iDestruct (own_valid_2 with "Hown Hl")*)
      (*as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.*)
    (*iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".*)
    (*{ by eapply auth_update, prod_local_update_1, singleton_local_update,*)
        (*(exclusive_local_update _ (Excl (fill K #()))). }*)
    (*iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".*)
    (*{ eapply auth_update, prod_local_update_2.*)
      (*apply: singleton_local_update.*)
      (*{ by rewrite /to_heap lookup_fmap Hl. }*)
      (*apply: (exclusive_local_update _*)
        (*(1%Qp, to_agree (Some v : leibnizO (option val)))).*)
      (*apply: pair_exclusive_l. done. }*)
    (*iFrame "Hj Hl". iApply "Hclose". iNext.*)
    (*iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ).*)
    (*rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.*)
    (*eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.*)
  (*Qed.*)

End heap.
