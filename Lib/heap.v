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
    Set Printing Implicit.
    unfold tpool_ghost in *.
    (* We cannot reach such heights of perfection.  It was not intended for us *)
    (*apply (join_ord (PCM_order := gmap_order (A_order := discrete_order))) in Hjoin.*)
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

  (* If any part of the tpool has a thread in it, the overall thread pool has that in it *)
  Lemma tpool_ref_sub_lookup j v sh gName (tp' : @G tpool_ghost) (σ' : @G heap_ghost) tp σ:
    ghost_part (P:=spec_ghost) sh (tp', σ') gName 
    * ghost_reference (P:=spec_ghost) (to_tpool tp, to_heap (heap σ)) gName 
     |-- (!! ((tp' !! j = Some (Some v) -> (to_tpool tp) !! j = Some (Some v)))).
  Proof.
    iIntros  "[Part Ref]".
    iDestruct (ref_sub (P := spec_ghost) with "[$Part $Ref]") as "%Hjoin".
    iPureIntro.
    if_tac in Hjoin.
    - inversion Hjoin; subst; auto.
    - intros Hsome.
      inv Hjoin. 
      inv H0.
      specialize (H1 j).
      inv H1.
      (* impossible case *)
      { rewrite Hsome in H3; inv H3. }
      (* actual case *)
      rewrite Hsome in H5; auto.
      (* show that we can't have any other possibility *)
      inv H5.
      + rewrite Hsome in H0; inv H0.
      + rewrite Hsome in H0; rewrite H0 in H4; auto.
      + inv H1.
  Qed.


  (* If a part of the heap has a value in it, the rest of the heap has to as well *)
  Lemma heap_ref_sub_lookup (l : loc) v vsh' gName (sh : Share.t) (tp' : @G tpool_ghost) (σ' : @G heap_ghost) tp σ:
    ghost_part (P:=spec_ghost) sh (tp', σ') gName 
    * ghost_reference (P:=spec_ghost) (to_tpool tp, to_heap (heap σ)) gName 
     |-- (!! (
      (σ' !! l = Some (Some (vsh', v))) -> (exists vsh, (to_heap (heap σ)) !! l = Some (Some (vsh, v))))).
  Proof.
    iIntros "[Part Ref]".
    iDestruct (ref_sub (P := spec_ghost) with "[$Part $Ref]") as "%Hjoin".
    iPureIntro.
    intros Hsome.
    if_tac in Hjoin.
    (* full share means they agree by default *)
    { exists vsh'; inv Hjoin; subst; auto. }
    (* if we don't have full share, we have to show they agree *)
    inv Hjoin; inv H0.
    specialize (H2 l); inv H2.
    (* same set of cases, essentially *)
    { rewrite Hsome in H3; inv H3. } (* None != Some *)
    { rewrite Hsome in H5; exists vsh'; auto. } (* other joined piece is None, so equal *)

    (* Both x and our ghost_part are pieces and join *)
    (* here we prove that no matter what share we have or what x is, we get the same value v in the heap *)
    destruct a1; [|rewrite Hsome in H0; inv H0]. (* Hone != Some but different *)
    assert (p = (vsh', v)) by (rewrite Hsome in H0; inv H0; auto); subst. (* we already know what p is *)
    (* What values can the overall heap store at l? *)
    destruct a3.
    - destruct p.
      exists s.
      apply eq_sym in H4; rewrite H4.
      destruct a2.
      + destruct p.
        inv H5; destruct H6 as [Hs0NE [Hshjoin Hvjoin]].
        inv Hvjoin.
        reflexivity.
      + inv H5.
        reflexivity.
    (* in this case, we show that we can't somehow get None from Some, but again *)
    - destruct a2.
      + destruct p.
        inv H5.
      + inv H5.
  Qed.


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

    (* we need to know later that j is in the thread pool, 
       so we prove it now while we have Hj and Hown around *)
    iDestruct (tpool_ref_sub_lookup j with "[$Hj $Hown]") as "%HhasJ"; 
      rewrite lookup_singleton in HhasJ;
      specialize (HhasJ eq_refl).

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

    (* we need the HhasJ here for to_tpool_insert' *)
    rewrite to_heap_insert to_tpool_insert'; last auto. 
    iFrame; iSplit; auto. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros. assert (i = 0) as -> by lia. by rewrite loc_add_0.
  Qed.

  Lemma step_load E j K l hSh v:
    nclose nspace ⊆ E → 
    spec_ctx ∗ (tpool_mapsto j (fill K (Load (Val (LitV (LitLoc l)))))) ∗ (heapS_mapsto hSh l v)
    ={E}=∗ (spec_ctx ∗ (tpool_mapsto j (fill K (of_val v))) ∗ (heapS_mapsto hSh l v)).
  Proof.
    iIntros (?) "(#Hinv & [[%sj [Hsjne Hj]] [%sl [Hslne Hl]]])". iFrame "Hinv".
    iDestruct "Hsjne" as %Hsjne.
    iDestruct "Hslne" as %Hslne.
    rewrite /spec_ctx /spec_inv /tpool_mapsto.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /heapS_mapsto /=.
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    rewrite /UsrGhost.
    (* before we do any updates, we want to pull out that both things are in the main heap *)
    iDestruct (tpool_ref_sub_lookup j with "[$Hown $Hj]") as "%HtpJ"; 
      rewrite lookup_singleton in HtpJ;
      specialize (HtpJ eq_refl).
    iDestruct (heap_ref_sub_lookup l with "[$Hown $Hl]") as "%Hheapl";
      rewrite lookup_singleton in Hheapl;
      specialize (Hheapl eq_refl);
      destruct Hheapl as [valueShare Hheapl].

    (* Now we can update the load to the value *)
    iCombine "Hj Hown" as "Hown".
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hown") as "Hown".
    iDestruct (part_ref_update (P:= spec_ghost) _ _ _ _
    ({[j := Some (fill K (Val v))]}, to_heap gmap_empty)
     (<[j := Some (fill K (Val v)) ]> (to_tpool tp), to_heap (heap σ)) with "Hown") as ">Hown".
    {
      intros g Hjoin.
      split.
      (* the new values can join *)
      - inv Hjoin; simpl in H1, H2.
        pose proof (H1 j) as Hj.
        rewrite lookup_singleton HtpJ in Hj.
        inv Hj; subst.
        (* g does not cointain j *)
        { 
          split; auto.  (* heap doesn't change *)
          intros thread.
          destruct (eq_dec thread j); subst.
          - simpl.
            rewrite lookup_singleton.
            rewrite lookup_insert.
            rewrite <- H5.
            apply lower_None2.
          - simpl.
            rewrite lookup_singleton_ne; auto.
            rewrite lookup_insert_ne; auto.
            pose proof (H1 thread) as Htd.
            inv Htd; first apply lower_None1.
            {
              rewrite lookup_singleton_ne; auto.
              apply lower_None1.
            }
            {
              rewrite lookup_singleton_ne in H3; auto.
              inv H3.
            }
        }
        (* g contains j *)
        {
          split; auto.
          intros thread.
          destruct (decide (thread = j)); subst.
          - simpl.
            rewrite lookup_singleton.
            rewrite lookup_insert.
            inv H6.
            { rewrite <- H4; apply lower_Some; apply lower_None2. }
            { inv H8. }
          - rewrite lookup_singleton_ne; auto.
            rewrite lookup_insert_ne; auto.
            pose proof (H1 thread) as Htd.
            inv Htd. 
            { rewrite H8; apply lower_None1. }
            { 
              rewrite lookup_singleton_ne in H8; auto.
              (* It didn't want to let me rewrite None = _ equations so we do this *)
              rewrite H8 in H7.
              rewrite H7.
              apply lower_None1.
            }
            inv H8.
            { rewrite H5 in H7; rewrite H7; apply lower_None1. }
            { rewrite lookup_singleton_ne in H3; auto; inv H3. }
            inv H9.
        }
      (* show that if this is the only piece they're equal *)
      - intros Hsub.
        inv Hsub; subst.
        rewrite insert_singleton.
        reflexivity.
    }
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "[$Hown]") as "[Hj Hown]".
    iMod ("Hclose" with "[Hown]") as "_".
    { 
    iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    split; auto.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    rewrite /to_heap in Hheapl.
    rewrite lookup_fmap in Hheapl.
    destruct (heap σ !! l) eqn:Hpos; rewrite Hpos in Hheapl; simpl; try discriminate.
    simpl in Hheapl.
    inv Hheapl.
    reflexivity.
    }
    iModIntro.
    iSplitL "Hj".
    { iExists sj; iFrame; iPureIntro; auto. }
    iExists sl. 
    iSplitR; first (iPureIntro; auto).
    iFrame.
  Qed.

  Lemma ref_right_load E ctx K l sh v:
    nclose nspace ⊆ E → 
    (refines_right ctx (fill K (Load (Val (LitV (LitLoc l))))) * (heapS_mapsto sh l v) 
     |-- |={E}=> refines_right ctx (fill K (of_val v)) * (heapS_mapsto sh l v))%logic.
  Proof.
    intros Hnspace.
    unfold refines_right.
    iIntros "[[Rctx Rtp] Rlv]".
    iPoseProof (step_load with "[Rctx Rtp Rlv]") as "Rstep"; first apply Hnspace.
    {
      iFrame "Rctx".
      rewrite <- fill_app.
      iSplitL "Rtp".
      iApply "Rtp".
      iApply "Rlv".
    }
    iMod "Rstep".
    iDestruct "Rstep" as "(Rctx & Rtp & Rpt)".
    iModIntro.
    rewrite <- fill_app.
    iFrame.
  Qed.
   


Lemma step_store E j K l v' e v:
    IntoVal e v →
    nclose nspace ⊆ E →
    spec_ctx ∗ (tpool_mapsto j (fill K (Store (Val (LitV (LitLoc l))) e))) ∗ (heapS_mapsto fullshare l v')
    ={E}=∗ spec_ctx ∗ (tpool_mapsto j (fill K (Val (LitV LitUnit)))) ∗ (heapS_mapsto fullshare l v).
  Proof.
    iIntros (<-?) "(#Hinv & [[%sj [Hsjne Hj]] [%sl [Hslne Hl]]])". iFrame "Hinv".
    iDestruct "Hsjne" as %Hsjne.
    iDestruct "Hslne" as %Hslne.
    rewrite /spec_ctx /tpool_mapsto.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv nspace as (tp σ) ">[% Hown]" "Hclose".
    rewrite /heapS_mapsto /=.

    (* we probably need the fact that the things in the heap exist *)
    iDestruct (tpool_ref_sub_lookup j with "[$Hown $Hj]") as "%HtpJ";
      rewrite lookup_singleton in HtpJ;
      specialize (HtpJ eq_refl).
    iDestruct (heap_ref_sub_lookup l with "[$Hown $Hl]") as "%Hheapl";
      rewrite lookup_singleton in Hheapl;
      specialize (Hheapl eq_refl);
      destruct Hheapl as [valueShare Hheapl].

    (* we need to update both "Hj" and "Hl" and the heap and thread pool *)
    (* First the "tpool_mapsto" *)
    iCombine "Hj Hown" as "Hown".
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hown") as "Hown".
    iDestruct (part_ref_update (P:= spec_ghost) _ _ _ _
    ({[j := Some (fill K (Val (LitV LitUnit)))]}, to_heap gmap_empty)
    (<[j := Some (fill K (Val (LitV LitUnit))) ]> (to_tpool tp), to_heap (heap σ)) with "Hown") as ">Hown".
    {
      intros g Hj.
      split.
      (* these values join properly *)
      {
        destruct Hj as [Htp Hheap].
        split; auto. (* we only changed the thread pool here *)
        simpl.
        clear Hheap.
        (* now we prove this joins for any arbitrary thread *)
        intros thread.
        specialize (Htp thread).
        destruct (eq_dec thread j); subst.
        - rewrite lookup_singleton in Htp.
          rewrite lookup_singleton.
          rewrite lookup_insert.
          inv Htp. 
          { apply lower_None2. }
          inv H4.
          { apply lower_Some; apply lower_None2. }
          inv H5.
        - rewrite ? lookup_insert_ne; auto.
          rewrite ? lookup_insert_ne in Htp; auto.
      }
      (* if this is the only piece, it still joins *)
      {
        intros Heq; inv Heq.
        rewrite insert_singleton.
        reflexivity.
      }
    }
    (* don't forget to break up the ghost_part_ref *)
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "[$Hown]") as "[Hj Hown]".

    (* now the "heapS_mapsto" *)
    iCombine "Hl Hown" as "Hown".
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hown") as "Hown".
    (* NOTE: we include the prior update in this!!!  We'd be "removing" otherwise if we could even prove it *)
    iDestruct (part_ref_update (P:= spec_ghost) _ _ _ _
    (to_tpool [], {[l := Some (fullshare, Some v)]})
    (<[j:=Some (fill K (Val (LitV LitUnit)))]> (to_tpool tp), <[l := Some (fullshare, Some v)]> (to_heap (heap σ))) with "Hown") as ">Hown".
    {
      intros g Hhp.
      split.
      (* The update joins *)
      {
        destruct Hhp as [Htp Hhp].
        simpl in Htp, Hhp. 
        simpl.
        split; auto.
        clear Htp. (* we don't care about the thread pool since it's static *)
        intros loc.
        simpl.
        destruct (decide (loc = l)); subst.
        (* loc = l *)
        - specialize (Hhp l).
          rewrite ? lookup_insert in Hhp.
          rewrite ? lookup_insert.
          inv Hhp.
          { apply lower_None2. }
          apply lower_Some.
          destruct a3.
          { 
            destruct p.
            destruct a2.
            - destruct p.
              inv H4.
              destruct H5; destruct H5.
              apply join_Tsh in H5.
              inv H5.
              contradiction.
            - unfold sepalg.join.
              reflexivity.
          }
          {
            destruct a2.
            - destruct p.
              inv H4.
            - inv H4.
          }
        (* loc ≠ l *)
        - specialize (Hhp loc).
          rewrite ? lookup_insert_ne; auto.
          rewrite ? lookup_insert_ne in Hhp; auto.
      }
      (* if this is the only piece it is the full *)
      {
        intros Heq.
        inv Heq.
        rewrite insert_singleton.
        rewrite H2.
        reflexivity.
      }
    }
    iDestruct (ghost_part_ref_join (P:= spec_ghost) with "[$Hown]") as "[Hl Hown]".
    rewrite /UsrGhost.
    iMod ("Hclose" with "[Hown]") as "_".
    {
    iNext.
    rewrite /spec_inv.
    iExists (<[j:=fill K (Val (LitV LitUnit))]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro; split; auto.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.

    (* show we *did* in fact have something in the heap *)
    (* NOTE: if I find a better way to do this, update it here too! *)
    rewrite /to_heap in Hheapl.
    rewrite lookup_fmap in Hheapl.
    destruct (heap σ !! l) eqn:Hpos; rewrite Hpos in Hheapl; simpl.
    { 
      simpl in Hheapl.
      inv Hheapl.
      auto.
    }
    {
      simpl in Hheapl.
      inv Hheapl.
    }
    }
    iModIntro.
    iSplitL "Hj".
    { iExists sj; iFrame; iPureIntro; auto. }
    iExists sl.
    iSplitR; first (iPureIntro; auto).
    iFrame.
  Qed.

End heap.
