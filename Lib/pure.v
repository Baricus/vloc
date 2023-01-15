Require Import Vloc.Lib.core.

Section lemmas.

Context `{ref_ctx: refines_ctx}.

(* Going to try to define the refines pure right *)
(* "stolen" from theories/logic/spec_rules.v *)
(** * Aux. lemmas *)
Lemma step_insert K tp j e σ κ e' σ' efs :
  tp !! j = Some (fill K e) → head_step e σ κ e' σ' efs →
  erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
Proof.
  intros. rewrite -(take_drop_middle tp j (fill K e)) //.
  rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
    eauto using lookup_lt_Some, Nat.lt_le_incl.
  rewrite -(assoc_L (++)) /=. eexists.
  eapply step_atomic; eauto. by apply: Ectx_step'.
Qed.

Lemma step_insert_no_fork K tp j e σ κ e' σ' :
  tp !! j = Some (fill K e) → head_step e σ κ e' σ' [] →
  erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

Lemma step_pure E j K e e' (P : Prop) n :
  P →
  PureExec P n e e' →
  nclose nspace ⊆ E →
  spec_ctx * tpool_mapsto j (fill K e) |-- |={E}=> spec_ctx ∗ tpool_mapsto j (fill K e').
Proof.
  iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
  iDestruct "Hspec" as (ρ) "Hspec".
  iInv nspace as (tp σ) "[>Hrtc >Hown]" "Hclose".
  iDestruct "Hrtc" as %Hrtc.
  iDestruct "Hj" as (sh) "[Hnonempty Hj]".
  iPure "Hnonempty" as shNonEmpty.
  iDestruct (ref_sub (P:= spec_ghost) with "[$Hown $Hj]") as "%Hghost_join".
  iCombine "Hj Hown" as "Hghost_ref".
  (* NOTE: this replaces the iris ghost-update entirely; we prove it's valid in the { } *)
  iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hghost_ref") as "Hghost_ref".
  iDestruct ((part_ref_update (P:= spec_ghost) _ _ _ _ (({[j := Some (fill K e')]}),
                 to_heap gmap_empty) ((<[ j := Some (fill K e') ]> (to_tpool tp)), to_heap (heap σ))) with "Hghost_ref") as ">Hghost_ref". 
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
          (* inv is just like inversion *)
          inv Htp; constructor.
          inv H3; constructor.
          inv H4.
        + rewrite ! lookup_insert_ne; auto.
          rewrite lookup_empty.
          pose proof Htp k as Htpk.
          rewrite lookup_singleton_ne in Htpk; auto.
      * auto.
    - intros Oldg.
      inv Oldg.
      rewrite insert_singleton.
      reflexivity.
  }
  iDestruct (ghost_part_ref_join (P:= spec_ghost) with "[$Hghost_ref]") as "[Hj Hown]".
  iExists sh.
  (* NOTE: I am not sure why I need to do this manually *)
  (* pull out the pure fact to solve *)
  iApply fupd_frame_l.
  iSplitR. { auto. }
  iFrame "Hj". 
  iApply "Hclose".
  iNext.
  iExists (<[j:=fill K e']> tp), σ.
  iFrame. 
  assert ((to_tpool tp) !!  j = Some (Some (fill K e))) as Htpj.
  {
      if_tac in Hghost_join.
      - inversion Hghost_join.
        rewrite lookup_singleton.
        reflexivity.
      - destruct Hghost_join as [full_state Hghost_join].
        inversion Hghost_join as [Htp Hheap]; simpl in *.
        specialize (Htp j).
        rewrite lookup_singleton in Htp.
        inv Htp; auto.
        inv H4; auto.
        inv H5.
  }
  rewrite to_tpool_insert'; last eauto. 
  iSplit; auto.
  iPureIntro.
  apply rtc_nsteps_1 in Hrtc; destruct Hrtc as [m Hrtc].
  specialize (Hex HP). apply (rtc_nsteps_2 (m + n)).
  eapply nsteps_trans; eauto.
  clear Hghost_join.
  revert e e' Htpj Hex.
  induction n => e e' Htpj Hex.
  - inversion Hex; subst.
    rewrite list_insert_id; eauto. econstructor.
  - apply nsteps_inv_r in Hex.
    destruct Hex as [z [Hex1 Hex2]].
    specialize (IHn _ _ Htpj Hex1).
    eapply nsteps_r; eauto.
    replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert. apply lookup_lt_is_Some; eauto. }
Qed.

(* refines_right_pure_r
    We can take pure steps!
*)
Lemma refines_right_pure_r e e' Φ E j K' n:
  PureExec Φ n e e' ->  Φ ->
  nclose nspace ⊆ E ->
  (refines_right j (ectxi_language.fill K' e)) |-- 
    |={E}=> (refines_right j (ectxi_language.fill K' e') ).
Proof.
  intros.
  iIntros "Rprev".
  iPoseProof ((step_pure _ _ _ _ _ _ _ H0 H) with "[Rprev]") as "Rprev"; first eauto.
  unfold refines_right.
  rewrite <- fill_app.
  iFrame.
  unfold refines_right.
  rewrite <- fill_app.
  auto.
Qed.

End lemmas.
