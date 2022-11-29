Require Export iris.program_logic.language.
Require Export iris.program_logic.ectxi_language.

Require Export iris.bi.lib.atomic.
From iris.heap_lang Require Export lang derived_laws metatheory.
From iris.heap_lang Require Export proofmode.
Require Export stdpp.list.

From VST.veric Require Export rmaps compcert_rmaps.

Require Export VST.veric.bi.

Require Export VST.floyd.library.
Require Export VST.zlist.sublist.
Require Export Program.Equality.
From iris.algebra Require Export excl gmap.
Require Export VST.floyd.proofauto.
Require Export VST.concurrency.invariants.
(*Separate import needed!*)
Require Export VST.concurrency.ghosts.
Require Export VST.concurrency.ghostsI.
Require Export VST.concurrency.fupd.

Require Export VST.floyd.library.

(* Taken from theories/logic/proofmode/spec_tactics!!! *)
(** Tactics for updating the specification program. *)
From iris.proofmode Require Export
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.


Section refinement.

(* declare context; a name for the state, the location type, and the ectxi language *)
Class refines_ctx := { gName : own.gname; nspace : namespace }.
Context `{ref_ctx: refines_ctx}.

(*define shorthand *)
Definition ival := heap_lang.val.
Definition iexp := heap_lang.expr.

(*map => gmap*)
Definition tpool_ghost := (gmap_ghost (K:=nat) (A:=(exclusive_PCM iexp))).
(*This feels weird; why does gmap_ghost take a Type?  I hope this works *)
Definition heap_ghost := (gmap_ghost (K:=loc) (A:=(@pos_PCM (discrete_PCM (option ival))))). (*(@pos_PCM (discrete_PCM (option ival)))).*)
(*Compute @G heap_ghost. [>it has the right type at least<]*)
Definition spec_ghost := prod_PCM tpool_ghost heap_ghost.

(*The reference has no share, so we can't combine it*)
Definition InvGhost (map : @G spec_ghost) := @ghost_reference spec_ghost map gName.
Definition UsrGhost (map : @G spec_ghost) := EX s, (@ghost_part spec_ghost s map gName).

(*convert list of expressions to thread pool*)
(*Compute @G tpool_ghost.*)
Definition to_tpool (exps : list iexp) : @G tpool_ghost
  := Some <$> (map_seq 0 exps).

(*Converts a standard heap-lang heap to a form we can store it in VST*)
(*Largely a function of keys to values*)
Definition to_heap (heap : gmap loc (option ival)) : @G heap_ghost :=
  fmap (λ v, (Some (fullshare, v))) heap.

Definition spec_inv (c : cfg (heap_lang)) : mpred := 
    EX exp_list : list iexp, EX σ,
    (* tp is a list of expressions! σ is the state *)
    ⌜rtc erased_step c (exp_list, σ)⌝ &&
      (* take the left side of the ghost share *)
    @InvGhost ((to_tpool exp_list), to_heap (heap σ)).

Definition spec_ctx : mpred := 
  (EX ρ, inv nspace (spec_inv ρ)). 

(*Define our own singleton map and turn it to a VST map for the non-invariant side *)
Definition tpool_mapsto (j : nat) (e : iexp) := 
  UsrGhost ({[j := Some e]}, to_heap gmap_empty).
Notation "a |=> b" := (tpool_mapsto a b) (at level 20).

(*ref id maps references *)
Record ref_id : Set := RefId { tp_id : nat;  tp_ctx : list ectx_item }.

Definition add_to_ctx id (ctx : list ectx_item) : ref_id :=
  RefId (tp_id id) (ctx ++ tp_ctx id).

Definition refines_right (r : ref_id) (e : iexp) := 
  (spec_ctx * (tp_id r) |=> (fill (tp_ctx r) e))%logic.

End refinement.

Section lemmas.

Context `{ref_ctx: refines_ctx}.

Lemma refines_right_add_ctx ref K e :
  (refines_right ref (fill K e) = refines_right (add_to_ctx ref K) e).
Proof.
  unfold add_to_ctx, refines_right; simpl.
  rewrite fill_app.
  auto.
Qed.

Lemma tpool_lookup tp j : to_tpool tp !! j = Some <$> tp !! j.
Proof.
  unfold to_tpool. rewrite lookup_fmap.
  by rewrite lookup_map_seq_0.
Qed.

Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Some (Some e) → tp !! j = Some e.
Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
Hint Resolve tpool_lookup_Some : core.

(* Borrowed from spec_ra *)
(*Compute @G tpool_ghost.*)
Lemma to_tpool_insert tp (j:nat) (e:iexp) :
  (j < length tp)%nat →
  to_tpool (<[j:=e]> tp) = <[j:=Some e]> (to_tpool tp).
Proof.
  intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
  - by rewrite tpool_lookup lookup_insert list_lookup_insert.
  - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
    by rewrite tpool_lookup.
Qed.
Lemma to_tpool_insert' tp (j:nat) (e:iexp) :
  is_Some (to_tpool tp !! j) →
  to_tpool (<[j:=e]> tp) = <[j:=Some e]> (to_tpool tp).
Proof.
  rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
Qed.
Lemma to_tpool_snoc tp e :
  to_tpool (tp ++ [e]) = <[length tp:=Some e]>(to_tpool tp).
Proof.
  intros. apply: map_eq=> i.
  destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
  - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
  - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
  - rewrite lookup_insert_ne; last lia.
    rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
       change (ofe_car exprO) with expr; lia.
Qed.

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
  iDestruct "Hj" as (sh) "Hj".
  iDestruct (ref_sub (P:= spec_ghost) with "[$Hown $Hj]") as "%Hghost_join".
  iCombine "Hj Hown" as "Hghost_ref".
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

Lemma refines_right_split e j K E:
  nclose nspace ⊆ E →
  (refines_right j (ectxi_language.fill K e) |-- 
  |={E}=> (refines_right j (e))).
Proof.
  intros.
  iIntros "[#ctx tpool]".
  unfold refines_right.
  iModIntro.
  iSplit; auto.
  iDestruct "ctx" as (ρ) "ctx".
  unfold spec_inv.
Admitted.

End lemmas.

#[local] Ltac try_pures e' := first [
     apply pure_injrc 
   | apply pure_injlc 
   | apply pure_unop 
   | apply pure_binop 
   | apply pure_fst 
   | apply pure_snd 
   | apply pure_pairc 

   (* needed to ensure we can properly infer the true and false cases for some reason *)
   | match goal with
     | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
         subst e'; first [apply pure_if_false | apply pure_if_true]
     end
   (*| apply pure_if_true*)
   (*| apply pure_if_false*)
   | apply pure_case_inr 
   | apply pure_case_inl 
   (* Removes the goal created by pure_beta? *)
   | apply pure_beta; apply AsRecV_recv
   | apply pure_eqop
       (* since we're reshaping, this shouldn't be needed *)
   (*| apply pure_exec_fill *)
       (*I shouldn't need this one, I think?*)
   (*| apply pure_exec*)
   | apply (pure_recc _) (* allows inferrence? *)
   (* TODO: figure out how to actually fail with this *)
   | fail "Could not find a pure step to take (no pure_ tactic found)"
  ].

#[export] Ltac step_pure_r ctx :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try lia;
        clear Hcond
    (* otherwise, try to step to the next instruction *)
    | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          viewshift_SEP 0 (refines_right ctx (fill K e'));
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            [try_pures e' | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.


#[export] Ltac print_goal := match goal with
                   | |- ?p => idtac "GOAL IS: " p
                   end.
