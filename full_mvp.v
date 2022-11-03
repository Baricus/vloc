Require Import iris.program_logic.language.
Require Import iris.program_logic.ectxi_language.

Require Import iris.bi.lib.atomic.
From iris.heap_lang Require Export lang derived_laws metatheory.
From iris.heap_lang Require Import proofmode.
Require Import stdpp.list.

From VST.veric Require Import rmaps compcert_rmaps.

Require Import VST.veric.bi.

Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import Program.Equality.
From iris.algebra Require Import excl gmap.
Require Import VST.floyd.proofauto.
Require Import VST.concurrency.invariants.
(*Separate import needed!*)
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.ghostsI.
Require Import VST.concurrency.fupd.

Require Import VST.floyd.library.

(* Taken from theories/logic/proofmode/spec_tactics!!! *)
(** Tactics for updating the specification program. *)
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.

(*Not needed currently *)
Require Import Top.mvp.


Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Section refinement.

(* declare context; a name for the state, the location type, and the ectxi language *)
Context `{gName : own.gname, nspace : namespace}.

(*define shorthand *)
Definition ival := heap_lang.val.
Definition iexp := heap_lang.expr.

(*map => gmap*)
Definition tpool_ghost := (gmap_ghost (K:=nat) (A:=(exclusive_PCM iexp))).
(*This feels weird; why does gmap_ghost take a Type?  I hope this works *)
Definition heap_ghost := (gmap_ghost (K:=loc) (A:=(@pos_PCM (discrete_PCM (option ival))))). (*(@pos_PCM (discrete_PCM (option ival)))).*)
Compute @G heap_ghost. (*it has the right type at least*)
Definition spec_ghost := prod_PCM tpool_ghost heap_ghost.

(*The reference has no share, so we can't combine it*)
Definition InvGhost (map : @G spec_ghost) := @ghost_reference spec_ghost map gName.
Definition UsrGhost (map : @G spec_ghost) := EX s, (@ghost_part spec_ghost s map gName).


(*Couldn't use the nice things :( *)
(*Fixpoint map_seq_int {t} (n : nat) (exps : list t) := *)
  (*match exps with*)
  (*| [] => []*)
  (*| e :: es => (n, e) :: map_seq_int (n+1) es*)
  (*end.*)
(*Definition map_seq {t} exps := @map_seq_int t 0 exps.*)

(*heap stuff, this is painful*)
(*Fixpoint lookup {K : Type} {V : Type} (eq : K -> K -> bool) (l : list (K * V)) (key : K) : option V :=*)
  (*match l with*)
  (*| [] => None*)
  (*| ((k, v) :: pairs) => if eq key k then Some v else lookup eq pairs key*)
  (*end.*)

(*convert list of expressions to thread pool*)
Compute @G tpool_ghost.
Definition to_tpool (exps : list iexp) : @G tpool_ghost
  := Some <$> (map_seq 0 exps).

 (*this is horrible and a case for using gmaps directly *)
(*Compute (@G tpool_ghost).*)
(*Definition tpool_update (gtp : @G tpool_ghost) (j : nat) (e : iexp) : @G tpool_ghost*)
  (*:= λ n, (if n =? j then Some (Some e) else gtp n).*)

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

Definition refines_right (r : ref_id) (e : iexp) := 
  (spec_ctx * (tp_id r) |=> (fill (tp_ctx r) e))%logic.

Definition refines f2 A : funspec :=
  WITH gv: globals, ctx: ref_id
  PRE [ (* types of function parameters *) ]
    PROP()
    PARAMS((* NOTE: how to handle parameters *))
    GLOBALS((* do we need anything to correlate globals and Context? Hopefully not *))
    SEP(refines_right ctx f2)
  POST [ tint ] (* NOTE: type!!! A map of iris types to vst types? *)
    EX v' : ival, EX v : val,
    PROP()
    RETURN(v)
    SEP(refines_right ctx (ectxi_language.of_val v') * A v v').

End refinement.

Context `{gName : own.gname, nspace : namespace}.
Definition refines_heap_lang e A : funspec := refines  (gName := gName) (nspace:= nspace) e A.

Definition ret_one : iexp := Val (LitV (heap_lang.LitInt 1%Z)).
(*NOTE: diff between ectxi language and ectx language?*)
Definition fspec := DECLARE _returns_one refines_heap_lang ret_one 
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z))&&emp)%logic.
Definition Gprog : funspecs := [fspec].

Lemma one: semax_body Vprog Gprog f_returns_one fspec.
Proof.
  unfold fspec, refines_heap_lang, refines.
  start_function.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
  unfold ret_one.
  simpl.
  cancel.
Qed.

  
Lemma tpool_lookup tp j : to_tpool tp !! j = Some <$> tp !! j.
Proof.
  unfold to_tpool. rewrite lookup_fmap.
  by rewrite lookup_map_seq_0.
Qed.

Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Some (Some e) → tp !! j = Some e.
Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
Hint Resolve tpool_lookup_Some : core.

(*#[export] Instance insert_test : Insert nat iexp (list iexp).*)
(*Proof.*)
  (*unfold Insert.*)
  (*auto.*)
(*Qed.*)
(*#[export] Instance insert_test' : Insert nat (option iexp) (@G tpool_ghost).*)
(*Proof.*)
  (*unfold Insert; auto.*)
(*Qed.*)

(* Borrowed from spec_ra *)
Compute @G tpool_ghost.
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

(*#[export] Instance gmap_alg : Perm_alg (gmap nat (option iexp)).*)

Lemma step_pure E j K e e' (P : Prop) n :
  P →
  PureExec P n e e' →
  (*NOTE: I don't know if this is how you use a vst namespace in Iris logic *)
  nclose nspace ⊆ E →
  @spec_ctx gName nspace * @tpool_mapsto gName j (fill K e) |-- |={E}=> @spec_ctx gName nspace ∗ @tpool_mapsto gName j (fill K e').
Proof.
  iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
  iDestruct "Hspec" as (ρ) "Hspec".
  (* unfolded the things to try to debug *)
  (*unfold spec_inv, UsrGhost.*)
  (*unfold ghost_part, InvGhost, ghost_reference.*)
  (* I should be able to remove the modality here to progress *)
  iInv nspace as (tp σ) "[>Hrtc >Hown]" "Hclose".
  iDestruct "Hrtc" as %Hrtc.
  iDestruct "Hj" as (sh) "Hj".
  iDestruct (ref_sub (P:= spec_ghost) with "[$Hown $Hj]") as "%Hghost_join".
  (* Turns out we need the ghost_part_ref for the easy update *)
  iCombine "Hj Hown" as "Hghost_ref".
  iDestruct (ghost_part_ref_join (P:= spec_ghost) with "Hghost_ref") as "Hghost_ref".
  iDestruct ((part_ref_update (P:= spec_ghost) _ _ _ _ (({[j := Some (fill K e')]}),
                 to_heap gmap_empty) ((<[ j := Some (fill K e') ]> (to_tpool tp)), to_heap (heap σ))) with "Hghost_ref") as ">Hghost_ref". 
  {
    intros Gframe Hjoin.
    split.
    - hnf.
      destruct Hjoin as [Htp Hheap].
      split; simpl in *.
      * iIntros (k).
        destruct (eq_dec k j).
        + subst.
          rewrite lookup_singleton.
          specialize (Htp j).
          rewrite lookup_singleton in Htp.
          rewrite lookup_insert.
          inv Htp; constructor.
          inv H3; constructor.
          inv H4.
        + 
          rewrite ! lookup_insert_ne; auto.
          rewrite lookup_empty.
          pose proof Htp k as Htpk.
          rewrite lookup_singleton_ne in Htpk; auto.
      * auto.
    - intros Oldg.
      inversion Oldg.
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
    (*TODO: get rid of if_tac*)
      if_tac in Hghost_join.
      - inversion Hghost_join.
        fold (lookup (M:=gmap _ _) j {[j := fill K e]}).
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


(* Taken from theories/logic/proofmode/spec_tactics!!! *)

(** ** bind *)
Lemma tac_tp_bind_gen k Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, @refines_right gName nspace k e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (@refines_right gName nspace k e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_tp_bind k e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, @refines_right gName nspace k e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (@refines_right gName nspace k (fill K' e'))) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_tp_bind_gen. Qed.

Ltac tp_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "tp_normalise" constr(j) :=
  iStartProof;
  eapply (tac_tp_bind_gen j);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "tp_bind" constr(j) open_constr(efoc) :=
  iStartProof;
  eapply (tac_tp_bind j efoc);
    [iAssumptionCore (* prove the lookup *)
    |tp_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].

Lemma tac_tp_pure e K' e1 k e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them
     with backtracking using reashape_expr; see the accompanying Ltac.
     the first premise decomposes the expression, the second one checks
     that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose nspace ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, @refines_right gName nspace k e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (@refines_right gName nspace k e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. 
  intros -> Hpure ??? Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite /refines_right.
  rewrite -!fill_app.
  rewrite step_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Lemma refines_right_pure_r e e' Φ E j K' n:
  PureExec Φ n e e' ->  Φ ->
  nclose nspace ⊆ E ->
  (@refines_right gName nspace j (ectxi_language.fill K' e)) |-- 
    |={E}=> (@refines_right gName nspace j (ectxi_language.fill K' e') ).
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

Definition ret_one_plus : iexp := BinOp PlusOp (Val (LitV (heap_lang.LitInt 1%Z))) (Val (LitV (heap_lang.LitInt 0%Z))).

Ltac try_pures := try apply pure_injrc; try apply pure_injlc; try apply pure_fst; try apply pure_snd; try apply pure_pairc; try apply pure_exec; try apply pure_recc; try apply pure_if_false; try apply pure_if_true; try apply pure_case_inr; try apply pure_case_inl; try apply pure_exec_fill; try apply pure_unop; try apply pure_binop; try apply pure_beta; try apply pure_eqop.

Ltac step_pure_r ctx :=
  let e' := fresh "e'" in
  evar (e' : iexp);
  viewshift_SEP 0 (@refines_right gName nspace ctx e');
  first (
    go_lower;
    eapply (refines_right_pure_r _ _ _ _ _ [] 1);
    [ try_pures | auto | auto]
  );
  simpl in e';
  subst e'.

Lemma one_plus_zero : semax_body Vprog Gprog f_returns_one (DECLARE _returns_one refines_heap_lang ret_one_plus
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic).
Proof.
  unfold fspec, refines_heap_lang, refines.
  start_function.
  unfold ret_one_plus.
  step_pure_r ctx.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
  apply derives_refl.
Qed.
