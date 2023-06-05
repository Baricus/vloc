Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.rev.

(* NOTE: don't need a module! *)
Definition rev_internal : heap_lang.val := 
  (* NOTE: there is a difference between λ: and rec:  besides notation! Recursion! *)
  (rec: "rev_internal" "prev" "cur" :=
    match: "cur" with
      (* return the new head of the list, the end *)
      NONE        => "prev"
      (* turn rest to previous and return *)
    | SOME "node" => 
        (* Due to notation differences, we need to have a few paranthesis lying about *)
        let: "elem" := Fst (!"node") in
        let: "rest" := Snd (!"node") in
        "node" <- ("elem", "prev");;
        "rev_internal" (SOME "node") "rest" 
    end%Ei). (* without this scope tag, this does not work; I do not know why *)

(* NOTE: "rev_internal" (quotes) does not work, but rev_internal does *)
Definition iRev : heap_lang.val := λ: "list", (rev_internal NONE "list").

#[local] Instance prog_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(*
   We'll need a way to compare VST lists and iris lists.
   We could do something direct, but it's probably easier
   to just say that they both equal the same Coq level list.

   For simplicity, let's stick to integers. 
*)

(* first a VST list *)
Definition node_t := Tstruct _node noattr.

Fixpoint Vlist (sigma: list Z) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
    (* NOTE: should malloc_token be here? -> Probably!  It makes sense here. *)
    data_at Ews node_t (Vint (Int.repr h),y) p  *  malloc_token Ews node_t p * Vlist hs y
 | nil => 
    (!! (p = nullval) && emp)%logic
 end.

(* now an iris list *)

(* NOTE: we don't want an iris heap here directly, we want our simulated one. *)
Fixpoint Ilist (sigma : list Z) v : mpred :=
  match sigma with
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (#p) ⌝ ∗ ∃ (v' : ival), p |-> ((#x), v')%V ∗ Ilist xs v'
  | [] => (!! (v = InjLV (LitV LitUnit)) && emp)%logic
  end.

(* and we can compare them *)
Definition EquivList σ V I : mpred
  := (Ilist σ I * Vlist σ V)%logic.

(*NOTE: gather_SEP really runs let i := fresh "i" in freeze i := L; thaw i. for any input L *)

(* We'll need a bunch of helpers describing how EquivList works *)
(* It would also be good to have stuff for Vlist and Ilist but we can wrap them up for this proof *)

(* If either value is it's NULL equivalent, the list is empty *)
Lemma Equiv_null_l σ Ival :
  EquivList σ nullval Ival |-- EquivList [] nullval Ival.
Proof.
  destruct σ; auto.
  (*NOTE: how to do in one step? *) 
  iIntros "[Ri Rv]".
  iDestruct "Rv" as (y) "[[Rnull Rtok] Rrest]"; fold Vlist.
  (* I feel like this should be automatic at this point, but I don't know for sure *)
  iDestruct (field_at_ptr_neq_null with "Rnull") as "%Hcontra".
  exfalso.
  apply Hcontra.
  apply ptr_eq_nullval.
Qed.

Lemma Equiv_null_r σ Vval :
  EquivList σ Vval (InjLV (#())) |-- (EquivList [] Vval (InjLV (#()))).
Proof.
  destruct σ; auto.
  iIntros "[Ril Rvl]".
  iDestruct "Ril" as (p) "[%Hcontra RUselessButICantDrop]"; fold Ilist.
  discriminate.
Qed.

(* If the list is empty, both values are known to be null *)
Lemma Equiv_empty Vval Ival :
  EquivList [] Vval Ival |-- (!! (Vval = nullval) && !! (Ival = (InjLV (#()))) && EquivList [] Vval Ival).
Proof.
  iIntros "[[%Ri _] [%Rv _]]".
  auto.
Qed.

(* Null is the same as an empty list *)
Lemma Equiv_emp_nullList:
  emp |-- EquivList [] nullval (InjLV (#())).
Proof.
  iIntros "_".
  auto.
Qed.


(* for the non-empty cases *)

(* If either value is not null, then both aren't null and the list has a head *)
Lemma Equiv_not_null σ Vval Ival :
  (Vval ≠ nullval \/ Ival ≠ (InjLV (#()))) ->
  (EquivList σ Vval Ival |-- EX (s : Z), EX (σ' : list Z), (!! (Vval ≠ nullval /\ Ival ≠ (InjLV (#())))) &&  (EquivList (s :: σ') Vval Ival))%logic.
Proof.
  (* exhaustive check of all the cases *)
  intros H; destruct H as [HV | HI]; destruct σ as [| s σ'].
  {
    iIntros "[_ [%Contra _]]".
    contradiction.
  }
  2:{
    iIntros "[[%Contra _] _]".
    contradiction.
  }
  1,2:
    iIntros "[Ri Rv]";
    iDestruct "Rv" as (Vval') "[[Rdat Rmal] Rvr]";
    iDestruct "Ri" as (l HIval') "[%iv [Ripts Rir]]";
    iDestruct (field_at_ptr_neq_null with "Rdat") as "%Hvpt";
    iExists s;
    iExists σ';
    fold Vlist Ilist.
  - iSplitR; auto.
    + iPureIntro; split; auto.
      rewrite HIval'.
      auto.
    + unfold EquivList; simpl.
      iSplitL "Ripts Rir".
      { iExists l. iSplitR; auto. iExists iv. iFrame.  }
      { iExists Vval'. iFrame. }
  - iSplitR; auto.
    + iPureIntro; split; auto.
      destruct (eq_dec Vval nullval); auto.
      subst Vval.
      exfalso.
      apply Hvpt.
      apply ptr_eq_nullval.
    + unfold EquivList; simpl.
      iSplitL "Ripts Rir".
      { iExists l. iSplitR; auto. iExists iv. iFrame.  }
      { iExists Vval'. iFrame. }
Qed.

(* If the list has a head, then we can pull out the head of both sublists *)
Lemma Equiv_pop s σ' Vval Ival:
  EquivList (s :: σ') Vval Ival |-- 
      (EX Vval', EX Ival', EX (p : loc), (
      (!! (Ival = InjRV (#p) /\ Vval ≠ nullval) && (data_at Ews node_t (Vint (Int.repr s),Vval') Vval * malloc_token Ews node_t Vval) * p |-> (#s, Ival')%V *
      EquivList σ' Vval' Ival'))).
Proof.
  iIntros  "[RI RV]".
  simpl.
  iDestruct "RI" as (p Hip Ival') "(RIpts & Ri')".
  iDestruct "RV" as (Vval') "[[Rvdata Rvmal] Rv']".
  iExists Vval'.
  iExists Ival'.
  iExists p.
  iSplitR "Ri' Rv'".
  2: iFrame.
  iSplitR "RIpts"; auto.
  iSplit; last iFrame.
  iSplit; auto.
  iPoseProof (field_at_ptr_neq_null with "Rvdata") as "%H".
  iPureIntro.
  intro Hcontra.
  subst Vval.
  assert (ptr_eq nullval nullval = true); auto.
  apply ptr_eq_True.
  apply mapsto_memory_block.is_pointer_or_null_nullval.
  destruct H.
  rewrite H0.
  auto.
Qed.


(* Likewise, if we have all the stuff to add a head, we can *)
Lemma EquivList_push v v' i i' (l : loc) s σ:
  ((i = InjRV (#l)) /\ (v ≠ nullval)) -> (EquivList σ v' i' * data_at Ews node_t (Vint (Int.repr s), v') v * malloc_token Ews node_t v * l |-> (#s, i')%V) |-- EquivList (s :: σ) v i.
Proof.
  iIntros (Hnnull) "[[[[Ri Rv] Rdata] Rmalloc] Rpts]".
  destruct Hnnull as [Hi Hv].
  unfold EquivList.
  iSplitL "Rpts Ri".
  - iExists l; fold Ilist.
    iSplitR; auto.
    iExists i'.
    iFrame.
  - iExists v'; fold Vlist.
    iFrame.
Qed.
  
(* VST helper so we don't have to reprove things about nullval al the time *)
Lemma EquivList_local_facts σ v i:
   EquivList σ v i |--
       !! (is_pointer_or_null v /\ (v=nullval <-> σ=nil) /\ (i=(InjLV (#())) <-> σ=nil)).
Proof.
  iIntros "EqList".
  destruct σ.
  - iDestruct "EqList" as "[[%Ilist _] [%Vlist _]]".
    subst v; subst i.
    iPureIntro.
    split; first apply mapsto_memory_block.is_pointer_or_null_nullval. (* I hope I never apply this lemma again *)
    split; split; auto.
  - iDestruct (Equiv_pop with "EqList") as (v' i' p) "[[[[%Hi %Hv] [Hdata Hmalloc]] ptsTo] EqList']".
    subst i.
    iDestruct (data_at_valid_ptr with "Hdata") as "Hvalid"; auto.
    { rewrite sizeof_Tstruct; simpl. lia. } (* NOTE: This is a weird goal.  Why does it come up? *)
    iSplitL.
    { destruct v; auto. }
    iPureIntro; split; split; intro; try contradiction; try list_solve.
Qed.
#[export] Hint Resolve EquivList_local_facts : saturate_local.


(* replace P with 2 args ->
    one is black box precondition (prop + local)
    one is list of mpreds (add on before SEPx)
*)
(*
Definition refines argTs retT with_type (P : with_type -> argsEnviron -> mpred)  (rhs : with_type -> sum iexp ref_id) (A : val -> ival -> mpred) :=
    NDmk_funspec (argTs, retT) cc_default (with_type * ref_id)
    (fun '(w_typ, ctx) => P w_typ * 
      liftx (H:=LiftAEnviron _) (
      match rhs w_typ with
      | inl e' => refines_right ctx e'
      | inr k => !! (ctx = k) && emp
      end
    ))%logic
    (
    fun '(_, ctx) =>
    PROP()
    LOCAL()
    SEP(EX Vres, EX Ires, (sepcon (A Vres Ires) (refines_right ctx (of_val Ires))))
    )
    .

Notation "'GIVEN' ( g1 * .. * gn ) 'PRE' [ t ; .. ; t' ] spec 'POST' [ rtyp ] 'RHS' ( rhs ) 'A' ( a )" :=  (
  refines (cons t .. (cons t' nil) ..) rtyp
  (prod g1 (.. (prod gn ()) ..))
    spec
  rhs
  a
  ) (only parsing).
 *)


Definition refines argTs retT with_type propL paramsL globalsL sepL (rhs : with_type -> sum iexp ref_id) (A : val -> ival -> mpred) :=
  NDmk_funspec (argTs, retT) cc_default (with_type * ref_id)
    (fun '(wth_vals, ctx) =>
      PROPx (propL wth_vals) (PARAMSx (paramsL wth_vals) (GLOBALSx (globalsL wth_vals) (SEPx
      (cons 
        (match rhs wth_vals with
         | inl e' => refines_right ctx e'
         | inr k => !! (ctx = k) && emp
         end
        )%logic 
        (sepL wth_vals))
      )))
    ) 
    (fun '(_, ctx) =>
      PROP()
      LOCAL()
      SEP(EX Vres, EX Ires, ((A Vres Ires) * (refines_right ctx (of_val Ires))))
    )
  .


Notation "'GIVEN' ( g1 * .. * gn ) 'PRE' [ t ; .. ; t' ] spec 'POST' [ rtyp ] 'RHS' ( rhs ) 'A' ( a )" :=  (
  refines (cons t .. (cons t' nil) ..) rtyp
  (prod g1 (.. (prod gn ()) ..))
    spec
  rhs
  a
  ) (only parsing).

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
  GIVEN (globals * val * val * heap_lang.val * heap_lang.val * list Z * list Z)
  PRE [tptr node_t ; tptr node_t]
  (fun '(gv, Vprev, Vcur, Iprev, Icur, Lcur, Lprev, _) =>
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur)
    )
  POST [tptr node_t]
  RHS(fun '(gv, Vprev, Vcur, Iprev, Icur, Lcur, Lprev, _) => inl (of_val rev_internal Iprev Icur))
  A(fun v i => EX σ, EquivList σ v i)
  .
  
Definition rev_list_internal_spec_old :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival, Lcur: list Z, Lprev: list Z
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur ;
            refines_right ctx ((of_val rev_internal) Iprev Icur))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


(* the wrapper to just reverse a list *)
Definition rev_list_spec :=
  DECLARE _rev_list
    WITH gv: globals, ctx: ref_id, Vhead: val, Ihead: ival, σ: list Z
    PRE [ tptr node_t ]
      PROP()
      PARAMS(Vhead)
      GLOBALS()
      SEP(EquivList σ Vhead Ihead ;
            refines_right ctx ((of_val iRev) Ihead))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


(* While this isn't really needed, I wanted to test out allocation, so we'll verify this too *)

(* heap lang version of an empty node *)
Definition empty_node : heap_lang.val :=
  λ: "_", (let: "l" := (Alloc ((#0), InjLV (#()))) in (SOME "l")%V)%Ei.

Definition empty_node_spec :=
  DECLARE _empty_node
    WITH gv: globals, ctx: ref_id
    PRE []
      PROP()
      PARAMS()
      GLOBALS(gv)
      SEP(mem_mgr gv; refines_right ctx ((of_val empty_node) (#())))
    POST [tptr node_t ]
      EX V: val, EX I : ival,
      PROP()
      RETURN(V)
      SEP(mem_mgr gv; EquivList [0]%Z V I; (refines_right ctx (ectxi_language.of_val I))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec ;
    empty_node_spec
  ]).

Ltac start_function1_mod :=
  leaf_function;
   lazymatch goal with
   | |- semax_body ?V ?G ?F ?spec =>
         check_normalized F; function_body_unsupported_features F;
          (let s := fresh "spec" in
           pose (s := spec); hnf in s; cbn zeta in s;
            repeat
             lazymatch goal with
             | s:=(_, NDmk_funspec _ _ _ _ _):_ |- _ => fail
             | s:=(_, mk_funspec _ _ _ _ _ _ _):_ |- _ => fail
             | s:=(_, ?a _ _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _):_ |- _ => unfold a in s
             | s:=(_, ?a):_ |- _ => unfold a in s
             end;
            lazymatch goal with
            | s:=(_, WITH _ : globals PRE [ ] main_pre _ _ _ POST [tint] _):_
              |- _ => idtac
            | s:=?spec':_ |- _ => check_canonical_funspec spec'
            end; change (semax_body V G F s); subst s; 
            unfold NDmk_funspec')
   end;
   (let DependedTypeList := fresh "DependedTypeList" in
    unfold NDmk_funspec;
     match goal with
     | |- semax_body _ _ _ (_, mk_funspec _ _ _ ?Pre _ _ _) =>
           split3; [ check_parameter_types' | check_return_type |  ];
            match Pre with
            | λ _, convertPre _ _ (λ i, _) =>
                intros Espec DependedTypeList i
            | λ _ x, match _ with
                     | (a, b) => _
                     end => intros Espec DependedTypeList [a b]
            | λ _ i, _ => intros Espec DependedTypeList i
            end; simpl fn_body; simpl fn_params; simpl fn_return
     end;
     try
      match goal with
      | |- semax _ (λ rho, (?A rho * ?B rho)%logic) _ _ =>
            change (λ rho, (?A rho * ?B rho)%logic) with (A * B)%logic
      end; simpl _functor in *; simpl dependent_type_functor_rec; clear
     DependedTypeList; rewrite_old_main_pre;
     repeat
      match goal with
      | |- semax _ (match ?p with
                    | (a, b) => _
                    end * _)%logic _ _ => destruct p as [a b]
      | |-
        semax _
          (close_precondition _ match ?p with
                                | (a, b) => _
                                end * _)%logic _ _ => 
        destruct p as [a b]
      | |-
        semax _
          (close_precondition _ (match ?p with
                                | (a, b) => _
                                end * _) * _)%logic _ _ => 
        destruct p as [a b]
      | |- semax _ (match ?p with
                    | (a, b) => _
                    end eq_refl * _)%logic _ _ => 
        destruct p as [a b]
      | |-
        semax _
          (close_precondition _ (match ?p with
                                 | (a, b) => _
                                 end eq_refl) * _)%logic _ _ =>
            destruct p as [a b]
      | |-
        semax _
          (close_precondition _
             (λ ae,
                !! (length ae.2 = ?A) &&
                ?B (make_args ?C ae.2 (mkEnviron ae.1 _ _))) * _)%logic _ _
        =>
            match B with
            | match ?p with
              | (a, b) => _
              end => destruct p as [a b]
            end
      end; try start_func_convert_precondition).

Lemma PROP_PARAMS_GLOBALS_SEP_cons F P1 P2 P3 P4: 
  PROPx P1 (PARAMSx P2 (GLOBALSx P3 (SEPx (F :: P4)))) = (liftx (H:=LiftAEnviron _) F * PROPx P1 (PARAMSx P2 (GLOBALSx P3 (SEPx P4))))%logic.
Proof.
  change (SEPx (F :: P4)) with (liftx (H:=LiftAEnviron _) F * SEPx P4)%logic.
  unfold PROPx, GLOBALSx, LOCALx.
  unfold_lift; extensionality rho.
  unfold local, lift1.
  simpl.
  apply pred_ext;
    normalize;
    iIntros "[Ra [Rb [Rc Rd]]]";
    iFrame.
Qed.

Ltac start_refinement spec :=
  unfold spec;
  unfold refines;
  start_function1_mod; 
  repeat match goal with
  | [H : (?w * ref_id) |- ?b] => destruct H as [a ctx]
  end;
  rewrite (sepcon_comm (PROP () PARAMS (_ ; _) SEP (_ ; _)));
  rewrite <- (PROP_PARAMS_GLOBALS_SEP_cons);
  start_function2;
  start_function3;
  simpl.

Lemma rev_internal_lemma : semax_body Vprog Gprog f_rev_list_internal rev_list_internal_spec.
Proof.
  start_refinement rev_list_internal_spec.
  (*start_function.*)
  unfold rev_internal.
  (* NOTE: To get rid of the %Ei tag *)
  (*Open Scope iris_expr_scope.*)
  SPR_beta; fold rev_internal. (* do remember to fold this! Things are messy otherwise *)
  SPR_recc; SPR_beta.
  (* either cur is null or not *)
  destruct (eq_dec Vcur nullval); subst.
  {
    (* if it is null, then the iris one is too *)
    sep_apply Equiv_null_l; sep_apply Equiv_empty.
    Intros.
    rename H into HIcurNull.
    subst Icur.

    (* Step iris to ending *)
    SPR_inl.
    SPR_recc.
    SPR_beta.

    (* We cannot get past this if statement in this case *)
    forward_if (
      PROP (False)
      LOCAL()
      SEP()
    ).
    {
      forward.
      iIntros "[[ReqNull _] ReqPrev]".
      iExists Vprev.
      iExists Iprev.
      iSplitR "ReqNull"; iFrame.
      iExists Lprev.
      iFrame.
    }
    {
      (* Null != Null *)
      contradiction.
    }
  }
  {
    (* If it's not null, then... *)

    (* we have an element in BOTH lists *)
    sep_apply (Equiv_not_null Lcur); [left; auto|].
    Intros c Lcur'; clear Lcur.
    sep_apply (Equiv_pop c Lcur').
    Intros Vcur' Icur' IlocCur.
    rename H0 into HIlocCur; subst Icur.

    (* and we can reduce the right hand side! *)
    SPR_inr.
    SPR_recc; SPR_beta.

    (* including loads *)
    SPR_load IlocCur.
    SPR_fst.
    SPR_recc.
    SPR_beta.
    SPR_load IlocCur.
    SPR_snd.
    SPR_recc.
    SPR_beta.

    SPR_pairc. (* I hate this :( *)
    SPR_store IlocCur (#c, Iprev)%V. (* NOTE: how to get rid of the %V here? -> needed for notation to fire *)

    (* now we step *)
    SPR_recc; SPR_beta.

    (* run the right side to the same point now *)

    (* This if statement cannot be entered *)
    forward_if.
    { contradiction. }

    forward.
    forward.

    (* we added a new element to the front of Lprev *)
    sep_apply (EquivList_push Vcur Vprev (InjRV (#IlocCur))); auto.
    (*viewshift_SEP' (IlocCur |-> _) (data_at _ _ _ _) (malloc_token _ _ _) (EquivList Lprev _ _) *)
        (*(EquivList (c :: Lprev) Vcur (InjRV (#IlocCur))%V).*)
    (*{*)
      (*entailer!.*)
      (*iIntros "[[[Rpt Rdta] Rmlc] Reqt]".*)
      (*iModIntro.*)
      (*iApply EquivList_push; auto.*)
      (*iFrame.*)
    (*}*)

    (* Almost forgot this step! *)
    SPR_injrc.

    (* If Ei is open here, this will break; I think it conflicts *)
    forward_call (gv, Vcur, Vcur', (InjRV (#IlocCur))%V, Icur', Lcur', (c :: Lprev), (), ctx).

    Intros ret.
    destruct ret as [p lret]; destruct p as [vret iret].
    forward.

    Exists vret.
    Exists iret.
    Exists lret.
    entailer!.
  }
Qed.


Lemma rev_list_lemma : semax_body Vprog Gprog f_rev_list rev_list_spec.
Proof.
  start_function; unfold iRev.
  SPR_beta.
  SPR_injlc.
  forward_call (gv, ctx, nullval, Vhead, (InjLV (#())), Ihead, σ, ([] : list Z)).
  { iIntros "Re". iDestruct (Equiv_emp_nullList with "Re") as "R". iVST; cancel. }

  Intros tuple.
  destruct tuple as [[v' i'] σ'].
  simpl.
  forward.
  Exists v'.
  Exists i'.
  Exists σ'.
  entailer!.
  unfold ectxi_language.of_val; simpl.
  cancel.
Qed.


Lemma empty_node_lemma : semax_body Vprog Gprog f_empty_node empty_node_spec.
Proof.
  start_function.
  unfold empty_node.

  (* allocate the C node *)
  forward_call (node_t, gv).
  Intros ptr.

  (* allocate the heap_lang node *)
  SPR_beta.
  SPR_pairc.

  SPR_alloc.
  Intros l.

  SPR_recc.
  SPR_beta.

  (* now we go through the if statement *)
  destruct (eq_dec ptr nullval).
  {
    (* If we have null, we can prove false since exit *)
    forward_if (PROP(False) LOCAL() SEP()).
    {
      forward_call.
      contradiction.
    }
    contradiction.
  }

  {
    (* If we don't have null, we continue *)
    rewrite if_false; auto.
    evar (e : iexp); evar (v : ival). (* so we don't rewrite them all *)
    forward_if (
      PROP()
      LOCAL(temp _ptr ptr; gvars gv)
      SEP(refines_right ctx e; (l |-> v); mem_mgr gv; malloc_token Ews node_t ptr; data_at_ Ews node_t ptr)
    ); subst e v.
    {
      (* We can't enter the if *)
      contradiction.
    }
    {
      (* Skipping it just gives us what we already know in this case *)
      forward.
      entailer!.
      apply derives_refl.
    }

    rename n into HnotNull.

    (* Now we initialize memory *)
    do 2 forward.

    (* Don't forget to build our list *)
    (* NOTE: this doesn't seem to like sep_apply *)
    viewshift_SEP' (malloc_token _ _ _) (EquivList [] nullval (InjLV (#())) * malloc_token Ews node_t ptr)%logic.
    {
      go_lower.
      iIntros "Rmalloc"; iFrame.
      iApply Equiv_emp_nullList.
      auto.
    }
    Intros.
    SPR_injrc.

    (* also add the one element to it *)
    viewshift_SEP' (EquivList [] _ _) (malloc_token _ _ _) (data_at _ _ _ _) (_ |-> _) (EquivList [0]%Z ptr (InjRV (#l))%V).
    {
      go_lower.
      iIntros "[[Rm Ra] Rpt]".
      iApply EquivList_push; auto.
      iModIntro.
      iFrame.
    }

    (* and return *)
    forward.

    Exists ptr.
    Exists (InjRV (#l)).
    simpl.
    entailer!.
  }
Qed.
