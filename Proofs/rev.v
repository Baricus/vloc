(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

(* used for our modulus *)
Import compcert.lib.Integers.
Import proofmode notation.

Definition rev_internal : val := 
  (* NOTE: there is a difference between λ: and rec:  besides notation! Recursion! *)
  rec: "rev_internal" "prev" "cur" :=
    match: "cur" with
      (* return the new head of the list, the end *)
      NONE        => "prev"
      (* turn rest to previous and return *)
    | SOME "node" => 
        let: "elem" := Fst !"node" in
        let: "rest" := Snd !"node" in
        "node" <- ("elem", "prev");;
        "rev_internal" (SOME "node") "rest" 
    end.

(* NOTE: "rev_internal" (quotes) does not work, but rev_internal does *)
Definition iRev : val := λ: "list", (rev_internal NONE "list").

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.rev.


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
     (!! (p = nullval) && emp)%logic  (* NOTE: I used to have an emp here; why? -> Allows binding logic to empty memory *)
 end.

(* now an iris list *)
(* NOTE: should these be notations? *)
Definition iLit x := (LitV x).
Definition iUnit  := (LitUnit).
Definition iInt x := iLit (LitInt x).
Definition iPair l r := (PairV l r).

(* NOTE: we don't want an iris heap here directly, we want our simulated one. *)
Fixpoint Ilist (sigma : list Z) v : mpred :=
  match sigma with
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iLit (LitLoc p)) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => (!! (v = InjLV (LitV LitUnit)) && emp)%logic
  end.

(* and we can compare them *)
Definition EquivList σ V I : mpred
  := (Ilist σ I * Vlist σ V)%logic.


(* so I can stop seeing so many App constructors *)
Notation "a <AP> b" := (App a b) (at level 21, left associativity).

(*Notation "'RR' a b" := (refines_right a b) (at level 20, only printing).*)

(*NOTE: gather_SEP really runs let i := fresh "i" in freeze i := L; thaw i. for any input L *)


Lemma Equiv_null_l σ Ival :
  EquivList σ nullval Ival |-- EquivList [] nullval Ival.
Proof.
  destruct σ; auto.
  (*NOTE: how to do in one step? *)
  iIntros "[Ri Rv]".
  iDestruct "Rv" as (y) "[[Rnull Rtok] Rrest]".
  fold Vlist.
  iDestruct (field_at_ptr_neq_null with "Rnull") as "%Hcontra".
  exfalso.
  apply Hcontra.
  apply ptr_eq_nullval.
Qed.

Lemma Equiv_null_r σ Vval :
  EquivList σ Vval (InjLV (iLit iUnit)) |-- (EquivList [] Vval (InjLV (iLit iUnit))).
Proof.
  destruct σ; auto.
  iIntros "[Ril Rvl]".
  iDestruct "Ril" as (p) "[%Hcontra RUselessButICantDrop]".
  discriminate.
Qed.

Lemma Equiv_empty Vval Ival :
  EquivList [] Vval Ival |-- EquivList [] Vval Ival * (!! (Vval = nullval) && emp) * (!! (Ival = (InjLV (iLit (iUnit)))) && emp).
Proof.
  iIntros "[[%Ri _] [%Rv _]]".
  auto.
Qed.

(* for the non-empty cases *)
Lemma Equiv_not_null σ Vval Ival :
  (Vval ≠ nullval \/ Ival ≠ (InjLV (iLit iUnit))) ->
  EquivList σ Vval Ival |-- EX (s : Z), EX (σ' : list Z), (EquivList (s :: σ') Vval Ival).
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
    iIntros "R";
    iExists s;
    iExists σ';
    iFrame.
Qed.

Lemma Equiv_pop s σ' Vval Ival:
  EquivList (s :: σ') Vval Ival |-- 
      EX Vval', EX Ival', EX p:loc, (
      (data_at Ews node_t (Vint (Int.repr s),Vval') Vval * malloc_token Ews node_t Vval) *
      (!! (Ival = InjRV (iLit (LitLoc p))) && emp) * p |-> (iPair (iInt s) Ival') *
      EquivList σ' Vval' Ival').
Proof.
  iIntros  "[RI RV]".
  simpl.
  iDestruct "RI" as (p Hip Ival') "(RIpts & Ri')".
  iDestruct "RV" as (Vval') "[[Rvdata Rvmal] Rv']".
  iExists Vval'.
  iExists Ival'.
  iExists p.
  (*NOTE: where does this true come from? *)
  iFrame.
  auto.
Qed.
  

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival, Lcur: list Z, Lprev: list Z
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur ;
            refines_right ctx ((of_val iris.rev_internal) <AP> (Val Iprev) <AP> (Val Icur)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).

(* the equivalent wrappers *)
Definition rev_list_spec :=
  DECLARE _rev_list
    WITH gv: globals, ctx: ref_id, Vhead: val, Ihead: ival, σ: list Z
    PRE [ tptr node_t ]
      PROP()
      PARAMS(Vhead)
      GLOBALS()
      SEP(EquivList σ Vhead Ihead ;
            refines_right ctx ((of_val iris.iRev) <AP> (Val Ihead)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec
  ]).

Lemma test ctx IlocCur Iprev c Icur':
exists v,
(refines_right ctx
      (fill
         [FstCtx;
          AppRCtx
            (heap_lang.Rec <> "elem"
               (heap_lang.Rec <> "rest"
                  (heap_lang.Rec <> <>
                     (Val iris.rev_internal <AP> InjR (Val (iLit (LitLoc IlocCur))) <AP> Var "rest") <AP>
                   Store (Val (iLit (LitLoc IlocCur))) (Pair (Var "elem") (Val Iprev))) <AP>
                Snd (Load (Val (iLit (LitLoc IlocCur))))))] (Load (Val (iLit (LitLoc IlocCur))))) *
    IlocCur |-> iPair (iInt c) Icur'
    |-- (|={⊤}=>
           refines_right ctx
             (fill
                [FstCtx;
                 AppRCtx
                   (heap_lang.Rec <> "elem"
                      (heap_lang.Rec <> "rest"
                         (heap_lang.Rec <> <>
                            (Val iris.rev_internal <AP> InjR (Val (iLit (LitLoc IlocCur))) <AP> Var "rest") <AP>
                          Store (Val (iLit (LitLoc IlocCur))) (Pair (Var "elem") (Val Iprev))) <AP>
                       Snd (Load (Val (iLit (LitLoc IlocCur))))))] (Val v)) * IlocCur |-> v)).
Proof.
  eexists.
  eapply (ref_right_load _ ctx _ IlocCur fullshare _).
Admitted.


Lemma rev_internal_lemma : semax_body Vprog Gprog f_rev_list_internal rev_list_internal_spec.
Proof.
  start_function.
  unfold iris.rev_internal.
  (* NOTE: this works! *)
  (*viewshift_SEP' (refines_right _ _) (EquivList Vprev Iprev).*)
  SPR_beta.
  fold iris.rev_internal. (* do remember to fold this! *)
  SPR_recc.
  SPR_beta.
  (* either cur is null or not *)
  destruct (eq_dec Vcur nullval); subst.
  {
    (* if it is null, then the iris one is too *)
    sep_apply Equiv_null_l; sep_apply Equiv_empty.
    (* NOTE: why do I need this here? It can't pull the emp's apart right otherwise? *)
    autorewrite with norm.
    Intros.
    rename H into HIcurNull.
    rewrite HIcurNull. (* cannot subst for some reason *)
    unfold iLit, iUnit.

    (* Step iris to ending *)
    SPR_inl.
    SPR_recc.
    SPR_beta.

    evar (e : iexp).
    (* We cannot get past this if statement in this case *)
    forward_if (
      PROP (False)
      LOCAL (temp _prev Vprev; temp _cur nullval)
      SEP (refines_right ctx e; EquivList Lprev Vprev Iprev; EquivList [] nullval (InjLV (LitV LitUnit)))
    ).
    {
      forward.
      iIntros "[[ReqNull RrefR] ReqPrev]".
      iExists Vprev.
      iExists Iprev.
      iExists Lprev.
      iFrame.
      auto.
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
    (*NOTE: why do I get an emp here? I can't pull stuff out without getting it *)
    (* Pulling out the location just rips the pure hypothesis out as well *)
    Intros Vcur' Icur' IlocCur.
    autorewrite with norm.
    rename H into HIlocCur; rewrite ! HIlocCur.

    (* and we can reduce the right hand side! *)
    SPR_inr.
    SPR_recc; SPR_beta.

    (* including loads *)
    SPR_load IlocCur.

    Ltac step_pure_r_instr tactic :=
      let e' := fresh "e'" in
      let Hcond := fresh "Hcond" in
        lazymatch goal with
        (* if we have a decision, make it before we try to step further *)
        | |- context [ bool_decide ?cond ] => 
            destruct (bool_decide cond) eqn:Hcond;
            [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
            try contradiction; try lia; 
            clear Hcond
        (* anything else we carry on *)
        | |- ?anything => idtac (* do nothing tactic *)
        end;
        (* try to step to the next instruction *)
      lazymatch goal with
        | |- context[refines_right ?ctx ?expr] => 
            reshape_expr expr ltac:(fun K e => 
              replace expr with (fill K e) by (by rewrite ? fill_app);
              evar (e' : iexp);
              print_goal;
              viewshift_SEP' (refines_right ctx _) (refines_right ctx (fill K e'));
              idtac "hi!";
              first (
                go_lower; 
                eapply (refines_right_pure_r e e' _ _ _ K 1);
                [tactic e' | auto | auto]
              );
              simpl in e';
              subst e';
              simpl 
              )
        | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
      end;
      simpl.
      unfold iPair.

      Ltac SPR_fst      := step_pure_r_instr  ltac:(fun _ => apply (pure_fst _ _)).
      SPR_fst.

      

    lazymatch goal with
      | |- context[refines_right ?ctx ?expr] => 
          reshape_expr expr ltac:(fun K e => 
            replace expr with (fill K e) by (by rewrite ? fill_app);
            let v := fresh "v" in evar (v : ival);
            print_goal;
            viewshift_SEP' (refines_right ctx _) (IlocCur |-> _) (refines_right ctx (fill K (Val v)) * (IlocCur |-> v))%logic;
            first (
              unfold v;
              go_lower;
              print_goal;
              simple eapply (ref_right_load _ ctx K IlocCur fullshare _); first auto
            );
            simpl 
            )
      | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
    end.

  }

  ).
