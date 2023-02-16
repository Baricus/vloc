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
     ⌜ (p = nullval) ⌝ (* NOTE: I used to have an emp here; why? *)
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
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iInt x) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => ⌜ v = InjLV (LitV LitUnit) ⌝
  end.

(* and we can compare them *)
Definition EquivList V I : mpred
  := ∃ σ, Ilist σ I ∗ Vlist σ V.


(* so I can stop seeing so many App constructors *)
Notation "a <AP> b" := (App a b) (at level 21, left associativity).

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Vprev Iprev ; EquivList Vcur Icur ;
            refines_right ctx ((of_val iris.rev_internal) <AP> (Val Iprev) <AP> (Val Icur)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).

(* the equivalent wrappers *)
Definition rev_list_spec :=
  DECLARE _rev_list
    WITH gv: globals, ctx: ref_id, Vhead: val, Ihead: ival
    PRE [ tptr node_t ]
      PROP()
      PARAMS(Vhead)
      GLOBALS()
      SEP(EquivList Vhead Ihead ;
            refines_right ctx ((of_val iris.iRev) <AP> (Val Ihead)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival,
      PROP()
      RETURN(Vres)
      SEP(EquivList Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec
  ]).

(* NOTE: TEMPORARY COPY FOR DEBUG *)
#[local] Ltac step_pure_r_instr tactic :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    try lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try contradiction; try lia; 
        clear Hcond
    end;
    (* try to step to the next instruction *)
    lazymatch goal with
    | |- context[refines_right ?ctx ?expr] =>
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          (*TODO: look at how this works *)
          gather_SEP (refines_right _ _);
          viewshift_SEP 0 (refines_right ctx (fill K e'));
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

#[export] Ltac SPR_beta     := step_pure_r_instr  ltac:(fun _ => apply pure_beta; apply AsRecV_recv).

Notation "'RR' a b" := (refines_right a b) (at level 20, only printing).

Lemma rev_internal_lemma : semax_body Vprog Gprog f_rev_list_internal rev_list_internal_spec.
Proof.
  start_function.
  unfold iris.rev_internal.
  SPR_beta.
  Set Ltac Debug.
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    (* try to step to the next instruction *)
    lazymatch goal with
    | |- context[refines_right ?ctx ?expr] => idtac "found the refines";
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          idtac "current expression: ";
          idtac e;
          gather_SEP (refines_right _ _); (* NOTE: pulls refines_right to position 0 *)
          viewshift_SEP 0 (refines_right ctx (fill K e')); (* works on position 0 *)
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            idtac "applied pure_r";
            [apply pure_beta; apply AsRecV_recv | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.
