(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Module iris.

Import proofmode notation.

Definition factI : heap_lang.expr :=
  rec: "factI" "n" :=
    if: "n" = #0 then #1 else "factI" * ("n" - #1)
    .

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.fact.

Instance fact_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* here, the refines we had before won't work... *)
Definition int_relate vVST vHL :=
  (!! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic.

Definition fspec :=
  DECLARE _factorial
  WITH gv: globals, ctx: ref_id, n : Z
  PRE [ tint ]
    PROP()
    PARAMS(Vint (Int.repr n))
    GLOBALS()
    SEP(refines_right ctx (App iris.factI (Val (LitV (LitInt n)))))
  POST [ tint ] 
    EX v' : ival, EX v : val,
    PROP()
    RETURN(v)
    SEP(refines_right ctx (ectxi_language.of_val v') * int_relate v v').

Definition Gprog : funspecs := [fspec].

Ltac print_goal := match goal with
                   | |- ?p => idtac "GOAL IS: " p
                   end.

Lemma one_plus_zero : semax_body Vprog Gprog f_factorial fspec.
Proof.
  start_function. 
  unfold iris.factI.
  forward.

  (*evar (thing : iexp).*)
  (*assert ((PureExec True  1*)
   (*(heap_lang.Rec "factI" "n"*)
      (*(If (BinOp EqOp (Var "n") (Val (LitV (LitInt 0))))*)
         (*(Val (LitV (LitInt 1)))*)
         (*(BinOp MultOp (Var "factI")*)
            (*(BinOp MinusOp (Var "n") (Val (LitV (LitInt 1))))))) thing)).*)
            (*{*)
              (*eapply (pure_recc _).*)
            (*}*)

  match goal with
  | |- context[refines_right ctx ?expr] => 
      reshape_expr expr ltac:(fun K e => 
        replace expr with (fill K e) by (by rewrite ? fill_app);
        evar (e' : iexp);
        viewshift_SEP 0 (refines_right ctx (fill K e'));
        first (
          go_lower; 
          eapply (refines_right_pure_r e e' _ _ _ K 1);
          [try_pures | auto | auto]
        );
        simpl in e';
        subst e'
        )
  end.
  evar (e' : iexp);
  match goal with
  | |- context[refines_right ctx expr] =>
      replace expr with () 
  end.



        go_lower; eapply (refines_right_pure_r _ _ _ _ _ K' 1) ) end.
        [ try_pures | auto | auto ]; simpl in e''; subst e''
     )
  end.
  eapply (refines_right_pure_r _ _ _ _ _ [] 1); [| auto | auto].
  eapply (pure_exec_ctx (Λ := heap_lang) _ [Val (RecV "FactI" "n" _)]).

  step_pure_r ctx.
  unfold refines_right.
  unfold spec_ctx.
  unfold spec_inv.

  evar (e' : iexp).
  viewshift_SEP 0 (@refines_right theory.gName theory.nspace ctx e').
  go_lower.
  eapply (refines_right_pure_r _ _ _ _ _ [] 1); [| auto | auto].
  eapply (pure_exec_ctx (Λ := heap_lang) _ [Val (RecV "FactI" "n" _)]).



  forward_loop (acc).
  
