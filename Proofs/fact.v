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

#[local] Instance fact_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
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
  step_pure_r ctx.
  forward.
  step_pure_r ctx.
Admitted.
