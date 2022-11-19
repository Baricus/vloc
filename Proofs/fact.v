(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Module iris.

Import proofmode notation.

Definition factI : heap_lang.expr :=
  rec: "factI" "n" :=
    if: "n" < #1 then #1 else "factI" * ("n" - #1)
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
    PROP((n <= Int.max_signed)%Z)
    PARAMS(Vint (Int.repr n))
    GLOBALS()
    SEP(refines_right ctx (App iris.factI (Val (LitV (LitInt n)))))
  POST [ tint ] 
    EX v' : ival, EX v : val,
    PROP()
    RETURN(v)
    SEP(refines_right ctx (ectxi_language.of_val v') * int_relate v v').

Definition Gprog : funspecs := [fspec].

Lemma one_plus_zero : semax_body Vprog Gprog f_factorial fspec.
Proof.
  start_function. 
  step_pure_r ctx.
  forward.
  destruct (eq_dec n 0).
  - forward_for_simple_bound n (EX i:Z,
      PROP()
      LOCAL(temp _acc (Vint (Int.repr 1)); temp _n (Vint (Int.repr n)))
      SEP(refines_right ctx (App
             (Val
                (RecV "factI" "n"
                   (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                      (Val (LitV (LitInt 1)))
                      (BinOp MultOp (Var "factI")
                         (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1))))))))
             (Val (LitV (LitInt n)))))
    ).
    entailer!.
    lia.
    step_pure_r ctx.
    step_pure_r ctx.
    step_pure_r ctx.
    step_pure_r ctx.
    forward.
    Exists (LitV (heap_lang.LitInt 1%Z)).
    Exists (Vint (Int.repr 1)).
    iIntros "H".
    iSplit; first iPureIntro; auto.
    iSplit; last iPureIntro; eauto.

  - forward_for_simple_bound n (EX i:Z, 
      PROP()
      LOCAL(temp _acc (Vint (Int.repr 1)); temp _n (Vint (Int.repr n)))
      SEP()
    )%assert.

Admitted.
