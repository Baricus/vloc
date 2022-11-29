(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Module iris.

Import proofmode notation.

Definition factI : heap_lang.expr :=
  rec: "factI" "n" :=
    if: "n" < #1 then #1 else "n" * "factI" ("n" - #1)
    .

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.fact.

#[local] Instance fact_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Definition nat_relate n vVST vHL :=
  (((Int.min_signed <= n <= Int.max_signed)%Z -> (vVST = Vint (Int.repr n))%Z) /\ vHL = LitV (heap_lang.LitInt n%Z)).

(* for simplicity, we're ignoring out of bounds errors here *)
Fixpoint fact n : nat :=
  match n with
  | O => 1
  | S (n') => n * (fact n')
  end.

(* here, the refines we had before won't work... *)
Definition fspec :=
  DECLARE _factorial
  WITH gv: globals, ctx: ref_id, n : Z
  PRE [ tint ]
    PROP((Int.min_signed <= n <= Int.max_signed)%Z)
    PARAMS(Vint (Int.repr n))
    GLOBALS()
    SEP(refines_right ctx (App iris.factI (Val (LitV (LitInt n)))))
  POST [ tint ] 
    EX n : Z, EX v' : ival, EX v : val,
    PROP(nat_relate n v v')
    RETURN(v)
    SEP((refines_right ctx (ectxi_language.of_val v'))).

Definition Gprog : funspecs := [fspec].


Lemma fact_lemma : semax_body Vprog Gprog f_factorial fspec.
Proof.
  start_function. 
  forward_if (
    PROP((n >= 1)%Z) 
    LOCAL(temp _n (Vint (Int.repr n))) 
    SEP(refines_right ctx
       (BinOp MultOp (Val (LitV (LitInt n)))
          (App
             (Val
                (RecV "factI" "n"
                   (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                      (Val (LitV (LitInt 1)))
                      (BinOp MultOp (Var "n")
                         (App (Var "factI")
                            (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1)))))))))
             (Val (LitV (LitInt (n - 1)))))))
  ).
  (* n is zero or less *)
  {
    (* step hl to right form *)
    do 5 step_pure_r ctx.
    forward.
    simpl.
    replace (Z.pos (1 * 1)) with (Z.pos 1) by lia.
    Exists 1%Z.
    Exists (LitV (heap_lang.LitInt 1%Z)).
    Exists (Vint (Int.repr 1)).
    entailer!.
    unfold nat_relate.
    auto.
  }
  {
    (* step hl through 1 cycle *)
    do 6 step_pure_r ctx.
    forward.
    entailer!.
  }
  Intros.
  forward_call (gv, add_to_ctx ctx [BinOpRCtx MultOp (Val (LitV (LitInt n)))], (n-1)%Z); try lia.
  {
    unfold iris.factI.
    (* we need to step the rhs once to handle the fact that it didn't recure fully? *)
    replace (App (heap_lang.Rec _ _ _)) with 
      (App (Val
           (RecV "factI" "n"
              (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                 (Val (LitV (LitInt 1)))
                 (BinOp MultOp (Var "n")
                    (App (Var "factI")
                       (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1)))))))))).
     2:{
       (* TODO: figure out how to turn heap_lang.Rec into Val (RecV ... or rewrite the program *)
       admit.
     }
    replace (BinOp _ _ _) with (fill [BinOpRCtx MultOp (Val (LitV (LitInt n)))] (App
        (Val
           (RecV "factI" "n"
              (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                 (Val (LitV (LitInt 1)))
                 (BinOp MultOp (Var "n")
                    (App (Var "factI")
                       (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1)))))))))
        (Val (LitV (LitInt (n - 1)))))) by by rewrite ? fill_app.
    rewrite refines_right_add_ctx.
    cancel.
  }
  (* extract recursive value *)
  Intros ret.
  destruct ret as [[rn iret] vret]; simpl; simpl in H1. 
  rewrite <- refines_right_add_ctx; simpl.
  forward.
  - unfold nat_relate in H1; destruct H1 as [Hl Hr].
    subst.
    entailer!.
    (* TODO: how to get bounds? I can try to add it to the implication but then other things break *)
    admit.
  - unfold nat_relate in H1; destruct H1 as [Hl Hr].
    Exists 
Admitted.
