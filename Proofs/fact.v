(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

Import compcert.lib.Integers.
Import proofmode notation.

Definition factI : heap_lang.val :=
  rec: "factI" "n" :=
    if: "n" < #1 then #1 else ("n" * "factI" ("n" - #1)) `rem` #(Int.max_unsigned)
    .

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.fact.

#[local] Instance fact_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Definition nat_relate vVST vHL :=
  ((exists n, ((vVST = Vint (Int.repr n))%Z) /\ vHL = LitV (heap_lang.LitInt n%Z))).

(* for simplicity, we're ignoring out of bounds errors here *)
Fixpoint fact n : nat :=
  match n with
  | O => 1
  | S (n') => n * (fact n')
  end.

(* here, the refines we had before won't work... *)
Definition fspec :=
  DECLARE _factorial
  WITH gv: globals, ctx: ref_id, n : int
  PRE [ tuint ]
    PROP()
    PARAMS(Vint n)
    GLOBALS()
    SEP(refines_right ctx (App (Val iris.factI) (Val (LitV (LitInt (Int.unsigned n))))))
  POST [ tuint ] 
    EX v' : ival, EX v : val,
    PROP(nat_relate v v')
    RETURN(v)
    SEP((refines_right ctx (ectxi_language.of_val v'))).

Definition Gprog : funspecs := [fspec].

Lemma fact_lemma : semax_body Vprog Gprog f_factorial fspec.
Proof.
  start_function. 
  forward_if (
    PROP((Int.unsigned n >= 1)%Z) 
    LOCAL(temp _n (Vint n)) 
    SEP(refines_right ctx
       (BinOp RemOp
          (BinOp MultOp (Val (LitV (LitInt (Int.unsigned n))))
             (App
                (Val
                   (RecV "factI" "n"
                      (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                         (Val (LitV (LitInt 1)))
                         (BinOp RemOp
                            (BinOp MultOp (Var "n")
                               (App (Var "factI")
                                  (BinOp MinusOp (Var "n")
                                     (Val (LitV (LitInt 1))))))
                            (Val (LitV (LitInt Int.max_unsigned)))))))
                (BinOp MinusOp (Val (LitV (LitInt (Int.unsigned n))))
                   (Val (LitV (LitInt 1))))))
          (Val (LitV (LitInt Int.max_unsigned)))))
  ).
  (* n is zero or less *)
  {
    (* step hl to right form *)
    do 4 step_pure_r ctx.
    forward.
    simpl.
    replace (Z.pos (1 * 1)) with (Z.pos 1) by lia.
    Exists (LitV (heap_lang.LitInt 1%Z)).
    Exists (Vint (Int.repr 1)).
    entailer!.
    unfold nat_relate.
    eauto.
  }
  {
    (* step hl through 1 cycle *)
    do 4 step_pure_r ctx.
    forward.
    unfold iris.factI.
    entailer!.
  }
  Intros.
  step_pure_r ctx.
  forward_call (gv, add_to_ctx ctx ([BinOpRCtx MultOp (Val (LitV (LitInt (Int.unsigned n))))] ++ [BinOpLCtx RemOp ((LitV (LitInt Int.max_unsigned)))]), (Int.sub n Int.one)); try lia.
  {
    unfold iris.factI.
    replace (BinOp _ _ _) with (
    fill ([BinOpRCtx MultOp (Val (LitV (LitInt (Int.unsigned n))))] ++ [BinOpLCtx RemOp ((LitV (LitInt Int.max_unsigned)))])
    (App
         (Val
            (RecV "factI" "n"
               (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                  (Val (LitV (LitInt 1)))
                  (BinOp RemOp
                     (BinOp MultOp (Var "n")
                        (App (Var "factI")
                           (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1))))))
                     (Val (LitV (LitInt Int.max_unsigned)))))))
                     (Val (LitV (LitInt (Int.unsigned n - 1)))))
    ) by by rewrite ? fill_app.
    rewrite refines_right_add_ctx.
    rewrite Int.unsigned_sub_borrow.
    rewrite ? Int.unsigned_repr; try rep_lia.
    unfold Int.sub_borrow; simpl.
    rewrite if_false.
    {
    rewrite ? Int.unsigned_repr; try rep_lia.
    rewrite Z.add_0_r.
    cancel.
  }
    rewrite ? Int.unsigned_repr; try rep_lia.
  }
  (* extract recursive value *)
  Intros ret.
  destruct ret as [iret vret]; simpl; simpl in H0. 
  rewrite <- refines_right_add_ctx; simpl.
  unfold nat_relate in H0.
  destruct H0 as [rn [Hvst Hiris]]; subst.
  step_pure_r ctx.
  forward.
  entailer!.
  unfold nat_relate.
  Exists (LitV (LitInt (Int.unsigned n * rn))).
  Exists (Vint (Int.mul n (Int.repr rn))).
  simpl.
  entailer!.
  exists (Int.unsigned n * rn)%Z.
  split.
  - unfold Int.mul.
    rewrite Int.unsigned_repr; try rep_lia; auto.

    admit.
  - auto.
  (* again, I need bounds to solve this *)
Admitted.
