(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

(* used for our modulus *)
Import compcert.lib.Integers.
Import proofmode notation.

(* TODO: Add heap_lang rev equivalent *)

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.rev.

#[local] Instance prog_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.



(* here, the refines we had before won't work... *)
Definition fspec :=
  DECLARE _rev
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

