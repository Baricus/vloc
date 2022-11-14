(* workaround for not having notation *)
Module iris.

From iris.heap_lang Require Import proofmode notation.

Definition factI : val :=
  rec: "factI" "n" :=
    if: "n" = #0 then #1 else "factI" * ("n" - #1)
    .

End iris.

Require Import Vloc.Lib.theory.

(*Require Import Vloc.CCode.fact.*)



