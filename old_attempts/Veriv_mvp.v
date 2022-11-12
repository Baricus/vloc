From VST.veric Require Import rmaps compcert_rmaps.
Require Export iris.bi.lib.atomic.
Require Export VST.veric.bi.
Require Import VST.floyd.library.
Require Export VST.zlist.sublist.
Require Import Program.Equality.
From iris.heap_lang Require Import proofmode.



Require Import VST.floyd.proofauto.
(*Separate import needed!*)
Require Import VST.concurrency.ghosts.

Require Import VST.floyd.library.

Require Import Top.mvp.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Context `{Σ : gFunctors}.

(*Definition ret_1_i : val := *)
  (*(rec: "ret_1" "val" := "#1").*)

(* some notations to simplify a bit *)
Notation Vval := compcert.common.Values.val.
(*Notation Ival := iris.heap_lang.lang.heap_lang.val.*)

Notation Vexpr := VST.veric.local.expr.
Notation Iexpr := iris.heap_lang.lang.heap_lang.expr.

(* a relation between two types as a predicate *)
Definition lrel : Type := Vval -> Ival -> mpred.

Axiom of_val : Ival -> Iexpr.
Axiom fill : Iexpr -> mpred.
Axiom fancy_ghost_state : mpred.

Notation VGown := ghost_seplog.own.

(* Both of these cause universe inconsistencies *)
Type (@map_PCM (loc) (@pos_PCM (discrete_PCM Ival))).
Type (@map_disj_PCM loc (Ival)). (* forces exclusivity *)

Definition refines_right (e : Iexpr) : mpred := (fancy_ghost_state * fill e)%logic.

(*Parameter refines : function -> expr -> funspec.*)
(*NOTE: should f1 be an AST.Ident so we can DECLARE?*)
Definition refines (f2 : Iexpr) (A : lrel) : funspec :=
  WITH gv: globals
  PRE [ (* types of function parameters *) ]
    PROP()
    PARAMS()
    GLOBALS((* do we need anything to correlate globals and Context? Hopefully not *))
    SEP(refines_right f2)
  POST [ tint ] (*NOTE: what type?*)
    EX v' : Ival, EX v : Vval,
    PROP()
    RETURN(v)
    SEP(refines_right (of_val v') * A v v').

(* this works! *)
Definition n f f2 A :=  DECLARE f (refines f2 A).
