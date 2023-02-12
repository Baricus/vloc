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
Fixpoint Ilist (sigma : list Z) v :=
  match sigma with
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iInt x) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => ⌜ v = InjLV (LitV LitUnit) ⌝
  end.



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

