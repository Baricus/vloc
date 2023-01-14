Require Export iris.program_logic.language.
Require Export iris.program_logic.ectxi_language.

Require Export iris.bi.lib.atomic.
From iris.heap_lang Require Export lang derived_laws metatheory.
From iris.heap_lang Require Export proofmode.
Require Export stdpp.list.

From VST.veric Require Export rmaps compcert_rmaps.

Require Export VST.veric.bi.

Require Export VST.floyd.library.
Require Export VST.zlist.sublist.
Require Export Program.Equality.
From iris.algebra Require Export excl gmap.
Require Export VST.floyd.proofauto.
Require Export VST.concurrency.invariants.
(*Separate import needed!*)
Require Export VST.concurrency.ghosts.
Require Export VST.concurrency.ghostsI.
Require Export VST.concurrency.fupd.

Require Export VST.floyd.library.

(* Taken from theories/logic/proofmode/spec_tactics!!! *)
(** Tactics for updating the specification program. *)
From iris.proofmode Require Export
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.


Section refinement.

(* declare context; a name for the state, the location type, and the ectxi language *)
Class refines_ctx := { gName : own.gname; nspace : namespace }.
Context `{ref_ctx: refines_ctx}.

(*define shorthand *)
Definition ival := heap_lang.val.
Definition iexp := heap_lang.expr.

(* the tpool is a map of numbers to expressions.  The "exclusive_PCM" is for ownership; 
   it mirrors the vloc Excl *)
Definition tpool_ghost := (gmap_ghost (K:=nat) (A:=(exclusive_PCM iexp))).
(* the heap is another map, of locations (essentially just nats?) to a share of ownership of a value *)
Definition heap_ghost := (gmap_ghost (K:=loc) (A:=(@pos_PCM (discrete_PCM (option ival))))). (*(@pos_PCM (discrete_PCM (option ival)))).*)
(* The whole ghost state is just the combination of both the tpool and heap ghost states *)
Definition spec_ghost := prod_PCM tpool_ghost heap_ghost.

(*The reference has no share, so we can't combine it*)
Definition InvGhost (map : @G spec_ghost) := @ghost_reference spec_ghost map gName.
(* NOTE: S is "some share" which may not be enough later!  It works for now *)
Definition UsrGhost (map : @G spec_ghost) := ∃ s, (!!(s ≠ emptyshare) * (@ghost_part spec_ghost s map gName))%logic.

(* NOTE: G is the type of any ghost state; which is by default opaque
    one way to show the actual type is below *)
(*Compute @G spec_ghost.*)

(* to_tpool
    converts a list of expressions to a thread pool,
    a map of thread indexes to their expressions 
*)
Definition to_tpool (exps : list iexp) : @G tpool_ghost
  := Some <$> (map_seq 0 exps).

(* to_heap
    Converts the standard heap_lang heap to the heap_ghost type.  
    This is largely just a reformatting to fit the form
*)
Definition to_heap (heap : gmap loc (option ival)) : @G heap_ghost :=
  fmap (λ v, (Some (fullshare, v))) heap.

(* assert that we have a value in the heap *)
(* heapS_mapsto
    An assertion that there is a value v in the heap at location l 
*)
Definition heapS_mapsto (l : loc) (v: ival) (s : share) :=
  UsrGhost (to_tpool [], {[ l := Some (s, (Some v)) ]} ).

Definition spec_inv (c : cfg (heap_lang)) : mpred := 
    EX exp_list : list iexp, EX σ,
    (* tp is a list of expressions! σ is the state *)
    ⌜rtc erased_step c (exp_list, σ)⌝ &&
      (* take the left side of the ghost share *)
    @InvGhost ((to_tpool exp_list), to_heap (heap σ)).

Definition spec_ctx : mpred := 
  (EX ρ, inv nspace (spec_inv ρ)). 

(*Define our own singleton map and turn it to a VST map for the non-invariant side *)
(* tpool_mapsto
    an assertion that the expression e is thread j's (numbered as nat's) 
*)
Definition tpool_mapsto (j : nat) (e : iexp) := 
  UsrGhost ({[j := Some e]}, to_heap gmap_empty).
(* TODO: figure out if this is actually exported? My bet is ... no *)
Notation "a |=> b" := (tpool_mapsto a b) (at level 20).

(* ref_id
    A context and associated thread identifier
*)
Record ref_id : Set := RefId { tp_id : nat;  tp_ctx : list ectx_item }.

Definition add_to_ctx id (ctx : list ectx_item) : ref_id :=
  RefId (tp_id id) (ctx ++ tp_ctx id).

Definition refines_right (r : ref_id) (e : iexp) := 
  (spec_ctx * (tp_id r) |=> (fill (tp_ctx r) e))%logic.

End refinement.
