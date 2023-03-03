From Vloc Require Import core.

(* helper stuff that isn't entirely related *)
#[export] Ltac print_goal := match goal with
                   | |- ?p => idtac "GOAL IS: " p
                   end.
  
(*NOTE: trying out making a nicer viewshift_SEP *)
#[export] Tactic Notation "viewshift_SEP'" uconstr(a) uconstr(L') :=
  let i := fresh "i" in freeze i := a; thaw'' i; viewshift_SEP 0 L'.

#[export] Tactic Notation "viewshift_SEP'" uconstr(a) uconstr(b) uconstr(L') :=
  let i := fresh "i" in freeze i := a b; thaw'' i; viewshift_SEP 0 L'.

#[export] Tactic Notation "viewshift_SEP'" uconstr(a) uconstr(b) uconstr(c) uconstr(L') :=
  let i := fresh "i" in freeze i := a b c; thaw'' i; viewshift_SEP 0 L'.

#[export] Tactic Notation "viewshift_SEP'" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(L') :=
  let i := fresh "i" in freeze i := a b c d; thaw'' i; viewshift_SEP 0 L'.
