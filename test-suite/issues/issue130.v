From Coq.Lists Require Import List.
From Equations Require Import Equations.
Set Equations Transparent.
Inductive foo :=
| Foo : foo -> nat -> foo.

Equations foo_type1 (t : foo) : Type := {
  foo_type1 (Foo t _) := foo_type1 t}.

Equations foo_type2 (t : foo) : Type := {
  foo_type2 (Foo t _) := foo_type2 t}.

Equations (struct t) foo_t1_to_t2 (t : foo) (val : foo_type1 t) : foo_type2 t := {
                                                                                  foo_t1_to_t2 (Foo t _) val := foo_t1_to_t2 t val}.

Definition test := foo_t1_to_t2_elim.