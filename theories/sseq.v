From Coq Require Import ssreflect ssrbool ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SnocList.
Context (A : Type).

Inductive sseq : Type :=
	snil : sseq | snoc : sseq -> A -> sseq.

Fixpoint scat s1 s2 := if s1 is snoc s1' x then snoc (scat s1' s2) x else s2.

End SnocList.

Section SnocPred.
Context (A : Type).
Variable a : pred A.

Fixpoint sall s := if s is snoc s' x then sall s' && a x else true.

Fixpoint shas s := if s is snoc s' x then shas s' || a x else false.

End SnocPred.
