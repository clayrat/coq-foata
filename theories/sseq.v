From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SnocList.
Context (A : Type).

Inductive sseq : Type :=
	snil : sseq | snoc : sseq -> A -> sseq.

Fixpoint scat s1 s2 := if s2 is snoc s2' x then snoc (scat s1 s2') x else s1.

End SnocList.

Section Fun.

Fixpoint smap {A B} (f : A -> B) (s : sseq A) : sseq B :=
  if s is snoc xs x then snoc (smap f xs) (f x) else @snil B.

Fixpoint to_seq {A} (s : sseq A) : seq A :=
  if s is snoc xs x then rcons (to_seq xs) x else [::].

Fixpoint from_seq {A} (s : seq A) : sseq A :=
  if s is x::xs then scat (snoc (@snil A) x) (from_seq xs) else @snil A.

End Fun.

Section Eqtype.
Context {T : eqType}.

Fixpoint eq_sseq (t1 t2 : sseq T) :=
  match t1, t2 with
  | snil, snil => true
  | snoc s x, snoc t y => eq_sseq s t && (x == y)
  | _, _ => false
  end.

Lemma eq_sseqP : Equality.axiom eq_sseq.
Proof.
move; elim=> [|s IH x][|t y] /=; try by constructor.
have [<-/=|neqx] := x =P y; last by rewrite andbF; apply: ReflectF; case.
rewrite andbT; apply: (iffP idP).
- by move/IH=>->.
by case=><-; apply/IH.
Qed.

Canonical sseq_eqMixin := EqMixin eq_sseqP.
Canonical sseq_eqType := Eval hnf in EqType (sseq T) sseq_eqMixin.

End Eqtype.

Section SnocPred.
Context (A : Type).
Variable a : pred A.

Fixpoint sall s := if s is snoc s' x then a x && sall s' else true.

Fixpoint shas s := if s is snoc s' x then a x || shas s' else false.

End SnocPred.
