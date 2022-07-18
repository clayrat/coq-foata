From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order ssrnat seq.
From Foata Require Import sseq traces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NF.
Context {disp : unit} {A : orderType disp}.
Variable (ind : rel A) (ind_irr : irreflexive ind) (ind_sym : symmetric ind).

Definition step : Type := sseq A.

Definition foata : Type := sseq step.

Definition fstring : Type := seq (@string disp A).

Definition emb' (ss : foata) : fstring := to_seq (smap to_seq ss).

Definition emb (ss : foata) : string := flatten (emb' ss).

Lemma emb_cat' xs ys : emb' (scat xs ys) = emb' xs ++ emb' ys.
Proof.
elim: ys=>[|s IH a] /=.
- by rewrite /emb' /= cats0.
by rewrite /emb' /= in IH *; rewrite IH rcons_cat.
Qed.

Lemma emb_cat xs ys : emb (scat xs ys) = emb xs ++ emb ys.
Proof.
elim: ys=>[|s IH a] /=.
- by rewrite /emb /= cats0.
rewrite /emb /emb' /= in IH *.
by rewrite !flatten_rcons IH catA.
Qed.

(* independence from step elements decider *)
Definition si_dec (s : step) (a : A) : bool := all_ind ind a s.

End NF.

