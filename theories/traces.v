From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order ssrnat seq.
From Foata Require Import sseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Independency.
Context {disp : unit} {A : orderType disp}.
Variable (ind : rel A) (ind_irr : irreflexive ind) (ind_sym : symmetric ind).

Definition all_ind (a : A) := sall (fun x => ind x a).

Definition dep : rel A :=
  fun x y => ~~ ind x y.

Fact dep_sym : symmetric dep.
Proof. by move=>*; rewrite /dep ind_sym. Qed.

Definition has_dep (a : A) := shas (fun x => dep x a).

End Independency.

Section Traces.
Context {disp : unit} {A : orderType disp}.
Variable (ind : rel A) (ind_irr : irreflexive ind) (ind_sym : symmetric ind).

Definition string := seq A.

Inductive perm : string -> string -> Prop :=
| perm_swap a b s t of ind a b : perm (s ++ [:: a; b] ++ t) (s ++ [:: b; a] ++ t).

Inductive perm_star : string -> string -> Prop :=
| perm_refl s t of s = t : perm_star s t
| perm_cons s t u of perm s t & perm_star t u : perm_star s u.

Lemma perm_to_perm_star s t : perm s t -> perm_star s t.
Proof. by move=>H; apply: (perm_cons H); apply: perm_refl. Qed.

Lemma eq_to_perm s t : s = t -> perm_star s t.
Proof. by move/perm_refl. Qed.

Lemma perm_trans s t u : perm_star s t -> perm_star t u -> perm_star s u.
Proof.
elim=>{}s {}t; first by move=>->.
move=>w Hst _ IH /IH Htu.
by apply/perm_cons/Htu.
Qed.

Lemma perm_sym' s t : perm s t -> perm t s.
Proof.
case=>a b {}s {}t; rewrite ind_sym=>H.
by apply: perm_swap.
Qed.

Lemma perm_sym s t : perm_star s t -> perm_star t s.
Proof.
elim=>{}s {}t; first by move=>->; apply: perm_refl.
move=>w [a b {}s {}t Hab] Htw Hwt.
apply: (perm_trans Hwt).
apply: (perm_cons).
- by apply: perm_swap; rewrite ind_sym.
by apply: perm_refl.
Qed.

Lemma append_perm' s t (c : A) : perm s t -> perm (rcons s c) (rcons t c).
Proof.
case=>a b {}s {}t H.
by rewrite -!cats1 -!catA; apply: perm_swap.
Qed.

Lemma append_perm s t (c : A) : perm_star s t -> perm_star (rcons s c) (rcons t c).
Proof.
elim=>{}s {}t; first by move=>->; apply: perm_refl.
move=>w Ht _ IH.
by apply/perm_cons/IH; apply: append_perm'.
Qed.

Lemma prepend_perm' s t (c : A) : perm s t -> perm (c::s) (c::t).
Proof.
case=>a b {}s {}t H.
by rewrite -!cat_cons; apply: perm_swap.
Qed.

Lemma prepend_perm s t (c : A) : perm_star s t -> perm_star (c::s) (c::t).
Proof.
elim=>{}s {}t; first by move=>->; apply: perm_refl.
move=>w Ht _ IH.
by apply/perm_cons/IH; apply: prepend_perm'.
Qed.

Lemma perm_size' u v : perm u v -> size u = size v.
Proof.
by case=>a b {}u {}v H /=; rewrite !size_cat.
Qed.

Lemma perm_size u v : perm_star u v -> size u = size v.
Proof.
elim=>{}u {}v; first by move=>->.
by move=>w /perm_size' <-.
Qed.

Lemma perm_size2 u v : perm u v -> 2 <= size u.
Proof.
by case=>a b {}u {}v H; rewrite size_cat /= !addnS.
Qed.

Corollary perm_nil xs : ~ perm [::] xs.
Proof. by move/perm_size2. Qed.

Corollary perm_single a xs : ~ perm [::a] xs.
Proof. by move/perm_size2. Qed.

(* contribute to mathcomp? *)
Lemma rem_cat {T : eqType} (x : T) s t :
  rem x (s ++ t) = if x \in s then rem x s ++ t else s ++ rem x t.
Proof.
rewrite !remE index_cat; case: ifP=>Hx.
- rewrite !takel_cat; try by exact: index_size.
  rewrite drop_cat; case: ltnP=>Hs.
  - by rewrite catA.
  rewrite -index_mem in Hx.
  have ->: (index x s).+1 = size s by apply/eqP; rewrite eqn_leq Hx.
  by rewrite subnn !drop0 drop_size cats0.
by rewrite take_cat drop_cat !ltnNge -addnS !leq_addr /= -!addnBAC // subnn !add0n catA.
Qed.

Lemma rem_perm c x y : perm x y -> perm_star (rem c x) (rem c y).
Proof.
case=>a b {}x {}y H.
rewrite !rem_cat; case: ifP=>Hx.
- by apply/perm_to_perm_star/perm_swap.
case: ifP; rewrite !inE=>Hab.
- move: (Hab); rewrite orbC=>->.
  suff: rem c [:: a; b] = rem c [:: b; a] by move=>->; apply: perm_refl.
  by move: Hab; case/orP=>/= /eqP->; rewrite eq_refl; case: ifP=>// /eqP->.
case: ifP=>[|_]; last by apply/perm_to_perm_star/perm_swap.
by case/orP=>E; rewrite E //= orbT in Hab.
Qed.

Lemma rem_perm_star c x y : perm_star x y -> perm_star (rem c x) (rem c y).
Proof.
elim=>{}x {}y; first by move=>->; apply: perm_refl.
move=>w H _ IH; apply/perm_trans/IH.
by apply: rem_perm.
Qed.

Corollary hd_diff_perm_star a b c w z :
  perm_star [::a;b;w] [::b;c;z] -> perm_star [::a;w] [::c;z].
Proof.
move/(rem_perm_star b)=>/=; rewrite eq_refl.
by case: eqP=>//->.
Qed.

Lemma tail_perm u v c : perm (c::u) (c::v) -> perm u v.
Proof.
move=>H; case: {-1}_ {-1}_ / H (erefl (c::u)) (erefl (c::v))=>a b s t H.
case: s=>[|h s]/=; case=>->->; case.
- move=>E; rewrite E in H.
  by move: (ind_irr b); rewrite H.
by move=>->; apply: perm_swap.
Qed.

Corollary tail_perm_star u v c : perm_star (c::u) (c::v) -> perm_star u v.
Proof. by move/(rem_perm_star c)=>/=; rewrite eq_refl. Qed.

Lemma catl_perm_star s t u : perm_star s t -> perm_star (s ++ u) (t ++ u).
Proof.
elim: u=>[|h u IH] in s t *; first by rewrite !cats0.
move=>H; rewrite -cat1s !catA !cats1; apply: IH.
by apply: append_perm.
Qed.

Lemma catr_perm_star s t u : perm_star s t <-> perm_star (u ++ s) (u ++ t).
Proof.
elim: u=>[|h u IH]; first by rewrite !cat0s.
split=>/=.
- by move/IH; exact: prepend_perm.
by move/tail_perm_star/IH.
Qed.

Lemma cat_perm_star s t u v :
  perm_star s t -> perm_star u v ->
  perm_star (s ++ u) (t ++ v).
Proof.
move=>H1 H2; apply: (perm_trans (t:=s++v)).
- by move/(catr_perm_star _ _ s): H2.
by apply: catl_perm_star.
Qed.

Lemma step_perm s a : all (ind^~ a) s -> perm_star (rcons s a) (a::s).
Proof.
elim: s=>/=[_|h t IH]; first by apply: perm_refl.
case/andP=>Ha /IH /(prepend_perm h) H; apply: (perm_trans H).
rewrite (_ : [::h, a & t] = [::] ++ [::h;a] ++ t) //
        (_ : [::a, h & t] = [::] ++ [::a;h] ++ t) //.
by apply/perm_to_perm_star/perm_swap.
Qed.

(* TODO perm_eq + pairwise ind? *)

End Traces.
