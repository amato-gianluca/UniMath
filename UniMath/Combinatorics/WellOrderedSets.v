(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.OrderedSets.
Local Open Scope poset.
Local Open Scope subtype.
Local Open Scope logic.

Notation "'pr11' x" := (pr1 (pr1 x)) (at level 9).
Notation "'pr12' x" := (pr1 (pr2 x)) (at level 9).
Notation "'pr21' x" := (pr2 (pr1 x)) (at level 9).
Notation "'pr22' x" := (pr2 (pr2 x)) (at level 9).

Notation "'pr111' x" := (pr1 (pr1 (pr1 x))) (at level 9).
Notation "'pr112' x" := (pr1 (pr1 (pr2 x))) (at level 9).
Notation "'pr121' x" := (pr1 (pr2 (pr1 x))) (at level 9).
Notation "'pr122' x" := (pr1 (pr2 (pr2 x))) (at level 9).
Notation "'pr211' x" := (pr2 (pr1 (pr1 x))) (at level 9).
Notation "'pr212' x" := (pr2 (pr1 (pr2 x))) (at level 9).
Notation "'pr221' x" := (pr2 (pr2 (pr1 x))) (at level 9).
Notation "'pr222' x" := (pr2 (pr2 (pr2 x))) (at level 9).

Notation "'pr1111' x" := (pr1 (pr1 (pr1 (pr1 x)))) (at level 9).
Notation "'pr1112' x" := (pr1 (pr1 (pr1 (pr2 x)))) (at level 9).
Notation "'pr1121' x" := (pr1 (pr1 (pr2 (pr1 x)))) (at level 9).
Notation "'pr1122' x" := (pr1 (pr1 (pr2 (pr2 x)))) (at level 9).
Notation "'pr1211' x" := (pr1 (pr2 (pr1 (pr1 x)))) (at level 9).
Notation "'pr1212' x" := (pr1 (pr2 (pr1 (pr2 x)))) (at level 9).
Notation "'pr1221' x" := (pr1 (pr2 (pr2 (pr1 x)))) (at level 9).
Notation "'pr1222' x" := (pr1 (pr2 (pr2 (pr2 x)))) (at level 9).
Notation "'pr2111' x" := (pr2 (pr1 (pr1 (pr1 x)))) (at level 9).
Notation "'pr2112' x" := (pr2 (pr1 (pr1 (pr2 x)))) (at level 9).
Notation "'pr2121' x" := (pr2 (pr1 (pr2 (pr1 x)))) (at level 9).
Notation "'pr2122' x" := (pr2 (pr1 (pr2 (pr2 x)))) (at level 9).
Notation "'pr2211' x" := (pr2 (pr2 (pr1 (pr1 x)))) (at level 9).
Notation "'pr2212' x" := (pr2 (pr2 (pr1 (pr2 x)))) (at level 9).
Notation "'pr2221' x" := (pr2 (pr2 (pr2 (pr1 x)))) (at level 9).
Notation "'pr2222' x" := (pr2 (pr2 (pr2 (pr2 x)))) (at level 9).

Notation "'pr11111' x" := (pr1 (pr1 (pr1 (pr1 (pr1 x))))) (at level 9).
Notation "'pr11112' x" := (pr1 (pr1 (pr1 (pr1 (pr2 x))))) (at level 9).
Notation "'pr11121' x" := (pr1 (pr1 (pr1 (pr2 (pr1 x))))) (at level 9).
Notation "'pr11122' x" := (pr1 (pr1 (pr1 (pr2 (pr2 x))))) (at level 9).
Notation "'pr11211' x" := (pr1 (pr1 (pr2 (pr1 (pr1 x))))) (at level 9).
Notation "'pr11212' x" := (pr1 (pr1 (pr2 (pr1 (pr2 x))))) (at level 9).
Notation "'pr11221' x" := (pr1 (pr1 (pr2 (pr2 (pr1 x))))) (at level 9).
Notation "'pr11222' x" := (pr1 (pr1 (pr2 (pr2 (pr2 x))))) (at level 9).
Notation "'pr12111' x" := (pr1 (pr2 (pr1 (pr1 (pr1 x))))) (at level 9).
Notation "'pr12112' x" := (pr1 (pr2 (pr1 (pr1 (pr2 x))))) (at level 9).
Notation "'pr12121' x" := (pr1 (pr2 (pr1 (pr2 (pr1 x))))) (at level 9).
Notation "'pr12122' x" := (pr1 (pr2 (pr1 (pr2 (pr2 x))))) (at level 9).
Notation "'pr12211' x" := (pr1 (pr2 (pr2 (pr1 (pr1 x))))) (at level 9).
Notation "'pr12212' x" := (pr1 (pr2 (pr2 (pr1 (pr2 x))))) (at level 9).
Notation "'pr12221' x" := (pr1 (pr2 (pr2 (pr2 (pr1 x))))) (at level 9).
Notation "'pr12222' x" := (pr1 (pr2 (pr2 (pr2 (pr2 x))))) (at level 9).
Notation "'pr21111' x" := (pr2 (pr1 (pr1 (pr1 (pr1 x))))) (at level 9).
Notation "'pr21112' x" := (pr2 (pr1 (pr1 (pr1 (pr2 x))))) (at level 9).
Notation "'pr21121' x" := (pr2 (pr1 (pr1 (pr2 (pr1 x))))) (at level 9).
Notation "'pr21122' x" := (pr2 (pr1 (pr1 (pr2 (pr2 x))))) (at level 9).
Notation "'pr21211' x" := (pr2 (pr1 (pr2 (pr1 (pr1 x))))) (at level 9).
Notation "'pr21212' x" := (pr2 (pr1 (pr2 (pr1 (pr2 x))))) (at level 9).
Notation "'pr21221' x" := (pr2 (pr1 (pr2 (pr2 (pr1 x))))) (at level 9).
Notation "'pr21222' x" := (pr2 (pr1 (pr2 (pr2 (pr2 x))))) (at level 9).
Notation "'pr22111' x" := (pr2 (pr2 (pr1 (pr1 (pr1 x))))) (at level 9).
Notation "'pr22112' x" := (pr2 (pr2 (pr1 (pr1 (pr2 x))))) (at level 9).
Notation "'pr22121' x" := (pr2 (pr2 (pr1 (pr2 (pr1 x))))) (at level 9).
Notation "'pr22122' x" := (pr2 (pr2 (pr1 (pr2 (pr2 x))))) (at level 9).
Notation "'pr22211' x" := (pr2 (pr2 (pr2 (pr1 (pr1 x))))) (at level 9).
Notation "'pr22212' x" := (pr2 (pr2 (pr2 (pr1 (pr2 x))))) (at level 9).
Notation "'pr22221' x" := (pr2 (pr2 (pr2 (pr2 (pr1 x))))) (at level 9).
Notation "'pr22222' x" := (pr2 (pr2 (pr2 (pr2 (pr2 x))))) (at level 9).

Notation "'pr111111' x" := (pr1 (pr1 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr111112' x" := (pr1 (pr1 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr111121' x" := (pr1 (pr1 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr111122' x" := (pr1 (pr1 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr111211' x" := (pr1 (pr1 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr111212' x" := (pr1 (pr1 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr111221' x" := (pr1 (pr1 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr111222' x" := (pr1 (pr1 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr112111' x" := (pr1 (pr1 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr112112' x" := (pr1 (pr1 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr112121' x" := (pr1 (pr1 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr112122' x" := (pr1 (pr1 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr112211' x" := (pr1 (pr1 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr112212' x" := (pr1 (pr1 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr112221' x" := (pr1 (pr1 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr112222' x" := (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr121111' x" := (pr1 (pr2 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr121112' x" := (pr1 (pr2 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr121121' x" := (pr1 (pr2 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr121122' x" := (pr1 (pr2 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr121211' x" := (pr1 (pr2 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr121212' x" := (pr1 (pr2 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr121221' x" := (pr1 (pr2 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr121222' x" := (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr122111' x" := (pr1 (pr2 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr122112' x" := (pr1 (pr2 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr122121' x" := (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr122122' x" := (pr1 (pr2 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr122211' x" := (pr1 (pr2 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr122212' x" := (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr122221' x" := (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr122222' x" := (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr211111' x" := (pr2 (pr1 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr211112' x" := (pr2 (pr1 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr211121' x" := (pr2 (pr1 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr211122' x" := (pr2 (pr1 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr211211' x" := (pr2 (pr1 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr211212' x" := (pr2 (pr1 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr211221' x" := (pr2 (pr1 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr211222' x" := (pr2 (pr1 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr212111' x" := (pr2 (pr1 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr212112' x" := (pr2 (pr1 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr212121' x" := (pr2 (pr1 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr212122' x" := (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr212211' x" := (pr2 (pr1 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr212212' x" := (pr2 (pr1 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr212221' x" := (pr2 (pr1 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr212222' x" := (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr221111' x" := (pr2 (pr2 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr221112' x" := (pr2 (pr2 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr221121' x" := (pr2 (pr2 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr221122' x" := (pr2 (pr2 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr221211' x" := (pr2 (pr2 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr221212' x" := (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr221221' x" := (pr2 (pr2 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr221222' x" := (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr222111' x" := (pr2 (pr2 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr222112' x" := (pr2 (pr2 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr222121' x" := (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr222122' x" := (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 9).
Notation "'pr222211' x" := (pr2 (pr2 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 9).
Notation "'pr222212' x" := (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 9).
Notation "'pr222221' x" := (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 9).
Notation "'pr222222' x" := (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 9).

Definition SubsetWithWellOrdering (X:hSet) :=
  (∑ (S:hsubtype X) (R : hrel S), isWellOrder R)%type.

Definition SubsetWithWellOrdering_to_subtype {X:hSet} : SubsetWithWellOrdering X -> hsubtype X
  := pr1.

Coercion SubsetWithWellOrdering_to_subtype : SubsetWithWellOrdering >-> hsubtype.

Local Definition rel {X:hSet} (S : SubsetWithWellOrdering X) : hrel S := pr12 S.

Delimit Scope wosubset with wosubset. (* subsets equipped with a well ordering *)

Open Scope wosubset.

Delimit Scope wosubset with wosubset.

Notation "s ≤ s'" := (rel _ s s') : wosubset.

Notation "s < s'" := ((s ≤ s') ∧ ¬ (s = s')) : wosubset.

Open Scope logic.

Open Scope prop.

Definition subposet {X:hSet} (S T:SubsetWithWellOrdering X) : hProp
  := ∑ (le : S ⊆ T), ∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s'.

Notation " S ⊑ T " := (subposet S T) (at level 95) : wosubset.

Notation " S ⊏ T " := ((S ⊑ T) ∧ (T ⊈ S)) (at level 95) : wosubset.

Definition subposet_to_subtype {X:hSet} {S T:SubsetWithWellOrdering X} : S ⊑ T -> S ⊆ T
  := pr1.

Local Definition inc' {X} {S T : SubsetWithWellOrdering X} : (S ⊑ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (subposet_to_subtype le) s).
Defined.

Definition subposet_reflect {X:hSet} {S T:SubsetWithWellOrdering X} (le : S ⊑ T)
      (s s' : S) : inc' le s ≤ inc' le s' -> s ≤ s'.
Proof.
  intro l.
  unfold SubsetWithWellOrdering,isWellOrder,isTotalOrder in S.
  apply (squash_to_prop (pr2122 S s s')).
  { apply propproperty. }
  change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
  intro c. induction c as [c|c].
  - exact c.
  - induction le as [le b].
    assert (k := b s' s c).
    unfold SubsetWithWellOrdering,isWellOrder,isTotalOrder,istotal,isPartialOrder in T.
    assert (k' := pr21122 T _ _ l k); clear k. simpl in k'.
    assert (p : s = s').
    { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
    induction p.
    unfold isPartialOrder,ispreorder in S.
    exact (pr211122 S _).
Defined.

Definition isclosed {X:hSet} (S T:SubsetWithWellOrdering X) : hProp
  := ∑ (le : S ⊑ T), ∀ (s:S) (t:T), t ≤ inc' le s ⇒ (t ∈ S).

Notation "S ≼ T" := (isclosed S T) (at level 95) : wosubset.

Definition isclosed_smaller {X:hSet} (S T:SubsetWithWellOrdering X) : hProp := (S ≼ T) ∧ (T ⊊ S).

Notation "S ≺ T" := (isclosed_smaller S T) (at level 95) : wosubset.

Definition upto {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : hsubtype X
  := λ x, ∑ h:S x, (x,,h) < s.

Definition isInterval {X:hSet} (S T:SubsetWithWellOrdering X) : S ≺ T -> ∑ t:T, S ≡ upto t.
Proof.
  intro lt.
Abort.