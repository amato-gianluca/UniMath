(** * Boolean reflection. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
Boolean reflection, in the spirit of SSReflect.
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Bool.

(* Preliminary material that has to be moved elsewhere. *)

Definition iffb : bool → bool →  bool.
Proof.
intros b1. induction b1.
- exact (λ b2, b2).
- exact negb.
Defined.

Lemma isaproplogeq {X Y : UU}
  : isaprop X → isaprop Y → isaprop (X <-> Y).
Proof.
intros. unfold logeq.
apply isapropdirprod; apply isapropimpl; assumption.
Defined.

Definition natltb (m n : nat) : bool := natgtb n m.

Definition natleb (m n : nat) : bool := negb (natgtb m n).

Definition natgeb (m n : nat) : bool := negb (natgtb n m).

Definition nateqb (m n : nat) : bool.
Proof.
revert n. induction m as [|m recur].
- exact (λ n, match n with 0 => true | _ => false end).
- exact (λ n, match n with 0 => false | S n => recur n end).
Defined.

(* reflect predicate *)

Definition reflect (X : UU) (b : bool) : UU
  := X <-> b = true.

Definition true_to_reflect {X : UU}
  : X -> reflect X true.
Proof.
intros x; split.
- intros _; apply idpath.
- intros; exact x.
Qed.

Definition reflect_to_true {X : UU}
  : reflect X true -> X.
Proof.
induction 1 as (h1,h2).
apply h2. apply idpath.
Qed.

Lemma reflect_true {X : UU}
  : X <-> reflect X true.
Proof.
unfold reflect. apply make_dirprod.
- apply true_to_reflect.
- apply reflect_to_true.
Qed.

Definition reflect_to_false {X : UU}
  : reflect X false -> ¬ X.
Proof.
induction 1 as (h1,h2).
intros x. apply nopathsfalsetotrue. apply h1, x.
Qed.

Definition false_to_reflect {X : UU}
  : ¬ X -> reflect X false.
Proof.
intros nx. apply make_dirprod.
- intros x. apply fromempty. apply nx, x.
- intros h. apply fromempty. apply nopathsfalsetotrue. exact h.
Qed.

Definition reflect_false {X : UU}
  : ¬ X <-> reflect X false.
Proof.
unfold reflect. apply make_dirprod.
- apply false_to_reflect.
- apply reflect_to_false.
Qed.

Ltac unfold_reflect :=
  repeat (
    match goal with
    |- reflect ?X true => apply true_to_reflect
    | |- reflect ?X false => apply false_to_reflect
    | H : reflect ?X true |- _ => apply reflect_to_true in H
    | H : reflect ?X false |- _ => apply reflect_to_false in H
    end
  ).

Lemma reflect_logrewr {X Y : UU} (b : bool)
  : (X <-> Y) -> reflect X b -> reflect Y b.
Proof.
intros H r.
induction b; unfold_reflect.
- apply H. auto.
- intros y. apply r. apply H. auto.
Qed.

Lemma reflect_logeq {X Y : UU} {b c : bool}
    (r1 : reflect X b) (r2 : reflect Y c)
  : reflect (X <-> Y) (iffb b c).
Proof.
induction b; induction c; cbn; unfold_reflect;
try (apply logeq_both_true; assumption);
try (apply logeq_both_false; assumption).
- intros h. apply r2. apply h. exact r1.
- intros h. apply r1. apply h. exact r2. 
Qed.

Lemma reflect_dirprod {X Y : UU} {b c : bool}
      (r1 : reflect X b) (r2 : reflect Y c)
  : reflect (X × Y) (andb b c).
Proof.
induction b; induction c; cbn; unfold_reflect;
try (apply make_dirprod; assumption);
induction 1 as (x, y); try apply r1; try apply r2; auto.
Qed.

Lemma reflect_coprod {X Y : UU} {b c : bool}
      (r1 : reflect X b) (r2 : reflect Y c)
  : reflect (X ⨿ Y) (orb b c).
Proof.
induction b; induction c; cbn; unfold_reflect;
try (apply ii1; assumption);
try (apply ii2; assumption).
induction 1 as [x | y].
- apply r1; assumption.
- apply r2; assumption.
Qed.

Lemma reflect_neg {X : UU} {b : bool} (r : reflect X b)
  : reflect (¬ X) (negb b).
Proof.
induction b; cbn; unfold_reflect.
- intros H; apply H; auto.
- assumption.
Qed.

Lemma reflect_natgtb (m n : nat) : reflect (m > n) (natgtb m n).
Proof.
unfold natgth. simpl. unfold reflect.
apply isrefl_logeq.
Qed.

Lemma reflect_natltb (m n : nat) : reflect (m < n) (natltb m n).
Proof.
apply reflect_natgtb.
Qed.

Lemma reflect_natgeb (m n : nat) : reflect (m ≥ n) (natgeb m n).
Proof.
unfold natgeh, natgeb.
apply (reflect_logrewr (X := ¬ (n > m))).
- apply neggth_logeq_leh.
- apply reflect_neg.
  apply reflect_natltb.
Qed.

Lemma reflect_natleb (m n : nat) : reflect (m ≤ n) (natleb m n).
Proof.
unfold natleb.
apply (reflect_logrewr (X := ¬ (n < m))).
- unfold natlth. apply neggth_logeq_leh.
- apply reflect_neg.
  apply reflect_natltb.
Qed.

Lemma reflect_nateqb (m n : nat) : reflect (m = n) (nateqb m n).
Proof.
revert n. induction m as [|m Hm]; intro n.
- induction n as [|n Hn].
  + apply true_to_reflect. reflexivity.
  + apply false_to_reflect. apply negpaths0sx.
- induction n as [|n _].
  + apply false_to_reflect. apply negpathssx0.
  + simpl. apply (reflect_logrewr (X := m = n)).
    * split.
      -- intros H. apply maponpaths, H.
      -- apply invmaponpathsS.
    * apply Hm.
Qed.

Lemma reflect_to_decidable {X : UU} {b : bool} : reflect X b -> decidable X.
Proof.
intros H; induction b.
- apply reflect_to_true in H. apply ii1. assumption.
- apply reflect_to_false in H. apply ii2. assumption.
Qed.

Lemma decidable_to_reflect {X : UU} {b : bool} (H : decidable X)
  : reflect X (coprodtobool H).
Proof.
induction H as [H|H]; simpl.
- apply true_to_reflect. exact H.
- apply false_to_reflect. exact H.
Qed.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.MoreLists.
