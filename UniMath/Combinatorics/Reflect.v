(** * Boolean reflection. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
Boolean reflection, in the spirit of SSReflect.
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Bool.

(* Preliminary material that has to be moved elsewhere. *)

Lemma isaproplogeq {X Y : UU}
  : isaprop X → isaprop Y → isaprop (X <-> Y).
Proof.
intros. unfold logeq.
apply isapropdirprod; apply isapropimpl; assumption.
Defined.

Lemma fiber_paths_simple {A : UU} (Aset : isaset A) (B : A → UU)
        (a : A) (b b' : B a) (p : a,,b = a,,b')
  : b = b'.
Proof.
refine (_ @ fiber_paths (B := B) p). cbn.
apply pathsinv0. apply transportf_set. exact Aset.
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

Lemma feq_reflect {X Y : UU} (f : X → Y) {x y : X} (b : bool)
         (inj : ∏ x y, f x = f y → x = y)
         (H : reflect (f x = f y) b)
  : reflect (x = y) b.
Proof.
induction b; cbn; unfold_reflect.
- apply inj. exact H.
- intros p. exact (H (maponpaths f p)).
Qed.

Lemma reflect_feq {X Y : UU} (f : X → Y) {x y : X} (b : bool)
        (inj : ∏ x y, f x = f y → x = y)
        (H : reflect (x = y) b)
  : reflect (f x = f y) b.
Proof.
induction b; cbn; unfold_reflect.
- apply maponpaths. exact H.
- intros p. apply H. apply inj. exact p.
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
- induction n as [|n Hn]; cbn; unfold_reflect.
  + apply idpath.
  + apply negpaths0sx.
- induction n as [|n _]; cbn; unfold_reflect.
  + apply negpathssx0.
  + simpl. apply (reflect_logrewr (X := m = n)).
    * split.
      -- intros H. apply maponpaths, H.
      -- apply invmaponpathsS.
    * apply Hm.
Qed.

Lemma reflect_to_decidable {X : UU} (b : bool) : reflect X b -> decidable X.
Proof.
intros H; induction b; unfold_reflect.
- apply ii1. assumption.
- apply ii2. assumption.
Qed.

Lemma decidable_to_reflect {X : UU} (b : bool) (H : decidable X)
  : reflect X (coprodtobool H).
Proof.
induction H as [H|H]; simpl; unfold_reflect; exact H.
Qed.

Definition uniteqB : unit → unit → bool := λ x y, true.

Lemma reflect_uniteqB (x y : unit)
  : reflect (x = y) true.
Proof.
  unfold_reflect.
  induction x; induction y; apply idpath.
Qed.

Definition coprodeqB {X Y : UU}
             (XeqB : X → X → bool)
             (YeqB : Y → Y → bool)
             (a b : X ⨿ Y) : bool
  := match a with
     | inl x => match b with inl x' => XeqB x x' | inr _ => false end
     | inr y => match b with inl _ => false | inr y' => YeqB y y' end
  end.

Lemma reflect_coprodeqB
        {X : UU} (XeqB : X → X → bool) (HX : ∏ x x', reflect (x = x') (XeqB x x'))
        {Y : UU} (YeqB : Y → Y → bool) (HY : ∏ y y', reflect (y = y') (YeqB y y'))
        (a b : X ⨿ Y)
  : reflect (a = b) (coprodeqB XeqB YeqB a b).
Proof.
induction a; induction b; cbn; unfold_reflect.
- apply reflect_feq.
  + apply ii1_injectivity.
  + apply HX.
- apply negpathsii1ii2.
- apply negpathsii2ii1.
- apply reflect_feq.
  + apply ii2_injectivity.
  + apply HY.
Qed.

Definition total2eqB {X : UU} (Y : X → UU)
             (eqB : ∏ x : X, Y x → ∏ x' : X, Y x' → bool)
             (a b : ∑ x : X, Y x)
  : bool
  := eqB (pr1 a) (pr2 a) (pr1 b) (pr2 b).

Lemma reflect_total2eqB {X : UU} (Y : X → UU)
        (eqB : ∏ x : X, Y x → ∏ x' : X, Y x' → bool)
        (H : ∏ x (y : Y x) x' (y' : Y x'), reflect (x,,y = x',,y') (eqB _ y _ y'))
        (a b : ∑ x : X, Y x)
  : reflect (a = b) (total2eqB Y eqB a b).
Proof.
induction a as (x,y); induction b as (x',y').
unfold total2eqB. cbn.
apply H.
Qed.
