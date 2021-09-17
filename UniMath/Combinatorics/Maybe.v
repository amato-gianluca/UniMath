(** * A simple implementation of the maybe/option monad which does not require category theory. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.Foundations.PartC.
Require Import UniMath.Combinatorics.Reflect.

Definition maybe (A: UU):= A ⨿ unit.

Definition just {A: UU}: A → maybe A := ii1.

Definition nothing {A: UU}: maybe A := ii2 tt.

Definition just_injectivity {A: UU}: ∏ (x y: A), just x = just y → x = y := ii1_injectivity.

Lemma isasetmaybe {A: UU} (H: isaset A): isaset (maybe A).
Proof.
  apply isasetcoprod.
  - exact H.
  - exact isasetunit.
Defined.

Lemma negpathjustnothing {A : UU} (a : A) : just a != nothing.
Proof.
apply negpathsii1ii2.
Defined.

Lemma negpathnothingjust {A : UU} (a : A) : nothing != just a.
Proof.
apply negpathsii2ii1.
Defined.

Definition flatmap {A B: UU} (f: A → maybe B): maybe A → maybe B
  := coprod_rect _ f (λ _, nothing).

Lemma flatmap_just {A B: UU} (f: A → maybe B) (a: A)
  : flatmap f (just a) = f a.
Proof.
  apply idpath.
Defined.

Lemma flatmap_nothing {A B: UU} (f: A → maybe B)
  : flatmap f nothing = nothing.
Proof.
  apply idpath.
Defined.

Lemma flatmap_ind {A: UU} (P: ∏ (x: maybe A),  UU): (P nothing) → (∏ a: A, P (just a)) → ∏ x: maybe A, P x.
Proof.
  intros Pnothing Pjust.
  induction x as [ok | error].
  - exact (Pjust ok).
  - induction error.
    exact Pnothing.
Defined.

Definition frommaybe {X Y : UU} (f : X → Y) (d : Y) (x : maybe X) : Y
  := match x with inl a => f a | inr _ => d end.

Lemma frommaybe_just {X Y : UU} {x d} (f : X → Y)
  : frommaybe f d (just x) = f x.
Proof.
apply idpath.
Defined.

Lemma frommaybe_nothing {X Y : UU} {d} (f : X → Y)
  : frommaybe f d nothing = d.
Proof.
apply idpath.
Defined.

Definition maybeeqB {X : UU} (eqB : X → X → bool)
  : maybe X → maybe X → bool
  := coprodeqB eqB uniteqB.

Lemma reflect_maybeeqB {X : UU} (eqB : X → X → bool)
        (H : ∏ x y : X, reflect (x = y) (eqB x y))
        (x y : maybe X)
  : reflect (x = y) (maybeeqB eqB x y).
Proof.
  apply reflect_coprodeqB.
  + apply H.
  + apply reflect_uniteqB.
Qed.

Definition maybetobool {A : UU}
  : maybe A → bool
  := coprodtobool.

Lemma reflect_maybetobool {A : UU} (x : maybe A)
  : reflect (x != nothing) (maybetobool x).
Proof.
revert x.
refine (flatmap_ind _ _ _); cbn; intros; unfold_reflect; intros H.
- apply H. apply idpath.
- apply (negpathjustnothing _ H).
Qed.
