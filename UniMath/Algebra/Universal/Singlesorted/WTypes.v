(** * Algebra, functor algebras and w-types. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.
Require Import UniMath.Induction.W.Wtypes.
Require Import UniMath.Induction.FunctorAlgebras_legacy.

Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Singlesorted.Signatures.
Require Import UniMath.Algebra.Universal.Singlesorted.Algebras.
Require Import UniMath.Algebra.Universal.Singlesorted.Terms.
Require Import UniMath.Algebra.Universal.Singlesorted.TermAlgebras.

Local Open Scope stn.
Local Open Scope cat.
Local Open Scope hom.
Local Open Scope vec.

Context (σ: signature).

Definition A := names σ.

Definition B (a: A) := ⟦ arity a ⟧.

(* Funtore polinomiale corrispondente alla segnatura σ *)

Local Notation F := (polynomial_functor A B).

(** Prove that algebra_ob and algebra are equal types *)

Definition algebra_to_functoralgebra (a: algebra σ)
  : algebra_ob F.
Proof.
  induction a as [carrier ops].
  unfold algebra_ob.
  exists carrier.
  simpl.
  intro X.
  induction X as [nm subterms].
  refine (ops nm _).
  exact (make_vec subterms).
Defined.

Definition functoralgebra_to_algebra (FAlg: algebra_ob F)
  : algebra σ.
Proof.
  induction FAlg as [carrier ops].
  simpl in ops.
  exists carrier.
  intro nm.
  intro subterms.
  exact (ops (nm ,, el subterms)).
Defined.

Lemma alg_funcalg_alg (a: algebra_ob F)
  : algebra_to_functoralgebra (functoralgebra_to_algebra a) = a.
Proof.
  use total2_paths2_f.
  - apply idpath.
  - rewrite idpath_transportf.
    apply funextfun.
    intro X.
    simpl.
    rewrite el_make_vec_fun.
    apply idpath.
Qed.

(** Helper lemma on transport *)

Definition transportf_dirprod' (A : UU) (B B' : A -> UU) (a a': A) (x: B a)
                               (x': B' a) (p : a = a')
  : transportf (λ a, B a × B' a) p (x,, x') =
      make_dirprod (transportf (λ a, B a) p x) (transportf (λ a, B' a) p x').
Proof.
  induction p.
  apply idpath.
Qed.

Lemma transportb_sec_constant {A B : UU} {C : A -> B -> UU} {x1 x2 : A} (p : x1 = x2)
                              (f : ∏ y : B, C x2 y)
 : transportb (λ x, ∏ y : B, C x y) p f = (λ y, transportb (λ x, C x y) p (f y)).
Proof.
 induction p.
 apply idpath.
Qed.

Lemma transportb_fun {P: (unit → UU) → UU} {Q: (unit → UU) → UU} {a a': unit → UU}
                     {p: a = a'} {f: P a' → Q a'} {x: P a}
  : transportb (λ x: unit → UU, P x → Q x) p f x =
       transportb (λ x: unit → UU, Q x) p (f (transportf (λ x: unit → UU, P x) p x)).
Proof.
  induction p.
  apply idpath.
Qed.

Lemma funcalg_alg_funcalg (a: algebra σ)
  : functoralgebra_to_algebra (algebra_to_functoralgebra a) = a.
Proof.
  use total2_paths2_b.
  - apply idpath.
  - apply funextsec.
    intro nm.
    apply funextfun.
    intro x.
    simpl.
    rewrite make_vec_el.
    rewrite transportb_sec_constant.
    apply idpath.
Defined.

Definition alegbra_weq_functoralgebra: algebra σ ≃ algebra_ob F.
Proof.
  apply (weq_iso algebra_to_functoralgebra functoralgebra_to_algebra).
  exact funcalg_alg_funcalg.
  exact alg_funcalg_alg.
Defined.

Definition alegbra_eq_functoralgebra: algebra σ = algebra_ob F.
Proof.
  apply univalence.
  exact alegbra_weq_functoralgebra.
Defined.

(** Prove that the ground term algebra is a W-type *)

(* Definition make_h1const {A: UU} {n: nat}: (⟦ n ⟧ → A) → *)

Local Definition U := gterm σ.

Local Definition sup: ∏ x : A, (B x → U) → U.
Proof.
  intros nm subterms.
  refine (build_gterm nm _).
  exact (make_vec subterms).
Defined.

Local Lemma build_gterm_sup (nm: A) (v: vec (gterm σ) (arity nm)):
  build_gterm nm v = sup nm (el v).
Proof.
  unfold sup.
  apply maponpaths.
  apply pathsinv0.
  apply make_vec_el.
Qed.

Local Definition ind: ∏ P : U → UU, (∏ (x : A) (f : B x → U)
                                     , (∏ u : B x, P (f u)) → P (sup x f)) → ∏ w : U, P w.
Proof.
  unfold U in *.
  intros P e_s w.
  apply term_ind.
  intros nm v IH.
  apply (transportb _ (build_gterm_sup nm v)).
  apply e_s.
  intro u.
  set (IHu := hel IH u).
  rewrite el_vec_map in IHu.
  assumption.
Defined.

(*
Lemma transport_lemma {C : UU} (P: C → UU) (e_s : ∏ (x : A) (f : B x → U), (∏ u : B x, P (f u)) → P (sup x f)
  : transportb B p (e_s x f) = e_s x (transportb (H x)).


Local Lemma lemma_beta (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (sup x f)) (x: A) (f: B x → U)
                       (IH: ∏ u: B x, P (el (h1const_to_vec (vec_to_h1const (make_vec f))) u))
  : ∑ A:(∏ u: B x, P (f u)), transportb P (build_gterm_sup x (vec_to_h1const (make_vec f))) (e_s x (el (h1const_to_vec (vec_to_h1const (make_vec f)))) IH)
    = e_s x f A.
Proof.
  eexists.
  set (path := build_gterm_sup x (vec_to_h1const (make_vec f))).
  clearbody path.
  unfold sup in path.

  revert path.
  rewrite vec_h1const_vec.

  generalize path.
  intro path0
  Search transportb "fun".
Abort.

Lemma transport_const {X Y Z: UU} (P: Z → UU) (f: ∏ (x: X) (y: Y), Z) (i: ∏ (x: X) (y: Y), P (f x y)) (x: X) (y1 y2: Y) (p: f x y1 = f x y2)
  : transportb P p (i x y2) = i x y1.
Proof.

Local Definition beta (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (sup x f))
                      (x : A) (f : B x → U)
  : ind P e_s (sup x f) = e_s x f (λ u, ind P e_s (f u)).
Proof.
  unfold ind.
  unfold sup.
  rewrite (term_ind_step _ _ x).

  rewrite XX.
  rewrite <- functtransportb
  Search transportb maponpaths.

  simpl.
Abort.
*)