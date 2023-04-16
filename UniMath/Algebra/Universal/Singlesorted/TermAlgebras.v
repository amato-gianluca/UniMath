(** * The ground term algebra and the proof it is initial. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)

Require Import UniMath.Foundations.All.

Require Export UniMath.Algebra.Universal.Singlesorted.Algebras.
Require Export UniMath.Algebra.Universal.Singlesorted.Terms.

Local Open Scope hom.

Section TermAlgebra.

  Definition term_algebra (σ: signature): algebra σ
    := make_algebra (gterm σ) build_gterm.

  Definition has_supportsets_termalgebra (σ: signature): has_supportsets (term_algebra σ)
    := isasetterm σ.

  Definition term_hSetalgebra (σ: signature): hSetalgebra σ
    := make_hSetalgebra (has_supportsets_termalgebra σ).

  Context {σ: signature}.

  Definition geval (a: algebra σ): term_algebra σ → a
    := @fromgterm σ a (ops a).

  Lemma gevalstep {a: algebra σ} (nm: names σ) (v: vec (gterm σ) (arity nm))
    : geval a  (build_gterm nm v) = ops a nm (vec_map (geval a) v).
  Proof.
    unfold geval.
    apply fromtermstep.
  Defined.

  Lemma ishomgeval (a: algebra σ): ishom (geval a).
  Proof.
    red.
    intros.
    apply gevalstep.
  Defined.

  Definition gevalhom (a: algebra σ): term_algebra σ ↷ a
    := make_hom (ishomgeval a).

  Lemma vec_map_path {A B: UU} {n: nat}
      (f g: A → B) (v: vec A n)
      (h1path: hvec (vec_map (λ p, f p = g p) v))
      : vec_map f v = vec_map g v.
  Proof.
    revert n v h1path.
    refine (vec_ind _ _ _).
    - induction v.
      reflexivity.
    - simpl.
      intros x n xs IHxs h2path.
      use map_on_two_paths.
      + exact (pr1 h2path).
      + exact (IHxs (pr2 h2path)).
  Defined.

  Lemma gevalhom_is_unique {a: algebra σ} (f: term_algebra σ ↷ a):
    pr1 f = pr1 (gevalhom a).
  Proof.
    induction f as [f fishom].
    apply funextsec.
    intro t.
    apply (term_ind (λ t, f t = geval a t)).
    unfold term_ind_HP.
    intros.
    change (build_gterm nm v) with (ops (term_algebra σ) nm v) at 1.
    rewrite fishom.
    rewrite gevalstep.
    apply maponpaths.
    apply vec_map_path.
    exact IH.
  Qed.

  Definition iscontrhomsfromgterm (a: algebra σ) (setprop: has_supportsets a)
    : iscontr (term_algebra σ ↷ a).
  Proof.
    exists (gevalhom a).
    intro f.
    apply subtypePairEquality'.
    - apply gevalhom_is_unique.
    - apply isapropishom.
      exact setprop.
  Defined.

End TermAlgebra.
