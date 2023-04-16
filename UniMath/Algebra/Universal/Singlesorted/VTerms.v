(** ** Variables and terms with variables *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)
(**
Given a signature σ, a [varspec] (variable specification) is a map from an [hSet] of _variables_
to the corresponding sort. A signature σ and a variable specification [V] give origin to a new
signature, [vsignature σ V] where variables in [v] become constant symbols. A term over
signature σ and variables in V is, i.e., a [vterm σ v], is a plain (ground) term over this
extended signature.
*)

Require Import UniMath.Foundations.All.

Require Export UniMath.Algebra.Universal.Singlesorted.Terms.

Section VTerms.

  Definition vsignature (σ : signature) (V: hSet): signature
    := make_signature (setcoprod (names σ) V) (sumofmaps (@arity σ) (λ v, 0)).

  Context {σ : signature}.

  Definition namelift (V: hSet) (nm: names σ): names (vsignature σ V) := inl nm.

  Definition varname {V: hSet} (v: V): names (vsignature σ V) := inr v.

  Definition term (σ: signature) (V: hSet): UU := gterm (vsignature σ V).

  Definition termset (σ: signature) (V: hSet): UU := gtermset (vsignature σ V).

  Definition build_term {V: hSet} (nm: names σ) (v:  vec (term σ V) (arity nm))
    : term σ V  := build_gterm (namelift V nm) v.

  Definition varterm {V: hSet} (v: V): term σ V := build_gterm (varname v) [()].

  (** Evaluation maps for terms and corresponding unfolding properties *)

  Definition fromterm {A: UU} {V: hSet}
                      (op : (∏ nm : names σ, vec A (arity nm) → A))
                      (α : V → A)
    : term σ V → A.
  Proof.
    refine (@fromgterm (vsignature σ V) A _).
    induction nm as [nm | v].
    - exact (op nm).
    - exact (λ _, α v).
  Defined.

  Lemma fromtermstep {A: UU} {V: hSet}
                     (op : (∏ nm : names σ, vec A (arity nm) → A))
                     (α : V → A)
                     (nm: names σ) (v: vec (term σ V) (arity nm))
    : fromterm op α (build_term nm v) = op nm (vec_map (fromterm op α) v).
  Proof.
    unfold fromterm, fromgterm, build_term.
    rewrite (term_ind_step _ _  (namelift V nm)).
    simpl.
    rewrite h1lower_h1map_hlift.
    apply idpath.
  Defined.

  (** This used to be provable with apply idpath in the single sorted case **)
  Lemma fromtermstep' {A: UU} {V: hSet}
                      (op : (∏ nm : names σ, vec A (arity nm) → A))
                      (α : V → A)
                      (v: V)
    : fromterm op α (varterm v) = α v.
  Proof.
    apply idpath.
  Defined.

  (** ** Helpers for working with curried functions *)

  Definition build_term' {V: hSet} (nm: names σ)
    : Vectors.iterfun (arity (namelift V nm)) (term σ V) (term σ V)
    := build_gterm' (namelift V nm).

End VTerms.
