(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.

(** Basic definitions **)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names (sigma: Signature): hSet := pr1 sigma.

Definition arity {sigma: Signature}: names sigma → Arity := pr2 sigma.

Definition mk_signature {n: nat} (v: Vector nat n): Signature
  := (stnset n,, el v).

Definition Algebra (sigma: Signature): UU
  := ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

Definition support {sigma: Signature} (a: Algebra sigma): hSet := pr1 a.

Definition dom {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  Vector (support a) (arity nm).

Definition cod {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  support a.

Definition op {sigma: Signature} {a: Algebra sigma} (nm: names sigma): (dom nm) → (cod nm)
  := pr2 a nm.

Definition mk_algebra {sigma : Signature} (support : hSet)
           (ops: ∏ nm: names sigma, Vector support (arity nm) → support) : Algebra sigma
  := (support,, ops).

(** Algebra homomorphism **)

Section Homomorphisms.

  Context { sigma: Signature }.

  Definition is_hom {a1 a2: Algebra sigma} (f: support a1 → support a2): UU :=
    ∏ (nm: names sigma) (x: dom nm), (f (op nm x) = (op nm (vector_map f x))).

  Definition hom (a1 a2: Algebra sigma): UU :=  ∑ (f: support a1 → support a2), is_hom f.

  Local Notation "a1 ↦ a2" := (hom a1 a2)  (at level 80, right associativity).

  Definition hom_to_fun {a1 a2: Algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Definition hom_to_proof {a1 a2: Algebra sigma} (f: a1 ↦ a2): is_hom (hom_to_fun f) := pr2 f.

  Definition hom_id {a: Algebra sigma}: a ↦ a.
  Proof.
    exists (idfun (support a)).
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3.
  Proof.
    exists (funcomp (hom_to_fun h1) (hom_to_fun h2)).
    red.
    intros.
    induction h1 as [f1 ishomf1].
    induction h2 as [f2 ishomf2].
    cbn.
    rewrite vector_map_comp.
    rewrite ishomf1.
    rewrite ishomf2.
    reflexivity.
  Defined.

End Homomorphisms.

(** Terminal algebra **)

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mk_algebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

  Definition terminal_hom (a : Algebra sigma): hom a terminal_algebra.
  Proof.
    red.
    exists (λ _, tt).
    red.
    intros.
    apply iscontrunit.
  Defined.

  Theorem terminal_hom_unicity (a: Algebra sigma) (f: hom a terminal_algebra): f = terminal_hom a.
  Proof.
    eapply total2_paths2_f.
    Unshelve.
    2: apply iscontrfuntounit.
    assert (isprop: ∏ (f: support a → support terminal_algebra), isaprop (is_hom f)).
    - intro.
      apply isapropifcontr.
      unfold is_hom.
      apply impred_iscontr.
      intros.
      apply impred_iscontr.
      intros.
      apply iscontrpathsinunit.
    - apply isprop.
  Defined.

End TerminalAlgebra.

(** Term algebra **)

Definition Stack (sigma: Signature): UU := list (names sigma).

Definition Status: UU := nat ⨿ unit.

Definition stackok n: Status := ii1 n.

Definition stackerror: Status := ii2 tt.

Section StackStatus.

  Context { sigma: Signature }.

  Definition status_cons (nm: names sigma) (status: Status): Status.
  Proof.
    induction status as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (stackok ( S(n - arity nm) )).
      + exact stackerror.
    - exact stackerror.
  Defined.

  Lemma status_cons_stackok {nm: names sigma} {n: nat}:
    status_cons nm (stackok n) != stackerror →  arity nm ≤ n.
  Proof.
    intro noerror.
    cbn [stackok status_cons coprod_rect] in noerror.
    induction (isdecrelnatleh (arity nm) n).
    * assumption.
    * cbn in noerror.
      contradiction.
  Defined.

  Lemma status_cons_stackok2 {nm: names sigma} {n: nat} {m: nat}:
    status_cons nm (stackok n) = stackok m → m = S(n - arity nm).
  Proof.
    intro scons.
    cbn [stackok status_cons coprod_rect] in scons.
    induction (isdecrelnatleh (arity nm) n).
    * cbn in scons.
      apply ii1_injectivity in scons.
      apply pathsinv0.
      assumption.
    * cbn in scons.
      apply negpathsii2ii1 in scons.
      contradiction.
  Defined.

  Lemma status_cons_noerror {nm: names sigma} {status: Status}:
    status_cons nm status != stackerror → ∑ n: nat, status = stackok n × arity nm ≤ n.
  Proof.
    intro noerror.
    induction status.
    - exists a.
      split.
      + apply idpath.
      + apply status_cons_stackok. assumption.
    - contradiction.
  Defined.

  Lemma status_cons_noerror2 {nm: names sigma} {status: Status}:
    status_cons nm status != stackerror → status != stackerror.
  Proof.
    apply negf.
    intro status_err.
    rewrite status_err.
    reflexivity.
  Defined.

  Definition status_concatenate (status1 status2: Status): Status.
  Proof.
    induction status2 as [len_s2 | error2].
    - induction status1 as [len_s1 | error1].
      + exact (stackok (len_s1 + len_s2)).
      + exact stackerror.
    - exact stackerror.
  Defined.

  (** to be proved later ***)
  Axiom natleh_add: ∏( n1 n2 m: nat), n1 ≤ n2 → n1 ≤ n2 + m.

  (** to be proved later ***)
  Axiom natleh_adddiff: ∏( n1 n2 n3: nat), n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.

  Lemma status_concatenate_statuscons {nm: names sigma} {status1 status2: Status}:
    (status_cons nm status1 != stackerror) →
    status_concatenate (status_cons nm status1) status2
    = status_cons nm (status_concatenate status1 status2).
  Proof.
    induction status1 as [a1 | error1].
    2: contradiction.
    induction status2 as [a2 | error2].
    2: reflexivity.
    intro noerror.
    cbn [status_concatenate status_cons stackok stackerror coprod_rect].
    induction (isdecrelnatleh (arity nm) a1).
    - cbn [stackok coprod_rect].
      induction (isdecrelnatleh (arity nm) (a1 + a2)) as [okarity | badarity].
      + cbn.
        apply maponpaths.
        apply (maponpaths S).
        apply natleh_adddiff.
        assumption.
      + apply fromempty, badarity, natleh_add.
        assumption.
    - apply fromempty, b.
      apply status_cons_stackok; assumption.
  Defined.

  Definition stack2status: Stack sigma → Status := foldr status_cons (stackok 0).

  Lemma stack2status_length {s: Stack sigma}:
    ( ∑ n: nat, stack2status s = stackok n × n > 0 ) → length s > 0.
  Proof.
    apply (list_ind (λ s, (∑ n : nat, stack2status s = stackok n × n > 0) → length s > 0)).
    - intro status.
      induction status as [ n [ n_is_status n_gt_0 ]].
      cbn in n_is_status.
      apply ii1_injectivity in n_is_status.
      rewrite n_is_status in n_gt_0.
      set (contr := isirreflnatgth n).
      contradiction.
    - intros.
      reflexivity.
  Defined.

  Lemma stack2status_cons {nm: names sigma} {s: Stack sigma}:
    stack2status (cons nm s) = status_cons nm (stack2status s).
  Proof.
    reflexivity.
  Defined.

  Lemma stack2status_compositional {s1 s2: Stack sigma}:
    stack2status s1 != stackerror →
    status_concatenate (stack2status s1) (stack2status s2) = stack2status (concatenate s1 s2).
  Proof.
    apply (list_ind (λ s, stack2status s != stackerror →
                          status_concatenate (stack2status s) (stack2status s2)
                          = stack2status (concatenate s s2))).
    - intros.
      change (stack2status (concatenate nil s2)) with (stack2status s2).
      induction (stack2status s2) as [oks2 | bads2].
      + reflexivity.
      + induction bads2.
        reflexivity.
    - intros nm s1tail IH noerror.
      rewrite stack2status_cons.
      rewrite status_concatenate_statuscons by (assumption).
      rewrite IH.
      + rewrite <- stack2status_cons.
        reflexivity.
      + apply (status_cons_noerror2(nm:=nm)).
        assumption.
  Defined.

  Definition stack_is_term (s: Stack sigma): UU := stack2status s = stackok 1.

  Lemma nil_not_term: ¬ stack_is_term nil.
  Proof.
    unfold stack_is_term.
    cbn.
    intro s0s1.
    apply ii1_injectivity in s0s1.
    apply negpaths0sx in s0s1.
    contradiction.
  Defined.

End StackStatus.

Definition term (sigma: Signature) := ∑ s: Stack sigma, stack_is_term s.

Coercion term2stack {sigma: Signature} (t: term sigma): Stack sigma := pr1 t.

Coercion term2list {sigma: Signature} (t: term sigma): list (names sigma) := pr1 t.

Definition term2proof {sigma: Signature} (t: term sigma): stack_is_term (term2stack t) := pr2 t.

Section Terms.

  Context {sigma: Signature}.

  Definition mkseq {n: nat} (vec: Vector (term sigma) n):
    ∑ s: Stack sigma, stack2status s = stackok n.
  Proof.
    induction n.
    - exists nil.
      reflexivity.
    - induction (IHn (tl vec)) as [rest rest_status].
      exists (concatenate (term2stack (hd vec)) rest).
      rewrite <- stack2status_compositional.
      + rewrite (term2proof (hd vec)).
        rewrite rest_status.
        reflexivity.
      + rewrite (term2proof (hd vec)).
        apply negpathsii1ii2.
  Defined.

  Definition mkterm (n: names sigma) (vec: Vector (term sigma) (arity n)): term sigma.
  Proof.
    induction (mkseq vec) as [tail tail_status].
    exists (cons n tail).
    unfold stack_is_term.
    rewrite stack2status_cons.
    rewrite tail_status.
    unfold stackok.  (* replace stackok with inl *)
    unfold status_cons.
    unfold coprod_rect at 1.
    induction (isdecrelnatleh (arity n) (arity n)).
    - cbn.
      rewrite minuseq0'.
      apply idpath.
    - induction b.
      apply isreflnatleh.
  Defined.

  Lemma term_isaset: isaset (term sigma).
  Proof.
    apply isaset_total2.
    apply isofhlevellist.
    - exact (pr2 (names sigma)).
    - intro nm.
      unfold stack_is_term.
      apply hlevelntosn.
      apply isaproppathstoisolated.
      apply isolatedtoisolatedii1.
      apply isisolatedn.
  Defined.

End Terms.

Definition term_hset (sigma : Signature): hSet := make_hSet (term sigma) term_isaset.

Definition term_algebra (sigma: Signature): Algebra sigma
   := mk_algebra (term_hset sigma) mkterm.

Section TermInduction.

  Context {sigma: Signature}.

  Definition princ_op (t: term sigma): names sigma.
  Proof.
    induction t as [s s_is_term].
    generalize s_is_term.
    apply (list_ind (λ s : Stack sigma, stack_is_term s → names sigma)).
    - intro nilterm.
      unfold stack_is_term in nilterm.
      cbn in nilterm.
      apply ii1_injectivity in nilterm.
      apply negpaths0sx in nilterm.
      contradiction.
    - intros.
      exact x.
  Defined.

  (*** These axioms probably needs some additional hypotheses **)

  Axiom natlehandminusl: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natlehandminusr: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natdiff0: ∏ a b: nat, 0 = a - b → b ≥ a.

  Axiom natdiffasymm: ∏ a b: nat, a ≤ b → a ≥ b → a=b.

  Axiom nat_ax: ∏ a b c: nat, a = S (b - c) → b = a + c -1.

  Axiom nat_ax3: ∏ a b c : nat, a + b - 1 - (c + b - 1) = a-c.

  Lemma nat_notgeh1: ∏ n: nat, ¬ (n ≥ 1) → n = 0.
  Proof.
    intro.
    induction n.
    - intro.
      apply idpath.
    - intro n_gte_1.
      apply fromempty.
      apply n_gte_1.
      apply natgthtogehsn.
      apply natgthsn0.
  Defined.

  Lemma nat_notgeh1_inv: ∏ n: nat, n != 0 → n ≥ 1.
  Proof.
    intros.
    apply natgthtogehsn.
    apply natneq0togth0.
    apply nat_nopath_to_neq.
    assumption.
  Defined.

  Definition extract_substack (s: Stack sigma):
    ∏ n m: nat, stack2status s = stackok m → n ≤ m  →
                ∑ first second: Stack sigma,
                        stack2status first = stackok n ×
                        stack2status second = stackok (m - n) ×
                        concatenate first second = s.
  Proof.
    apply (list_ind (λ s : Stack sigma, ∏ n m: nat, stack2status s = stackok m → n ≤ m →
                     ∑ first second: Stack sigma, stack2status first = stackok n ×
                                                  stack2status second = stackok (m - n) ×
                                                  concatenate first second = s)).
    - intros n m s_status.
      cbn in s_status.
      apply ii1_injectivity in s_status.
      rewrite <- s_status.
      intro n_leh_0.
      apply nat0gehtois0 in n_leh_0.
      rewrite n_leh_0.
      exists nil.
      exists nil.
      do 2 ( split; try reflexivity ).
    - intros nm tail IH n m s_status m_geh_n.
      induction (isdeceqnat n 0) as [n_is_0 | n_gt_0].
      + rewrite n_is_0.
        exists nil.
        exists (cons nm tail).
        do 2 ( split; try reflexivity ).
        rewrite natminuseqn.
        assumption.
      + apply nat_notgeh1_inv in n_gt_0.
        rewrite stack2status_cons in s_status.
        assert ( tail_ok: ∑ tail_ar: nat, stack2status tail = stackok tail_ar ×
                                                                      arity nm ≤ tail_ar ).
        {
          apply status_cons_noerror.
          rewrite s_status.
          apply negpathsii1ii2.
        }
        induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound]].
        rewrite tail_status_prf in s_status.
        apply status_cons_stackok2 in s_status.
        apply nat_ax in s_status.
        assert (tail_ar_newbound: n + arity nm - 1 ≤ tail_ar).
        {
          rewrite s_status.
          apply natlehandminusl.
          apply natlehandplus.
          - assumption.
          - apply isreflnatleh.
        }
        set (IH1 := IH (n + arity nm - 1) tail_ar tail_status_prf tail_ar_newbound).
        induction IH1 as [fst [snd [status_fst_prf [status_snd_prf conc]]]].
        rewrite s_status in status_snd_prf.
        rewrite nat_ax3 in status_snd_prf.
        set (realfirst := cons nm fst).
        assert (stack2status realfirst = stackok n).
        {
          unfold realfirst.
          rewrite stack2status_cons.
          rewrite status_fst_prf.
          unfold stackok.
          unfold status_cons.
          unfold coprod_rect at 1.
          induction (isdecrelnatleh (arity nm) (n + arity nm - 1)).
          - cbn.
            rewrite natminusminus.
            rewrite (natpluscomm 1 (arity nm)).
            rewrite <- natminusminus.
            rewrite plusminusnmm.
            change (S (n - 1)) with (1 + (n - 1)).
            rewrite natplusminusle.
            * rewrite natpluscomm.
              rewrite plusminusnmm.
              apply idpath.
            * assumption.
          - induction b.
            rewrite natpluscomm.
            rewrite <- natplusminusle.
            + apply natlehnplusnm.
            + assumption.
        }
        exists realfirst.
        exists snd.
        do 2 ( split ; try assumption ).
        unfold realfirst.
        rewrite concatenateStep.
        rewrite conc.
        apply idpath.
  Defined.

  Definition subterm (t: term sigma): ⟦ arity (princ_op t) ⟧ → term sigma.
  Proof.
    assert (subterm2: ∏ (s: Stack sigma) (s_is_term: stack_is_term s),
            ⟦ arity (princ_op (s ,, s_is_term)) ⟧ → term sigma).
    2: exact (subterm2 (term2stack t) (term2proof t)).
    apply (list_ind (λ (s: Stack sigma),
                     ∏ s_is_term : stack_is_term s,
                                   ⟦ arity (princ_op (s,, s_is_term)) ⟧ → term sigma)).
    - intro.
      set (contr := nil_not_term s_is_term).
      contradiction.
    - intros x tail IH s_is_term.
      cbn.
      intro arx.
      induction arx as [n n_lt_arx].
      red in s_is_term.
      rewrite stack2status_cons in s_is_term.
      assert (s_ok: status_cons x (stack2status tail) != stackerror).
      {
        rewrite s_is_term.
        apply negpathsii1ii2.
      }
      set ( tail_ok := status_cons_noerror s_ok).
      induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound ]].
      rewrite tail_status_prf in s_is_term.
      assert ( tail_ar_x: tail_ar = arity x).
      {
        set ( X := status_cons_stackok2  s_is_term).
        change (1) with (1+0) in X.
        change (S (tail_ar - arity x)) with (1 + (tail_ar - arity x)) in X.
        set (Y := natpluslcan _ _ _ X).
        set (Z := natdiff0 _ _ Y).
        apply natdiffasymm; assumption.
      }
      rewrite tail_ar_x in tail_status_prf.
      induction (isdecrelnatgeh n 1) as [n_gte_1 | n_eq_0].
      + assert ( extractok: n - 1 ≤ arity x).
        {
          apply (istransnatleh(m := arity x - 1)).
          - apply natlehandminusl.
            apply natlthtoleh.
            assumption.
          - apply natminuslehn.
        }
        set (remove := extract_substack tail (n - 1) (arity x) tail_status_prf extractok).
        induction remove as [first [ second  [ firstss [ secondss conc] ] ] ].
        assert ( extractok2: 1 ≤ arity x - (n - 1) ).
        {
          apply (natlehandplusrinv _ _ (n - 1)).
          rewrite minusplusnmm by (assumption).
          rewrite natplusminusle by (assumption).
          rewrite natpluscomm.
          rewrite <- natplusminusle by (apply idpath).
          simpl (1 - 1).
          rewrite natplusr0.
          apply natlthtoleh.
          assumption.
        }
        set (res := extract_substack second 1 (arity x - (n - 1)) secondss extractok2).
        induction res as [result [second0 [result_is_term [second_ss conc1]]]].
        exact (result ,, result_is_term).
      + apply nat_notgeh1 in n_eq_0.
        assert (extractok: 1 ≤ arity x ).
        {
          apply natlthtolehsn.
          rewrite <- n_eq_0.
          assumption.
        }
        set (res := extract_substack tail 1 (arity x) tail_status_prf extractok).
        induction res as [result  [second0 [result_is_term [second_ss conc1]]]].
        exact (result ,, result_is_term).
  Defined.

  Definition term_ind: UU :=
    ∏ (P: term sigma → UU),
    ( ∏ (nm: names sigma) (vterm: Vector (term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (mkterm nm vterm) )
    → (∏ t: (term sigma), P t).

End TermInduction.
