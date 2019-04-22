(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.
Local Open Scope transport.

(** Basic definitions **)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names (sigma: Signature): hSet := pr1 sigma.

Definition arity {sigma: Signature} (nm: names sigma): Arity := pr2 sigma nm.

Definition mk_signature {n: nat} (v: Vector nat n): Signature := (stnset n,, el v).

Definition Algebra (sigma: Signature): UU
  := ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

Coercion support {sigma: Signature} (a: Algebra sigma): hSet := pr1 a.

Definition dom {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
  := Vector (support a) (arity nm).

Definition cod {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
  := support a.

Definition op {sigma: Signature} (a: Algebra sigma) (nm: names sigma): (dom a nm) → (cod a nm)
  := pr2 a nm.

Definition mk_algebra {sigma : Signature} (support : hSet)
           (ops: ∏ nm: names sigma, Vector support (arity nm) → support) : Algebra sigma
  := (support,, ops).

(** Algebra homomorphism **)

Section Homomorphisms.

  Context { sigma: Signature }.

  Definition is_hom {a1 a2: Algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition hom (a1 a2: Algebra sigma): UU :=  ∑ (f: a1 → a2), is_hom f.

  Local Notation "a1 ↦ a2" := (hom a1 a2)  (at level 80, right associativity).

  Definition hom2fun {a1 a2: Algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2proof {a1 a2: Algebra sigma} (f: a1 ↦ a2): is_hom f := pr2 f.

  Definition mk_hom {a1 a2: Algebra sigma} (f: a1 → a2) (f_is_hom: is_hom f)
    : a1 ↦ a2 := f ,, f_is_hom.

  Theorem hom_isaset (a1 a2: Algebra sigma): isaset (hom a1 a2).
  Proof.
    unfold hom.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      unfold is_hom.
      apply impred_isaset.
      intros.
      apply impred_isaset.
      intros.
      apply isasetaprop.
      apply (setproperty a2).
  Defined.

  Lemma idfun_is_hom (a: Algebra sigma): is_hom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_id (a: Algebra sigma): a ↦ a := mk_hom (idfun a) (idfun_is_hom a).

  Lemma comp_is_hom  {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): is_hom (funcomp h1 h2).
  Proof.
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

  Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
    := mk_hom (funcomp h1 h2) (comp_is_hom h1 h2).

End Homomorphisms.

(** Terminal algebra **)

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mk_algebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

  Lemma is_hom_terminalhom {a: Algebra sigma}: is_hom(a2 := terminal_algebra) (λ x: a, tt).
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition terminal_hom (a : Algebra sigma): hom a terminal_algebra
    :=  mk_hom(a2 := terminal_algebra) (λ _: a, tt) is_hom_terminalhom.

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

Section Natlemmas.

  Lemma nat_movesubleft {a b c: nat}: c ≤ b → a = b - c  → a + c =b.
  Proof.
    intros hp1 hp2.
    apply (maponpaths  (λ n: nat, n + c)) in hp2.
    rewrite minusplusnmm in hp2 ; assumption.
  Defined.

  Lemma nat_movaddleft {a b c: nat}: a = b + c → a - c = b.
  Proof.
    intros hp.
    apply (maponpaths (λ n: nat, n - c)) in hp.
    rewrite plusminusnmm in hp.
    assumption.
  Defined.

  Lemma natleh_add { n1 n2 m: nat }: n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    apply (istransnatleh(m:=n2)).
    - assumption.
    - apply natlehnplusnm.
  Defined.

  (** Forward chaining variant
  Lemma natleh_add { n1 n2 m: nat }: n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    set (H := natlehnplusnm n2 m).
    exact (istransnatleh X H).
  Defined.
  **)

  Lemma natleh_adddiff {n1 n2 n3: nat}: n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.
  Proof.
    intros.
    apply nat_movesubleft.
    - rewrite natpluscomm.
      rewrite <- natplusminusle.
      + apply natlehnplusnm.
      + assumption.
    - rewrite NaturalNumbers.natminusminus.
      replace (n3 + n2) with (n2 + n3) by (rewrite natpluscomm; reflexivity).
      rewrite <- NaturalNumbers.natminusminus.
      rewrite plusminusnmm.
      reflexivity.
  Defined.

  (*** These axioms probably needs some additional hypotheses ***)

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

End Natlemmas.

(** Status **)

Section Status.

  Context {sigma: Signature}.

  Definition Status: UU := nat ⨿ unit.

  Definition statusok (n: nat): Status := ii1 n.

  Definition statuserror: Status := ii2 tt.

  Lemma Status_isaset: isaset Status.
  Proof.
    apply isasetcoprod.
    - apply isasetnat.
    - apply isasetunit.
  Defined.

  Definition status_cons (nm: names sigma) (status: Status): Status.
  Proof.
    induction status as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (statusok ( S(n - arity nm) ) ).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_cons_statusok_cases (nm: names sigma) (n: nat):
    (arity nm ≤ n × status_cons nm (statusok n) = statusok (S(n - arity nm)))
      ⨿ (¬ (arity nm ≤ n) × status_cons nm (statusok n) = statuserror).
  Proof.
    cbn [status_cons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) n) as [ok | error].
    - left.
      exact (ok ,, idpath _).
    - right.
      exact (error ,, idpath _).
  Defined.

  Lemma status_cons_statusok {nm: names sigma} {n m: nat}:
    status_cons nm (statusok n) = statusok m → arity nm ≤ n × m = S(n - arity nm).
  Proof.
    intro scons.
    induction (status_cons_statusok_cases nm n) as [ [aritynm ok] | [aritynm error] ].
    - rewrite scons in ok.
      apply ii1_injectivity in ok.
      exact (aritynm ,, ok).
    - rewrite scons in error.
      apply negpathsii1ii2 in error.
      contradiction.
  Defined.

  Lemma status_cons_statusok_r {nm: names sigma} {status: Status} {m: nat}:
    status_cons nm status = statusok m → status = statusok (m + arity nm - 1).
  Proof.
    intro hp.
    induction status as [n | noerror].
    - apply status_cons_statusok in hp.
      induction hp as [aritynm valm].
      change (S (n - arity nm)) with (1 + (n - (arity nm))) in valm.
      rewrite natplusminusle in valm.
      assert (aritynm2: arity nm <= 1+n).
      {
        rewrite natpluscomm.
        apply (istransnatleh(m:=n)).
        - assumption.
        - apply natlehnplusnm.
      }
      apply (nat_movesubleft aritynm2) in valm.
      replace (1+n) with (n+1) in valm.
      * apply (nat_movaddleft) in valm.
        rewrite <- valm.
        apply idpath.
      * rewrite natpluscomm.
        reflexivity.
      * assumption.
    - rewrite noerror in hp.
      cbn in hp.
      apply negpathsii2ii1 in hp.
      contradiction.
  Defined.

  Lemma status_cons_noerror_r {nm: names sigma} {status: Status}:
    status_cons nm status != statuserror → ∑ n: nat, status = statusok n × arity nm ≤ n.
  Proof.
    intro noerror.
    induction status.
    - induction (status_cons_statusok_cases nm a) as [ [aritynm ok] | [aritynm error] ].
      + exists a.
        exact (idpath _ ,, aritynm).
      + contradiction.
    - contradiction.
  Defined.

  Lemma status_cons_noerror2_r {nm: names sigma} {status: Status}:
    status_cons nm status != statuserror → status != statuserror.
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
      + exact (statusok (len_s1 + len_s2)).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_concatenate_statuscons {nm: names sigma} {status1 status2: Status}:
    (status_cons nm status1 != statuserror) →
    status_concatenate (status_cons nm status1) status2
    = status_cons nm (status_concatenate status1 status2).
  Proof.
    induction status1 as [a1 | error1].
    2: contradiction.
    induction status2 as [a2 | error2].
    2: reflexivity.
    intro noerror.
    change inl with statusok.
    induction (status_cons_statusok_cases nm a1) as [ [aritynm ok] | [aritynm error] ].
    - rewrite ok.
      cbn [status_concatenate statusok coprod_rect].
      induction (status_cons_statusok_cases nm (a1+a2)) as [ [aritynm2 ok2] | [aritynm2 error2] ].
      + rewrite ok2.
        apply maponpaths.
        apply (maponpaths S).
        apply natleh_adddiff.
        assumption.
      + apply fromempty.
        apply aritynm2.
        apply natleh_add.
        assumption.
    - contradiction.
  Defined.

End Status.

Section Stack.

  Definition list2status {sigma: Signature} (l: list (names sigma)): Status
    := foldr status_cons (statusok 0) l.

  Definition Stack (sigma: Signature) (n: nat)
    : UU := ∑ s: list (names sigma), list2status s = statusok n.

  Lemma Stack_isaset (sigma: Signature) (n: nat): isaset (Stack sigma n).
  Proof.
    apply isaset_total2.
    - apply isofhlevellist.
      exact (pr2 (names sigma)).
    - intros.
      apply isasetaprop.
      apply Status_isaset.
  Defined.

  Definition mk_stack {sigma: Signature} {n: nat} (s: list (names sigma))
             (proofs: list2status s = statusok n)
    : Stack sigma n := s ,, proofs.

  Coercion stack2list {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list (names sigma) := pr1 s.

  Definition stack2proof {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list2status s = statusok n := pr2 s.

  Definition Term (sigma: Signature) : UU := Stack sigma 1.

  Coercion term2list {sigma: Signature}: Term sigma → list (names sigma) := pr1.

  Definition Term_hset (sigma : Signature): hSet := hSetpair (Term sigma) (Stack_isaset sigma 1).

End Stack.

Section StackOps.

  Context {sigma: Signature}.

  Definition stack_nil: Stack sigma 0 := mk_stack nil (idpath (list2status nil)).

  Lemma stack_extens {n: nat} {s1 s2 : Stack sigma n} (p : stack2list s1 = stack2list s2)
    : s1 = s2.
  Proof.
    apply subtypeEquality.
    2: exact p.
    intros s.
    apply Status_isaset.
  Defined.

  Lemma list2status_cons {nm: names sigma} {l: list (names sigma)}:
    list2status (cons nm l) = status_cons nm (list2status l).
  Proof.
    reflexivity.
  Defined.

  Lemma stack_zero (s: Stack sigma 0): s = stack_nil.
  Proof.
    induction s as [[len vec] proof].
    induction len.
    - induction vec.
      apply stack_extens.
      reflexivity.
    - apply fromempty.
      change (S len,, vec) with (cons (hd vec) (len ,, tl vec)) in proof.
      rewrite list2status_cons in proof.
      set (contr := proof).
      apply status_cons_statusok_r in contr.
      rewrite contr in proof.
      apply status_cons_statusok in proof.
      induction proof as [_  zero_is_Sx].
      apply negpaths0sx in zero_is_Sx.
      assumption.
  Defined.

  Lemma stack_positive {n: nat} (s: Stack sigma (S n)):
    ∑ (lentail: nat) (v: Vector (names sigma) (S lentail)) (proofs: _),
    s = mk_stack (cons (hd v) (lentail ,, tl v)) proofs.
  Proof.
    induction s as [[len vec] s_is_stack].
    induction len.
    - induction vec.
      apply fromempty.
      apply ii1_injectivity in s_is_stack.
      apply negpaths0sx in s_is_stack.
      assumption.
    - exists len.
      exists vec.
      exists s_is_stack.
      apply idpath.
  Defined.

  Definition stack_cons (nm: names sigma) {n: nat} (s: Stack sigma n) (p: arity nm ≤ n)
    : Stack sigma (S(n - arity nm)).
  Proof.
    exists (cons nm s).
    rewrite list2status_cons.
    rewrite (stack2proof s).
    induction (status_cons_statusok_cases nm n) as [ [aritynm ok] | [aritynm error] ].
    - assumption.
    - contradiction.
  Defined.

  Definition stack_hd {n: nat} (s: Stack sigma (S n)): names sigma.
  Proof.
    set (s_struct := stack_positive s).
    induction s_struct as [lentail [v _]].
    exact (hd v).
  Defined.

  Definition stack_tl {n: nat} (s: Stack sigma (S n)): Stack sigma (n + arity (stack_hd s)).
  Proof.
    set (s_struct := stack_positive s).
    induction s_struct as [lentail [v [proofs s2]]].
    exists (lentail ,, tl v).
    set (s_status := proofs).
    rewrite list2status_cons in s_status.
     apply status_cons_statusok_r  in s_status.
    rewrite natpluscomm in s_status.
    change (S n) with (1+n) in s_status.
    replace (1+n) with (n+1)  in s_status by (rewrite natpluscomm; reflexivity).
    rewrite <- natplusassoc in s_status.
    rewrite plusminusnmm in s_status.
    rewrite natpluscomm in s_status.
    replace (stack_hd s) with (hd v).
    - exact s_status.
    - rewrite s2.
      reflexivity.
  Defined.

  Lemma stack_cons_normalize1 (nm: names sigma) {n: nat} (s: Stack sigma n) (p: arity nm ≤ n)
    : stack_hd ( stack_cons nm s p ) = nm.
  Proof.
    apply idpath.
  Defined.

  Lemma stack_cons_normalize2 (nm: names sigma) {n: nat} (s: Stack sigma n) (p: arity nm ≤ n)
    : transportf (Stack sigma) (minusplusnmm _ _ p) (stack_tl ( stack_cons nm s p )) = s.
  Proof.
    unfold Stack.
    rewrite transportf_total2.
    apply stack_extens.
    simpl.
    rewrite transportf_const.
    reflexivity.
  Defined.

  Lemma stack_cons_normalize3 {n: nat} (s: Stack sigma (S n))
    : transportf (Stack sigma) (maponpaths S (plusminusnmm _ _)) (stack_cons (stack_hd s) (stack_tl s) (natlehmplusnm _ _) ) = s.
  Proof.
    unfold Stack.
    rewrite transportf_total2.
    apply stack_extens.
    cbn [stack2list pr1].
    rewrite transportf_const.
    cbv [idfun].
    set (struct :=  stack_positive s).
    induction struct as [lentail [v [proofs s2]]].
    rewrite s2.
    reflexivity.
  Defined.

  Lemma stack_cases_arith1 {n m: nat}: n > 0 → m ≤ n + m - 1.
  Proof.
    intro n0.
    rewrite natpluscomm.
    rewrite <- natplusminusle.
    - apply natlehnplusnm.
    - assumption.
  Defined.

  Lemma stack_cases_arith2 {n m: nat}: n > 0 → S(n + m - 1 - m) = n.
  Proof.
    intro n0.
    rewrite natminusminusassoc.
    replace (1 + m) with (m + 1) by (rewrite natpluscomm; reflexivity).
    rewrite <- natminusminusassoc.
    rewrite plusminusnmm.
    change (S(n-1)) with (1 + (n-1)).
    rewrite natplusminusle.
    rewrite natpluscomm.
    - rewrite plusminusnmm.
      apply idpath.
    - assumption.
  Defined.

  Lemma stack_cases {n: nat} (s: Stack sigma n)
    : (∑ (proofn: n = 0), s = (! proofn) # stack_nil)
        ⨿ (∑ (proofn: n > 0) (nm: names sigma) (s': Stack sigma (n + (arity nm) - 1)),
           s = (stack_cases_arith2 proofn) # (stack_cons nm s' (stack_cases_arith1 proofn))).
  Proof.
    induction n.
    - left.
      exists (idpath _).
      set (snil := stack_zero s).
      rewrite snil.
      reflexivity.
    - right.
      set (struct := stack_positive s).
      induction struct as [lentail [v [proofs sconstr]]].
      exists (natgthsn0 n).
      exists (hd v).
      set (proofs' := proofs).
      rewrite list2status_cons in proofs'.
      apply status_cons_statusok_r in proofs'.
      exists ((lentail ,, tl v) ,, proofs').
      unfold Stack.
      rewrite transportf_total2.
      apply stack_extens.
      simpl.
      rewrite transportf_const.
      unfold mk_stack in sconstr.
      exact (maponpaths pr1 sconstr).
  Defined.

  Theorem stack_ind:
    ∏ (P: ∏ {n: nat}, Stack sigma n → UU),
    ( P stack_nil ) →
    ( ∏ (nm: names sigma) {m: nat} (s: Stack sigma m) (p: arity nm ≤ m),
      P s → P (stack_cons nm s p) ) →
    ∏ (n: nat) (s: Stack sigma n), P s.
  Proof.
    intros P Pnil Pind.
    assert (stack_ind: ∏ (len: nat) (n : nat) (s : Stack sigma n), length s = len → P n s).
    - intro len.
      induction len.
      + intros n s slen.
        induction n.
        * set (snil := stack_zero s).
          rewrite snil.
          assumption.
        * induction s as [[len vec] proofs].
          cbn in slen.
          apply fromempty.
          induction len.
          ++ induction vec.
             apply ii1_injectivity in proofs.
             apply pathsinv0 in proofs.
             apply negpathssx0 in proofs.
             assumption.
          ++ apply negpathssx0 in slen.
             assumption.
      + intros n s slen.
        induction (stack_cases s) as [snil | snotnil].
        * induction snil as [proofn sdef].
          set (Pnil' := (transportf2 (λ n: nat, P n) (! proofn) stack_nil) Pnil).
          rewrite sdef.
          assumption.
        * induction snotnil as [proofn [nm [s' sdef]]].
          set (s'len := slen).
          rewrite sdef in s'len.
          unfold Stack in s'len.
          rewrite transportf_total2 in s'len.
          simpl in s'len.
          rewrite transportf_const in s'len.
          cbn in s'len.
          apply invmaponpathsS in s'len.
          set (Ps' := IHlen (n + arity nm - 1) s' s'len).
          set (Ps := Pind nm (n + arity nm - 1) s' (stack_cases_arith1 proofn) Ps').
          set (Ps2 := (transportf2 (λ n: nat, P n) (stack_cases_arith2 proofn) (stack_cons nm s' (stack_cases_arith1 proofn))) Ps).
          cbn in Ps2.
          rewrite sdef.
          assumption.
    - intros.
      exact (stack_ind (length s) n s (idpath _)).
  Defined.

  Local Lemma stack_concatenate_arith {n1 n2 m: nat}: m ≤ n1 →  S(n1 - m) + n2 = S(n1 + n2 - m).
  Proof.
    intro hp.
    change (S (n1 - m) + n2) with (S (n1 - m + n2)).
    apply maponpaths.
    rewrite  natleh_adddiff.
    - apply idpath.
    - assumption.
  Defined.

  Definition stack_concatenate2 {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : Stack sigma (n1 + n2).
  Proof.
    apply (stack_ind (λ (n1: nat) (s1: Stack sigma n1), Stack sigma (n1+n2))).
    - assumption.
    - intros nm ntail stail aritynm HP.
      set (res := stack_cons nm HP (natleh_add aritynm)).
      exact ( (! (stack_concatenate_arith aritynm)) # res).
    - exact s1.
  Defined.

  Lemma list2status_compositional {l1 l2: list (names sigma)}:
    list2status l1 != statuserror →
    status_concatenate (list2status l1) (list2status l2) = list2status (concatenate l1 l2).
  Proof.
    apply (list_ind (λ s, list2status s != statuserror →
                          status_concatenate (list2status s) (list2status l2)
                          = list2status (concatenate s l2))).
    - intros.
      change (list2status (concatenate nil l2)) with (list2status l2).
      induction (list2status l2) as [okl2 | badl2].
      + reflexivity.
      + induction badl2.
        reflexivity.
    - intros nm l1tail IH noerror.
      rewrite list2status_cons.
      rewrite status_concatenate_statuscons by (assumption).
      rewrite IH.
      + rewrite <- list2status_cons.
        reflexivity.
      + apply (status_cons_noerror2_r(nm:=nm)).
        assumption.
  Defined.

  Definition stack_concatenate {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : Stack sigma (n1 + n2).
  Proof.
    exists (concatenate s1 s2).
    rewrite <- list2status_compositional.
    - rewrite (stack2proof s1).
      rewrite (stack2proof s2).
      reflexivity.
    - rewrite (stack2proof s1).
      apply negpathsii1ii2.
  Defined.

  Lemma stack_concatenate_cons {n1 n2: nat} (nm: names sigma)
        (s1: Stack sigma n1) (s2: Stack sigma n2) (p: arity nm ≤ n1)
    : transportf (Stack sigma) (stack_concatenate_arith  p)
                 (stack_concatenate (stack_cons nm s1 p) s2 )
      = stack_cons nm (stack_concatenate s1 s2) (natleh_add p).
  Proof.
    unfold Stack.
    rewrite transportf_total2.
    apply stack_extens.
    cbn [stack2list pr1].
    rewrite transportf_const.
    cbv [idfun].
    (* reflexivity.*)
  Abort.

  Definition terms2stack {n: nat} (vec: Vector (Term sigma) n): Stack sigma n.
  Proof.
    induction n.
    - exact stack_nil.
    - exact (stack_concatenate (hd vec) (IHn (tl vec))).
  Defined.

  Definition term_op (nm: names sigma) (vec: Vector (Term sigma) (arity nm)): Term sigma.
  Proof.
    set (res := stack_cons nm (terms2stack vec) (isreflnatleh (arity nm))).
    rewrite minuseq0' in res.
    assumption.
  Defined.

End StackOps.

Definition term_algebra (sigma: Signature): Algebra sigma
  := mk_algebra (Term_hset sigma) term_op.

Section TermInduction.

  Context {sigma: Signature}.

  Definition princ_op (t: Term sigma): names sigma := stack_hd t.

  Definition extract_sublist (s: list (names sigma)):
    ∏ n m: nat, list2status s = statusok m → n ≤ m  →
                ∑ first second: list (names sigma),
                        list2status first = statusok n ×
                        list2status second = statusok (m - n) ×
                        concatenate first second = s.
  Proof.
    apply (list_ind (λ s : list (names sigma), ∏ n m: nat, list2status s = statusok m → n ≤ m →
                     ∑ first second: list (names sigma), list2status first = statusok n ×
                                                  list2status second = statusok (m - n) ×
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
        split.
        2: split.
        * apply idpath.
        * (**** THIS PROOF DOES NOT COMPUTE WELL ****)
          rewrite natminuseqn.
          assumption.
        * apply idpath.
      + apply nat_notgeh1_inv in n_gt_0.
        rewrite list2status_cons in s_status.
        assert ( tail_ok: ∑ tail_ar: nat, list2status tail = statusok tail_ar ×
                                                                      arity nm ≤ tail_ar ).
        {
          apply status_cons_noerror_r.
          rewrite s_status.
          apply negpathsii1ii2.
        }
        induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound]].
        rewrite tail_status_prf in s_status.
        apply status_cons_statusok in s_status.
        induction s_status as [aritynm valm].
        apply nat_ax in valm.
        assert (tail_ar_newbound: n + arity nm - 1 ≤ tail_ar).
        {
          abstract
            (rewrite valm;
             apply natlehandminusl;
             apply natlehandplus;
             [ assumption |
               apply isreflnatleh ]).
        }
        set (IH1 := IH (n + arity nm - 1) tail_ar tail_status_prf tail_ar_newbound).
        induction IH1 as [fst [snd [status_fst_prf [status_snd_prf conc]]]].
        rewrite valm in status_snd_prf.
        rewrite nat_ax3 in status_snd_prf.
        set (realfirst := cons nm fst).
        assert (list2status realfirst = statusok n).
        {
          unfold realfirst.
          rewrite list2status_cons.
          rewrite status_fst_prf.
          induction (status_cons_statusok_cases nm (n + arity nm - 1))
            as [ [aritynm2 ok] | [aritynm2 error] ].
          - rewrite ok.
            rewrite natminusminusassoc.
            rewrite (natpluscomm 1 (arity nm)).
            rewrite <- natminusminusassoc.
            rewrite plusminusnmm.
            change (S (n - 1)) with (1 + (n - 1)).
            rewrite natplusminusle.
            * apply maponpaths.
              abstract
                (rewrite natpluscomm, plusminusnmm;
                 apply idpath).
            * assumption.
          - induction aritynm2.
            abstract
              (rewrite natpluscomm;
               rewrite <- natplusminusle;
               [ apply natlehnplusnm | assumption ]).
        }
        exists realfirst.
        exists snd.
        do 2 ( split ; try assumption ).
        unfold realfirst.
        rewrite concatenateStep.
        rewrite conc.
        apply idpath.
  Defined.

  Local Lemma extract_substack_arith {m n: nat}: n ≤ m → n + (m - n) = m.
  Proof.
    intro.
    rewrite natplusminusle.
    - rewrite natpluscomm.
      rewrite plusminusnmm.
      apply idpath.
    - assumption.
  Defined.

  Definition extract_substack {m: nat} (s: Stack sigma m) (n: nat) (okn: n ≤ m):
    ∑ (first: Stack sigma n) (second: Stack sigma (m - n)),
    (transportf (λ x: nat, Stack sigma x) (extract_substack_arith okn)
                (stack_concatenate first second)) = s.
  Proof.
    set (res := extract_sublist s n m (stack2proof s) okn).
    induction res as [fsupp [ssupp [fproof [sproof concproof]]]].
    exists (mk_stack fsupp fproof).
    exists (mk_stack ssupp sproof).
    apply stack_extens.
    unfold Stack.
    rewrite transportf_total2.
    simpl.
    rewrite transportf_const.
    assumption.
  Defined.

  Lemma nil_not_term: @list2status sigma nil != statusok 1.
  Proof.
    cbn.
    intro H.
    apply ii1_injectivity in H.
    apply negpaths0sx in H.
    contradiction.
  Defined.

  Definition subterm (t: Term sigma): ⟦ arity (princ_op t) ⟧ → Term sigma.
  Proof.
    assert (subterm2: ∏ (s: list (names sigma)) (s_is_term: list2status s = statusok 1),
            ⟦ arity (princ_op (mk_stack s s_is_term)) ⟧ → Term sigma).
    2: exact (subterm2 t (stack2proof t)).
    apply (list_ind (λ (s: list (names sigma)),
                     ∏ s_is_term : list2status s = statusok 1,
                                   ⟦ arity (princ_op (mk_stack s s_is_term)) ⟧ → Term sigma)).
    - intro.
      set (contr := nil_not_term s_is_term).
      contradiction.
    - intros x tail IH s_is_term.
      cbn.
      intro arx.
      induction arx as [n n_lt_arx].
      rewrite list2status_cons in s_is_term.
      assert (s_ok: status_cons x (list2status tail) != statuserror).
      {
        rewrite s_is_term.
        apply negpathsii1ii2.
      }
      set (tail_ok := status_cons_noerror_r s_ok).
      induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound ]].
      rewrite tail_status_prf in s_is_term.
      assert ( tail_ar_x: tail_ar = arity x).
      {
        set (X := pr2( status_cons_statusok s_is_term)).
        change (1) with (1+0) in X.
        change (S (tail_ar - arity x)) with (1 + (tail_ar - arity x)) in X.
        set (Y := natpluslcan _ _ _ X).
        set (Z := natdiff0 _ _ Y).
        apply natdiffasymm; assumption.
      }
      rewrite tail_ar_x in tail_status_prf.
      set (n_le_arx := natlthtoleh _ _ n_lt_arx).
      set (remove := extract_sublist tail n (arity x) tail_status_prf n_le_arx).
      induction remove as [first [ second  [ firstss [ secondss conc] ] ] ].
      assert ( extractok2: 1 ≤ arity x - n ).
      {
        apply (natlehandplusrinv _ _ n).
        rewrite minusplusnmm by (assumption).
        rewrite natpluscomm.
        apply natlthtolehp1.
        exact n_lt_arx.
      }
      set (res := extract_sublist second 1 (arity x - n) secondss extractok2).
      induction res as [result [second0 [result_is_term [second_ss conc1]]]].
      exact (mk_stack result result_is_term).
  Defined.

  Definition extract_term {n: nat} (s: Stack sigma (S n)):
    ∑ (term: Term sigma) (rest: Stack sigma n), stack_concatenate term rest = s.
  Proof.
    set (rest := extract_sublist s 1 (S n) (stack2proof s) (natleh0n n)).
    induction rest as [fsupp [ssupp [fproof [sproof conc]]]].
    exists (mk_stack fsupp fproof).
    change (S n) with (1 + n) in sproof.
    rewrite natpluscomm in sproof.
    rewrite plusminusnmm in sproof.
    exists (mk_stack ssupp sproof).
    apply stack_extens.
    assumption.
  Defined.

  Definition stack_first {n: nat} (s: Stack sigma (S n)): Term sigma
    := pr1 (extract_term s).

  Definition stack_rest {n: nat} (s: Stack sigma (S n)): Stack sigma n
    := pr12 (extract_term s).

  Lemma stack_concatenate_normalize1 {n: nat} (s: Stack sigma (S n))
    : stack_concatenate (stack_first s) (stack_rest s) = s.
  Proof.
    exact (pr22 (extract_term s)).
  Defined.

  (*
  Lemma stack_concatenate_normalize2 (t: Term sigma) {n: nat} (s: Stack sigma n)
    : stack_first (stack_concatenate t s) = t.
  Proof.
    Check stack_ind.
    apply stack_concatenate_normalize2
    induction t as [l proofl].
    generalize proofl.
    clear proofl.
    apply (list_ind (λ l: list (names sigma), ∏ proofl: list2status l = statusok 1,
                          stack_first (stack_concatenate (l,, proofl) s) = l,, proofl)).
    - intro proofl.
      apply fromempty.
      apply nil_not_term in proofl.
      assumption.
    - intros x xs HP proofxs.
      apply stack_extens.
      cbv [stack2list pr1].
   *)

  Definition stack2terms {n: nat} (s: Stack sigma n): Vector (Term sigma) n.
  Proof.
    induction n.
    - exact vnil.
    - exact (vcons (stack_first s) (IHn (stack_rest s))).
  Defined.

  Lemma stack2terms_concat {t: Term sigma} {n: nat} (s: Stack sigma n):
    stack2terms (stack_concatenate t  s) = vcons t (stack2terms s).
  Proof.
    unfold stack2terms at 1.
  Abort.

  Lemma stack2terms2stack {n: nat} (s: Stack sigma n): terms2stack (stack2terms s) = s.
  Proof.
    induction n.
    - cbn.
      rewrite stack_zero.
      apply idpath.
    - replace s with (stack_concatenate (stack_first s) (stack_rest s)).
      2: { rewrite stack_concatenate_normalize1. reflexivity. }
  Abort.

  Theorem term_ind:
    ∏ (P: Term sigma → UU),
    ( ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (term_op nm vterm) )
    → (∏ t: Term sigma, P t).
  Proof.
    intros P HPind.
    assert (∏ (l: list (names sigma)) (lp: list2status l = statusok 1), P (mk_stack l lp)).
    intros.
    induction l as [lenl vecl].
    induction lenl.
    - induction vecl.
      apply fromempty.
      apply nil_not_term in lp.
      assumption.
    - pose (l := lp).
      change  (S lenl,, vecl) with (cons (hd vecl) (lenl ,, tl vecl)) in l.
      rewrite list2status_cons in l.
      apply status_cons_statusok_r in l.
      rewrite natpluscomm in l.
      rewrite plusminusnmm in l.
  Abort.

End TermInduction.
