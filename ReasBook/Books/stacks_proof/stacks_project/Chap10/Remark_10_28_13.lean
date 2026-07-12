import StacksProject_2024.Chap10.Remark_10_28_13.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MvPolynomial

universe u v

section

variable (k : Type u) [Field k] (T : Type v)

/-- Helper for Remark 10.28.13: keep only the `t`-chain and collapse it to the unique `PUnit`
chain in the target quotient ring. -/
private noncomputable def remark102813SingleChainQuotAux [DecidableEq T] (t : T) :
    MvPolynomial (Remark102813Var T) k →+* remark102813Ring k PUnit :=
  (Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)).comp <|
    MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Remark102813Var PUnit) k)
      (fun i =>
        match i with
        | Remark102813Var.x n => remark102813X k PUnit n
        | Remark102813Var.z u n =>
            if u = t then remark102813Z k PUnit PUnit.unit n else 0)

/-- Helper for Remark 10.28.13: the single-chain specialization sends each `x_n` to the
corresponding `PUnit` generator. -/
private lemma remark102813SingleChainQuotAux_apply_x [DecidableEq T] (t : T) (n : ℕ) :
    remark102813SingleChainQuotAux (k := k) (T := T) t (remark102813X k T n) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit) (remark102813X k PUnit n) := by
  -- Proof comment: unfold the specialization and evaluate it on the `x_n` polynomial generator.
  change
    (Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit))
        ((MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Remark102813Var PUnit) k)
          (fun i =>
            match i with
            | Remark102813Var.x n => remark102813X k PUnit n
            | Remark102813Var.z u n =>
                if u = t then remark102813Z k PUnit PUnit.unit n else 0))
          (remark102813X k T n)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit) (remark102813X k PUnit n)
  rw [remark102813X, MvPolynomial.eval₂Hom_X']

/-- Helper for Remark 10.28.13: the single-chain specialization keeps the chosen `t`-chain and
kills every other `z`-chain. -/
private lemma remark102813SingleChainQuotAux_apply_z [DecidableEq T] (t u : T) (n : ℕ) :
    remark102813SingleChainQuotAux (k := k) (T := T) t (remark102813Z k T u n) =
      if u = t then
        Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)
          (remark102813Z k PUnit PUnit.unit n)
      else 0 := by
  -- Proof comment: unfold the specialization and evaluate it on the `z_{u,n}` polynomial
  -- generator, leaving exactly the defining `if u = t` split.
  change
    (Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit))
        ((MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Remark102813Var PUnit) k)
          (fun i =>
            match i with
            | Remark102813Var.x n => remark102813X k PUnit n
            | Remark102813Var.z v n =>
                if v = t then remark102813Z k PUnit PUnit.unit n else 0))
          (remark102813Z k T u n)) =
      if u = t then
        Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)
          (remark102813Z k PUnit PUnit.unit n)
      else 0
  rw [remark102813Z, MvPolynomial.eval₂Hom_X']
  by_cases h : u = t
  · simp [h]
  · simp [h]

/-- Helper for Remark 10.28.13: the single-chain specialization annihilates the defining
relations, so it descends to the quotient ring. -/
private lemma remark102813_relationsIdeal_le_singleChainQuotAux_ker [DecidableEq T] (t : T) :
    remark102813RelationsIdeal k T ≤
      RingHom.ker (remark102813SingleChainQuotAux (k := k) (T := T) t) := by
  -- Route correction: only the specialization map descends through the quotient; the detector
  -- stays upstairs on the one-chain polynomial ring.
  -- Proof comment: check the three families of defining generators one by one inside
  -- `Ideal.span_le`, using the stable specialization formulas on `x` and `z`.
  refine Ideal.span_le.2 ?_
  intro f hf
  change remark102813SingleChainQuotAux (k := k) (T := T) t f = 0
  rcases hf with hf | hf
  · rcases hf with hf | hf
    · rcases hf with ⟨n, rfl⟩
      rw [map_pow, remark102813SingleChainQuotAux_apply_x]
      exact remark102813_x_square_eq_zero (k := k) (T := PUnit) n
    · rcases hf with ⟨p, rfl⟩
      rcases p with ⟨u, n⟩
      by_cases hu : u = t
      · rw [map_pow, remark102813SingleChainQuotAux_apply_z, if_pos hu]
        exact remark102813_z_square_eq_zero (k := k) (T := PUnit) PUnit.unit n
      · rw [map_pow, remark102813SingleChainQuotAux_apply_z, if_neg hu]
        rw [pow_two]
        exact zero_mul (0 : remark102813Ring k PUnit)
  · rcases hf with ⟨p, rfl⟩
    rcases p with ⟨u, n⟩
    rw [map_sub, map_mul, remark102813SingleChainQuotAux_apply_x,
      remark102813SingleChainQuotAux_apply_z, remark102813SingleChainQuotAux_apply_z]
    by_cases hu : u = t
    · rw [if_pos hu, if_pos hu]
      rw [remark102813_z_recurrence (k := k) (T := PUnit) PUnit.unit n]
      exact sub_self _
    · rw [if_neg hu, if_neg hu]
      calc
        (Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit) (remark102813X k PUnit (n + 1))) *
            0 - 0 =
          0 - 0 := by rw [mul_zero]
        _ = 0 := sub_self 0

/-- Helper for Remark 10.28.13: the specialization to a single distinguished chain descends to the
quotient ring. -/
private noncomputable def remark102813SingleChainMap [DecidableEq T] (t : T) :
    remark102813Ring k T →+* remark102813Ring k PUnit :=
  Ideal.Quotient.lift (remark102813RelationsIdeal k T)
    (remark102813SingleChainQuotAux (k := k) (T := T) t)
    (remark102813_relationsIdeal_le_singleChainQuotAux_ker (k := k) (T := T) t)

/-- Helper for Remark 10.28.13: the single-chain specialization fixes the `x_n` generators. -/
private lemma remark102813_singleChainMap_mk_x [DecidableEq T] (t : T) (n : ℕ) :
    remark102813SingleChainMap (k := k) (T := T) t
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813X k T n)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit) (remark102813X k PUnit n) := by
  -- Proof comment: evaluate the descended quotient map on the class of `x_n`.
  change
    Ideal.Quotient.lift (remark102813RelationsIdeal k T)
        (remark102813SingleChainQuotAux (k := k) (T := T) t)
        (remark102813_relationsIdeal_le_singleChainQuotAux_ker (k := k) (T := T) t)
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813X k T n)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit) (remark102813X k PUnit n)
  rw [Ideal.Quotient.lift_mk]
  exact remark102813SingleChainQuotAux_apply_x (k := k) (T := T) t n

/-- Helper for Remark 10.28.13: the chosen `t`-chain maps to the unique `PUnit`-chain. -/
private lemma remark102813_singleChainMap_mk_z_eq [DecidableEq T] (t : T) (n : ℕ) :
    remark102813SingleChainMap (k := k) (T := T) t
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t n)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)
        (remark102813Z k PUnit PUnit.unit n) := by
  -- Proof comment: on the chosen chain the specialization sends `z_{t,n}` to `z_{*,n}`.
  change
    Ideal.Quotient.lift (remark102813RelationsIdeal k T)
        (remark102813SingleChainQuotAux (k := k) (T := T) t)
        (remark102813_relationsIdeal_le_singleChainQuotAux_ker (k := k) (T := T) t)
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t n)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)
        (remark102813Z k PUnit PUnit.unit n)
  rw [Ideal.Quotient.lift_mk, remark102813SingleChainQuotAux_apply_z, if_pos rfl]

/-- Helper for Remark 10.28.13: every other chain is killed by the single-chain specialization. -/
private lemma remark102813_singleChainMap_mk_z_ne [DecidableEq T] {t u : T} (h : u ≠ t) (n : ℕ) :
    remark102813SingleChainMap (k := k) (T := T) t
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T u n)) = 0 := by
  -- Proof comment: off the chosen chain the specialization kills the generator immediately.
  change
    Ideal.Quotient.lift (remark102813RelationsIdeal k T)
        (remark102813SingleChainQuotAux (k := k) (T := T) t)
        (remark102813_relationsIdeal_le_singleChainQuotAux_ker (k := k) (T := T) t)
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T u n)) = 0
  rw [Ideal.Quotient.lift_mk, remark102813SingleChainQuotAux_apply_z, if_neg h]
  rfl

/-- Helper for Remark 10.28.13: the one-chain detector tracks the monomials
`z_0, x_1 z_1, x_1 x_2 z_2, ...`. -/
private def remark102813ChainBaseExponent : ℕ → Remark102813Var PUnit →₀ ℕ
  | 0 => 0
  | n + 1 => remark102813ChainBaseExponent n + Finsupp.single (Remark102813Var.x (n + 1)) 1

/-- Helper for Remark 10.28.13: the detector monomial at level `n` is `x_1 ... x_n z_n`. -/
private def remark102813OneChainExponent (n : ℕ) : Remark102813Var PUnit →₀ ℕ :=
  remark102813ChainBaseExponent n + Finsupp.single (Remark102813Var.z PUnit.unit n) 1

/-- Helper for Remark 10.28.13: the recursive base exponent never uses any `z`-variable. -/
private lemma remark102813_chainBaseExponent_apply_z (n m : ℕ) :
    remark102813ChainBaseExponent n (Remark102813Var.z PUnit.unit m) = 0 := by
  induction n with
  | zero =>
      simp [remark102813ChainBaseExponent]
  | succ n ih =>
      simp [remark102813ChainBaseExponent, ih]

/-- Helper for Remark 10.28.13: the chosen detector exponents are pairwise distinct because the
`z_n` coordinate remembers `n`. -/
private lemma remark102813_oneChainExponent_injective :
    Function.Injective remark102813OneChainExponent := by
  -- Evaluate the exponent equality at the `z_n` coordinate, which is present only at level `n`.
  intro n m hnm
  by_contra hne
  have hz := congrArg (fun e => e (Remark102813Var.z PUnit.unit n)) hnm
  simp [remark102813OneChainExponent, remark102813_chainBaseExponent_apply_z, hne] at hz

/-- Helper for Remark 10.28.13: the recursive base exponent never uses any future variable
`x_i` with `n < i`. -/
private lemma remark102813_chainBaseExponent_apply_x_of_lt {n i : ℕ} (hni : n < i) :
    remark102813ChainBaseExponent n (Remark102813Var.x i) = 0 := by
  induction n with
  | zero =>
      simp [remark102813ChainBaseExponent]
  | succ n ih =>
      have hne : i ≠ n + 1 := by omega
      have hnlt : n < i := lt_trans (Nat.lt_succ_self n) hni
      simpa [remark102813ChainBaseExponent, hne] using ih hnlt

/-- Helper for Remark 10.28.13: the base exponent never uses an `x_i` with multiplicity more than
one. -/
private lemma remark102813_chainBaseExponent_apply_x_le_one (n i : ℕ) :
    remark102813ChainBaseExponent n (Remark102813Var.x i) ≤ 1 := by
  induction n with
  | zero =>
      simp [remark102813ChainBaseExponent]
  | succ n ih =>
      by_cases hi : i = n + 1
      · subst hi
        simp [remark102813ChainBaseExponent, remark102813_chainBaseExponent_apply_x_of_lt]
      · simpa [remark102813ChainBaseExponent, hi] using ih

/-- Helper for Remark 10.28.13: the detector exponents also use each `x_i` with multiplicity at
most one. -/
private lemma remark102813_oneChainExponent_apply_x_le_one (n i : ℕ) :
    remark102813OneChainExponent n (Remark102813Var.x i) ≤ 1 := by
  -- The extra `z_n` coordinate does not affect any `x_i`.
  simpa [remark102813OneChainExponent] using
    remark102813_chainBaseExponent_apply_x_le_one n i

/-- Helper for Remark 10.28.13: the detector monomial at level `m` contains `z_n` exactly when
`m = n`, and then with exponent one. -/
private lemma remark102813_oneChainExponent_apply_z (m n : ℕ) :
    remark102813OneChainExponent m (Remark102813Var.z PUnit.unit n) = if n = m then 1 else 0 := by
  -- Proof comment: the base exponent contributes no `z` terms, so only the final `z_m` factor
  -- matters.
  by_cases h : n = m
  · subst h
    simp [remark102813OneChainExponent, remark102813_chainBaseExponent_apply_z]
  · simp [remark102813OneChainExponent, remark102813_chainBaseExponent_apply_z, h]

/-- Helper for Remark 10.28.13: the detector sees coefficient data only along the selected chain
monomials. -/
private noncomputable def remark102813OneChainCoeffs :
    MvPolynomial (Remark102813Var PUnit) k →ₗ[k] ℕ →₀ k :=
  Finsupp.lcomapDomain (R := k) (M := k)
    remark102813OneChainExponent remark102813_oneChainExponent_injective

/-- Helper for Remark 10.28.13: summing the detected chain coefficients gives the PUnit detector. -/
private noncomputable def remark102813OneChainCoeff :
    MvPolynomial (Remark102813Var PUnit) k →ₗ[k] k :=
  (Finsupp.lsum k fun _ : ℕ ↦ (LinearMap.id : k →ₗ[k] k)).comp
    (remark102813OneChainCoeffs (k := k))

/-- Helper for Remark 10.28.13: the detector coefficient at level `n` is the coefficient of the
monomial `x_1 ... x_n z_n`. -/
private lemma remark102813_oneChainCoeffs_apply
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeffs (k := k) f n =
      MvPolynomial.coeff (remark102813OneChainExponent n) f := by
  -- Unfold `lcomapDomain`: its value at `n` is exactly the coefficient indexed by the detector
  -- exponent at level `n`.
  rfl

/-- Helper for Remark 10.28.13: multiplying by `z_n` shifts the detector to the base monomial
`x_1 ... x_n`. -/
private lemma remark102813_oneChainCoeffs_mul_z
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeffs (k := k) (f * remark102813Z k PUnit PUnit.unit n) =
      Finsupp.single n (MvPolynomial.coeff (remark102813ChainBaseExponent n) f) := by
  classical
  -- Proof comment: compare detector coordinates one index at a time.
  ext m
  by_cases hm : m = n
  · subst hm
    -- Proof comment: the `n`-th detector coordinate drops the unique `z_n` factor.
    rw [remark102813_oneChainCoeffs_apply, remark102813Z, MvPolynomial.coeff_mul_X']
    simp [remark102813OneChainExponent, remark102813_chainBaseExponent_apply_z]
  · -- Proof comment: all other detector monomials have no `z_n` support, so their coefficients
    -- vanish after multiplying by `z_n`.
    rw [remark102813_oneChainCoeffs_apply, remark102813Z, MvPolynomial.coeff_mul_X']
    simp [remark102813OneChainExponent, remark102813_chainBaseExponent_apply_z, hm]

/-- Helper for Remark 10.28.13: multiplying by `x_(n+1) z_(n+1)` shifts the detector to the same
base monomial `x_1 ... x_n`. -/
private lemma remark102813_oneChainCoeffs_mul_xz
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeffs (k := k)
        (f * (remark102813X k PUnit (n + 1) * remark102813Z k PUnit PUnit.unit (n + 1))) =
      Finsupp.single (n + 1) (MvPolynomial.coeff (remark102813ChainBaseExponent n) f) := by
  -- Proof comment: first strip the `z_(n+1)` factor, then strip the matching `x_(n+1)` factor.
  have hz :
      remark102813OneChainCoeffs (k := k)
          (f * (remark102813X k PUnit (n + 1) * remark102813Z k PUnit PUnit.unit (n + 1))) =
        Finsupp.single (n + 1)
          (MvPolynomial.coeff (remark102813ChainBaseExponent (n + 1))
            (f * remark102813X k PUnit (n + 1))) := by
    simpa [mul_assoc] using
      (remark102813_oneChainCoeffs_mul_z (k := k)
        (f := f * remark102813X k PUnit (n + 1))
        (n := n + 1))
  rw [hz]
  congr 1
  simpa [remark102813ChainBaseExponent, remark102813X] using
    (MvPolynomial.coeff_mul_X
      (m := remark102813ChainBaseExponent n)
      (s := Remark102813Var.x (n + 1))
      (p := f))

/-- Helper for Remark 10.28.13: the detector kills the square relation `x_n^2` after arbitrary
left multiplication. -/
private lemma remark102813_oneChainCoeff_mul_x_square
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeff (k := k) (f * remark102813X k PUnit n ^ 2) = 0 := by
  -- Proof comment: every tracked monomial uses `x_n` at most once, so a second `x_n` forces the
  -- coefficient to vanish.
  -- Proof comment: first show every detector coordinate vanishes after the second `x_n`, then
  -- sum those zero coordinates.
  have hcoeffs :
      remark102813OneChainCoeffs (k := k) (f * remark102813X k PUnit n ^ 2) = 0 := by
    classical
    ext m
    rw [remark102813_oneChainCoeffs_apply, pow_two, remark102813X, ← mul_assoc,
      MvPolynomial.coeff_mul_X']
    by_cases hx : Remark102813Var.x n ∈ (remark102813OneChainExponent m).support
    · rw [if_pos hx, MvPolynomial.coeff_mul_X']
      have hxn_pos :
          0 < remark102813OneChainExponent m (Remark102813Var.x n) := by
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
      have hxn_eq_one :
          remark102813OneChainExponent m (Remark102813Var.x n) = 1 := by
        exact le_antisymm
          (remark102813_oneChainExponent_apply_x_le_one m n)
          (Nat.succ_le_of_lt hxn_pos)
      have hxn_sub_eq_zero :
          remark102813OneChainExponent m (Remark102813Var.x n) - 1 = 0 := by
        omega
      have hx' :
          Remark102813Var.x n ∉
            (remark102813OneChainExponent m - Finsupp.single (Remark102813Var.x n) 1).support := by
        rw [Finsupp.notMem_support_iff, Finsupp.tsub_apply]
        simpa using hxn_sub_eq_zero
      rw [if_neg hx']
      rfl
    · simp [hx]
  rw [remark102813OneChainCoeff, LinearMap.comp_apply, hcoeffs]
  simp

/-- Helper for Remark 10.28.13: the detector kills the square relation `z_n^2` after arbitrary
left multiplication. -/
private lemma remark102813_oneChainCoeff_mul_z_square
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeff (k := k) (f * remark102813Z k PUnit PUnit.unit n ^ 2) = 0 := by
  -- Proof comment: the tracked monomial at level `m` contains exactly one `z_m`, so multiplying by
  -- `z_n²` always overshoots the detector support.
  -- Proof comment: as in the `x_n²` case, prove all detector coordinates vanish before summing.
  have hcoeffs :
      remark102813OneChainCoeffs (k := k) (f * remark102813Z k PUnit PUnit.unit n ^ 2) = 0 := by
    classical
    ext m
    rw [remark102813_oneChainCoeffs_apply, pow_two, remark102813Z, ← mul_assoc,
      MvPolynomial.coeff_mul_X']
    by_cases hz : Remark102813Var.z PUnit.unit n ∈ (remark102813OneChainExponent m).support
    · rw [if_pos hz, MvPolynomial.coeff_mul_X']
      have hzn_pos :
          0 < remark102813OneChainExponent m (Remark102813Var.z PUnit.unit n) := by
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
      have hzn_eq_one :
          remark102813OneChainExponent m (Remark102813Var.z PUnit.unit n) = 1 := by
        rw [remark102813_oneChainExponent_apply_z] at hzn_pos ⊢
        split_ifs at hzn_pos ⊢ with hnm
        · rfl
        · omega
      have hzn_sub_eq_zero :
          remark102813OneChainExponent m (Remark102813Var.z PUnit.unit n) - 1 = 0 := by
        omega
      have hz' :
          Remark102813Var.z PUnit.unit n ∉
            (remark102813OneChainExponent m -
              Finsupp.single (Remark102813Var.z PUnit.unit n) 1).support := by
        rw [Finsupp.notMem_support_iff, Finsupp.tsub_apply]
        simpa using hzn_sub_eq_zero
      rw [if_neg hz']
      rfl
    · simp [hz]
  rw [remark102813OneChainCoeff, LinearMap.comp_apply, hcoeffs]
  simp

/-- Helper for Remark 10.28.13: the detector kills the recurrence relation
`x_(n+1) z_(n+1) - z_n` after arbitrary left multiplication. -/
private lemma remark102813_oneChainCoeff_mul_recurrence
    (f : MvPolynomial (Remark102813Var PUnit) k) (n : ℕ) :
    remark102813OneChainCoeff (k := k)
        (f *
          (remark102813X k PUnit (n + 1) * remark102813Z k PUnit PUnit.unit (n + 1) -
            remark102813Z k PUnit PUnit.unit n)) = 0 := by
  -- Proof comment: the two adjacent-chain terms contribute the same base coefficient, so they
  -- cancel after summing detector coordinates.
  rw [mul_sub, map_sub]
  have hxz :
      remark102813OneChainCoeff (k := k)
          (f * (remark102813X k PUnit (n + 1) *
            remark102813Z k PUnit PUnit.unit (n + 1))) =
        MvPolynomial.coeff (remark102813ChainBaseExponent n) f := by
    simp [remark102813OneChainCoeff, remark102813_oneChainCoeffs_mul_xz]
  have hz :
      remark102813OneChainCoeff (k := k) (f * remark102813Z k PUnit PUnit.unit n) =
        MvPolynomial.coeff (remark102813ChainBaseExponent n) f := by
    simp [remark102813OneChainCoeff, remark102813_oneChainCoeffs_mul_z]
  rw [hxz, hz, sub_self]

/-- Helper for Remark 10.28.13: the one-chain detector vanishes on the defining relation ideal. -/
private lemma remark102813_oneChainCoeff_mem_relationsIdeal_eq_zero
    {f : MvPolynomial (Remark102813Var PUnit) k}
    (hf : f ∈ remark102813RelationsIdeal k PUnit) :
    remark102813OneChainCoeff (k := k) f = 0 := by
  -- Proof comment: prove the stronger statement that left multiplication by any polynomial still
  -- has detector value zero, then specialize to the multiplier `1`.
  have hmul :
      ∀ g ∈ remark102813RelationsIdeal k PUnit,
        ∀ a : MvPolynomial (Remark102813Var PUnit) k,
          remark102813OneChainCoeff (k := k) (a * g) = 0 := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ ↦
        ∀ a : MvPolynomial (Remark102813Var PUnit) k,
          remark102813OneChainCoeff (k := k) (a * g) = 0) ?_ ?_ ?_ ?_ hg
    · intro g hg a
      rcases hg with hg | hg
      · rcases hg with hg | hg
        · rcases hg with ⟨n, rfl⟩
          simpa [pow_two, mul_assoc] using
            (remark102813_oneChainCoeff_mul_x_square (k := k) (f := a) (n := n))
        · rcases hg with ⟨p, rfl⟩
          rcases p with ⟨u, n⟩
          cases u
          simpa [pow_two, mul_assoc] using
            (remark102813_oneChainCoeff_mul_z_square (k := k) (f := a) (n := n))
      · rcases hg with ⟨p, rfl⟩
        rcases p with ⟨u, n⟩
        cases u
        simpa [mul_assoc] using
          (remark102813_oneChainCoeff_mul_recurrence (k := k) (f := a) (n := n))
    · intro a
      simp [remark102813OneChainCoeff]
    · intro g h hg hh hg_zero hh_zero a
      rw [mul_add, map_add, hg_zero a, hh_zero a, add_zero]
    · intro c g hg hg_zero a
      simpa [smul_eq_mul, mul_assoc] using hg_zero (a * c)
  simpa using hmul f hf 1

/-- Helper for Remark 10.28.13: in the one-chain quotient, the class of `z_{*,0}` is nonzero. -/
private lemma remark102813_singleChain_z_zero_ne_zero :
    Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit)
      (remark102813Z k PUnit PUnit.unit 0) ≠ 0 := by
  -- Proof comment: if the class were zero, then `z_{*,0}` would lie in the relation ideal, but
  -- the detector vanishes on that ideal and sends `z_{*,0}` to `1`.
  intro hz
  have hmem :
      remark102813Z k PUnit PUnit.unit 0 ∈ remark102813RelationsIdeal k PUnit :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hzero :
      remark102813OneChainCoeff (k := k) (remark102813Z k PUnit PUnit.unit 0) = 0 :=
    remark102813_oneChainCoeff_mem_relationsIdeal_eq_zero (k := k) hmem
  have honeCoeffs :
      remark102813OneChainCoeffs (k := k) (remark102813Z k PUnit PUnit.unit 0) = Finsupp.single 0 1 := by
    simpa [remark102813ChainBaseExponent] using
      (remark102813_oneChainCoeffs_mul_z (k := k) (f := 1) (n := 0))
  have hone :
      remark102813OneChainCoeff (k := k) (remark102813Z k PUnit PUnit.unit 0) = 1 := by
    rw [remark102813OneChainCoeff, LinearMap.comp_apply, honeCoeffs]
    simp
  exact one_ne_zero (hone.symm.trans hzero)

/-- Helper for Chap10 Remark 10 28 13: the upstairs ideal generated by all `z_{t,n}` variables in
the source polynomial ring. -/
private noncomputable def remark102813SourceZIdeal :
    Ideal (MvPolynomial (Remark102813Var T) k) :=
  Ideal.span <| Set.range fun p : T × ℕ ↦ remark102813Z k T p.1 p.2

/-- Helper for Chap10 Remark 10 28 13: the quotient image of the upstairs `z`-ideal is exactly the
bad ideal `(z_{t,n})` downstairs. -/
private lemma remark102813_sourceZIdeal_map_eq_badIdeal :
    Ideal.map (Ideal.Quotient.mk (remark102813RelationsIdeal k T))
      (remark102813SourceZIdeal k T) =
      remark102813BadIdeal k T := by
  -- Proof comment: push the span of the upstairs `z`-generators through the quotient map and
  -- identify the resulting image set with the defining generators of the bad ideal.
  unfold remark102813SourceZIdeal remark102813BadIdeal
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨remark102813Z k T p.1 p.2, ⟨p, rfl⟩, rfl⟩

/-- Helper for Chap10 Remark 10 28 13: membership in the bad ideal is equivalent to having an
upstairs lift from the source `z`-ideal. -/
private lemma remark102813_mem_badIdeal_iff_exists_sourceZIdealLift
    {x : remark102813Ring k T} :
    x ∈ remark102813BadIdeal k T ↔
      ∃ f : MvPolynomial (Remark102813Var T) k,
        f ∈ remark102813SourceZIdeal k T ∧
          Ideal.Quotient.mk (remark102813RelationsIdeal k T) f = x := by
  -- Proof comment: rewrite the bad ideal as a quotient-map image and use surjectivity of the
  -- quotient map to pass between downstairs membership and upstairs witnesses.
  rw [← remark102813_sourceZIdeal_map_eq_badIdeal (k := k) (T := T)]
  constructor
  · intro hx
    rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (remark102813RelationsIdeal k T))
      Ideal.Quotient.mk_surjective).1 hx with
      ⟨f, hf, hfx⟩
    exact ⟨f, hf, hfx⟩
  · rintro ⟨f, hf, rfl⟩
    exact Ideal.mem_map_of_mem _ hf

/-- Helper for Chap10 Remark 10 28 13: one polynomial only uses countably many `t`-chains. -/
private lemma remark102813_zChainSet_countable
    (f : MvPolynomial (Remark102813Var T) k) :
    ({t : T | ∃ n, Remark102813Var.z t n ∈ f.vars} : Set T).Countable := by
  classical
  -- Proof comment: the used chains are the first-coordinate image of the finite set of pairs
  -- whose `z_{t,n}` variable appears in `f.vars`.
  let e : T × ℕ ↪ Remark102813Var T :=
    ⟨fun p => Remark102813Var.z p.1 p.2, by
      intro a b h
      cases a
      cases b
      cases h
      rfl⟩
  have hpairs :
      ({p : T × ℕ | Remark102813Var.z p.1 p.2 ∈ f.vars} : Set (T × ℕ)).Finite := by
    simpa [e, Set.preimage] using
      Set.Finite.preimage_embedding
        (f := e) (s := (f.vars : Set (Remark102813Var T)))
        (Finset.finite_toSet f.vars)
  have hcount :
      (Prod.fst '' ({p : T × ℕ | Remark102813Var.z p.1 p.2 ∈ f.vars} : Set (T × ℕ))).Countable :=
    hpairs.countable.image Prod.fst
  refine hcount.mono ?_
  intro t ht
  rcases ht with ⟨n, hn⟩
  exact ⟨(t, n), hn, rfl⟩

/-- Helper for Chap10 Remark 10 28 13: if an upstairs polynomial lies in the source `z`-ideal and
avoids the chosen `t`-chain in its variable set, then the single-chain specialization kills it. -/
private lemma remark102813_singleChainQuotAux_eq_zero_of_memSourceZIdeal_avoidsChain
    [DecidableEq T] (t : T) {f : MvPolynomial (Remark102813Var T) k}
    (hf : f ∈ remark102813SourceZIdeal k T)
    (hvars : ∀ n, Remark102813Var.z t n ∉ f.vars) :
    remark102813SingleChainQuotAux (k := k) (T := T) t f = 0 := by
  -- Proof comment: every support monomial of an element of the source `z`-ideal contains some
  -- `z`-variable, and the chain-avoidance hypothesis forces that variable to lie off the chosen
  -- chain, so the specialization evaluates the monomial to zero.
  let zVars : Set (Remark102813Var T) := Set.range fun p : T × ℕ ↦ Remark102813Var.z p.1 p.2
  have hzSpan :
      remark102813SourceZIdeal k T =
        Ideal.span (MvPolynomial.X '' zVars : Set (MvPolynomial (Remark102813Var T) k)) := by
    -- Proof comment: the source `z`-ideal is exactly the span of the `X`-variables indexed by the
    -- `z`-chains.
    unfold remark102813SourceZIdeal zVars
    congr 1
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨Remark102813Var.z p.1 p.2, ⟨p, rfl⟩, by simp [remark102813Z]⟩
    · rintro ⟨i, ⟨p, hp⟩, hi⟩
      subst hp hi
      exact ⟨p, by simp [remark102813Z]⟩
  have hf' :
      f ∈ Ideal.span (MvPolynomial.X '' zVars : Set (MvPolynomial (Remark102813Var T) k)) := by
    simpa [hzSpan] using hf
  have hEval :
      MvPolynomial.eval₂Hom
          (MvPolynomial.C : k →+* MvPolynomial (Remark102813Var PUnit) k)
          (fun i =>
            match i with
            | Remark102813Var.x n => remark102813X k PUnit n
            | Remark102813Var.z u n =>
                if u = t then remark102813Z k PUnit PUnit.unit n else 0)
          f = 0 := by
    refine MvPolynomial.eval₂Hom_eq_zero _ _ _ ?_
    intro d hd
    let hd' : d ∈ f.support := Finsupp.mem_support_iff.mpr hd
    obtain ⟨i, hi, hdi⟩ :=
      (MvPolynomial.mem_ideal_span_X_image.mp hf') d hd'
    rcases hi with ⟨⟨u, n⟩, rfl⟩
    have huz : u ≠ t := by
      intro hut
      have hzmem : Remark102813Var.z t n ∈ f.vars := by
        refine (MvPolynomial.mem_vars _).2 ?_
        refine ⟨d, hd', ?_⟩
        simpa [hut] using Finsupp.mem_support_iff.mpr hdi
      exact hvars n hzmem
    refine ⟨Remark102813Var.z u n, Finsupp.mem_support_iff.mpr hdi, ?_⟩
    simp [huz]
  -- Proof comment: after the source evaluation vanishes, its quotient class also vanishes.
  change
    (Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit))
        ((MvPolynomial.eval₂Hom
          (MvPolynomial.C : k →+* MvPolynomial (Remark102813Var PUnit) k)
          (fun i =>
            match i with
            | Remark102813Var.x n => remark102813X k PUnit n
            | Remark102813Var.z u n =>
                if u = t then remark102813Z k PUnit PUnit.unit n else 0))
          f) = 0
  rw [hEval]
  rfl

/-- Helper for Remark 10.28.13: the ideal `(z_{t,n})` cannot be generated by a countable subset
when `T` is uncountable. -/
private lemma remark102813_badIdeal_not_countably_generated [Uncountable T] :
    ¬ ∃ s : Set (remark102813Ring k T), s.Countable ∧ Ideal.span s = remark102813BadIdeal k T := by
  classical
  -- Route correction: work with pointwise lifts from the quotient bad ideal back to the upstairs
  -- `z`-ideal, so the used chains can be measured directly by `vars`.
  intro hcount
  rcases hcount with ⟨s, hs_count, hs_span⟩
  have hlift :
      ∀ y : s, ∃ f : MvPolynomial (Remark102813Var T) k,
        f ∈ remark102813SourceZIdeal k T ∧
          Ideal.Quotient.mk (remark102813RelationsIdeal k T) f = (y : remark102813Ring k T) := by
    intro y
    -- Proof comment: each chosen generator already lies in the bad ideal, so it admits an
    -- upstairs source-ideal lift.
    have hy_bad : (y : remark102813Ring k T) ∈ remark102813BadIdeal k T := by
      simpa [hs_span] using
        (Ideal.subset_span y.property :
          (y : remark102813Ring k T) ∈ Ideal.span s)
    exact
      (remark102813_mem_badIdeal_iff_exists_sourceZIdealLift (k := k) (T := T)
        (x := (y : remark102813Ring k T))).1 hy_bad
  let lift : s → MvPolynomial (Remark102813Var T) k := fun y => Classical.choose (hlift y)
  have hlift_mem :
      ∀ y : s, lift y ∈ remark102813SourceZIdeal k T := by
    intro y
    exact (Classical.choose_spec (hlift y)).1
  have hlift_mk :
      ∀ y : s,
        Ideal.Quotient.mk (remark102813RelationsIdeal k T) (lift y) =
          (y : remark102813Ring k T) := by
    intro y
    exact (Classical.choose_spec (hlift y)).2
  let used : Set T := ⋃ y : s, {t : T | ∃ n, Remark102813Var.z t n ∈ (lift y).vars}
  haveI : Countable s := hs_count.to_subtype
  have hused : used.Countable := by
    refine Set.countable_iUnion fun y => ?_
    exact remark102813_zChainSet_countable (k := k) (T := T) (lift y)
  have hused_ne_univ : used ≠ Set.univ := by
    intro hused_univ
    have : (Set.univ : Set T).Countable := hused_univ ▸ hused
    exact Set.not_countable_univ this
  obtain ⟨t0, ht0⟩ : ∃ t0 : T, t0 ∉ used := by
    by_contra hno
    apply hused_ne_univ
    ext t
    constructor
    · intro _
      trivial
    · intro _
      by_contra ht
      exact hno ⟨t, ht⟩
  let singleMap : remark102813Ring k T →+* remark102813Ring k PUnit.{v + 1} :=
    remark102813SingleChainMap (k := k) (T := T) t0
  have hkill :
      ∀ y : s, singleMap (y : remark102813Ring k T) = 0 := by
    intro y
    have ht0y : t0 ∉ {t : T | ∃ n, Remark102813Var.z t n ∈ (lift y).vars} := by
      intro hmem
      exact ht0 <| Set.mem_iUnion.2 ⟨y, hmem⟩
    have havoid : ∀ n, Remark102813Var.z t0 n ∉ (lift y).vars := by
      intro n hz
      exact ht0y ⟨n, hz⟩
    -- Proof comment: the fresh chain does not occur in this lift, so the single-chain
    -- specialization annihilates the lift upstairs and hence its quotient class downstairs.
    rw [← hlift_mk y]
    change
      Ideal.Quotient.lift (remark102813RelationsIdeal k T)
          (remark102813SingleChainQuotAux (k := k) (T := T) t0)
          (remark102813_relationsIdeal_le_singleChainQuotAux_ker (k := k) (T := T) t0)
          (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (lift y)) = 0
    rw [Ideal.Quotient.lift_mk]
    exact remark102813_singleChainQuotAux_eq_zero_of_memSourceZIdeal_avoidsChain
      (k := k) (T := T) t0 (hlift_mem y) havoid
  have hs_ker :
      Ideal.span s ≤ RingHom.ker singleMap := by
    -- Proof comment: the specialization kills every generator in the chosen countable set, so it
    -- kills their span.
    refine Ideal.span_le.2 ?_
    intro y hy
    simpa using hkill ⟨y, hy⟩
  have hbad_ker :
      remark102813BadIdeal k T ≤ RingHom.ker singleMap := by
    simpa [hs_span] using hs_ker
  have hz_mem :
      Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t0 0) ∈
        remark102813BadIdeal k T := by
    exact Ideal.subset_span (Set.mem_range_self (t0, 0))
  have hz_zero :
      singleMap
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t0 0)) = 0 :=
    hbad_ker hz_mem
  have hz_eq :
      singleMap
        (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t0 0)) =
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit.{v + 1})
        (remark102813Z k PUnit.{v + 1} PUnit.unit 0) := by
    simpa [singleMap] using
      (remark102813_singleChainMap_mk_z_eq (k := k) (T := T) t0 0)
  exact remark102813_singleChain_z_zero_ne_zero (k := k) <|
    calc
      Ideal.Quotient.mk (remark102813RelationsIdeal k PUnit.{v + 1})
          (remark102813Z k PUnit.{v + 1} PUnit.unit 0) =
        singleMap
          (Ideal.Quotient.mk (remark102813RelationsIdeal k T) (remark102813Z k T t0 0)) := by
          exact hz_eq.symm
      _ = 0 := hz_zero

/-- If `T` is uncountable, then the ideal `(z_{t,n})` in Remark 10.28.13 does not have span rank at
most `ℵ₀`. -/
-- Proof sketch: the relations force every countable generating family to involve only countably
-- many indices `t`, while the ideal contains generators `z_{t,0}` for uncountably many `t`.
lemma remark102813_badIdeal_not_spanRank_le_aleph0 [Uncountable T] :
    ¬ (remark102813BadIdeal k T).spanRank ≤ Cardinal.aleph0 := by
  -- TODO: Convert a countable span-rank bound into a countable generating set and apply the
  -- preceding countability obstruction.
  intro hspan
  rcases
      (Submodule.FG.spanRank_le_iff_exists_span_set_card_le (remark102813BadIdeal k T)
        (a := Cardinal.aleph0)).mp hspan with
    ⟨s, hs_card, hs_span⟩
  exact remark102813_badIdeal_not_countably_generated (k := k) (T := T)
    ⟨s, Cardinal.le_aleph0_iff_set_countable.mp hs_card, hs_span⟩

/-- Chap10 Remark 10 28 13: the explicit quotient ring
`k[{x_n}_{n ≥ 1}, {z_{t,n}}_{t ∈ T, n ≥ 0}] / (x_n^2, z_{t,n}^2, x_{n+1} z_{t,n+1} - z_{t,n})`
shows that all prime ideals have span rank at most `ℵ₀` while some ideal does not. This is the
canonical formulation of the countable-generation assertion. -/
-- Proof sketch: the only prime ideal is `(x_n)`, so every prime ideal has span rank at most `ℵ₀`
-- by the previous lemma. The ideal `(z_{t,n})` does not when `T` is uncountable.
@[stacks 05KJ]
theorem prime_ideals_spanRank_le_aleph0_but_some_ideal_is_not [Uncountable T] :
    (∀ P : Ideal (remark102813Ring k T), P.IsPrime → P.spanRank ≤ Cardinal.aleph0) ∧
      ∃ I : Ideal (remark102813Ring k T), ¬ I.spanRank ≤ Cardinal.aleph0 := by
  constructor
  · intro P hP
    -- The unique-prime computation reduces every prime ideal to `(x_n)`.
    rw [(remark102813_unique_prime (k := k) (T := T) P).mp hP]
    exact remark102813_maximalIdeal_spanRank_le_aleph0 (k := k) (T := T)
  · -- The ideal `(z_{t,n})` is the required counterexample.
    exact ⟨remark102813BadIdeal k T, remark102813_badIdeal_not_spanRank_le_aleph0 (k := k) (T := T)⟩

end
