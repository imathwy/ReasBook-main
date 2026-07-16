import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».FormalRecursiveSystem

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

section FormalRecursiveImplicitSystem

variable {𝕜 : Type u} [CommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Exercise 2: a parameter multi-index has total degree zero exactly when it is the
zero exponent. -/
lemma paramDegree_eq_zero_iff (d : ParamIndex n p →₀ ℕ) :
    paramDegree d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    ext u
    have hu : d u ≤ paramDegree d := by
      dsimp [paramDegree]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp)
    rw [hd] at hu
    exact Nat.eq_zero_of_le_zero hu
  · intro hd
    simp [paramDegree, hd]

/-- Helper for Exercise 2: on parameter multi-indices, the source-facing total degree agrees with
the standard `Finsupp.degree`. -/
lemma paramDegree_eq_degree (d : ParamIndex n p →₀ ℕ) :
    paramDegree d = d.degree := by
  -- Both notions are the same total sum of the coordinates on the finite parameter index type.
  simp [paramDegree, Finsupp.degree_eq_sum]

/-- Helper for Exercise 2: the universal linear coefficient series records one primitive system
coefficient variable for each `z`-monomial. -/
noncomputable def universalLinearCoeff (j i : Fin n) :
    MvPowerSeries (Fin p) (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
  fun d ↦ MvPolynomial.X (Sum.inl (Sum.inl ⟨j, i, d⟩))

/-- Helper for Exercise 2: the universal nonlinear remainder keeps only the coefficients whose
`x`-degree is at least `2`, mirroring the recursive-system hypothesis. -/
noncomputable def universalHigherCoeff (j : Fin n) :
    MvPowerSeries (Fin n ⊕ Fin p) (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
  fun d ↦
    if 2 ≤ xDegree d then
      MvPolynomial.X (Sum.inl (Sum.inr (j, d)))
    else
      0

/-- Helper for Exercise 2: the universal recursive system packages the primitive coefficients of
`(3)` as algebraically independent variables. -/
noncomputable def universalRecursiveImplicitSystem :
    RecursiveImplicitSystem (MvPolynomial (RecursiveCoeffVar n p) ℤ) n p where
  linearCoeff := universalLinearCoeff
  higher := universalHigherCoeff
  higher_xDegree_ge_two j d hd := by
    -- The universal nonlinear remainder was defined to vanish below `x`-degree `2`.
    change (if 2 ≤ xDegree d then MvPolynomial.X (Sum.inl (Sum.inr (j, d))) else 0) = 0
    split_ifs with hdeg
    · omega
    · rfl

/-- Helper for Exercise 2: the degree-`N` cutoff of a concrete candidate solution keeps exactly
the positive-degree coefficients of total `(y, z)`-degree strictly less than `N`. -/
noncomputable def truncatedSolution (N : ℕ)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    Fin n → MvPowerSeries (ParamIndex n p) 𝕜 :=
  fun j d ↦
    if 0 < paramDegree d ∧ paramDegree d < N then
      MvPowerSeries.coeff d (x j)
    else
      0

/-- Helper for Exercise 2: the universal cutoff solution replaces each kept coefficient by its
corresponding coefficient variable. -/
noncomputable def truncatedUniversalSolution (N : ℕ) :
    Fin n → MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
  fun j d ↦
    if 0 < paramDegree d ∧ paramDegree d < N then
      MvPolynomial.X (Sum.inr ⟨j, d⟩)
    else
      0

/-- Helper for Exercise 2: every cutoff universal solution still has vanishing constant
coefficient. -/
lemma truncatedUniversalSolution_constantCoeff (N : ℕ) (j : Fin n) :
    MvPowerSeries.constantCoeff (truncatedUniversalSolution (n := n) (p := p) N j) = 0 := by
  -- The zero exponent has total parameter degree `0`, so it is discarded by the positive-degree
  -- cutoff built into `truncatedUniversalSolution`.
  change truncatedUniversalSolution (n := n) (p := p) N j 0 = 0
  simp [truncatedUniversalSolution, paramDegree]

/-- Helper for Exercise 2: every concrete cutoff solution still has vanishing constant
coefficient. -/
lemma truncatedSolution_constantCoeff
    (N : ℕ) (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) (j : Fin n) :
    MvPowerSeries.constantCoeff (truncatedSolution (n := n) (p := p) N x j) = 0 := by
  -- The concrete truncation uses the same positive-degree cutoff, so its constant coefficient
  -- vanishes for the same reason as in the universal case.
  change truncatedSolution (n := n) (p := p) N x j 0 = 0
  simp [truncatedSolution, paramDegree]

/-- Helper for Exercise 2: below the cutoff degree, truncation does not change coefficients once
the candidate solution has vanishing constant coefficient. -/
lemma coeff_truncatedSolution_eq_of_lt_paramDegree
    (N : ℕ) (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d < N) :
    MvPowerSeries.coeff d (truncatedSolution (n := n) (p := p) N x j) =
      MvPowerSeries.coeff d (x j) := by
  -- Split according to whether the coefficient is positive-degree; the degree-zero branch is
  -- forced by the vanishing constant coefficient hypothesis.
  by_cases hpos : 0 < paramDegree d
  · change (if 0 < paramDegree d ∧ paramDegree d < N then MvPowerSeries.coeff d (x j) else 0) =
        MvPowerSeries.coeff d (x j)
    simp [hpos, hd]
  · have hzero : paramDegree d = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hpos)
    have hd0 : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hzero
    subst hd0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [truncatedSolution_constantCoeff]
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using (hx j).symm

/-- Helper for Exercise 2: if two parameter series agree below total degree `N`, then every power
of those series also agrees below total degree `N`. -/
lemma coeff_pow_eq_of_coeff_eq_below_paramDegree
    {φ ψ : MvPowerSeries (ParamIndex n p) 𝕜} {N : ℕ}
    (hEq : ∀ d, paramDegree d < N → MvPowerSeries.coeff d φ = MvPowerSeries.coeff d ψ) :
    ∀ q : ℕ, ∀ d : ParamIndex n p →₀ ℕ, paramDegree d < N →
      MvPowerSeries.coeff d (φ ^ q) = MvPowerSeries.coeff d (ψ ^ q)
  | q, d, hd => by
      classical
      -- Expand the power coefficient by the canonical finite antidiagonal formula and compare
      -- each factor coefficient using the low-degree agreement hypothesis.
      rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
      refine Finset.sum_congr rfl ?_
      intro l hl
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hl' := Finset.mem_finsuppAntidiag.mp hl
      have hsumdeg : paramDegree d = ∑ i ∈ Finset.range q, paramDegree (l i) := by
        rw [paramDegree_eq_degree, ← hl'.1]
        simp [paramDegree_eq_degree, map_sum]
      have hli : paramDegree (l i) ≤ paramDegree d := by
        rw [hsumdeg]
        simpa using
          (Finset.single_le_sum
            (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hi :
              paramDegree (l i) ≤ ∑ j ∈ Finset.range q, paramDegree (l j))
      exact hEq (l i) (lt_of_le_of_lt hli hd)

/-- Helper for Exercise 2: if two positive-degree parameter series agree below total degree `N`,
then the degree-`N` coefficient of every power with exponent at least `2` also agrees. The extra
power factor forces every surviving antidiagonal term to use a strictly lower-degree coefficient,
or else the whole term vanishes because another factor has degree `0`. -/
lemma coeff_pow_eq_of_coeff_eq_below_paramDegree_of_two_le
    {φ ψ : MvPowerSeries (ParamIndex n p) 𝕜} {N q : ℕ}
    (hq : 2 ≤ q)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (hψ0 : MvPowerSeries.constantCoeff ψ = 0)
    (hEq : ∀ d, paramDegree d < N → MvPowerSeries.coeff d φ = MvPowerSeries.coeff d ψ)
    (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d = N) :
    MvPowerSeries.coeff d (φ ^ q) = MvPowerSeries.coeff d (ψ ^ q) := by
  classical
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
  refine Finset.sum_congr rfl ?_
  intro l hl
  have hl' := Finset.mem_finsuppAntidiag.mp hl
  have hsumdeg : N = ∑ i ∈ Finset.range q, paramDegree (l i) := by
    rw [← hd, paramDegree_eq_degree, ← hl'.1]
    simp [paramDegree_eq_degree, map_sum]
  by_cases hlt : ∀ i ∈ Finset.range q, paramDegree (l i) < N
  · -- When every factor degree is already below `N`, compare each factor coefficient directly.
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact hEq (l i) (hlt i hi)
  · -- Otherwise one factor carries the full total degree `N`, forcing another factor to sit in
    -- degree `0`; the whole product then vanishes on both sides because `φ` and `ψ` have zero
    -- constant coefficient.
    push Not at hlt
    rcases hlt with ⟨i, hi, hNi⟩
    have hli_le : paramDegree (l i) ≤ N := by
      rw [hsumdeg]
      simpa using
        (Finset.single_le_sum
          (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hi :
            paramDegree (l i) ≤ ∑ j ∈ Finset.range q, paramDegree (l j))
    have hli_eq : paramDegree (l i) = N := le_antisymm hli_le hNi
    have hsumErase : ∑ j ∈ (Finset.range q).erase i, paramDegree (l j) = 0 := by
      have hsplit :
          ∑ j ∈ Finset.range q, paramDegree (l j) =
            paramDegree (l i) + ∑ j ∈ (Finset.range q).erase i, paramDegree (l j) := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_add_sum_diff_singleton_of_mem (f := fun j ↦ paramDegree (l j)) hi :
            ∑ j ∈ Finset.range q, paramDegree (l j) =
              paramDegree (l i) + ∑ x ∈ Finset.range q \ {i}, paramDegree (l x))
      have hsumdeg' : ∑ j ∈ Finset.range q, paramDegree (l j) = N := hsumdeg.symm
      rw [hsumdeg', hli_eq] at hsplit
      have hsub := congrArg (fun t : ℕ => t - N) hsplit.symm
      simpa using hsub
    have hcardErasePos : 0 < ((Finset.range q).erase i).card := by
      rw [Finset.card_erase_of_mem hi, Finset.card_range]
      omega
    rcases Finset.card_pos.mp hcardErasePos with ⟨j, hj⟩
    have hjrange : j ∈ Finset.range q := (Finset.mem_erase.mp hj).2
    have hjdeg0 : paramDegree (l j) = 0 := by
      have hle :
          paramDegree (l j) ≤ ∑ k ∈ (Finset.range q).erase i, paramDegree (l k) := by
        exact Finset.single_le_sum (fun k hk ↦ Nat.zero_le (paramDegree (l k))) hj
      rw [hsumErase] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hjEq0 : l j = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) (l j)).mp hjdeg0
    have hcoeffφ0 : MvPowerSeries.coeff (l j) φ = 0 := by
      simpa [hjEq0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ0
    have hcoeffψ0 : MvPowerSeries.coeff (l j) ψ = 0 := by
      simpa [hjEq0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hψ0
    rw [← Finset.mul_prod_erase (s := Finset.range q)
      (f := fun k ↦ MvPowerSeries.coeff (l k) φ) hjrange, hcoeffφ0, zero_mul]
    rw [← Finset.mul_prod_erase (s := Finset.range q)
      (f := fun k ↦ MvPowerSeries.coeff (l k) ψ) hjrange, hcoeffψ0, zero_mul]

/-- Helper for Exercise 2: every power of the cutoff solution agrees with the original solution in
all total degrees strictly below the cutoff. -/
lemma coeff_truncatedSolution_pow_eq_of_lt_paramDegree
    (N : ℕ) (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (q : ℕ) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d < N) :
    MvPowerSeries.coeff d ((truncatedSolution (n := n) (p := p) N x j) ^ q) =
      MvPowerSeries.coeff d ((x j) ^ q) := by
  -- Apply the generic power comparison lemma to the cutoff agreement proved above.
  exact coeff_pow_eq_of_coeff_eq_below_paramDegree (n := n) (p := p)
    (N := N)
    (fun e he ↦ coeff_truncatedSolution_eq_of_lt_paramDegree (n := n) (p := p)
      N x hx j e he)
    q d hd

/-- Helper for Exercise 2: the cutoff universal substitution is admissible because all substituted
`x`-series have zero constant coefficient. -/
theorem truncatedUniversalSolution_hasSubst (N : ℕ) :
    MvPowerSeries.HasSubst
      (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N)) :=
  solutionSubst_hasSubst _ (truncatedUniversalSolution_constantCoeff (n := n) (p := p) N)

/-- Helper for Exercise 2: the concrete cutoff substitution is admissible because all substituted
`x`-series have zero constant coefficient. -/
theorem truncatedSolution_hasSubst
    (N : ℕ) (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    MvPowerSeries.HasSubst (solutionSubst (truncatedSolution (n := n) (p := p) N x)) :=
  solutionSubst_hasSubst _ (truncatedSolution_constantCoeff (n := n) (p := p) N x)

/-- Helper for Exercise 2: evaluating the universal linear coefficient series recovers the
corresponding concrete coefficient series. -/
theorem map_universalLinearCoeff
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (j i : Fin n) :
    MvPowerSeries.map
      (MvPolynomial.eval₂Hom (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x))
      (universalLinearCoeff (n := n) (p := p) j i) =
        S.linearCoeff j i := by
  -- Evaluate coefficientwise; every universal variable is sent to the matching concrete
  -- coefficient of `S`.
  ext d
  rw [MvPowerSeries.coeff_map]
  change
    MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x)
        (MvPolynomial.X (Sum.inl (Sum.inl (j, i, d)))) =
      MvPowerSeries.coeff d (S.linearCoeff j i)
  simp [recursiveCoeffAssignment]

/-- Helper for Exercise 2: evaluating the universal nonlinear remainder recovers the corresponding
concrete nonlinear remainder. -/
theorem map_universalHigherCoeff
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (j : Fin n) :
    MvPowerSeries.map
      (MvPolynomial.eval₂Hom (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x))
      (universalHigherCoeff (n := n) (p := p) j) =
        S.higher j := by
  -- Evaluate coefficientwise and split according to whether the universal higher part keeps the
  -- coefficient indexed by `d`.
  ext d
  rw [MvPowerSeries.coeff_map]
  change
    MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x)
      (if 2 ≤ xDegree d then MvPolynomial.X (Sum.inl (Sum.inr (j, d))) else 0) =
      MvPowerSeries.coeff d (S.higher j)
  by_cases hdeg : 2 ≤ xDegree d
  · simp [hdeg, recursiveCoeffAssignment]
  · have hxdeg : xDegree d ≤ 1 := by omega
    rw [show MvPowerSeries.coeff d (S.higher j) = 0 from S.higher_xDegree_ge_two j d hxdeg]
    simp [hdeg]

/-- Helper for Exercise 2: evaluating the universal cutoff solution recovers the corresponding
concrete cutoff solution. -/
theorem map_truncatedUniversalSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (N : ℕ) (j : Fin n) :
    MvPowerSeries.map
      (MvPolynomial.eval₂Hom (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x))
      (truncatedUniversalSolution (n := n) (p := p) N j) =
        truncatedSolution (n := n) (p := p) N x j := by
  -- Compare coefficients termwise; on the kept degree range the universal coefficient variable
  -- evaluates to the corresponding coefficient of `x`, and outside it both sides are zero.
  ext d
  rw [MvPowerSeries.coeff_map]
  change
    MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x)
      (if 0 < paramDegree d ∧ paramDegree d < N then MvPolynomial.X (Sum.inr ⟨j, d⟩) else 0) =
      truncatedSolution (n := n) (p := p) N x j d
  by_cases hd : 0 < paramDegree d ∧ paramDegree d < N
  · simp [truncatedSolution, hd, recursiveCoeffAssignment]
  · simp [truncatedSolution, hd]

/-- Helper for Exercise 2: coefficient evaluation commutes with renaming the variables of a
multivariate power series. -/
theorem map_rename
    {σ τ : Type*}
    (f : σ → τ) [Filter.TendstoCofinite f]
    (φ : MvPolynomial (RecursiveCoeffVar n p) ℤ →+* 𝕜)
    (F : MvPowerSeries σ (MvPolynomial (RecursiveCoeffVar n p) ℤ)) :
    MvPowerSeries.map φ (MvPowerSeries.rename f F) =
      MvPowerSeries.rename f (MvPowerSeries.map φ F) := by
  -- This is the standard compatibility between coefficient maps and renaming.
  simpa using (MvPowerSeries.rename_map (f := f) (φ := φ) F).symm

/-- Helper for Exercise 2: evaluating the universal recursive system recovers the concrete system
series `Γ(z) y + H(x, z)`. -/
theorem map_universalRecursiveImplicitSystem
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (j : Fin n) :
    MvPowerSeries.map
      (MvPolynomial.eval₂Hom (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x))
      (universalRecursiveImplicitSystem (n := n) (p := p) j) =
        S j := by
  -- Rewrite the universal right-hand side coefficientwise and evaluate the primitive coefficient
  -- variables back to the corresponding concrete series.
  simp [RecursiveImplicitSystem.toSeries, universalRecursiveImplicitSystem,
    map_universalLinearCoeff, map_universalHigherCoeff, map_rename]

/-- Helper for Exercise 2: every recursive-system right-hand side has vanishing constant
coefficient. -/
theorem RecursiveImplicitSystem.constantCoeff_toSeries (S : RecursiveImplicitSystem 𝕜 n p)
    (j : Fin n) :
    MvPowerSeries.constantCoeff (S j) = 0 := by
  -- The linear part contains an explicit `y`-variable, and the nonlinear part vanishes in
  -- `x`-degree `0`.
  have hhigher : MvPowerSeries.constantCoeff (S.higher j) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact S.higher_xDegree_ge_two j 0 (by simp [xDegree])
  simp [RecursiveImplicitSystem.toSeries, hhigher]

/-- Helper for Exercise 2: the universal degree-`d` coefficient polynomial is obtained by
substituting the degree cutoff `paramDegree d` into the universal recursive system. -/
noncomputable def recursiveCoefficientPolynomial (j : Fin n) (d : ParamIndex n p →₀ ℕ) :
    MvPolynomial (RecursiveCoeffVar n p) ℤ :=
  MvPowerSeries.coeff d
    (MvPowerSeries.subst
      (solutionSubst (truncatedUniversalSolution (n := n) (p := p) (paramDegree d)))
      (universalRecursiveImplicitSystem (n := n) (p := p) j))

/-- Helper for Exercise 2: evaluating the universal degree-`d` coefficient polynomial yields the
degree-`d` coefficient obtained from the concrete cutoff substitution. -/
theorem eval_recursiveCoefficientPolynomial
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x)
      (recursiveCoefficientPolynomial (n := n) (p := p) j d) =
        MvPowerSeries.coeff d
          (MvPowerSeries.subst
            (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
            (S j)) := by
  -- Map the universal cutoff substitution to the concrete cutoff substitution, then read the
  -- degree-`d` coefficient.
  let φ : MvPolynomial (RecursiveCoeffVar n p) ℤ →+* 𝕜 :=
    MvPolynomial.eval₂Hom (Int.castRingHom 𝕜) (recursiveCoeffAssignment S x)
  have hsubst :
      (fun s ↦
        MvPowerSeries.map φ
          (solutionSubst (truncatedUniversalSolution (n := n) (p := p) (paramDegree d)) s)) =
        solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x) := by
    funext s
    cases s with
    | inl j' =>
        simpa [φ] using
          map_truncatedUniversalSolution (n := n) (p := p) (S := S) (x := x)
            (N := paramDegree d) j'
    | inr u =>
        simp [solutionSubst, φ]
  calc
    φ (recursiveCoefficientPolynomial (n := n) (p := p) j d)
      = MvPowerSeries.coeff d
          (MvPowerSeries.map φ
            (MvPowerSeries.subst
              (solutionSubst (truncatedUniversalSolution (n := n) (p := p) (paramDegree d)))
              (universalRecursiveImplicitSystem (n := n) (p := p) j))) := by
            simp [recursiveCoefficientPolynomial, MvPowerSeries.coeff_map]
    _ = MvPowerSeries.coeff d
          (MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.map φ
                (solutionSubst
                  (truncatedUniversalSolution (n := n) (p := p) (paramDegree d)) s))
            (MvPowerSeries.map φ
              (universalRecursiveImplicitSystem (n := n) (p := p) j))) := by
            rw [MvPowerSeries.map_subst
              (truncatedUniversalSolution_hasSubst (n := n) (p := p) (paramDegree d))]
    _ = MvPowerSeries.coeff d
          (MvPowerSeries.subst
            (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
            (MvPowerSeries.map φ
              (universalRecursiveImplicitSystem (n := n) (p := p) j))) := by
            simp [hsubst]
    _ = MvPowerSeries.coeff d
          (MvPowerSeries.subst
            (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
            (S j)) := by
            rw [map_universalRecursiveImplicitSystem (n := n) (p := p) (S := S) (x := x)]

end FormalRecursiveImplicitSystem
