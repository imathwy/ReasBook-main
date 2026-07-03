import DifferentialForms_Cartan_1970.VII.section27.«0003_Definition_VII_1_extra_1»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

-- Semantic recall note: the `lean_leansearch` MCP tool was unavailable in this environment, so
-- this item is stated directly with mathlib's multivariable power-series API via
-- `MvPowerSeries`, `MvPowerSeries.subst`, and `MvPolynomial`.

universe u

section FormalRecursiveImplicitSystem

variable {𝕜 : Type u} [CommRing 𝕜]
variable {n p : ℕ}

/-- The parameter variables `(y, z)` occurring in the formal solution series `(4)`. -/
abbrev ParamIndex (n p : ℕ) := Fin n ⊕ Fin p

/-- The variables `(x, y, z)` occurring in the recursive system `(3)`. -/
abbrev SystemIndex (n p : ℕ) := Fin n ⊕ ParamIndex n p

/-- The total `x`-degree of a monomial in the nonlinear remainder variables `(x, z)`. -/
def xDegree (d : (Fin n ⊕ Fin p) →₀ ℕ) : ℕ :=
  ∑ j : Fin n, d (Sum.inl j)

/-- The total `(y, z)`-degree of a monomial in the formal solution series `(4)`. -/
def paramDegree (d : ParamIndex n p →₀ ℕ) : ℕ :=
  ∑ u : ParamIndex n p, d u

/-- The coefficient variables used to encode the polynomial recursion for the coefficients of a
formal solution: the left summands index the primitive coefficients of the recursive system `(3)`,
while the right summands index lower-order coefficients of the candidate solution `(4)`. -/
abbrev SystemCoeffVar (n p : ℕ) :=
  (Fin n × Fin n × (Fin p →₀ ℕ)) ⊕ (Fin n × ((Fin n ⊕ Fin p) →₀ ℕ))

/-- The coefficient variables used to encode the polynomial recursion for the coefficients of a
formal solution. -/
abbrev RecursiveCoeffVar (n p : ℕ) :=
  SystemCoeffVar n p ⊕ (Fin n × (ParamIndex n p →₀ ℕ))

/-- A recursive implicit system of the form `(3)`: linear in the `y`-variables with `z`-series
coefficients, and with nonlinear remainder of `x`-degree at least `2`. -/
structure RecursiveImplicitSystem (𝕜 : Type u) [CommRing 𝕜] (n p : ℕ) where
  linearCoeff : Fin n → Fin n → MvPowerSeries (Fin p) 𝕜
  higher : Fin n → MvPowerSeries (Fin n ⊕ Fin p) 𝕜
  higher_xDegree_ge_two (j : Fin n) (d : (Fin n ⊕ Fin p) →₀ ℕ) (hd : xDegree d ≤ 1) :
    MvPowerSeries.coeff d (higher j) = 0

/-- Embed the `z`-variables into the full recursive-system variables `(x, y, z)`. -/
def zToSystem : Fin p → SystemIndex n p :=
  Sum.inr ∘ Sum.inr

/-- Embed the nonlinear-remainder variables `(x, z)` into the full recursive-system variables
`(x, y, z)`. -/
def higherToSystem : Fin n ⊕ Fin p → SystemIndex n p :=
  Sum.elim Sum.inl zToSystem

/-- The right-hand side family `x ↦ Γ(z) y + H(x, z)` associated to a recursive implicit system. -/
noncomputable def RecursiveImplicitSystem.toSeries
    (S : RecursiveImplicitSystem 𝕜 n p) :
    Fin n → MvPowerSeries (SystemIndex n p) 𝕜 :=
  fun j ↦
    (∑ i : Fin n,
        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
          MvPowerSeries.X (Sum.inr (Sum.inl i))) +
      MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j)

/-- The right-hand side family `x ↦ Γ(z) y + H(x, z)` attached to a recursive implicit system. -/
noncomputable instance : CoeFun (RecursiveImplicitSystem 𝕜 n p)
    (fun _ ↦ Fin n → MvPowerSeries (SystemIndex n p) 𝕜) where
  coe := RecursiveImplicitSystem.toSeries

/-- Substitute a candidate formal solution `x(y, z)` for the placeholder variables `x` in `(3)`,
while keeping the parameter variables `(y, z)` fixed. -/
noncomputable def solutionSubst
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    SystemIndex n p → MvPowerSeries (ParamIndex n p) 𝕜 :=
  Sum.elim x MvPowerSeries.X

/-- The substitution attached to a formal candidate solution is admissible as soon as all its
constant coefficients vanish. -/
theorem solutionSubst_hasSubst
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) :
    MvPowerSeries.HasSubst (solutionSubst x) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | u)
  · exact hx j
  · simp [solutionSubst]

/-- A family of formal series `x₁, ..., xₙ` solving the recursive system `(3)`. -/
structure FormalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) : Prop where
  constantCoeff_eq_zero (j : Fin n) : MvPowerSeries.constantCoeff (x j) = 0
  eq_subst (j : Fin n) : x j = MvPowerSeries.subst (solutionSubst x) (S j)

namespace FormalImplicitSolution

/-- A formal solution yields the admissible substitution needed to evaluate the recursive system on
that solution. This is derived from the vanishing constant coefficients and the finiteness of the
variable set. -/
theorem hasSubst
    {S : RecursiveImplicitSystem 𝕜 n p}
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (h : FormalImplicitSolution S x) :
    MvPowerSeries.HasSubst (solutionSubst x) :=
  solutionSubst_hasSubst x h.constantCoeff_eq_zero

end FormalImplicitSolution

/-- Evaluate the coefficient variables for the system coefficients and the coefficients of a
candidate formal solution. -/
noncomputable def recursiveCoeffAssignment
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    RecursiveCoeffVar n p → 𝕜
  | Sum.inl (Sum.inl ⟨j, i, d⟩) => MvPowerSeries.coeff d (S.linearCoeff j i)
  | Sum.inl (Sum.inr ⟨j, d⟩) => MvPowerSeries.coeff d (S.higher j)
  | Sum.inr ⟨j, d⟩ => MvPowerSeries.coeff d (x j)

/-- A candidate formal solution satisfies the coefficient recursion encoded by a polynomial family
`Q`. -/
structure RecursiveCoefficientRecurrence
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) : Prop where
  constantCoeff_eq_zero (j : Fin n) : MvPowerSeries.constantCoeff (x j) = 0
  coeff_eq_eval (j : Fin n) (d : ParamIndex n p →₀ ℕ) (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d (x j) =
      MvPolynomial.eval₂ (Int.castRingHom 𝕜)
        (recursiveCoeffAssignment S x) (Q j d)

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

/-- Helper for Exercise 2: the degree-`d` coefficient of the recursive-system substitution is
unchanged after replacing a solution family by its cutoff at total parameter degree
`paramDegree d`. -/
theorem coeff_subst_higher_eq_of_truncatedSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d
      (MvPowerSeries.subst
        (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
        (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j))) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst
          (solutionSubst x)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (S.higher j))) := by
  -- Route correction: the remaining blocker is purely nonlinear. The intended next step is to
  -- expand `coeff_subst_finite` on `S.higher j`, reduce termwise to monomials of `x`-degree at
  -- least `2`, and use the cutoff agreement below `paramDegree d` together with the vanishing
  -- constant coefficients to show that the degree-`d` coefficient is unchanged.
  sorry

/-- Helper for Exercise 2: the degree-`d` coefficient of the recursive-system substitution is
unchanged after replacing a solution family by its cutoff at total parameter degree
`paramDegree d`. -/
theorem coeff_subst_eq_of_truncatedSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d
      (MvPowerSeries.subst
        (solutionSubst (truncatedSolution (n := n) (p := p) (paramDegree d) x))
        (S j)) =
      MvPowerSeries.coeff d
        (MvPowerSeries.subst (solutionSubst x) (S j)) := by
  classical
  let linearPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    ∑ i : Fin n,
      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
        MvPowerSeries.X (Sum.inr (Sum.inl i))
  let higherPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j)
  let trunc := truncatedSolution (n := n) (p := p) (paramDegree d) x
  have htoSeries : S j = linearPart + higherPart := by
    -- Split the recursive-system series into its linear `Γ(z) y` part and its higher remainder.
    simp [RecursiveImplicitSystem.toSeries, linearPart, higherPart]
  have htruncSubst : MvPowerSeries.HasSubst (solutionSubst trunc) := by
    -- The cutoff solution is still admissible because the positive-degree truncation kills the
    -- constant coefficient.
    simpa [trunc] using truncatedSolution_hasSubst (n := n) (p := p) (paramDegree d) x
  have hxSubst : MvPowerSeries.HasSubst (solutionSubst x) :=
    solutionSubst_hasSubst x hx
  have hlinearCoeff_trunc (i : Fin n) :
      MvPowerSeries.subst (solutionSubst trunc)
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
        MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
    -- The linear coefficient series only uses the parameter variables `z`, so substituting the
    -- cutoff solution has no effect on it.
    calc
      MvPowerSeries.subst (solutionSubst trunc)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
          MvPowerSeries.subst (solutionSubst trunc)
            (MvPowerSeries.subst
              (MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p))
              (S.linearCoeff j i)) := by
                rw [← MvPowerSeries.rename_eq_subst]
      _ = MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.subst (solutionSubst trunc)
                ((MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p)) s))
            (S.linearCoeff j i) := by
              rw [MvPowerSeries.subst_comp_subst_apply
                (MvPowerSeries.HasSubst.X_comp (zToSystem : Fin p → SystemIndex n p))
                htruncSubst]
      _ = MvPowerSeries.subst
            (MvPowerSeries.X ∘ (Sum.inr : Fin p → ParamIndex n p))
            (S.linearCoeff j i) := by
              congr 1
              funext s
              simpa [zToSystem] using
                (MvPowerSeries.subst_X htruncSubst
                  (s := (Sum.inr (Sum.inr s) : SystemIndex n p)))
      _ = MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
            simpa using
              (MvPowerSeries.rename_eq_subst (f := (Sum.inr : Fin p → ParamIndex n p))
                (p := S.linearCoeff j i)).symm
  have hlinearCoeff_full (i : Fin n) :
      MvPowerSeries.subst (solutionSubst x)
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
        MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
    -- The same parameter-only argument applies to the full solution substitution.
    calc
      MvPowerSeries.subst (solutionSubst x)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
          MvPowerSeries.subst (solutionSubst x)
            (MvPowerSeries.subst
              (MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p))
              (S.linearCoeff j i)) := by
                rw [← MvPowerSeries.rename_eq_subst]
      _ = MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.subst (solutionSubst x)
                ((MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p)) s))
            (S.linearCoeff j i) := by
              rw [MvPowerSeries.subst_comp_subst_apply
                (MvPowerSeries.HasSubst.X_comp (zToSystem : Fin p → SystemIndex n p))
                hxSubst]
      _ = MvPowerSeries.subst
            (MvPowerSeries.X ∘ (Sum.inr : Fin p → ParamIndex n p))
            (S.linearCoeff j i) := by
              congr 1
              funext s
              simpa [zToSystem] using
                (MvPowerSeries.subst_X hxSubst
                  (s := (Sum.inr (Sum.inr s) : SystemIndex n p)))
      _ = MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
            simpa using
              (MvPowerSeries.rename_eq_subst (f := (Sum.inr : Fin p → ParamIndex n p))
                (p := S.linearCoeff j i)).symm
  have hlinear_trunc :
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
        ∑ i : Fin n,
          MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
            MvPowerSeries.X (Sum.inl i) := by
    -- Distribute substitution across the finite linear sum and simplify each term.
    calc
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
          ∑ i : Fin n,
            MvPowerSeries.subst (solutionSubst trunc)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inr (Sum.inl i))) := by
                  rw [show linearPart =
                    ∑ i : Fin n,
                      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inr (Sum.inl i)) by
                    rfl]
                  simpa [MvPowerSeries.substAlgHom_apply] using
                    (map_sum (MvPowerSeries.substAlgHom htruncSubst)
                      (fun i : Fin n ↦
                        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                            (S.linearCoeff j i) *
                          MvPowerSeries.X (Sum.inr (Sum.inl i)))
                      Finset.univ)
      _ = ∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [MvPowerSeries.subst_mul htruncSubst, hlinearCoeff_trunc]
                rw [MvPowerSeries.subst_X htruncSubst]
                simp [solutionSubst]
  have hlinear_full :
      MvPowerSeries.subst (solutionSubst x) linearPart =
        ∑ i : Fin n,
          MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
            MvPowerSeries.X (Sum.inl i) := by
    -- The same simplification shows that the full substitution produces the identical linear sum.
    calc
      MvPowerSeries.subst (solutionSubst x) linearPart =
          ∑ i : Fin n,
            MvPowerSeries.subst (solutionSubst x)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inr (Sum.inl i))) := by
                  rw [show linearPart =
                    ∑ i : Fin n,
                      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inr (Sum.inl i)) by
                    rfl]
                  simpa [MvPowerSeries.substAlgHom_apply] using
                    (map_sum (MvPowerSeries.substAlgHom hxSubst)
                      (fun i : Fin n ↦
                        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                            (S.linearCoeff j i) *
                          MvPowerSeries.X (Sum.inr (Sum.inl i)))
                      Finset.univ)
      _ = ∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [MvPowerSeries.subst_mul hxSubst, hlinearCoeff_full]
                rw [MvPowerSeries.subst_X hxSubst]
                simp [solutionSubst]
  -- Route correction: after splitting off the linear part, the only remaining work is the
  -- nonlinear cutoff-invariance statement for the higher remainder.
  rw [htoSeries, MvPowerSeries.subst_add htruncSubst, MvPowerSeries.subst_add hxSubst]
  change
    MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) linearPart) +
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) higherPart) =
      MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst x) linearPart) +
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst x) higherPart)
  congr 1
  · rw [hlinear_trunc, hlinear_full]
  · simpa [higherPart, trunc] using
      coeff_subst_higher_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x) hx j d hd

/-- Helper for Exercise 2: every coefficient of the cutoff substitution uses only the allowed
right-summand variables of total parameter degree strictly below the cutoff. -/
lemma vars_coeff_solutionSubst_truncatedUniversalSolution
    (N : ℕ) (s : SystemIndex n p) (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e
      (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Read the substituted series coefficientwise. Only the `x`-variable branch can contribute a
  -- right-summand coefficient variable, and there it appears exactly in the kept cutoff range.
  cases s with
  | inl j =>
      by_cases hcut : 0 < paramDegree e ∧ paramDegree e < N
      · cases u with
        | inl a =>
            trivial
        | inr a =>
            rcases a with ⟨j', d⟩
            change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
              ((truncatedUniversalSolution (n := n) (p := p) N j) e).vars at hu
            simp [truncatedUniversalSolution, hcut, MvPolynomial.vars_X] at hu
            rcases hu with ⟨rfl, rfl⟩
            simpa using hcut.2
      · change u ∈ ((truncatedUniversalSolution (n := n) (p := p) N j) e).vars at hu
        simp [truncatedUniversalSolution, hcut] at hu
  | inr a =>
      cases a with
      | inl i =>
          cases u with
          | inl a =>
              trivial
          | inr a =>
              rcases a with ⟨j', d⟩
              exact False.elim <| by
                change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
                  (MvPowerSeries.coeff e
                    (MvPowerSeries.X (Sum.inl i) :
                      MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ))).vars
                  at hu
                by_cases he : e = Finsupp.single (Sum.inl i) 1
                · simp [MvPowerSeries.coeff_X, he] at hu
                · simp [MvPowerSeries.coeff_X, he] at hu
      | inr k =>
          cases u with
          | inl a =>
              trivial
          | inr a =>
              rcases a with ⟨j', d⟩
              exact False.elim <| by
                change (Sum.inr ⟨j', d⟩ : RecursiveCoeffVar n p) ∈
                  (MvPowerSeries.coeff e
                    (MvPowerSeries.X (Sum.inr k) :
                      MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ))).vars
                  at hu
                by_cases he : e = Finsupp.single (Sum.inr k) 1
                · simp [MvPowerSeries.coeff_X, he] at hu
                · simp [MvPowerSeries.coeff_X, he] at hu

/-- Helper for Exercise 2: the cutoff bound on right-summand variables is preserved when passing to
coefficients of powers of a substituted series. -/
lemma vars_coeff_pow_below_cutoff
    {φ : MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ)}
    {N : ℕ}
    (hφ : ∀ e u, u ∈ (MvPowerSeries.coeff e φ).vars →
      match u with
      | Sum.inl _ => True
      | Sum.inr ⟨_, d⟩ => paramDegree d < N)
    (q : ℕ) (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e (φ ^ q)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Expand the coefficient of the power into antidiagonal products, then descend to a single
  -- factor coefficient where the cutoff hypothesis `hφ` applies directly.
  rw [MvPowerSeries.coeff_pow] at hu
  have hsum :
      (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
          ∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars ⊆
        (Finset.finsuppAntidiag (Finset.range q) e).biUnion fun l =>
          (∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars := by
    simpa using
      (MvPolynomial.vars_sum_subset
        (t := Finset.finsuppAntidiag (Finset.range q) e)
        (φ := fun l => ∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ))
  rcases Finset.mem_biUnion.mp (hsum hu) with ⟨l, hl, hul⟩
  have hprod :
      (∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ).vars ⊆
        (Finset.range q).biUnion fun i => (MvPowerSeries.coeff (l i) φ).vars := by
    simpa using
      (MvPolynomial.vars_prod
        (s := Finset.range q)
        (f := fun i => MvPowerSeries.coeff (l i) φ))
  rcases Finset.mem_biUnion.mp (hprod hul) with ⟨i, hi, hui⟩
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa using hφ (l i) (Sum.inr a) hui

/-- Helper for Exercise 2: the cutoff bound on right-summand variables is preserved under the
finite products appearing in the substitution coefficient formula. -/
lemma vars_coeff_prod_below_cutoff
    {ι : Type*} [DecidableEq ι]
    {f : ι → MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ)}
    {s : Finset ι} {N : ℕ}
    (hf : ∀ i ∈ s, ∀ e u, u ∈ (MvPowerSeries.coeff e (f i)).vars →
      match u with
      | Sum.inl _ => True
      | Sum.inr ⟨_, d⟩ => paramDegree d < N)
    (e : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e (∏ i ∈ s, f i)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Expand the coefficient of the finite product into antidiagonal products, then descend to a
  -- single factor coefficient where the cutoff hypothesis `hf` applies.
  rw [MvPowerSeries.coeff_prod] at hu
  have hsum :
      (∑ l ∈ Finset.finsuppAntidiag s e,
          ∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars ⊆
        (Finset.finsuppAntidiag s e).biUnion fun l =>
          (∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars := by
    simpa using
      (MvPolynomial.vars_sum_subset
        (t := Finset.finsuppAntidiag s e)
        (φ := fun l => ∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)))
  rcases Finset.mem_biUnion.mp (hsum hu) with ⟨l, hl, hul⟩
  have hprod :
      (∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)).vars ⊆
        s.biUnion fun i => (MvPowerSeries.coeff (l i) (f i)).vars := by
    simpa using
      (MvPolynomial.vars_prod
        (s := s)
        (f := fun i => MvPowerSeries.coeff (l i) (f i)))
  rcases Finset.mem_biUnion.mp (hprod hul) with ⟨i, hi, hui⟩
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa using hf i hi (l i) (Sum.inr a) hui

/-- Helper for Exercise 2: the monomial products arising from the substitution formula only use
cutoff solution variables of strictly smaller total parameter degree. -/
lemma vars_coeff_finsuppProd_solutionSubst_truncatedUniversalSolution
    (N : ℕ) (m : SystemIndex n p →₀ ℕ) (e : ParamIndex n p →₀ ℕ)
    (u : RecursiveCoeffVar n p)
    (hu : u ∈ (MvPowerSeries.coeff e
      (m.prod fun s q =>
        (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s) ^ q)).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d⟩ => paramDegree d < N := by
  classical
  -- Rewrite the `Finsupp` product over `m.support`, then apply the finite-product support lemma
  -- with the cutoff bound for each substituted power factor.
  cases u with
  | inl a =>
      trivial
  | inr a =>
      simpa [Finsupp.prod] using
        (vars_coeff_prod_below_cutoff
          (n := n) (p := p)
          (f := fun s =>
            (solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s) ^ m s)
          (s := m.support)
          (N := N)
          (hf := by
            intro s hs e' u' hu'
            cases u' with
            | inl a =>
                trivial
            | inr a =>
                simpa using vars_coeff_pow_below_cutoff
                  (n := n) (p := p)
                  (φ := solutionSubst (truncatedUniversalSolution (n := n) (p := p) N) s)
                  (N := N)
                  (hφ := by
                    intro e'' u'' hu''
                    cases u'' with
                    | inl a =>
                        trivial
                    | inr a =>
                        simpa using vars_coeff_solutionSubst_truncatedUniversalSolution
                          (n := n) (p := p) N s e'' (Sum.inr a) hu'')
                  (q := m s) (e := e') (u := Sum.inr a) hu')
          (e := e) (u := Sum.inr a) hu)

/-- Helper for Exercise 2: coefficients of the renamed universal linear coefficient series only
involve primitive system variables. -/
lemma vars_coeff_rename_universalLinearCoeff_left
    (j i : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i))).vars) :
    False := by
  classical
  let ez : Fin p ↪ SystemIndex n p := ⟨zToSystem, by
    intro a b h
    simpa [zToSystem] using h⟩
  by_cases hpre : ∃ d : Fin p →₀ ℕ, Finsupp.embDomain ez d = e
  · rcases hpre with ⟨d, rfl⟩
    -- On coefficients in the range of `zToSystem`, renaming simply recovers the unique universal
    -- linear coefficient indexed by that `z`-multi-index.
    have hcoeff :
        MvPowerSeries.coeff (Finsupp.embDomain ez d)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
            (universalLinearCoeff (n := n) (p := p) j i)) =
          MvPowerSeries.coeff d
            (universalLinearCoeff (n := n) (p := p) j i) := by
      simpa [ez] using
        (MvPowerSeries.coeff_embDomain_rename
          (e := ez)
          (p := universalLinearCoeff (n := n) (p := p) j i)
          (x := d))
    rw [hcoeff] at hu
    change (Sum.inr (j', d') : RecursiveCoeffVar n p) ∈
      (MvPolynomial.X (Sum.inl (Sum.inl (j, i, d)))).vars at hu
    have : False := by
      simpa [MvPolynomial.vars_X] using hu
    exact this
  · have hrange : e ∉ Set.range (Finsupp.mapDomain zToSystem) := by
      intro he
      rcases he with ⟨d, hd⟩
      exact hpre ⟨d, by simpa [Finsupp.embDomain_eq_mapDomain, ez] using hd⟩
    -- Off the `zToSystem` range, the renamed coefficient vanishes.
    rw [MvPowerSeries.coeff_rename_eq_zero
      (f := zToSystem)
      (p := universalLinearCoeff (n := n) (p := p) j i)
      hrange] at hu
    simpa using hu

/-- Helper for Exercise 2: coefficients of a universal linear summand only involve primitive
system variables. -/
lemma vars_coeff_universalLinearTerm_left
    (j i : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
          MvPowerSeries.X (Sum.inr (Sum.inl i)))).vars) :
    False := by
  classical
  let yIndex : SystemIndex n p := Sum.inr (Sum.inl i)
  let yMonomial : SystemIndex n p →₀ ℕ := Finsupp.single yIndex 1
  have hcoeff :
      MvPowerSeries.coeff e
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
          MvPowerSeries.X yIndex) =
        if yMonomial ≤ e then
          MvPowerSeries.coeff (e - yMonomial)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                (universalLinearCoeff (n := n) (p := p) j i)) *
            (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ)
        else
          0 := by
    -- The explicit `y_i` factor shifts the coefficient by one unit in that `y`-direction.
    simpa [yIndex, yMonomial, MvPowerSeries.X] using
      (MvPowerSeries.coeff_mul_monomial
        (m := e)
        (φ := MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i))
        (n := yMonomial)
        (a := (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ)))
  rw [hcoeff] at hu
  split_ifs at hu with hmono
  · -- After peeling off the explicit `y_i`, the remaining renamed coefficient is already known to
    -- use only left primitive-system variables.
    have hmul :
        Sum.inr ⟨j', d'⟩ ∈
          (MvPowerSeries.coeff (e - yMonomial)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                (universalLinearCoeff (n := n) (p := p) j i))).vars ∪
            (1 : MvPolynomial (RecursiveCoeffVar n p) ℤ).vars := by
      exact (MvPolynomial.vars_mul _ _) hu
    rcases Finset.mem_union.mp hmul with hleft | hright
    · exact vars_coeff_rename_universalLinearCoeff_left
        (n := n) (p := p) j i (e - yMonomial) j' d' hleft
    · simpa using hright
  · simpa using hu

/-- Helper for Exercise 2: coefficients of the renamed universal higher remainder only involve
primitive system variables. -/
lemma vars_coeff_rename_universalHigherCoeff_left
    (j : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
          (universalHigherCoeff (n := n) (p := p) j))).vars) :
    False := by
  classical
  let eh : Fin n ⊕ Fin p ↪ SystemIndex n p := ⟨higherToSystem, by
    intro a b h
    cases a <;> cases b <;> simpa [higherToSystem, zToSystem] using h⟩
  by_cases hpre : ∃ d : (Fin n ⊕ Fin p) →₀ ℕ, Finsupp.embDomain eh d = e
  · rcases hpre with ⟨d, rfl⟩
    -- On coefficients in the range of `higherToSystem`, renaming recovers the unique universal
    -- higher coefficient indexed by that `(x, z)`-multi-index.
    have hcoeff :
        MvPowerSeries.coeff (Finsupp.embDomain eh d)
          (MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
            (universalHigherCoeff (n := n) (p := p) j)) =
          MvPowerSeries.coeff d
            (universalHigherCoeff (n := n) (p := p) j) := by
      simpa [eh] using
        (MvPowerSeries.coeff_embDomain_rename
          (e := eh)
          (p := universalHigherCoeff (n := n) (p := p) j)
          (x := d))
    rw [hcoeff] at hu
    change (Sum.inr (j', d') : RecursiveCoeffVar n p) ∈
      (if 2 ≤ xDegree d then MvPolynomial.X (Sum.inl (Sum.inr (j, d))) else 0).vars at hu
    by_cases hdeg : 2 ≤ xDegree d
    · have : False := by
        simpa [hdeg, MvPolynomial.vars_X] using hu
      exact this
    · have : False := by
        simpa [hdeg] using hu
      exact this
  · have hrange : e ∉ Set.range (Finsupp.mapDomain higherToSystem) := by
      intro he
      rcases he with ⟨d, hd⟩
      exact hpre ⟨d, by simpa [Finsupp.embDomain_eq_mapDomain, eh] using hd⟩
    -- Off the `higherToSystem` range, the renamed higher coefficient vanishes.
    rw [MvPowerSeries.coeff_rename_eq_zero
      (f := higherToSystem)
      (p := universalHigherCoeff (n := n) (p := p) j)
      hrange] at hu
    simpa using hu

/-- Helper for Exercise 2: a coefficient of the universal recursive system only involves primitive
system coefficient variables, never solution-coefficient variables. -/
lemma vars_coeff_universalRecursiveImplicitSystem_left
    (j : Fin n) (e : SystemIndex n p →₀ ℕ) (j' : Fin n)
    (d' : ParamIndex n p →₀ ℕ)
    (hu : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e
        (universalRecursiveImplicitSystem (n := n) (p := p) j)).vars) :
    False := by
  classical
  let linearTerm : Fin n → MvPowerSeries (SystemIndex n p)
      (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
    fun i =>
      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
          (universalLinearCoeff (n := n) (p := p) j i) *
        MvPowerSeries.X (Sum.inr (Sum.inl i))
  let higherTerm : MvPowerSeries (SystemIndex n p)
      (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
    MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)
      (universalHigherCoeff (n := n) (p := p) j)
  have hu' : Sum.inr ⟨j', d'⟩ ∈
      (MvPowerSeries.coeff e ((∑ i : Fin n, linearTerm i) + higherTerm)).vars := by
    -- Route correction: rather than chasing support inside the universal system directly, split it
    -- into its linear and higher parts and handle their coefficients separately.
    simpa [RecursiveImplicitSystem.toSeries, universalRecursiveImplicitSystem, linearTerm,
      higherTerm] using hu
  have hadd :
      (MvPowerSeries.coeff e ((∑ i : Fin n, linearTerm i) + higherTerm)).vars ⊆
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i)).vars ∪
          (MvPowerSeries.coeff e higherTerm).vars := by
    simpa using
      (MvPolynomial.vars_add_subset
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i))
        (MvPowerSeries.coeff e higherTerm))
  rcases Finset.mem_union.mp (hadd hu') with hlinear | hhigher
  · have hsum :
        (MvPowerSeries.coeff e (∑ i : Fin n, linearTerm i)).vars ⊆
          Finset.univ.biUnion fun i => (MvPowerSeries.coeff e (linearTerm i)).vars := by
      simpa [linearTerm] using
        (MvPolynomial.vars_sum_subset
          (t := Finset.univ)
          (φ := fun i : Fin n => MvPowerSeries.coeff e (linearTerm i)))
    rcases Finset.mem_biUnion.mp (hsum hlinear) with ⟨i, hi, hui⟩
    exact vars_coeff_universalLinearTerm_left
      (n := n) (p := p) j i e j' d' (by simpa [linearTerm] using hui)
  · exact vars_coeff_rename_universalHigherCoeff_left
      (n := n) (p := p) j e j' d' (by simpa [higherTerm] using hhigher)

/-- Helper for Exercise 2: any solution-coefficient variable appearing in the universal degree-`d`
coefficient polynomial comes from the cutoff solution, hence has strictly smaller total parameter
degree than `d`. -/
theorem vars_recursiveCoefficientPolynomial
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) (u : RecursiveCoeffVar n p)
    (hu : u ∈ (recursiveCoefficientPolynomial (n := n) (p := p) j d).vars) :
    match u with
    | Sum.inl _ => True
    | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d := by
  classical
  -- Expand the universal substituted coefficient into the finite substitution sum, then split a
  -- surviving variable between the universal-system coefficient factor and the substituted
  -- monomial-product factor.
  cases u with
  | inl a =>
      trivial
  | inr a =>
      rcases a with ⟨j', d'⟩
      let N : ℕ := paramDegree d
      let aSubst :
          SystemIndex n p →
            MvPowerSeries (ParamIndex n p) (MvPolynomial (RecursiveCoeffVar n p) ℤ) :=
        solutionSubst (truncatedUniversalSolution (n := n) (p := p) N)
      have hSubst : MvPowerSeries.HasSubst aSubst := by
        simpa [aSubst, N] using truncatedUniversalSolution_hasSubst (n := n) (p := p) N
      let G : (SystemIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ :=
        fun m =>
          MvPowerSeries.coeff m
              (universalRecursiveImplicitSystem (n := n) (p := p) j) •
            MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)
      have hGfinite : G.HasFiniteSupport := by
        simpa [G, aSubst, N] using
          (MvPowerSeries.coeff_subst_finite hSubst
            (universalRecursiveImplicitSystem (n := n) (p := p) j) d)
      rw [recursiveCoefficientPolynomial, MvPowerSeries.coeff_subst hSubst,
        finsum_eq_sum G hGfinite] at hu
      have hsum :
          (∑ m ∈ hGfinite.toFinset, G m).vars ⊆
            hGfinite.toFinset.biUnion fun m => (G m).vars := by
        simpa [G] using
          (MvPolynomial.vars_sum_subset
            (t := hGfinite.toFinset)
            (φ := G))
      rcases Finset.mem_biUnion.mp (hsum hu) with ⟨m, hm, hmu⟩
      have hmul :
          (G m).vars ⊆
            (MvPowerSeries.coeff m
                (universalRecursiveImplicitSystem (n := n) (p := p) j)).vars ∪
              (MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)).vars := by
        simpa [G, smul_eq_mul] using
          (MvPolynomial.vars_mul
            (MvPowerSeries.coeff m
              (universalRecursiveImplicitSystem (n := n) (p := p) j))
            (MvPowerSeries.coeff d (m.prod fun s q => (aSubst s) ^ q)))
      rcases Finset.mem_union.mp (hmul hmu) with hleft | hright
      · exact False.elim <|
          vars_coeff_universalRecursiveImplicitSystem_left
            (n := n) (p := p) j m j' d' hleft
      · simpa [aSubst, N] using
          vars_coeff_finsuppProd_solutionSubst_truncatedUniversalSolution
            (n := n) (p := p) N m d (Sum.inr ⟨j', d'⟩) hright

/-- Exercise 2 (1): for the recursive system `(3)`, the coefficients of a formal solution `(4)`
are characterized by a family of integer-coefficient polynomials in the coefficients of `(3)` and
in lower-total-degree coefficients of the same solution. -/
theorem exists_recursive_coefficient_polynomials
    (S : RecursiveImplicitSystem 𝕜 n p) :
    ∃ Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ,
      (∀ j d u,
        u ∈ (Q j d).vars →
          match u with
          | Sum.inl _ => True
          | Sum.inr ⟨_, d'⟩ =>
              paramDegree d' < paramDegree d) ∧
      ∀ x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
        FormalImplicitSolution S x ↔
          RecursiveCoefficientRecurrence S Q x := by
  classical
  let Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ :=
    recursiveCoefficientPolynomial (n := n) (p := p)
  refine ⟨Q, ?_, ?_⟩
  · intro j d u hu
    -- Route correction: the variable bound is read directly from the existing universal cutoff
    -- polynomial, rather than by redesigning the universal system encoding.
    cases u with
    | inl a =>
        trivial
    | inr a =>
        simpa [Q] using
          vars_recursiveCoefficientPolynomial (n := n) (p := p) j d (Sum.inr a) hu
  · intro x
    constructor
    · intro hx
      refine ⟨hx.constantCoeff_eq_zero, ?_⟩
      intro j d hd
      -- Evaluate the universal degree-`d` coefficient polynomial on the concrete cutoff solution.
      rw [show Q j d =
        recursiveCoefficientPolynomial (n := n) (p := p) j d by rfl]
      rw [eval_recursiveCoefficientPolynomial (S := S) (x := x) (j := j) (d := d)]
      -- The positive-degree coefficient is cutoff-invariant, so the recursive polynomial computes
      -- the same coefficient as the full substitution appearing in the formal-solution equation.
      simpa [hx.eq_subst j] using
        (coeff_subst_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x)
          hx.constantCoeff_eq_zero j d hd).symm
    · intro hx
      refine ⟨hx.constantCoeff_eq_zero, ?_⟩
      intro j
      ext d
      by_cases hd0 : paramDegree d = 0
      · -- The constant coefficient vanishes on both sides.
        have hd_eq : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hd0
        subst hd_eq
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx.constantCoeff_eq_zero,
          MvPowerSeries.constantCoeff_subst_eq_zero]
        · exact solutionSubst_hasSubst x hx.constantCoeff_eq_zero
        · intro s
          cases s with
          | inl j' =>
              exact hx.constantCoeff_eq_zero j'
          | inr u =>
              simp [solutionSubst]
        · -- Each right-hand side series has zero constant coefficient by construction.
          simpa using S.constantCoeff_toSeries j
      · have hd : 0 < paramDegree d := Nat.pos_iff_ne_zero.mpr hd0
        -- Reduce the positive-degree coefficient equality to the same cutoff substitution formula.
        rw [hx.coeff_eq_eval j d hd]
        rw [show Q j d =
          recursiveCoefficientPolynomial (n := n) (p := p) j d by rfl]
        rw [eval_recursiveCoefficientPolynomial (S := S) (x := x) (j := j) (d := d)]
        -- The same cutoff invariance identifies the recurrence value with the full substitution
        -- coefficient, which closes the positive-degree branch of the extensionality proof.
        exact coeff_subst_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x)
          hx.constantCoeff_eq_zero j d hd

/-- Exercise 2 (2): every recursive system `(3)` admits a unique formal solution `(4)`. -/
theorem existsUnique_formalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p) :
    ∃! x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
      FormalImplicitSolution S x := by
  -- TODO: once the coefficient-polynomial equivalence above is complete, use strong induction on
  -- `paramDegree d` to prove uniqueness and define the unique solution coefficientwise.
  sorry

end FormalRecursiveImplicitSystem

section RecursiveImplicitSystemMajorant

variable {𝕜 : Type u} [CommRing 𝕜] [Norm 𝕜]
variable {n p : ℕ}

/-- The positive-degree norm profile of a `z`-series, regrouped by total `z`-degree and shifted
so that the total-degree `q + 1` slice becomes the coefficient of `X^(q + 1)`. Its coefficients
are the sums of the norms of the coefficients on each total-degree slice, which is the source-
faithful majorant datum needed to reuse the canonical one-variable owner
`PowerSeries.IsMajorantSeries`. -/
noncomputable def linearTailNormProfile (f : MvPowerSeries (Fin p) 𝕜) : ℝ⟦X⟧ :=
  PowerSeries.mk fun
    | 0 => 0
    | q + 1 =>
        Finset.sum (Finset.finAntidiagonal p (q + 1)) fun e ↦
          ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f‖

/-- The norm profile of a series in `(x, z)`, regrouped by total `x`-degree and total `z`-degree.
Its coefficient at `(a, b)` is the sum of the norms of the original coefficients whose total
`x`-degree is `a` and total `z`-degree is `b`, so the canonical two-variable owner
`MvPowerSeries.IsMajorantSeries` records the intended majorant inequality without allowing
cancellation inside a slice. -/
noncomputable def higherNormProfile (f : MvPowerSeries (Fin n ⊕ Fin p) 𝕜) : ℝ⟦X,Y⟧ :=
  fun d ↦
    Finset.sum ((Finset.finAntidiagonal n (d 0)).product (Finset.finAntidiagonal p (d 1)))
      fun e ↦
      ‖MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (Sum.elim e.1 e.2 : Fin n ⊕ Fin p → ℕ)) f‖

/-- The positive-degree tail of the geometric one-variable majorant attached to the parameters `M`
and `R`, with zero constant coefficient so that the canonical owner
`PowerSeries.IsMajorantSeries` applies to the linear-tail profile. -/
noncomputable def linearTailMajorantSeries (M R : NNReal) : NNReal⟦X⟧ :=
  PowerSeries.mk fun
    | 0 => 0
    | q + 1 => M * R⁻¹ ^ (q + 1)

/-- The quadratic two-variable majorant attached to the parameters `M` and `R`. -/
noncomputable def higherMajorantSeries (M R : NNReal) : NNReal⟦X,Y⟧ :=
  fun d ↦
    if 2 ≤ d 0 then
      M * R⁻¹ ^ (d 0 + d 1)
    else
      0

namespace RecursiveImplicitSystem

/-- Source-facing majorant data for the recursive system `(3)`: the constant term of each linear
coefficient series `Γᵢⱼ(z)` is bounded directly, the sum of the coefficient norms on each positive
total-`z`-degree slice is controlled by the canonical one-variable majorant owner from Section 27,
and the sum of the coefficient norms on each fixed total-`x`/total-`z` slice of the nonlinear
remainder is controlled by the canonical two-variable owner. -/
class IsMajorizedBy (S : RecursiveImplicitSystem 𝕜 n p) (M R : NNReal) : Prop where
  linearCoeff_constant_le (j i : Fin n) :
    ‖MvPowerSeries.constantCoeff (S.linearCoeff j i)‖ ≤ (M : ℝ)
  linearCoeff_tail_norm_isMajorantSeries (j i : Fin n) :
    PowerSeries.IsMajorantSeries
      (linearTailNormProfile (S.linearCoeff j i)) (linearTailMajorantSeries M R)
  higher_norm_isMajorantSeries (j : Fin n) :
    MvPowerSeries.IsMajorantSeries
      (higherNormProfile (S.higher j)) (higherMajorantSeries M R)

end RecursiveImplicitSystem

namespace FormalImplicitSolution

/-- A family of `NNReal`-coefficient series majorizes a family of formal series coefficientwise. -/
def IsMajorizedBy
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal) : Prop :=
  ∀ j d, ‖MvPowerSeries.coeff d (x j)‖ ≤ ((Ξ j) d : ℝ)

end FormalImplicitSolution

end RecursiveImplicitSystemMajorant

section ScalarQuadraticMajorant

variable {𝕜 : Type u} [CommRing 𝕜] [Norm 𝕜]
variable {n p : ℕ}

/-- The sum `Y₁ + ⋯ + Yₙ` of the parameter variables in the scalar quadratic majorant equation. -/
noncomputable def paramYSum : MvPowerSeries (ParamIndex n p) ℝ :=
  ∑ j : Fin n, MvPowerSeries.X (Sum.inl j)

/-- The sum `Z₁ + ⋯ + Zₚ` of the parameter variables in the scalar quadratic majorant equation. -/
noncomputable def paramZSum : MvPowerSeries (ParamIndex n p) ℝ :=
  ∑ k : Fin p, MvPowerSeries.X (Sum.inr k)

/-- The scalar majorant operator obtained from the family majorant after the symmetric
specialization `X₁ = ⋯ = Xₙ = X`. -/
noncomputable def scalarMajorantOperator
    (M R : NNReal) (X : MvPowerSeries (ParamIndex n p) NNReal) :
    MvPowerSeries (ParamIndex n p) ℝ :=
  let Xr := MvPowerSeries.map NNReal.toRealHom X
  MvPowerSeries.C (M : ℝ) *
      (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum)⁻¹ *
    (paramYSum +
      (1 - MvPowerSeries.C (((n : ℕ) : ℝ) / (R : ℝ)) * Xr)⁻¹ -
      1 -
      MvPowerSeries.C (((n : ℕ) : ℝ) / (R : ℝ)) * Xr)

/-- Bridge/view layer: a scalar `NNReal`-valued majorant solves the symmetric quadratic equation
and dominates each component of a family majorant. -/
def IsScalarMajorantBridge
    (Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal)
    (M R : NNReal) (X : MvPowerSeries (ParamIndex n p) NNReal) : Prop :=
  MvPowerSeries.map NNReal.toRealHom X = scalarMajorantOperator M R X ∧
    ∀ j d, ((Ξ j) d : ℝ) ≤ (X d : ℝ)

end ScalarQuadraticMajorant

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Exercise 2 (3): if the recursive system `(3)` is already equipped with source-facing majorant
data `M, R > 0`, then every formal solution admits a family majorant together with a scalar
quadratic majorant bridge for the symmetric specialization `X₁ = ⋯ = Xₙ = X`. -/
theorem exists_scalar_majorant_of_formalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal)
    (hM : 0 < M)
    (hR : 0 < R)
    (hS : S.IsMajorizedBy M R)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x) :
    ∃ Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal,
      FormalImplicitSolution.IsMajorizedBy x Ξ ∧
      ∃ X : MvPowerSeries (ParamIndex n p) NNReal,
        IsScalarMajorantBridge Ξ M R X := by
  -- TODO: first finish the formal recursive solution theorem above, then run the same total-degree
  -- recursion on the scalar majorant operator and compare coefficients inductively.
  sorry

end ScalarQuadraticMajorantExistence
