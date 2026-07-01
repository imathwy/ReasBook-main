import cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import cartan.IV.section13.«0007_Proposition_3_I»
import Mathlib

open Filter
open Set
open scoped Topology BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

/-- A local holomorphic solution of a first-order system on an open set `U`, with graph contained
in the coefficient domain `Ω` and prescribed initial value `b` at `x₀`. -/
structure IsHolomorphicSystemSolutionOn {n : ℕ}
    (Ω : Set (ℂ × (Fin n → ℂ))) (f : ℂ → (Fin n → ℂ) → Fin n → ℂ)
    (x₀ : ℂ) (b : Fin n → ℂ) (U : Set ℂ) (φ : ℂ → Fin n → ℂ) : Prop where
  isOpen : IsOpen U
  mem : x₀ ∈ U
  analytic : AnalyticOnNhd ℂ φ U
  mapsTo : MapsTo (fun z ↦ (z, φ z)) U Ω
  initial : φ x₀ = b
  deriv_eq {z} (hz : z ∈ U) : HasDerivAt φ (f z (φ z)) z

/-- A local holomorphic solution germ of the first-order system `φ' = f (x, φ)` with initial
value `b` at `x₀`, given by an open-neighborhood representative satisfying the open-set solution
predicate. -/
def IsHolomorphicSystemSolution {n : ℕ}
    (Ω : Set (ℂ × (Fin n → ℂ))) (f : ℂ → (Fin n → ℂ) → Fin n → ℂ)
    (x₀ : ℂ) (b : Fin n → ℂ) (φ : Germ (𝓝 x₀) (Fin n → ℂ)) : Prop :=
  ∃ U : Set ℂ, ∃ ψ : ℂ → Fin n → ℂ,
    IsHolomorphicSystemSolutionOn Ω f x₀ b U ψ ∧
    (ψ : Germ (𝓝 x₀) (Fin n → ℂ)) = φ

/-- The open-set solution predicate induces the corresponding local solution germ. -/
theorem IsHolomorphicSystemSolutionOn.isHolomorphicSystemSolution {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ}
    {x₀ : ℂ} {b : Fin n → ℂ} {U : Set ℂ} {φ : ℂ → Fin n → ℂ}
    (h : IsHolomorphicSystemSolutionOn Ω f x₀ b U φ) :
    IsHolomorphicSystemSolution Ω f x₀ b (φ : Germ (𝓝 x₀) (Fin n → ℂ)) := by
  exact ⟨U, φ, h, rfl⟩

private noncomputable def pairToFinsupp : ℕ × ℕ ≃ (Fin 2 →₀ ℕ) :=
  { toFun := fun n ↦ Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _)
    invFun := fun d ↦ (d 0, d 1)
    left_inv := fun _ ↦ rfl
    right_inv := fun d ↦ Finsupp.ofSupportFinite_fin_two_eq d }

/-- Helper for Theorem I: the pair `(p, q)` is the canonical `Fin 2 →₀ ℕ` exponent encoding the
monomial `X^p Y^q`. -/
private theorem pairToFinsupp_apply (n : ℕ × ℕ) :
    pairToFinsupp n = Finsupp.single 0 n.1 + Finsupp.single 1 n.2 := by
  -- Check the two coordinates directly on the finite index type `Fin 2`.
  ext i
  fin_cases i <;> simp [pairToFinsupp, Finsupp.ofSupportFinite_coe]

/-- Helper for Theorem I: the source-facing coefficient `coeffXY` is the canonical coefficient
indexed by the corresponding finitely supported exponent. -/
private theorem coeffXY_eq_coeff_pairToFinsupp {R : Type u} [Semiring R] (F : R⟦X,Y⟧)
    (n : ℕ × ℕ) :
    MvPowerSeries.coeffXY F n.1 n.2 = MvPowerSeries.coeff (pairToFinsupp n) F := by
  -- Rewrite the pair index by the explicit `Fin 2 →₀ ℕ` exponent.
  rw [MvPowerSeries.coeffXY, pairToFinsupp_apply, MvPowerSeries.coeff_apply]

/-- Helper for Theorem I: after reindexing by a pair, substituting `X` and `φ` produces the
monomial `X^p * φ^q`. -/
private theorem pairToFinsupp_prod_subst {R : Type u} [CommRing R] (φ : PowerSeries R)
    (n : ℕ × ℕ) :
    (pairToFinsupp n).prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e) =
      (X : PowerSeries R) ^ n.1 * φ ^ n.2 := by
  -- The product over the two coordinates is exactly the `X`-factor times the `φ`-factor.
  simp [pairToFinsupp_apply, Fin.prod_univ_two, mul_comm]

/-- Helper for Theorem I: if the total degree of a substituted monomial exceeds `n`, then its
`n`th coefficient vanishes. -/
private theorem coeff_prod_subst_eq_zero_of_lt_total_degree {R : Type u} [CommRing R]
    {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (d : Fin 2 →₀ ℕ) {n : ℕ}
    (hdeg : n < d 0 + d 1) :
    PowerSeries.coeff n (d.prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e)) = 0 := by
  -- Rewrite the `Fin 2` product into the concrete monomial `X^(d 0) * φ^(d 1)`.
  have hprod :
      d.prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e) =
        (X : PowerSeries R) ^ d 0 * φ ^ d 1 := by
    simpa [pairToFinsupp.right_inv d] using
      pairToFinsupp_prod_subst (φ := φ) (n := (d 0, d 1))
  rw [hprod]
  -- The order of that monomial is at least the total degree `d 0 + d 1`.
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hdeg) <|
    calc
      (((d 0 + d 1 : ℕ)) : ℕ∞) = (d 0 : ℕ∞) + d 1 := by simp
      _ ≤ PowerSeries.order ((X : PowerSeries R) ^ d 0) +
            PowerSeries.order (φ ^ d 1) := by
          gcongr
          · exact PowerSeries.le_order_pow_of_constantCoeff_eq_zero (φ := (X : PowerSeries R))
              (d 0) (by simp)
          · exact PowerSeries.le_order_pow_of_constantCoeff_eq_zero (φ := φ) (d 1) hφ
      _ ≤ PowerSeries.order ((X : PowerSeries R) ^ d 0 * φ ^ d 1) := PowerSeries.order_mul_ge _ _

/-- Helper for Theorem I: a `Fin 2` exponent of total degree at most `n` lies in the triangular
range `0 ≤ p ≤ n`, `0 ≤ q ≤ n - p`. -/
private theorem pair_mem_triangular_range (d : Fin 2 →₀ ℕ) {n : ℕ}
    (hdeg : d 0 + d 1 ≤ n) :
    d 0 ∈ Finset.range (n + 1) ∧ d 1 ∈ Finset.range (n + 1 - d 0) := by
  -- The total-degree bound gives both coordinate bounds needed for the triangular region.
  refine ⟨by simp [Finset.mem_range]; omega, by simp [Finset.mem_range]; omega⟩

/-- Helper for Theorem I: truncating the substitution coefficient formula by total degree
reindexes the contributing `Fin 2` exponents directly by triangular pairs. -/
private theorem PowerSeries.coeff_subst_X_phi_eq_sum_triangular_pairs {R : Type u} [CommRing R]
    {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (F : R⟦X,Y⟧) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) =
      ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeff (pairToFinsupp (p, q)) F *
          PowerSeries.coeff n
            ((pairToFinsupp (p, q)).prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e)) := by
  classical
  let hs : MvPowerSeries.HasSubst (![(X : PowerSeries R), φ]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
      fin_cases i
      · simpa [PowerSeries.constantCoeff] using (PowerSeries.constantCoeff_X (R := R))
      · simpa [PowerSeries.constantCoeff] using hφ
  let s : Finset ((p : ℕ) × ℕ) :=
    (Finset.range (n + 1)).sigma fun p ↦ Finset.range (n + 1 - p)
  let t : Finset (Fin 2 →₀ ℕ) :=
    s.image fun pq ↦ pairToFinsupp (pq.1, pq.2)
  have hcoeff :
      PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) =
        finsum
          (fun d ↦
            MvPowerSeries.coeff d F *
              PowerSeries.coeff n (d.prod fun s e ↦ (![X, φ] s : PowerSeries R) ^ e)) := by
    -- Specialize the multivariate substitution formula to the one-variable target index `n`.
    simpa [PowerSeries.coeff, smul_eq_mul] using
      (MvPowerSeries.coeff_subst hs F (Finsupp.single () n))
  -- Replace the infinite substitution sum by the finite triangular region singled out by the
  -- total-degree bound from the source proof.
  rw [hcoeff, finsum_eq_sum_of_support_subset (s := t)]
  · -- Reindex the remaining finite sum by the triangular pair coordinates `(p, q)`.
    have hpair_inj :
        Function.Injective (fun pq : (p : ℕ) × ℕ ↦ pairToFinsupp (pq.1, pq.2)) := by
      intro a b hab
      cases a with
      | mk pa qa =>
          cases b with
          | mk pb qb =>
              have hvals : (pa, qa) = (pb, qb) := pairToFinsupp.injective hab
              cases hvals
              rfl
    have hsum :
        Finset.sum t
            (fun d ↦
              MvPowerSeries.coeff d F *
                PowerSeries.coeff n (d.prod fun s e ↦ (![X, φ] s : PowerSeries R) ^ e)) =
          Finset.sum s
            (fun pq ↦
              MvPowerSeries.coeff (pairToFinsupp (pq.1, pq.2)) F *
                PowerSeries.coeff n
                  ((pairToFinsupp (pq.1, pq.2)).prod
                    fun s e ↦ (![X, φ] s : PowerSeries R) ^ e)) := by
      dsimp [t]
      rw [Finset.sum_image]
      · intro a ha b hb hab
        exact hpair_inj hab
    rw [hsum]
    simpa [s, Finset.sum_sigma', pairToFinsupp_apply]
  · -- Any nonzero summand must satisfy the total-degree bound `d 0 + d 1 ≤ n`.
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hdt
    have hdeg : n < d 0 + d 1 := by
      have hnot : ¬ d 0 + d 1 ≤ n := by
        intro hle
        have hmem := pair_mem_triangular_range d hle
        have : d ∈ t := by
          dsimp [t]
          rw [Finset.mem_image]
          refine ⟨⟨d 0, d 1⟩, ?_, ?_⟩
          · exact Finset.mem_sigma.mpr ⟨hmem.1, hmem.2⟩
          · exact pairToFinsupp.right_inv d
        exact hdt this
      omega
    have hzero :
        PowerSeries.coeff n (d.prod fun s e ↦ (![X, φ] s : PowerSeries R) ^ e) = 0 :=
      coeff_prod_subst_eq_zero_of_lt_total_degree hφ d hdeg
    have hprod :
        d.prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e) =
          (X : PowerSeries R) ^ d 0 * φ ^ d 1 := by
      simpa [pairToFinsupp.right_inv d] using
        pairToFinsupp_prod_subst (φ := φ) (n := (d 0, d 1))
    have hzero' : PowerSeries.coeff n ((X : PowerSeries R) ^ d 0 * φ ^ d 1) = 0 := by
      simpa [hprod] using hzero
    exact hd <| by simp [hprod, hzero']

/-- Helper for Theorem I: over a commutative ring, the canonical substitution `F(X, φ(X))` has
the expected source-facing coefficient formula. -/
private theorem PowerSeries.coeff_subst_X_phi_eq_sum_range {R : Type u} [CommRing R]
    {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (F : R⟦X,Y⟧) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) =
      ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q) := by
  -- First truncate the canonical substitution formula to the triangular region dictated by total
  -- degree, then rewrite each surviving term into the source-facing `(p, q)` coefficient.
  rw [PowerSeries.coeff_subst_X_phi_eq_sum_triangular_pairs hφ F n]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  -- On the triangular region, the substituted monomial is exactly `X^p * φ^q`, and
  -- `coeff_X_pow_mul'` reads its `n`th coefficient as the coefficient of `φ^q` at degree `n - p`.
  rw [← coeffXY_eq_coeff_pairToFinsupp, pairToFinsupp_prod_subst]
  rw [PowerSeries.coeff_X_pow_mul']
  have hp_le : p ≤ n := by
    simp at hp
    omega
  simp [hp_le]

/-- Helper for Theorem I: a one-variable formal power series with vanishing constant term solving
the recentered formal differential equation `y' = F(x, y)`. -/
private class PowerSeries.IsFormalRecenteredOdeSolution {R : Type u} [CommSemiring R]
    (φ : PowerSeries R) (F : R⟦X,Y⟧) : Prop where
  constantCoeff_eq_zero : φ.constantCoeff = 0
  equation (n : ℕ) :
    PowerSeries.coeff n (d⁄dX R φ) =
      ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q)

namespace PowerSeries.IsFormalRecenteredOdeSolution

/-- Helper for Theorem I: a formal recentered solution has zero constant coefficient. -/
private theorem coeff_zero {R : Type u} [CommSemiring R] {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalRecenteredOdeSolution φ F) :
    coeff 0 φ = 0 := by
  simpa [coeff_zero_eq_constantCoeff_apply] using hφ.constantCoeff_eq_zero

/-- Helper for Theorem I: over a commutative ring, the source-facing coefficient equation is the
canonical substitution identity. -/
private theorem equation_eq_subst {R : Type u} [CommRing R] {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalRecenteredOdeSolution φ F) :
    d⁄dX R φ = MvPowerSeries.subst ![(X : PowerSeries R), φ] F := by
  ext n
  rw [hφ.equation, PowerSeries.coeff_subst_X_phi_eq_sum_range hφ.constantCoeff_eq_zero]

end PowerSeries.IsFormalRecenteredOdeSolution

/-- Helper for Theorem I: multiplying by the rational inverse of `n + 1` cancels the
corresponding natural-number scalar in any `ℚ`-algebra. -/
private theorem rational_inverse_succ_mul_natCast {R : Type u} [CommRing R] [Algebra ℚ R]
    (n : ℕ) :
    algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * (n + 1 : R) = 1 := by
  -- Move the natural-number scalar back into `ℚ`, then cancel there.
  rw [show (n + 1 : R) = algebraMap ℚ R (n + 1 : ℚ) by norm_num, ← map_mul, inv_mul_cancel₀]
  · norm_num
  · exact_mod_cast Nat.succ_ne_zero n

/-- Helper for Theorem I: if two series agree through degree `n`, then the same is true for
every power of those series through degree `n`. -/
private theorem coeff_pow_eq_of_coeff_eq_upto {R : Type u} [CommSemiring R]
    {φ ψ : PowerSeries R} {n : ℕ}
    (hEq : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m ψ) :
    ∀ q k, k ≤ n → PowerSeries.coeff k (φ ^ q) = PowerSeries.coeff k (ψ ^ q)
  | q, k, hk => by
      -- Expand the coefficient of a power by the canonical antidiagonal formula.
      rw [PowerSeries.coeff_pow, PowerSeries.coeff_pow]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hl' := Finset.mem_finsuppAntidiag.mp hl
      have hli : l i ≤ k := by
        rw [← hl'.1]
        exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
      exact hEq (l i) (hli.trans hk)

/-- Helper for Theorem I: the degree-`n` coefficient of `F(X, φ(X))` only depends on the
coefficients of `φ` through degree `n`. -/
private theorem subst_coeff_eq_of_coeff_eq_upto {R : Type u} [CommRing R]
    {φ ψ : PowerSeries R} {F : R⟦X,Y⟧} {n : ℕ}
    (hφ : PowerSeries.constantCoeff φ = 0) (hψ : PowerSeries.constantCoeff ψ = 0)
    (hEq : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m ψ) :
    PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) =
      PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), ψ] F) := by
  -- Rewrite both substitution coefficients by the same finite coefficient sum.
  rw [PowerSeries.coeff_subst_X_phi_eq_sum_range hφ,
    PowerSeries.coeff_subst_X_phi_eq_sum_range hψ]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  congr 1
  exact coeff_pow_eq_of_coeff_eq_upto hEq q (n - p) (Nat.sub_le _ _)

/-- Helper for Theorem I: a formal recentered solution determines its next coefficient from the
degree-`n` coefficient of the substituted right-hand side. -/
private theorem formal_recentered_solution_next_coeff_eq {R : Type u} [CommRing R] [Algebra ℚ R]
    {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalRecenteredOdeSolution φ F) (n : ℕ) :
    PowerSeries.coeff (n + 1) φ =
      algebraMap ℚ R ((n + 1 : ℚ)⁻¹) *
        PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
  -- First rewrite the coefficient equation into the canonical substitution form.
  have hEq : PowerSeries.coeff (n + 1) φ * (n + 1 : R) =
      PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
    calc
      PowerSeries.coeff (n + 1) φ * (n + 1 : R) = PowerSeries.coeff n (d⁄dX R φ) := by
        rw [PowerSeries.coeff_derivative]
      _ =
          ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
            MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q) := hφ.equation n
      _ = PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
        symm
        exact PowerSeries.coeff_subst_X_phi_eq_sum_range hφ.constantCoeff_eq_zero F n
  -- Then multiply by the rational inverse of `n + 1` and simplify the scalar cancellation.
  calc
    PowerSeries.coeff (n + 1) φ
        = (PowerSeries.coeff (n + 1) φ) *
            ((n + 1 : R) * algebraMap ℚ R ((n + 1 : ℚ)⁻¹)) := by
              rw [mul_comm (n + 1 : R), rational_inverse_succ_mul_natCast]
              simp
    _ = (PowerSeries.coeff (n + 1) φ * (n + 1 : R)) *
          algebraMap ℚ R ((n + 1 : ℚ)⁻¹) := by
            simp [mul_assoc]
    _ =
        PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) *
          algebraMap ℚ R ((n + 1 : ℚ)⁻¹) := by rw [hEq]
    _ =
        algebraMap ℚ R ((n + 1 : ℚ)⁻¹) *
          PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
            simp [mul_comm]

/-- Helper for Theorem I: a formal recentered solution with vanishing constant term is unique once
the coefficient recursion for successive terms is fixed. -/
private theorem formal_recentered_solution_unique {R : Type u} [CommRing R] [Algebra ℚ R]
    {φ ψ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalRecenteredOdeSolution φ F)
    (hψ : PowerSeries.IsFormalRecenteredOdeSolution ψ F) :
    φ = ψ := by
  -- Compare coefficients inductively: the next coefficient is forced by the common prefix.
  have hcoeff : ∀ n, ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m ψ := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        simp [PowerSeries.IsFormalRecenteredOdeSolution.coeff_zero hφ,
          PowerSeries.IsFormalRecenteredOdeSolution.coeff_zero hψ]
    | succ n ih =>
        intro m hm
        by_cases hmn : m ≤ n
        · exact ih m hmn
        · have hm_eq : m = n + 1 := by omega
          subst hm_eq
          rw [formal_recentered_solution_next_coeff_eq hφ,
            formal_recentered_solution_next_coeff_eq hψ]
          congr 1
          exact subst_coeff_eq_of_coeff_eq_upto hφ.constantCoeff_eq_zero
            hψ.constantCoeff_eq_zero ih
  ext m
  exact hcoeff m m le_rfl

/-- Helper for Theorem I: the recursive step chooses the next coefficient from the current
substituted right-hand side. -/
private noncomputable def formalRecenteredSolutionStepCoeff {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) (φ : PowerSeries R) (n : ℕ) : R :=
  algebraMap ℚ R ((n + 1 : ℚ)⁻¹) *
    PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F)

/-- Helper for Theorem I: the `n`th approximant records the first `n` recursively determined
coefficients of the desired formal solution. -/
private noncomputable def formalRecenteredSolutionApproximant {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 =>
      formalRecenteredSolutionApproximant F n +
        C (formalRecenteredSolutionStepCoeff F (formalRecenteredSolutionApproximant F n) n) *
          X ^ (n + 1)

/-- Helper for Theorem I: each recursive approximant still has zero constant coefficient. -/
private theorem formal_recentered_solution_approximant_constantCoeff_eq_zero {R : Type u}
    [CommRing R] [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∀ n, PowerSeries.constantCoeff (formalRecenteredSolutionApproximant F n) = 0
  | 0 => by
      -- The zeroth approximant is the zero series.
      simp [formalRecenteredSolutionApproximant]
  | n + 1 => by
      -- The correction term lives in degree `n + 1`, so it does not change the constant term.
      simp [formalRecenteredSolutionApproximant,
        formal_recentered_solution_approximant_constantCoeff_eq_zero F n]

/-- Helper for Theorem I: once a coefficient has been created, the next recursive step leaves it
unchanged. -/
private theorem formal_recentered_solution_approximant_coeff_step_eq {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff m (formalRecenteredSolutionApproximant F (n + 1)) =
      PowerSeries.coeff m (formalRecenteredSolutionApproximant F n) := by
  -- The step from `n` to `n + 1` only adds a monomial of degree `n + 1`.
  have hmne : m ≠ n + 1 := Nat.ne_of_lt (lt_of_le_of_lt hmn (Nat.lt_succ_self n))
  rw [formalRecenteredSolutionApproximant, (PowerSeries.coeff m).map_add,
    PowerSeries.coeff_C_mul_X_pow]
  simp [hmne]

/-- Helper for Theorem I: the `m`th coefficient of the `n`th approximant vanishes before the
recursive construction reaches stage `m`. -/
private theorem formal_recentered_solution_approximant_coeff_eq_zero_of_lt {R : Type u}
    [CommRing R] [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∀ n m, n < m → PowerSeries.coeff m (formalRecenteredSolutionApproximant F n) = 0
  | 0, m, hm => by
      -- The initial approximant is zero, so all positive coefficients vanish.
      simp [formalRecenteredSolutionApproximant]
  | n + 1, m, hm => by
      -- A stage strictly below `m` cannot create the `m`th coefficient.
      have hlt : n < m := lt_trans (Nat.lt_succ_self n) hm
      rw [formalRecenteredSolutionApproximant, (PowerSeries.coeff m).map_add,
        PowerSeries.coeff_C_mul_X_pow]
      simp [Nat.ne_of_gt hm, formal_recentered_solution_approximant_coeff_eq_zero_of_lt F n m hlt]

/-- Helper for Theorem I: after stage `m`, the `m`th coefficient is frozen forever. -/
private theorem formal_recentered_solution_approximant_stabilizes {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) (m k : ℕ) :
    PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + k)) =
      PowerSeries.coeff m (formalRecenteredSolutionApproximant F m) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Later stages only add strictly higher-degree terms, so the `m`th coefficient persists.
      have hstep :
          PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + k + 1)) =
            PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + k)) := by
        simpa [Nat.add_assoc] using
          formal_recentered_solution_approximant_coeff_step_eq (F := F) (m := m) (n := m + k)
            (Nat.le_add_right m k)
      calc
        PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + (k + 1)))
            = PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + k + 1)) := by
                simp [Nat.add_assoc]
        _ = PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + k)) := hstep
        _ = PowerSeries.coeff m (formalRecenteredSolutionApproximant F m) := ih

/-- Helper for Theorem I: the degree-`n` derivative equation is enforced exactly at the
`(n + 1)`st recursive approximant. -/
private theorem formal_recentered_solution_approximant_step_equation {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX R (formalRecenteredSolutionApproximant F (n + 1))) =
      PowerSeries.coeff n
        (MvPowerSeries.subst ![(X : PowerSeries R), formalRecenteredSolutionApproximant F n] F) := by
  -- The coefficient added at stage `n + 1` is chosen precisely to satisfy the degree-`n`
  -- differential equation.
  have hnext :
      PowerSeries.coeff (n + 1) (formalRecenteredSolutionApproximant F (n + 1)) =
        formalRecenteredSolutionStepCoeff F (formalRecenteredSolutionApproximant F n) n := by
    rw [formalRecenteredSolutionApproximant, (PowerSeries.coeff (n + 1)).map_add]
    have hzero :
        PowerSeries.coeff (n + 1) (formalRecenteredSolutionApproximant F n) = 0 := by
      exact formal_recentered_solution_approximant_coeff_eq_zero_of_lt (F := F) n (n + 1)
        (Nat.lt_succ_self n)
    simp [hzero]
  calc
    PowerSeries.coeff n (d⁄dX R (formalRecenteredSolutionApproximant F (n + 1)))
        = PowerSeries.coeff (n + 1) (formalRecenteredSolutionApproximant F (n + 1)) *
            (n + 1 : R) := by
              rw [PowerSeries.coeff_derivative]
    _ = formalRecenteredSolutionStepCoeff F (formalRecenteredSolutionApproximant F n) n *
          (n + 1 : R) := by
            rw [hnext]
    _ = PowerSeries.coeff n
          (MvPowerSeries.subst ![(X : PowerSeries R), formalRecenteredSolutionApproximant F n] F) := by
          dsimp [formalRecenteredSolutionStepCoeff]
          set a : R :=
            PowerSeries.coeff n
              (MvPowerSeries.subst ![(X : PowerSeries R), formalRecenteredSolutionApproximant F n] F)
          calc
            (algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * a) * (n + 1 : R)
                = (algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * (n + 1 : R)) * a := by
                    ac_rfl
            _ = a := by
                  rw [rational_inverse_succ_mul_natCast (R := R) n, one_mul]

/-- Helper for Theorem I: the final series reads each coefficient from the stage where the
recursive construction has already stabilized it. -/
private noncomputable def formalRecenteredSolutionSeries {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m (formalRecenteredSolutionApproximant F m)

/-- Helper for Theorem I: the stabilized series agrees with the `n`th approximant through degree
`n`. -/
private theorem formal_recentered_solution_series_coeff_eq_approximant {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff m (formalRecenteredSolutionSeries F) =
      PowerSeries.coeff m (formalRecenteredSolutionApproximant F n) := by
  -- The limiting coefficient is read from stage `m`, and every later stage keeps it fixed.
  calc
    PowerSeries.coeff m (formalRecenteredSolutionSeries F) =
        PowerSeries.coeff m (formalRecenteredSolutionApproximant F m) := by
          simp [formalRecenteredSolutionSeries]
    _ = PowerSeries.coeff m (formalRecenteredSolutionApproximant F (m + (n - m))) := by
          symm
          exact formal_recentered_solution_approximant_stabilizes (F := F) m (n - m)
    _ = PowerSeries.coeff m (formalRecenteredSolutionApproximant F n) := by
          rw [Nat.add_sub_of_le hmn]

/-- Helper for Theorem I: the recursively stabilized coefficients define a formal power series
solution of the recentered first-order differential equation. -/
private theorem exists_formal_recentered_series_solution {R : Type u} [CommRing R] [Algebra ℚ R]
    (F : R⟦X,Y⟧) :
    ∃ φ : R⟦X⟧, PowerSeries.IsFormalRecenteredOdeSolution φ F := by
  -- Route correction: build the source-faithful recursive approximants first, then read the
  -- stabilized coefficients from the limit series they determine.
  let φ : PowerSeries R := formalRecenteredSolutionSeries F
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    -- The constant coefficient is inherited from the zeroth approximant, namely the zero series.
    have hcoeff0 : PowerSeries.coeff 0 φ = 0 := by
      simp [φ, formalRecenteredSolutionSeries, formalRecenteredSolutionApproximant]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff0
  refine ⟨φ, ?_⟩
  refine ⟨hφ0, ?_⟩
  intro n
  -- Compare the final series with the finite recursive stage that already controls degree `n`.
  have hderiv :
      PowerSeries.coeff n (d⁄dX R φ) =
        PowerSeries.coeff n (d⁄dX R (formalRecenteredSolutionApproximant F (n + 1))) := by
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      formal_recentered_solution_series_coeff_eq_approximant (F := F) (m := n + 1)
        (n := n + 1) le_rfl]
  have hprefix :
      ∀ m ≤ n,
        PowerSeries.coeff m (formalRecenteredSolutionApproximant F n) = PowerSeries.coeff m φ := by
    intro m hm
    symm
    exact formal_recentered_solution_series_coeff_eq_approximant (F := F) hm
  have hsubst :
      PowerSeries.coeff n
        (MvPowerSeries.subst ![(X : PowerSeries R), formalRecenteredSolutionApproximant F n] F) =
          PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
    exact subst_coeff_eq_of_coeff_eq_upto
      (formal_recentered_solution_approximant_constantCoeff_eq_zero (F := F) n) hφ0 hprefix
  calc
    PowerSeries.coeff n (d⁄dX R φ)
        = PowerSeries.coeff n (d⁄dX R (formalRecenteredSolutionApproximant F (n + 1))) := hderiv
    _ = PowerSeries.coeff n
          (MvPowerSeries.subst ![(X : PowerSeries R), formalRecenteredSolutionApproximant F n] F) := by
            exact formal_recentered_solution_approximant_step_equation (F := F) n
    _ = PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := hsubst
    _ =
        ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q) := by
            rw [PowerSeries.coeff_subst_X_phi_eq_sum_range hφ0]

/-- Helper for Theorem I: the recentered formal differential equation has a unique formal power
series solution over any `ℚ`-algebra of coefficients. -/
private theorem existsUnique_formal_series_solution_for_recentered_system
    {R : Type u} [CommRing R] [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∃! φ : R⟦X⟧, PowerSeries.IsFormalRecenteredOdeSolution φ F := by
  -- The source recursion gives existence, and the coefficient recursion above gives uniqueness.
  rcases exists_formal_recentered_series_solution (R := R) F with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  simpa using formal_recentered_solution_unique hψ hφ

/-- Helper for Theorem I: translating the vector variable by the initial value `b` produces the
correct recentered multilinear power-series germ at `(0, 0)`, still defined on a small ball sent
into `Ω`. -/
private theorem recentered_rhs_hasFPowerSeriesAt {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃ Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ),
      HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0) ∧
      ∃ r : ℝ, 0 < r ∧
        MapsTo (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
          (Metric.ball (0 : ℂ × (Fin n → ℂ)) r) Ω := by
  -- First record that the translation `(z, u) ↦ (z, b + u)` is analytic at the recentered origin.
  have htranslate_analytic :
      AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
        ((0 : ℂ), (0 : Fin n → ℂ)) := by
    exact analyticAt_fst.prod (analyticAt_const.add analyticAt_snd)
  -- Composing the original analytic germ with that translation gives the recentered analytic germ.
  have hrecentered_analytic :
      AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        ((0 : ℂ), (0 : Fin n → ℂ)) := by
    have htranslate_zero :
        (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2)) ((0 : ℂ), (0 : Fin n → ℂ)) = ((0 : ℂ), b) := by
      simp
    exact (hf ((0 : ℂ), b) h0).comp_of_eq htranslate_analytic htranslate_zero
  obtain ⟨Q, hQ⟩ := hrecentered_analytic
  -- Openness of `Ω` and continuity of the translation leave a small product ball inside `Ω`.
  have htranslate_nhds :
      (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2)) ⁻¹' Ω ∈ 𝓝 (0 : ℂ × (Fin n → ℂ)) := by
    exact htranslate_analytic.continuousAt.preimage_mem_nhds <| by
      simpa using (hΩ.mem_nhds h0)
  rcases Metric.mem_nhds_iff.mp htranslate_nhds with ⟨r, hrpos, hrsub⟩
  refine ⟨Q, hQ, r, hrpos, ?_⟩
  -- This ball is exactly the neighborhood on which the recentered graph stays in `Ω`.
  intro p hp
  exact hrsub hp

/-- Helper for Theorem I: the recentered curve uses the scalar coefficient sequence of `X`. -/
private noncomputable def recenteredXCoeff : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 0

/-- Helper for Theorem I: package the formal curve `z ↦ (z, ∑ aₖ z^k)` as a one-variable
formal multilinear series with values in `ℂ × (Fin n → ℂ)`. -/
private noncomputable def vectorOfScalarsSeries {n : ℕ} (a : ℕ → Fin n → ℂ) :
    FormalMultilinearSeries ℂ ℂ (Fin n → ℂ) :=
  FormalMultilinearSeries.pi fun i : Fin n ↦
    FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i)

/-- Helper for Theorem I: the coordinatewise scalar packaging `vectorOfScalarsSeries a` has
coefficient sequence exactly `a`. -/
private theorem vectorOfScalarsSeries_coeff {n : ℕ} (a : ℕ → Fin n → ℂ) (m : ℕ) :
    (vectorOfScalarsSeries a).coeff m = a m := by
  -- Read each coordinate from the corresponding scalar formal series.
  funext i
  change (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i)).coeff m = a m i
  rw [FormalMultilinearSeries.coeff_ofScalars]

/-- Helper for Theorem I: every one-variable vector-valued formal multilinear series is recovered
from its diagonal coefficient sequence. -/
private theorem formalMultilinearSeries_eq_vectorOfScalarsSeries {n : ℕ}
    (P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ)) :
    P = vectorOfScalarsSeries (fun m ↦ P.coeff m) := by
  -- Equality is checked coefficientwise, and those coefficients were packaged by construction.
  ext m i
  simpa using congrArg (fun v : Fin n → ℂ ↦ v i)
    (vectorOfScalarsSeries_coeff (fun k ↦ P.coeff k) m).symm

/-- Helper for Theorem I: package the formal curve `z ↦ (z, ∑ aₖ z^k)` as a one-variable
formal multilinear series with values in `ℂ × (Fin n → ℂ)`. -/
private noncomputable def recenteredCurveSeries {n : ℕ} (a : ℕ → Fin n → ℂ) :
    FormalMultilinearSeries ℂ ℂ (ℂ × (Fin n → ℂ)) :=
  (FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff).prod
    (vectorOfScalarsSeries a)

/-- Helper for Theorem I: the recentered composition coefficient is the degree-`m` coefficient of
`Q` composed with the formal curve `z ↦ (z, ∑ aₖ z^k)`. -/
private noncomputable def recenteredComposedCoeff {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    (a : ℕ → Fin n → ℂ) (m : ℕ) : Fin n → ℂ :=
  (Q.comp (recenteredCurveSeries a)).coeff m

/-- Helper for Theorem I: the degree-`m` coefficient of a formal composition only depends on the
inner series coefficients through degree `m`. -/
private theorem comp_coeff_eq_of_coeff_eq_upto {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {Q : FormalMultilinearSeries ℂ F G} {P P' : FormalMultilinearSeries ℂ ℂ F} {m : ℕ}
    (hPP' : ∀ k ≤ m, P.coeff k = P'.coeff k) :
    (Q.comp P).coeff m = (Q.comp P').coeff m := by
  -- Expand the composition coefficient as the finite sum over compositions of `m`.
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
  rw [FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _hc ↦ ?_
  -- Each block in a composition of `m` has size at most `m`, so the corresponding coefficients
  -- of the inner series already agree.
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  refine congrArg (Q c.length) ?_
  funext i
  exact hPP' (c.blocksFun i) (c.blocks_le (c.blocksFun_mem_blocks i))

/-- Helper for Theorem I: matching vector coefficients through degree `m` gives the same
recentered curve coefficients through degree `m`. -/
private theorem recenteredCurveSeries_coeff_eq_of_prefix {n : ℕ}
    {a b : ℕ → Fin n → ℂ} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    ∀ k ≤ m, (recenteredCurveSeries a).coeff k = (recenteredCurveSeries b).coeff k := by
  intro k hk
  -- The `X`-component is fixed, while the `y`-component reads the matching prefix data.
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    -- Read the `i`th coordinate through the coordinatewise scalar formal series.
    calc
      ((recenteredCurveSeries a).coeff k).2 i = ((vectorOfScalarsSeries a).coeff k) i := rfl
      _ = (FormalMultilinearSeries.ofScalars ℂ (fun j ↦ a j i)).coeff k := rfl
      _ = a k i := by rw [FormalMultilinearSeries.coeff_ofScalars]
      _ = b k i := congrArg (fun u : Fin n → ℂ ↦ u i) (hab k hk)
      _ = (FormalMultilinearSeries.ofScalars ℂ (fun j ↦ b j i)).coeff k := by
            rw [FormalMultilinearSeries.coeff_ofScalars]
      _ = ((vectorOfScalarsSeries b).coeff k) i := rfl
      _ = ((recenteredCurveSeries b).coeff k).2 i := rfl

/-- Helper for Theorem I: the exact recentered composition coefficient is triangular in the
coefficient data of the recentered curve. -/
private theorem recentered_composedCoeff_eq_of_prefix {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    {a b : ℕ → Fin n → ℂ} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    recenteredComposedCoeff Q a m = recenteredComposedCoeff Q b m := by
  -- The preceding generic composition lemma applies once the recentered curve coefficients agree
  -- through degree `m`.
  exact comp_coeff_eq_of_coeff_eq_upto
    (Q := Q) (P := recenteredCurveSeries a) (P' := recenteredCurveSeries b)
    (recenteredCurveSeries_coeff_eq_of_prefix hab)

/-- Helper for Theorem I: the exact multilinear recursion chooses the next vector coefficient
from the current recentered composition coefficient. -/
private noncomputable def formalRecenteredVectorSolutionStepCoeff {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    (φ : PowerSeries (Fin n → ℂ)) (m : ℕ) : Fin n → ℂ :=
  ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m

/-- Helper for Theorem I: the stage-`m` approximant records the first `m` coefficients forced by
the exact recentered multilinear recursion. -/
private noncomputable def formalRecenteredVectorSolutionApproximant {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ℕ → PowerSeries (Fin n → ℂ)
  | 0 => 0
  | m + 1 =>
      formalRecenteredVectorSolutionApproximant Q m +
        C (formalRecenteredVectorSolutionStepCoeff Q
          (formalRecenteredVectorSolutionApproximant Q m) m) * X ^ (m + 1)

/-- Helper for Theorem I: every vector approximant still has vanishing constant coefficient. -/
private theorem formal_recentered_vector_solution_approximant_constantCoeff_eq_zero {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∀ m, PowerSeries.constantCoeff (formalRecenteredVectorSolutionApproximant Q m) = 0
  | 0 => by
      -- The initial approximant is the zero series.
      simp [formalRecenteredVectorSolutionApproximant]
  | m + 1 => by
      -- The correction term lives in degree `m + 1`, so it leaves the constant term unchanged.
      simp [formalRecenteredVectorSolutionApproximant,
        formal_recentered_vector_solution_approximant_constantCoeff_eq_zero Q m]

/-- Helper for Theorem I: once a vector coefficient has been created, the next stage does not
change it. -/
private theorem formal_recentered_vector_solution_approximant_coeff_step_eq {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) {m k : ℕ} (hmk : m ≤ k) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (k + 1)) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
  -- The recursive step only adds a monomial in degree `k + 1`.
  have hmk_ne : m ≠ k + 1 := Nat.ne_of_lt (lt_of_le_of_lt hmk (Nat.lt_succ_self k))
  rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff m).map_add,
    PowerSeries.coeff_C_mul_X_pow]
  simp [hmk_ne]

/-- Helper for Theorem I: before stage `m`, the `m`th vector coefficient is still zero. -/
private theorem formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∀ k m, k < m → PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) = 0
  | 0, m, hm => by
      -- The zeroth approximant is the zero series.
      simp [formalRecenteredVectorSolutionApproximant]
  | k + 1, m, hm => by
      -- A stage strictly below `m` cannot yet create the `m`th coefficient.
      have hlt : k < m := lt_trans (Nat.lt_succ_self k) hm
      rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff m).map_add,
        PowerSeries.coeff_C_mul_X_pow]
      simp [Nat.ne_of_gt hm,
        formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt Q k m hlt]

/-- Helper for Theorem I: after stage `m`, the `m`th vector coefficient is frozen forever. -/
private theorem formal_recentered_vector_solution_approximant_stabilizes {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) (m k : ℕ) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Later stages add only higher-degree terms, so the `m`th coefficient persists.
      have hstep :
          PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k + 1)) =
            PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) := by
        simpa [Nat.add_assoc] using
          formal_recentered_vector_solution_approximant_coeff_step_eq
            (Q := Q) (m := m) (k := m + k) (Nat.le_add_right m k)
      calc
        PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + (k + 1)))
            = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k + 1)) := by
                simp [Nat.add_assoc]
        _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) := hstep
        _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := ih

/-- Helper for Theorem I: the stage `m + 1` approximant inserts exactly the coefficient required
by the recentered multilinear recursion. -/
private theorem formal_recentered_vector_solution_approximant_next_coeff_eq {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) (m : ℕ) :
    PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q (m + 1)) =
      formalRecenteredVectorSolutionStepCoeff Q
        (formalRecenteredVectorSolutionApproximant Q m) m := by
  -- The new coefficient is created only at stage `m + 1`.
  rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff (m + 1)).map_add]
  have hzero :
      PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q m) = 0 := by
    exact formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt
      (Q := Q) m (m + 1) (Nat.lt_succ_self m)
  simp [hzero, formalRecenteredVectorSolutionStepCoeff]

/-- Helper for Theorem I: the stabilized coefficients define the exact formal vector solution of
the recentered multilinear recursion. -/
private noncomputable def formalRecenteredVectorSolutionSeries {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    PowerSeries (Fin n → ℂ) :=
  PowerSeries.mk fun m ↦
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m)

/-- Helper for Theorem I: the stabilized vector series agrees with the `m`th approximant through
degree `m`. -/
private theorem formal_recentered_vector_solution_series_coeff_eq_approximant {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) {m k : ℕ} (hmk : m ≤ k) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
  -- Read the coefficient from stage `m`, then use stabilization to move to any later stage.
  calc
    PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q)
        = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := by
            simp [formalRecenteredVectorSolutionSeries]
    _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + (k - m))) := by
          symm
          exact formal_recentered_vector_solution_approximant_stabilizes (Q := Q) m (k - m)
    _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
          rw [Nat.add_sub_of_le hmk]

/-- Helper for Theorem I: the exact recentered multilinear coefficient recursion has a unique
formal vector-valued power-series solution. -/
private theorem existsUnique_formal_series_solution_for_recentered_multilinear_system {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∃! φ : PowerSeries (Fin n → ℂ),
      PowerSeries.constantCoeff φ = 0 ∧
      ∀ m, PowerSeries.coeff (m + 1) φ =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
  -- Route correction: solve the exact multilinear coefficient recursion first, before any
  -- analytic realization or majorant argument.
  let φ : PowerSeries (Fin n → ℂ) := formalRecenteredVectorSolutionSeries Q
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    -- The constant coefficient is inherited from the zeroth approximant, namely the zero series.
    have hcoeff0 : PowerSeries.coeff 0 φ = 0 := by
      simp [φ, formalRecenteredVectorSolutionSeries,
        formalRecenteredVectorSolutionApproximant]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff0
  have hφrec :
      ∀ m, PowerSeries.coeff (m + 1) φ =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
    intro m
    have hprefix :
        ∀ k ≤ m,
          PowerSeries.coeff k (formalRecenteredVectorSolutionApproximant Q m) =
            PowerSeries.coeff k φ := by
      intro k hk
      symm
      exact formal_recentered_vector_solution_series_coeff_eq_approximant
        (Q := Q) (m := k) (k := m) hk
    calc
      PowerSeries.coeff (m + 1) φ
          = PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q (m + 1)) := by
              exact formal_recentered_vector_solution_series_coeff_eq_approximant
                (Q := Q) (m := m + 1) (k := m + 1) le_rfl
      _ = formalRecenteredVectorSolutionStepCoeff Q
            (formalRecenteredVectorSolutionApproximant Q m) m := by
              exact formal_recentered_vector_solution_approximant_next_coeff_eq (Q := Q) m
      _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
            have hcomp :
                recenteredComposedCoeff Q
                    (fun k ↦
                      PowerSeries.coeff k (formalRecenteredVectorSolutionApproximant Q m)) m =
                  recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m :=
              recentered_composedCoeff_eq_of_prefix Q hprefix
            simpa [formalRecenteredVectorSolutionStepCoeff] using
              congrArg (fun v : Fin n → ℂ ↦ ((m + 1 : ℂ)⁻¹) • v) hcomp
  refine ⟨φ, ⟨hφ0, hφrec⟩, ?_⟩
  intro ψ hψ
  rcases hψ with ⟨hψ0, hψrec⟩
  -- Compare coefficients inductively: the next coefficient is forced by the common prefix.
  have hcoeff :
      ∀ d, ∀ k ≤ d, PowerSeries.coeff k φ = PowerSeries.coeff k ψ := by
    intro d
    induction d with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, hψ0]
    | succ d ih =>
        intro k hk
        by_cases hkd : k ≤ d
        · exact ih k hkd
        · have hk_eq : k = d + 1 := by omega
          subst hk_eq
          have hcomp :
              recenteredComposedCoeff Q (fun m ↦ PowerSeries.coeff m φ) d =
                recenteredComposedCoeff Q (fun m ↦ PowerSeries.coeff m ψ) d :=
            recentered_composedCoeff_eq_of_prefix Q (fun m hm ↦ ih m hm)
          simpa [hφrec d, hψrec d] using
            congrArg (fun v : Fin n → ℂ ↦ ((d + 1 : ℂ)⁻¹) • v) hcomp
  ext m i
  exact (congrArg (fun v : Fin n → ℂ ↦ v i) (hcoeff m m le_rfl)).symm

/-- Helper for Theorem I: any analytic open-set solution produces a recentered vector power series
at `0` with vanishing constant term. -/
private theorem recentered_solution_hasFPowerSeriesAt_zero {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {U : Set ℂ} {χ : ℂ → Fin n → ℂ}
    (hχ : IsHolomorphicSystemSolutionOn Ω f 0 b U χ) :
    ∃ χSeries : PowerSeries (Fin n → ℂ),
      PowerSeries.constantCoeff χSeries = 0 ∧
      HasFPowerSeriesAt (fun z ↦ χ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries) 0 := by
  -- Recenter the analytic solution by subtracting the initial value and choose its Taylor series.
  obtain ⟨P, hP⟩ := ((hχ.analytic 0 hχ.mem).sub analyticAt_const)
  let χSeries : PowerSeries (Fin n → ℂ) := PowerSeries.mk fun m ↦ P.coeff m
  have hχSeries :
      HasFPowerSeriesAt (fun z ↦ χ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries) 0 := by
    -- Replace the arbitrary one-variable multilinear series by its coefficient packaging.
    have hpack :
        P = vectorOfScalarsSeries (fun m ↦ PowerSeries.coeff m χSeries) := by
      simpa [χSeries] using formalMultilinearSeries_eq_vectorOfScalarsSeries (P := P)
    exact hpack ▸ hP
  have hχSeries_zero_coeff : PowerSeries.coeff 0 χSeries = 0 := by
    -- The recentered function vanishes at `0`, so the constant coefficient is forced to be zero.
    have hP_zero : P.coeff 0 = 0 := by
      have hP_zero_eval : P 0 (fun _ ↦ (0 : ℂ)) = 0 := by
        simpa [hχ.initial] using hP.coeff_zero (fun _ ↦ (0 : ℂ))
      have hone : (1 : Fin 0 → ℂ) = fun _ ↦ (0 : ℂ) := by
        funext i
        exact Fin.elim0 i
      rw [FormalMultilinearSeries.coeff, hone, hP_zero_eval]
    simpa [χSeries] using hP_zero
  have hχSeries_zero : PowerSeries.constantCoeff χSeries = 0 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hχSeries_zero_coeff
  exact ⟨χSeries, hχSeries_zero, hχSeries⟩

/-- Helper for Theorem I: once the exact recentered formal vector solution is known, the remaining
source-faithful existence step is to realize that series as an actual holomorphic solution on a
smaller ball whose translated graph stays inside `Ω`. -/
private theorem solutionOn_of_recentered_formal_series_on_ball {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0))
    {r : ℝ} (hrpos : 0 < r)
    (hballΩ : MapsTo (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
      (Metric.ball (0 : ℂ × (Fin n → ℂ)) r) Ω)
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) :
    ∃ U : Set ℂ, ∃ ψ : ℂ → Fin n → ℂ,
      IsHolomorphicSystemSolutionOn Ω f 0 b U ψ ∧
      HasFPowerSeriesAt (fun z ↦ ψ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ) 0 := by
  -- Route correction: the remaining existence gap is not the formal recursion anymore; it is the
  -- analytic realization of that exact recentered formal series on a small ball.
  -- TODO: attach the scalar majorant to `Q`, deduce a positive convergence radius for `φ`, realize
  -- `∑ coeff m φ * z^m` on a smaller ball by `FormalMultilinearSeries.hasFPowerSeriesOnBall`, and
  -- then transport the recentered differential equation back to `ψ z = b + …`.
  sorry

/-- Helper for Theorem I: any analytic competitor has the same recentered Taylor data as the exact
formal solution, so its germ agrees with the realized solution germ. -/
private theorem germ_eq_of_recentered_formal_solution {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0))
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m)
    {U : Set ℂ} {ψ : ℂ → Fin n → ℂ}
    (hψ : IsHolomorphicSystemSolutionOn Ω f 0 b U ψ)
    (hψseries : HasFPowerSeriesAt (fun z ↦ ψ z - b)
      (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ) 0) :
    ∀ {V : Set ℂ} {χ : ℂ → Fin n → ℂ}, IsHolomorphicSystemSolutionOn Ω f 0 b V χ →
      (χ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) = (ψ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) := by
  intro V χ hχ
  -- Route correction: uniqueness should proceed by recentering `χ`, showing its Taylor series
  -- satisfies the same exact multilinear recursion, and invoking formal uniqueness before passing
  -- back to germs.
  rcases recentered_solution_hasFPowerSeriesAt_zero (b := b) hχ with
    ⟨χSeries, hχSeries0, hχSeries⟩
  -- TODO: show `χSeries` satisfies the exact recentered multilinear recursion forced by `hQ` and
  -- `hχ.deriv_eq`, apply `existsUnique_formal_series_solution_for_recentered_multilinear_system`
  -- to identify `χSeries = φ`, then use `HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`
  -- to conclude that `χ - b` and `ψ - b` have the same germ near `0`.
  let _ := hQ
  let _ := hφ
  let _ := hψseries
  let _ := χSeries
  let _ := hχSeries0
  let _ := hχSeries
  sorry

/-- Theorem I: the holomorphic Cauchy problem for a first-order system with initial value `b` at
`0` has a unique local holomorphic solution germ. -/
theorem unique_local_solution_holomorphic_system {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃! φ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ), IsHolomorphicSystemSolution Ω f 0 b φ := by
  -- Route correction: the old two-variable `R⟦X,Y⟧` bridge is not adequate for a coupled vector
  -- system. The verified prefix now uses the correct multilinear Taylor germ of the recentered RHS.
  rcases recentered_rhs_hasFPowerSeriesAt (b := b) hΩ h0 hf with ⟨Q, hQ, r, hrpos, hballΩ⟩
  rcases existsUnique_formal_series_solution_for_recentered_multilinear_system Q with
    ⟨φ, hφ, hφ_unique⟩
  rcases solutionOn_of_recentered_formal_series_on_ball
      (hQ := hQ) hrpos hballΩ hφ with ⟨U, ψ, hψ, hψseries⟩
  refine ⟨(ψ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)), hψ.isHolomorphicSystemSolution, ?_⟩
  intro χ hχ
  -- The realized solution is unique because every analytic competitor has the same recentered
  -- Taylor data and hence the same germ at `0`.
  rcases hχ with ⟨V, χ', hχ', hχgerm⟩
  exact hχgerm.symm.trans <|
    germ_eq_of_recentered_formal_solution (hQ := hQ) hφ hψ hψseries hχ'

/-- Neighborhood-representative bridge for Theorem I. -/
theorem exists_eventuallyEq_unique_local_solution_holomorphic_system {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃ U : Set ℂ, ∃ φ : ℂ → Fin n → ℂ,
      IsHolomorphicSystemSolutionOn Ω f 0 b U φ ∧
      ∀ V : Set ℂ, ∀ ψ : ℂ → Fin n → ℂ,
        IsHolomorphicSystemSolutionOn Ω f 0 b V ψ →
        ψ =ᶠ[𝓝 (0 : ℂ)] φ := by
  rcases unique_local_solution_holomorphic_system hΩ h0 hf with ⟨φ, hφ, huniq⟩
  rcases hφ with ⟨U, ψ, hψ, hψφ⟩
  refine ⟨U, ψ, hψ, ?_⟩
  intro V χ hχ
  have hχ' : IsHolomorphicSystemSolution Ω f 0 b (χ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) :=
    hχ.isHolomorphicSystemSolution
  exact Germ.coe_eq.mp <| (huniq _ hχ').trans hψφ.symm
