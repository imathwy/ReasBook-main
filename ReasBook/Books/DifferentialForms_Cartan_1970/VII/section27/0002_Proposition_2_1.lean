import DifferentialForms_Cartan_1970.cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0007_Proposition_3_I»
import Mathlib

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

-- Domain sampling for this file:
-- * source-facing ODE data in this chapter: the coefficient formula for `F(X, φ(X))`
-- * core/canonical ring owner: `MvPowerSeries.subst ![(X : PowerSeries R), φ] F`
-- * source-facing bridge notation reused here: `MvPowerSeries.coeffXY`

-- Declarations for this item will be appended below by the statement pipeline.

private noncomputable def pairToFinsupp : ℕ × ℕ ≃ (Fin 2 →₀ ℕ) :=
  { toFun := fun n ↦ Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _)
    invFun := fun d ↦ (d 0, d 1)
    left_inv := fun _ ↦ rfl
    right_inv := fun d ↦ Finsupp.ofSupportFinite_fin_two_eq d }

/-- Helper for Proposition 2.1: the pair `(p, q)` is the canonical `Fin 2 →₀ ℕ` exponent
encoding the monomial `X^p Y^q`. -/
private theorem pairToFinsupp_apply (n : ℕ × ℕ) :
    pairToFinsupp n = Finsupp.single 0 n.1 + Finsupp.single 1 n.2 := by
  -- Check the two coordinates directly on the finite index type `Fin 2`.
  ext i
  fin_cases i <;> simp [pairToFinsupp, Finsupp.ofSupportFinite_coe]

/-- Helper for Proposition 2.1: the source-facing coefficient `coeffXY` is the canonical
coefficient indexed by the corresponding finitely supported exponent. -/
private theorem coeffXY_eq_coeff_pairToFinsupp {R : Type u} [Semiring R] (F : R⟦X,Y⟧)
    (n : ℕ × ℕ) :
    MvPowerSeries.coeffXY F n.1 n.2 = MvPowerSeries.coeff (pairToFinsupp n) F := by
  -- Rewrite the pair index by the explicit `Fin 2 →₀ ℕ` exponent.
  rw [MvPowerSeries.coeffXY, pairToFinsupp_apply, MvPowerSeries.coeff_apply]

/-- Helper for Proposition 2.1: after reindexing by a pair, substituting `X` and `φ` produces the
monomial `X^p * φ^q`. -/
private theorem pairToFinsupp_prod_subst {R : Type u} [CommRing R] (φ : PowerSeries R)
    (n : ℕ × ℕ) :
    (pairToFinsupp n).prod (fun s e ↦ (![X, φ] s : PowerSeries R) ^ e) =
      (X : PowerSeries R) ^ n.1 * φ ^ n.2 := by
  -- The product over the two coordinates is exactly the `X`-factor times the `φ`-factor.
  simp [pairToFinsupp_apply, Fin.prod_univ_two, mul_comm]

/-- Helper for Proposition 2.1: if the total degree of a substituted monomial exceeds `n`, then
its `n`th coefficient vanishes. -/
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

/-- Helper for Proposition 2.1: a `Fin 2` exponent of total degree at most `n` lies in the
triangular range `0 ≤ p ≤ n`, `0 ≤ q ≤ n - p`. -/
private theorem pair_mem_triangular_range (d : Fin 2 →₀ ℕ) {n : ℕ}
    (hdeg : d 0 + d 1 ≤ n) :
    d 0 ∈ Finset.range (n + 1) ∧ d 1 ∈ Finset.range (n + 1 - d 0) := by
  -- The total-degree bound gives both coordinate bounds needed for the triangular region.
  refine ⟨by simp [Finset.mem_range]; omega, by simp [Finset.mem_range]; omega⟩

/-- Helper for Proposition 2.1: truncating the substitution coefficient formula by total degree
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

/-- Over a commutative ring, the canonical substitution `F(X, φ(X))` has the expected
source-facing coefficient formula. -/
theorem PowerSeries.coeff_subst_X_phi_eq_sum_range {R : Type u} [CommRing R]
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

/-- A one-variable formal power series with vanishing constant term solving the formal differential
equation `y' = F(x, y)`, stated through the source-facing coefficient formula for `F(X, φ(X))`.
For commutative rings, the derived equation is the canonical substitution identity
`d⁄dX R φ = MvPowerSeries.subst ![(X : PowerSeries R), φ] F`. -/
class PowerSeries.IsFormalFirstOrderOdeSolution {R : Type u} [CommSemiring R]
    (φ : PowerSeries R) (F : R⟦X,Y⟧) : Prop where
  constantCoeff_eq_zero : φ.constantCoeff = 0
  equation (n : ℕ) :
    PowerSeries.coeff n (d⁄dX R φ) =
      ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q)

namespace PowerSeries.IsFormalFirstOrderOdeSolution

theorem coeff_zero {R : Type u} [CommSemiring R] {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ F) :
    coeff 0 φ = 0 := by
  simpa [coeff_zero_eq_constantCoeff_apply] using hφ.constantCoeff_eq_zero

theorem equation_eq_subst {R : Type u} [CommRing R] {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ F) :
    d⁄dX R φ = MvPowerSeries.subst ![(X : PowerSeries R), φ] F := by
  ext n
  rw [hφ.equation, PowerSeries.coeff_subst_X_phi_eq_sum_range hφ.constantCoeff_eq_zero]

end PowerSeries.IsFormalFirstOrderOdeSolution

/-- Helper for Proposition 2.1: multiplying by the rational inverse of `n + 1` cancels the
corresponding natural-number scalar in any `ℚ`-algebra. -/
private theorem rational_inverse_succ_mul_natCast {R : Type u} [CommRing R] [Algebra ℚ R]
    (n : ℕ) :
    algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * (n + 1 : R) = 1 := by
  -- Move the natural-number scalar back into `ℚ`, then cancel there.
  rw [show (n + 1 : R) = algebraMap ℚ R (n + 1 : ℚ) by norm_num, ← map_mul, inv_mul_cancel₀]
  · norm_num
  · exact_mod_cast Nat.succ_ne_zero n

/-- Helper for Proposition 2.1: if two series agree through degree `n`, then the same is true for
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

/-- Helper for Proposition 2.1: the degree-`n` coefficient of `F(X, φ(X))` only depends on the
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

/-- Helper for Proposition 2.1: a formal solution determines its next coefficient from the degree
`n` coefficient of the substituted right-hand side. -/
private theorem formal_solution_next_coeff_eq {R : Type u} [CommRing R] [Algebra ℚ R]
    {φ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ F) (n : ℕ) :
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

/-- Helper for Proposition 2.1: a formal solution with vanishing constant term is unique once the
coefficient recursion for successive terms is fixed. -/
private theorem formal_series_solution_unique {R : Type u} [CommRing R] [Algebra ℚ R]
    {φ ψ : PowerSeries R} {F : R⟦X,Y⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ F)
    (hψ : PowerSeries.IsFormalFirstOrderOdeSolution ψ F) :
    φ = ψ := by
  -- Compare coefficients inductively: the next coefficient is forced by the common prefix.
  have hcoeff : ∀ n, ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m ψ := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        simp [PowerSeries.IsFormalFirstOrderOdeSolution.coeff_zero hφ,
          PowerSeries.IsFormalFirstOrderOdeSolution.coeff_zero hψ]
    | succ n ih =>
        intro m hm
        by_cases hmn : m ≤ n
        · exact ih m hmn
        · have hm_eq : m = n + 1 := by omega
          subst hm_eq
          rw [formal_solution_next_coeff_eq hφ, formal_solution_next_coeff_eq hψ]
          congr 1
          exact subst_coeff_eq_of_coeff_eq_upto hφ.constantCoeff_eq_zero
            hψ.constantCoeff_eq_zero ih
  ext m
  exact hcoeff m m le_rfl

/-- Helper for Proposition 2.1: the recursive step chooses the next coefficient from the current
substituted right-hand side. -/
private noncomputable def formalSolutionStepCoeff {R : Type u} [CommRing R] [Algebra ℚ R]
    (F : R⟦X,Y⟧) (φ : PowerSeries R) (n : ℕ) : R :=
  algebraMap ℚ R ((n + 1 : ℚ)⁻¹) *
    PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F)

/-- Helper for Proposition 2.1: the `n`th approximant records the first `n` recursively determined
coefficients of the desired formal solution. -/
private noncomputable def formalSolutionApproximant {R : Type u} [CommRing R] [Algebra ℚ R]
    (F : R⟦X,Y⟧) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 =>
      formalSolutionApproximant F n +
        C (formalSolutionStepCoeff F (formalSolutionApproximant F n) n) * X ^ (n + 1)

/-- Helper for Proposition 2.1: each recursive approximant still has zero constant coefficient. -/
private theorem formal_solution_approximant_constantCoeff_eq_zero {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∀ n, PowerSeries.constantCoeff (formalSolutionApproximant F n) = 0
  | 0 => by
      -- The zeroth approximant is the zero series.
      simp [formalSolutionApproximant]
  | n + 1 => by
      -- The correction term lives in degree `n + 1`, so it does not change the constant term.
      simp [formalSolutionApproximant, formal_solution_approximant_constantCoeff_eq_zero F n]

/-- Helper for Proposition 2.1: once a coefficient has been created, the next recursive step leaves
it unchanged. -/
private theorem formal_solution_approximant_coeff_step_eq {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff m (formalSolutionApproximant F (n + 1)) =
      PowerSeries.coeff m (formalSolutionApproximant F n) := by
  -- The step from `n` to `n + 1` only adds a monomial of degree `n + 1`.
  have hmne : m ≠ n + 1 := Nat.ne_of_lt (lt_of_le_of_lt hmn (Nat.lt_succ_self n))
  rw [formalSolutionApproximant, (PowerSeries.coeff m).map_add, PowerSeries.coeff_C_mul_X_pow]
  simp [hmne]

/-- Helper for Proposition 2.1: the `m`th coefficient of the `n`th approximant vanishes before the
recursive construction reaches stage `m`. -/
private theorem formal_solution_approximant_coeff_eq_zero_of_lt {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∀ n m, n < m → PowerSeries.coeff m (formalSolutionApproximant F n) = 0
  | 0, m, hm => by
      -- The initial approximant is zero, so all positive coefficients vanish.
      simp [formalSolutionApproximant]
  | n + 1, m, hm => by
      -- A stage strictly below `m` cannot create the `m`th coefficient.
      have hlt : n < m := lt_trans (Nat.lt_succ_self n) hm
      rw [formalSolutionApproximant, (PowerSeries.coeff m).map_add, PowerSeries.coeff_C_mul_X_pow]
      simp [Nat.ne_of_gt hm, formal_solution_approximant_coeff_eq_zero_of_lt F n m hlt]

/-- Helper for Proposition 2.1: after stage `m`, the `m`th coefficient is frozen forever. -/
private theorem formal_solution_approximant_stabilizes {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) (m k : ℕ) :
    PowerSeries.coeff m (formalSolutionApproximant F (m + k)) =
      PowerSeries.coeff m (formalSolutionApproximant F m) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Later stages only add strictly higher-degree terms, so the `m`th coefficient persists.
      have hstep :
          PowerSeries.coeff m (formalSolutionApproximant F (m + k + 1)) =
            PowerSeries.coeff m (formalSolutionApproximant F (m + k)) := by
        simpa [Nat.add_assoc] using
          formal_solution_approximant_coeff_step_eq (F := F) (m := m) (n := m + k)
            (Nat.le_add_right m k)
      calc
        PowerSeries.coeff m (formalSolutionApproximant F (m + (k + 1)))
            = PowerSeries.coeff m (formalSolutionApproximant F (m + k + 1)) := by
                simp [Nat.add_assoc]
        _ = PowerSeries.coeff m (formalSolutionApproximant F (m + k)) := hstep
        _ = PowerSeries.coeff m (formalSolutionApproximant F m) := ih

/-- Helper for Proposition 2.1: the degree-`n` derivative equation is enforced exactly at the
`(n + 1)`st recursive approximant. -/
private theorem formal_solution_approximant_step_equation {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX R (formalSolutionApproximant F (n + 1))) =
      PowerSeries.coeff n
        (MvPowerSeries.subst ![(X : PowerSeries R), formalSolutionApproximant F n] F) := by
  -- The coefficient added at stage `n + 1` is chosen precisely to satisfy the degree-`n`
  -- differential equation.
  have hnext :
      PowerSeries.coeff (n + 1) (formalSolutionApproximant F (n + 1)) =
        formalSolutionStepCoeff F (formalSolutionApproximant F n) n := by
    rw [formalSolutionApproximant, (PowerSeries.coeff (n + 1)).map_add]
    have hzero :
        PowerSeries.coeff (n + 1) (formalSolutionApproximant F n) = 0 := by
      exact formal_solution_approximant_coeff_eq_zero_of_lt (F := F) n (n + 1)
        (Nat.lt_succ_self n)
    simp [hzero]
  calc
    PowerSeries.coeff n (d⁄dX R (formalSolutionApproximant F (n + 1)))
        = PowerSeries.coeff (n + 1) (formalSolutionApproximant F (n + 1)) * (n + 1 : R) := by
            rw [PowerSeries.coeff_derivative]
    _ = formalSolutionStepCoeff F (formalSolutionApproximant F n) n * (n + 1 : R) := by
          rw [hnext]
    _ = PowerSeries.coeff n
          (MvPowerSeries.subst ![(X : PowerSeries R), formalSolutionApproximant F n] F) := by
          dsimp [formalSolutionStepCoeff]
          set a : R :=
            PowerSeries.coeff n
              (MvPowerSeries.subst ![(X : PowerSeries R), formalSolutionApproximant F n] F)
          calc
            (algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * a) * (n + 1 : R)
                = (algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * (n + 1 : R)) * a := by
                    ac_rfl
            _ = a := by
                  rw [rational_inverse_succ_mul_natCast (R := R) n, one_mul]

/-- Helper for Proposition 2.1: the final series reads each coefficient from the stage where the
recursive construction has already stabilized it. -/
private noncomputable def formalSolutionSeries {R : Type u} [CommRing R] [Algebra ℚ R]
    (F : R⟦X,Y⟧) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m (formalSolutionApproximant F m)

/-- Helper for Proposition 2.1: the stabilized series agrees with the `n`th approximant through
degree `n`. -/
private theorem formal_solution_series_coeff_eq_approximant {R : Type u} [CommRing R]
    [Algebra ℚ R] (F : R⟦X,Y⟧) {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff m (formalSolutionSeries F) =
      PowerSeries.coeff m (formalSolutionApproximant F n) := by
  -- The limiting coefficient is read from stage `m`, and every later stage keeps it fixed.
  calc
    PowerSeries.coeff m (formalSolutionSeries F) =
        PowerSeries.coeff m (formalSolutionApproximant F m) := by
          simp [formalSolutionSeries]
    _ = PowerSeries.coeff m (formalSolutionApproximant F (m + (n - m))) := by
          symm
          exact formal_solution_approximant_stabilizes (F := F) m (n - m)
    _ = PowerSeries.coeff m (formalSolutionApproximant F n) := by
          rw [Nat.add_sub_of_le hmn]

/-- Helper for Proposition 2.1: the recursively stabilized coefficients define a formal power
series solution of the first-order differential equation. -/
private theorem exists_formal_series_solution {R : Type u} [CommRing R] [Algebra ℚ R]
    (F : R⟦X,Y⟧) :
    ∃ φ : R⟦X⟧, PowerSeries.IsFormalFirstOrderOdeSolution φ F := by
  -- Route correction: build the source-faithful recursive approximants first, then read the
  -- stabilized coefficients from the limit series they determine.
  let φ : PowerSeries R := formalSolutionSeries F
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    -- The constant coefficient is inherited from the zeroth approximant, namely the zero series.
    have hcoeff0 : PowerSeries.coeff 0 φ = 0 := by
      simp [φ, formalSolutionSeries, formalSolutionApproximant]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff0
  refine ⟨φ, ?_⟩
  refine ⟨hφ0, ?_⟩
  intro n
  -- Compare the final series with the finite recursive stage that already controls degree `n`.
  have hderiv :
      PowerSeries.coeff n (d⁄dX R φ) =
        PowerSeries.coeff n (d⁄dX R (formalSolutionApproximant F (n + 1))) := by
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      formal_solution_series_coeff_eq_approximant (F := F) (m := n + 1) (n := n + 1) le_rfl]
  have hprefix :
      ∀ m ≤ n,
        PowerSeries.coeff m (formalSolutionApproximant F n) = PowerSeries.coeff m φ := by
    intro m hm
    symm
    exact formal_solution_series_coeff_eq_approximant (F := F) hm
  have hsubst :
      PowerSeries.coeff n
        (MvPowerSeries.subst ![(X : PowerSeries R), formalSolutionApproximant F n] F) =
          PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := by
    exact subst_coeff_eq_of_coeff_eq_upto
      (formal_solution_approximant_constantCoeff_eq_zero (F := F) n) hφ0 hprefix
  calc
    PowerSeries.coeff n (d⁄dX R φ)
        = PowerSeries.coeff n (d⁄dX R (formalSolutionApproximant F (n + 1))) := hderiv
    _ = PowerSeries.coeff n
          (MvPowerSeries.subst ![(X : PowerSeries R), formalSolutionApproximant F n] F) := by
            exact formal_solution_approximant_step_equation (F := F) n
    _ = PowerSeries.coeff n (MvPowerSeries.subst ![(X : PowerSeries R), φ] F) := hsubst
    _ =
        ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (φ ^ q) := by
            rw [PowerSeries.coeff_subst_X_phi_eq_sum_range hφ0]

/-- Proposition 2.1: over a `ℚ`-algebra of coefficients, given a formal series in the variables
`x` and `y`, there exists a unique formal series in `x` with vanishing constant term whose formal
derivative is obtained by substituting `x = X` and `y = φ` into the given series. -/
theorem existsUnique_formal_series_solution
    {R : Type u} [CommRing R] [Algebra ℚ R] (F : R⟦X,Y⟧) :
    ∃! φ : R⟦X⟧, PowerSeries.IsFormalFirstOrderOdeSolution φ F := by
  -- The source recursion gives existence, and the coefficient recursion above gives uniqueness.
  rcases exists_formal_series_solution (R := R) F with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  simpa using formal_series_solution_unique hψ hφ
