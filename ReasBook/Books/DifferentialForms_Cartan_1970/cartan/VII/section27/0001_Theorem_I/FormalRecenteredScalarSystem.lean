import DifferentialForms_Cartan_1970.cartan.I.section02.«0012_Proposition_6_1»
import DifferentialForms_Cartan_1970.cartan.I.section02.«0016_Proposition_9_1»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0007_Proposition_3_I»
import Mathlib

open Filter
open Set
open scoped Topology BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

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

/-- Helper for Cartan section27 0001_Theorem_I: integrating a scalar power series coefficientwise
produces the unique primitive with vanishing constant term. -/
noncomputable def primitiveSeries (A : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 => ((n + 1 : ℝ)⁻¹) * PowerSeries.coeff n A

/-- Helper for Cartan section27 0001_Theorem_I: the coefficientwise primitive has zero constant
term by construction. -/
theorem primitiveSeries_constantCoeff (A : ℝ⟦X⟧) :
    PowerSeries.constantCoeff (primitiveSeries A) = 0 := by
  -- The primitive starts at degree `1`, so its constant coefficient vanishes.
  simp [primitiveSeries]

/-- Helper for Cartan section27 0001_Theorem_I: differentiating the coefficientwise primitive
recovers the original scalar series. -/
theorem derivative_primitiveSeries (A : ℝ⟦X⟧) :
    d⁄dX ℝ (primitiveSeries A) = A := by
  -- The derivative shifts the primitive coefficients back by one degree and cancels the factor
  -- `(n + 1)⁻¹`.
  ext n
  rw [PowerSeries.coeff_derivative]
  have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [primitiveSeries, hne, mul_comm]

/-- Helper for Cartan section27 0001_Theorem_I: the scalar fixed-point equation
`Φ' = S(X + Φ)` always has a formal solution with vanishing constant term. -/
theorem existsScalarSubstFormalSolution (S : ℝ⟦X⟧) :
    ∃ Φ : ℝ⟦X⟧,
      PowerSeries.constantCoeff Φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) Φ =
          ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst ((X : ℝ⟦X⟧) + Φ)) := by
  let F : ℝ⟦X,Y⟧ :=
    PowerSeries.subst
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1))
      S
  rcases existsUnique_formal_series_solution_for_recentered_system (R := ℝ) F with ⟨Φ, hΦ, -⟩
  have ha :
      MvPowerSeries.HasSubst
        (fun _ : Unit ↦
          ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1)) := by
    -- The recentered scalar owner has vanishing constant term, so scalar substitution is legal.
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro i
    simp
  have hb : MvPowerSeries.HasSubst ![(X : ℝ⟦X⟧), Φ] := by
    -- The inner substitution family uses the centered scalar series `Φ`, hence both coordinates
    -- have zero constant term.
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_X (R := ℝ)
    · simpa using hΦ.constantCoeff_eq_zero
  have hcomp :
      MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ] F = S.subst ((X : ℝ⟦X⟧) + Φ) := by
    -- First collapse the two successive substitutions, then evaluate the recentered linear form
    -- `X₀ + X₁` at `(X, Φ)`.
    calc
      MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ] F
          =
            MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ]
              (MvPowerSeries.subst
                (fun _ : Unit ↦
                  ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1))
                S) := by
                  rfl
      _ =
          MvPowerSeries.subst
            (fun _ : Unit ↦
              MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ]
                (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1)))
            S := by
              simpa using
                (MvPowerSeries.subst_comp_subst_apply (ha := ha) (hb := hb) (f := S))
      _ = S.subst ((X : ℝ⟦X⟧) + Φ) := by
            have hinner :
                MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ]
                  (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1)) =
                  (X : ℝ⟦X⟧) + Φ := by
              calc
                MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ]
                    (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℝ) + MvPowerSeries.X 1))
                    =
                      MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ] (MvPowerSeries.X 0) +
                        MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ] (MvPowerSeries.X 1) := by
                          simpa using
                            (MvPowerSeries.subst_add (a := ![(X : ℝ⟦X⟧), Φ]) hb
                              (MvPowerSeries.X 0) (MvPowerSeries.X 1))
                _ = (X : ℝ⟦X⟧) + Φ := by
                      simp [MvPowerSeries.subst_X, hb]
            congr 1
            funext u
            cases u
            exact hinner
  refine ⟨Φ, hΦ.constantCoeff_eq_zero, ?_⟩
  intro m
  -- Rewrite the generic recentered scalar recursion through the explicit substitution
  -- `S(X + Φ)`.
  calc
    PowerSeries.coeff (m + 1) Φ
        = ((m + 1 : ℝ)⁻¹) *
            PowerSeries.coeff m
              (MvPowerSeries.subst ![(X : ℝ⟦X⟧), Φ] F) := by
                simpa using formal_recentered_solution_next_coeff_eq (R := ℝ) hΦ m
    _ = ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst ((X : ℝ⟦X⟧) + Φ)) := by
          rw [hcomp]

/-- Helper for Cartan section27 0001_Theorem_I: if a real scalar power series has nonnegative
coefficients through degree `m`, then the same is true for the degree-`m` coefficient of every
power, provided the constant coefficient vanishes. -/
private theorem coeffPow_nonneg_of_nonnegativePrefix
    {U : ℝ⟦X⟧} (hU0 : PowerSeries.constantCoeff U = 0) {m : ℕ}
    (hU : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k U) :
    ∀ d, 0 ≤ PowerSeries.coeff m (U ^ d)
  | d => by
      -- Expand the coefficient into the positive-tuple formula and bound each product term.
      rw [coeff_pow_eq_sum_positive_tuples_of_constantCoeff_zero hU0 m d]
      refine Finset.sum_nonneg ?_
      intro e he
      by_cases hsum : ∑ i, e i = m
      · simp [hsum]
        refine Finset.prod_nonneg ?_
        intro i hi
        have hei_le : e i ≤ m := by
          rw [← hsum]
          exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        have heIco : ∀ i : Fin d, e i ∈ Finset.Ico 1 (m + 1) := by
          simpa [Fintype.mem_piFinset] using he
        exact hU (e i) hei_le
      · simp [hsum]

/-- Helper for Cartan section27 0001_Theorem_I: a scalar substitution with nonnegative outer
coefficients and nonnegative inner coefficients still has nonnegative coefficient in degree `m`. -/
private theorem coeffSubst_nonneg_of_nonnegativePrefix
    {S U : ℝ⟦X⟧} (hS : ∀ d, 0 ≤ PowerSeries.coeff d S)
    (hU0 : PowerSeries.constantCoeff U = 0) {m : ℕ}
    (hU : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k U) :
    0 ≤ PowerSeries.coeff m (S.subst U) := by
  -- Rewrite substitution by the finite coefficient sum and bound each summand separately.
  rw [coeff_subst_eq_sum_range_of_constantCoeff_zero hU0 m]
  refine Finset.sum_nonneg ?_
  intro d hd
  exact mul_nonneg (hS d) (coeffPow_nonneg_of_nonnegativePrefix hU0 hU d)

/-- Helper for Cartan section27 0001_Theorem_I: coefficientwise nonnegative prefix majorants
propagate through powers in the target degree. -/
private theorem coeffPow_mono_of_nonnegativePrefixMajorant
    {U V : ℝ⟦X⟧} (hU0 : PowerSeries.constantCoeff U = 0)
    (hV0 : PowerSeries.constantCoeff V = 0) {m : ℕ}
    (hU_nonneg : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k U)
    (hV_nonneg : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k V)
    (hUV : ∀ k ≤ m, PowerSeries.coeff k U ≤ PowerSeries.coeff k V) :
    ∀ d, PowerSeries.coeff m (U ^ d) ≤ PowerSeries.coeff m (V ^ d)
  | d => by
      -- Compare the positive-tuple formulas term by term using the prefix majorant.
      rw [coeff_pow_eq_sum_positive_tuples_of_constantCoeff_zero hU0 m d,
        coeff_pow_eq_sum_positive_tuples_of_constantCoeff_zero hV0 m d]
      refine Finset.sum_le_sum ?_
      intro e he
      by_cases hsum : ∑ i, e i = m
      · simp [hsum]
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          have hei_le : e i ≤ m := by
            rw [← hsum]
            exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
          have heIco : ∀ i : Fin d, e i ∈ Finset.Ico 1 (m + 1) := by
            simpa [Fintype.mem_piFinset] using he
          exact hU_nonneg (e i) hei_le
        · intro i hi
          have hei_le : e i ≤ m := by
            rw [← hsum]
            exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
          have heIco : ∀ i : Fin d, e i ∈ Finset.Ico 1 (m + 1) := by
            simpa [Fintype.mem_piFinset] using he
          exact hUV (e i) hei_le
      · simp [hsum]

/-- Helper for Cartan section27 0001_Theorem_I: substitution into a scalar series with
nonnegative coefficients is monotone for coefficientwise prefix majorants. -/
theorem coeffSubst_mono_of_nonnegative_prefixMajorant
    {S U V : ℝ⟦X⟧} {m : ℕ} (hS : ∀ d, 0 ≤ PowerSeries.coeff d S)
    (hU0 : PowerSeries.constantCoeff U = 0) (hV0 : PowerSeries.constantCoeff V = 0)
    (hU_nonneg : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k U)
    (hV_nonneg : ∀ k ≤ m, 0 ≤ PowerSeries.coeff k V)
    (hUV : ∀ k ≤ m, PowerSeries.coeff k U ≤ PowerSeries.coeff k V) :
    PowerSeries.coeff m (S.subst U) ≤ PowerSeries.coeff m (S.subst V) := by
  -- Rewrite both coefficients by the finite substitution formula and compare degree by degree.
  rw [coeff_subst_eq_sum_range_of_constantCoeff_zero hU0 m,
    coeff_subst_eq_sum_range_of_constantCoeff_zero hV0 m]
  refine Finset.sum_le_sum ?_
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (coeffPow_mono_of_nonnegativePrefixMajorant hU0 hV0 hU_nonneg hV_nonneg hUV d)
    (hS d)

/-- Helper for Cartan section27 0001_Theorem_I: the formal variable has infinite radius because
it is a polynomial of degree `1`. -/
private theorem powerSeriesX_radius_eq_top : (X : ℝ⟦X⟧).radius = ⊤ := by
  rw [PowerSeries.radius]
  apply (FormalMultilinearSeries.ofScalars ℝ fun n ↦
    PowerSeries.coeff n (X : ℝ⟦X⟧)).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro n hn
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := ℝ)
    (c := fun m ↦ PowerSeries.coeff m (X : ℝ⟦X⟧)) (by
      have hn1 : n ≠ 1 := by omega
      simp [PowerSeries.coeff_X, hn1])

/-- Helper for Cartan section27 0001_Theorem_I: scalar multiplication by a nonzero constant
preserves the convergence radius of a scalar power series. -/
private theorem radius_smul_eq_powerSeries (c : ℝ) (F : ℝ⟦X⟧) (hc : c ≠ 0) :
    (c • F).radius = F.radius := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ
    fun n ↦ PowerSeries.coeff n F
  have hsmul :
      FormalMultilinearSeries.ofScalars ℝ (fun n ↦ PowerSeries.coeff n (c • F)) = c • p := by
    ext n
    simp [p]
  calc
    (c • F).radius = (FormalMultilinearSeries.ofScalars ℝ fun n ↦ PowerSeries.coeff n (c • F)).radius := rfl
    _ = (c • p).radius := by rw [hsmul]
    _ = p.radius := FormalMultilinearSeries.radius_smul_eq p hc
    _ = F.radius := rfl

/-- Helper for Cartan section27 0001_Theorem_I: integrating coefficientwise does not destroy a
positive convergence radius. -/
private theorem primitiveSeries_radiusPos {A : ℝ⟦X⟧} (hA : 0 < A.radius) :
    0 < (primitiveSeries A).radius := by
  -- Compare the primitive coefficientwise with `X * A`, whose radius is controlled directly by
  -- the positive radius of `A`.
  have hcoeff :
      ∀ n, ‖PowerSeries.coeff n (primitiveSeries A)‖ ≤ ‖PowerSeries.coeff n ((X : ℝ⟦X⟧) * A)‖ := by
    intro n
    cases n with
    | zero =>
        simp [primitiveSeries]
    | succ n =>
        have hInv_nonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
        have hNat : (1 : ℝ) ≤ n + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have hInv_le_one : ((n + 1 : ℝ)⁻¹) ≤ 1 := by
          simpa using
            (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
              hNat)
        calc
          ‖PowerSeries.coeff (n + 1) (primitiveSeries A)‖
              = ‖((n + 1 : ℝ)⁻¹) * PowerSeries.coeff n A‖ := by
                  simp [primitiveSeries]
          _ = ‖(n + 1 : ℝ)⁻¹‖ * ‖PowerSeries.coeff n A‖ := by
                rw [norm_mul]
          _ = ((n + 1 : ℝ)⁻¹) * ‖PowerSeries.coeff n A‖ := by
                have hInv_pos : 0 < ((n + 1 : ℝ)⁻¹) := by positivity
                rw [Real.norm_eq_abs, abs_of_pos hInv_pos]
          _ ≤ 1 * ‖PowerSeries.coeff n A‖ := by
                exact mul_le_mul_of_nonneg_right hInv_le_one (norm_nonneg _)
          _ = ‖PowerSeries.coeff (n + 1) ((X : ℝ⟦X⟧) * A)‖ := by
                simp [PowerSeries.coeff_X_pow_mul']
  have hmul_le :
      ((X : ℝ⟦X⟧) * A).radius ≤ (primitiveSeries A).radius := by
    simpa [PowerSeries.radius, FormalMultilinearSeries.ofScalars_norm] using
      (FormalMultilinearSeries.radius_le_of_le
        (p := FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ PowerSeries.coeff n (primitiveSeries A)))
        (q := FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ PowerSeries.coeff n ((X : ℝ⟦X⟧) * A)))
        (fun n ↦ by
          simpa [FormalMultilinearSeries.ofScalars_norm] using hcoeff n))
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hA with ⟨r, hr0, hrA⟩
  have hrX : (r : ENNReal) ≤ (X : ℝ⟦X⟧).radius := by
    rw [powerSeriesX_radius_eq_top]
    simp
  have hrMul : (r : ENNReal) ≤ ((X : ℝ⟦X⟧) * A).radius := by
    exact radius_ge_mul (X : ℝ⟦X⟧) A r hrX hrA.le
  exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hr0) (le_trans hrMul hmul_le)

/-- Helper for Cartan section27 0001_Theorem_I: the scalar fixed-point series for
`Φ' = S(X + Φ)` has coefficientwise nonnegative coefficients when the owner `S` does. -/
theorem scalarSubstFormalSolution_coeff_nonneg {S Φ : ℝ⟦X⟧}
    (hS : ∀ d, 0 ≤ PowerSeries.coeff d S) (hΦ0 : PowerSeries.constantCoeff Φ = 0)
    (hΦrec : ∀ m, PowerSeries.coeff (m + 1) Φ =
      ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst ((X : ℝ⟦X⟧) + Φ))) :
    ∀ m, 0 ≤ PowerSeries.coeff m Φ := by
  -- Induct on the target degree and read the next coefficient from the substituted right-hand
  -- side, whose degree-`m` coefficient depends only on the already-controlled prefix.
  intro m
  have hcoeff : ∀ M, ∀ k ≤ M, 0 ≤ PowerSeries.coeff k Φ := by
    intro M
    induction M with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0]
    | succ M ih =>
        intro k hk
        by_cases hkM : k ≤ M
        · exact ih k hkM
        · have hk_eq : k = M + 1 := by omega
          subst hk_eq
          have hU0 : PowerSeries.constantCoeff ((X : ℝ⟦X⟧) + Φ) = 0 := by
            simp [hΦ0]
          have hU_nonneg : ∀ j ≤ M, 0 ≤ PowerSeries.coeff j ((X : ℝ⟦X⟧) + Φ) := by
            intro j hj
            cases j with
            | zero =>
                simp [hΦ0]
            | succ j =>
                cases j with
                | zero =>
                    have hΦ1 : 0 ≤ PowerSeries.coeff 1 Φ := ih 1 hj
                    simpa using add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hΦ1
                | succ j =>
                    have hj' : j + 2 ≤ M := by omega
                    simpa [PowerSeries.coeff_X] using ih (j + 2) hj'
          -- The fixed-point recursion reduces positivity to the substituted right-hand side.
          rw [hΦrec M]
          exact mul_nonneg (by positivity)
            (coeffSubst_nonneg_of_nonnegativePrefix hS hU0 hU_nonneg)
  exact hcoeff m m le_rfl

/-- Helper for Cartan section27 0001_Theorem_I: the scalar fixed-point series for
`Φ' = S(X + Φ)` has positive convergence radius as soon as `S` does. -/
theorem scalarSubstFormalSolution_radiusPos {S Φ : ℝ⟦X⟧}
    (hS0 : 0 ≤ PowerSeries.constantCoeff S) (hSrad : 0 < S.radius)
    (hΦ0 : PowerSeries.constantCoeff Φ = 0)
    (hΦrec : ∀ m, PowerSeries.coeff (m + 1) Φ =
      ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst ((X : ℝ⟦X⟧) + Φ))) :
    0 < Φ.radius := by
  let Ψ : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + Φ
  let T : ℝ⟦X⟧ := ((1 : ℝ⟦X⟧) + S)⁻¹
  let G : ℝ⟦X⟧ := primitiveSeries T
  have hΨ0 : PowerSeries.constantCoeff Ψ = 0 := by
    simp [Ψ, hΦ0]
  have hΨsub : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero' hΨ0
  have hΦderiv :
      d⁄dX ℝ Φ = S.subst Ψ := by
    -- The coefficient recursion is exactly the derivative equation for the scalar fixed point.
    ext m
    calc
      PowerSeries.coeff m (d⁄dX ℝ Φ)
          = PowerSeries.coeff (m + 1) Φ * (m + 1 : ℝ) := by
              rw [PowerSeries.coeff_derivative]
      _ = (((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst Ψ)) * (m + 1 : ℝ) := by
            rw [hΦrec m]
      _ = PowerSeries.coeff m (S.subst Ψ) := by
            have hne : (m + 1 : ℝ) ≠ 0 := by positivity
            calc
              (((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m (S.subst Ψ)) * (m + 1 : ℝ)
                  = PowerSeries.coeff m (S.subst Ψ) * (((m + 1 : ℝ)⁻¹) * (m + 1 : ℝ)) := by
                      ring
              _ = PowerSeries.coeff m (S.subst Ψ) := by
                    simp [hne]
  have hΨderiv :
      d⁄dX ℝ Ψ = 1 + S.subst Ψ := by
    -- Differentiate `Ψ = X + Φ` and insert the fixed-point identity for `Φ'`.
    simp [Ψ, hΦderiv]
  have hOneRadius : (1 : ℝ⟦X⟧).radius = ⊤ := by
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ
      fun n ↦ PowerSeries.coeff n (1 : ℝ⟦X⟧)
    change p.radius = ⊤
    refine p.radius_eq_top_of_forall_image_add_eq_zero 1 ?_
    intro m
    simp [p, PowerSeries.coeff_one]
  have hOneAddSrad : 0 < ((1 : ℝ⟦X⟧) + S).radius := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hSrad with ⟨r, hr0, hrS⟩
    have hrOne : (r : ENNReal) ≤ (1 : ℝ⟦X⟧).radius := by
      rw [hOneRadius]
      simp
    have hrAdd : (r : ENNReal) ≤ ((1 : ℝ⟦X⟧) + S).radius := by
      exact radius_ge_add (1 : ℝ⟦X⟧) S r hrOne hrS.le
    exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hr0) hrAdd
  have hTmul : ((1 : ℝ⟦X⟧) + S) * T = 1 := by
    -- The constant coefficient of `1 + S` is `1`, so its inverse is a genuine multiplicative
    -- inverse in the scalar power-series ring.
    have hconst : PowerSeries.constantCoeff ((1 : ℝ⟦X⟧) + S) ≠ 0 := by
      have hconst' : (1 + PowerSeries.constantCoeff S : ℝ) ≠ 0 := by
        linarith
      simpa using hconst'
    simpa [T] using PowerSeries.mul_inv_cancel ((1 : ℝ⟦X⟧) + S) hconst
  have hTpos : 0 < T.radius := by
    have hTne :
        T.radius ≠ 0 :=
      radius_ne_zero_of_mul_eq_one ((1 : ℝ⟦X⟧) + S) T (ne_of_gt hOneAddSrad) hTmul
    exact pos_iff_ne_zero.2 hTne
  have hGpos : 0 < G.radius := primitiveSeries_radiusPos hTpos
  have hsubOne : PowerSeries.subst Ψ (1 : ℝ⟦X⟧) = (1 : ℝ⟦X⟧) := by
    rw [show (1 : ℝ⟦X⟧) = C (1 : ℝ) by simp, PowerSeries.subst_C]
    simp
  have hsubstInverse :
      PowerSeries.subst Ψ T * (1 + PowerSeries.subst Ψ S) = 1 := by
    -- Transport the inverse relation for `1 + S` through substitution by `Ψ`.
    calc
      PowerSeries.subst Ψ T * (1 + PowerSeries.subst Ψ S)
          = PowerSeries.subst Ψ T * PowerSeries.subst Ψ ((1 : ℝ⟦X⟧) + S) := by
              rw [PowerSeries.subst_add hΨsub (1 : ℝ⟦X⟧) S, hsubOne]
      _ = PowerSeries.subst Ψ (T * ((1 : ℝ⟦X⟧) + S)) := by
            symm
            exact PowerSeries.subst_mul hΨsub T ((1 : ℝ⟦X⟧) + S)
      _ = 1 := by
            have hTmul' : T * ((1 : ℝ⟦X⟧) + S) = 1 := by
              simpa [mul_comm] using hTmul
            rw [hTmul', hsubOne]
  have hGsubstDeriv :
      d⁄dX ℝ (G.subst Ψ) = 1 := by
    -- Differentiate the composed primitive and collapse the derivative to the inverse identity.
    calc
      d⁄dX ℝ (G.subst Ψ)
          = PowerSeries.subst Ψ (d⁄dX ℝ G) * d⁄dX ℝ Ψ := by
              rw [PowerSeries.derivative_subst (A := ℝ) (f := G) (g := Ψ) hΨsub]
      _ = PowerSeries.subst Ψ T * (1 + S.subst Ψ) := by
            rw [derivative_primitiveSeries, hΨderiv]
      _ = 1 := by simpa using hsubstInverse
  have hGsubst0 : PowerSeries.constantCoeff (G.subst Ψ) = 0 := by
    -- The primitive has vanishing constant term, so the same holds after substituting a
    -- zero-constant inner series.
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [coeff_subst_eq_sum_range_of_constantCoeff_zero hΨ0 0]
    simp [G, primitiveSeries_constantCoeff]
  have hGsubst : G.subst Ψ = (X : ℝ⟦X⟧) := by
    -- Equal derivatives and equal constant coefficients force equality of scalar series.
    apply PowerSeries.derivative.ext
    · simpa [PowerSeries.derivative_X] using hGsubstDeriv
    · simpa [hGsubst0]
  have hΨpos : 0 < Ψ.radius := by
    have hΨne :
        Ψ.radius ≠ 0 :=
      radius_ne_zero_of_subst_eq_X G Ψ hΨ0 hGsubst (ne_of_gt hGpos)
    exact pos_iff_ne_zero.2 hΨne
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hΨpos with ⟨r, hr0, hrΨ⟩
  have hrX : (r : ENNReal) ≤ (-((X : ℝ⟦X⟧))).radius := by
    rw [show (-((X : ℝ⟦X⟧))).radius = (X : ℝ⟦X⟧).radius by
      simpa using radius_smul_eq_powerSeries (-1 : ℝ) (X : ℝ⟦X⟧) (by norm_num)]
    rw [powerSeriesX_radius_eq_top]
    simp
  have hrΦ : (r : ENNReal) ≤ Φ.radius := by
    simpa [Ψ, sub_eq_add_neg] using radius_ge_add Ψ (-((X : ℝ⟦X⟧))) r hrΨ.le hrX
  exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hr0) hrΦ
