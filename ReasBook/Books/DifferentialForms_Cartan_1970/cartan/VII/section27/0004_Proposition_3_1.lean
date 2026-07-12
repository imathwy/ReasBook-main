import DifferentialForms_Cartan_1970.VII.section27.«0002_Proposition_2_1»
import DifferentialForms_Cartan_1970.VII.section27.«0003_Definition_VII_1_extra_1»

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

-- Domain sampling for this file:
-- * source-facing ODE owner: `PowerSeries.IsFormalFirstOrderOdeSolution`
-- * source-facing majorant owners: `MvPowerSeries.IsMajorantSeries`,
--   `PowerSeries.IsMajorantSeries`
-- * canonical derived coefficient bridge used by the source proof: `PowerSeries.coeff_derivative`

/-- Helper for Proposition 3.1: coefficientwise domination through degree `n` is preserved by
taking powers of the formal series. -/
private theorem coeff_pow_le_of_coeff_le_upto {φ : ℂ⟦X⟧} {Φ : NNReal⟦X⟧} {n : ℕ}
    (hcoeff : ∀ m ≤ n, ‖PowerSeries.coeff m φ‖ ≤ ((PowerSeries.coeff m Φ : NNReal) : ℝ)) :
    ∀ q k, k ≤ n →
      ‖PowerSeries.coeff k (φ ^ q)‖ ≤ ((PowerSeries.coeff k (Φ ^ q) : NNReal) : ℝ)
  | 0, k, hk => by
      -- The zeroth power is `1`, so only the constant coefficient can be nonzero.
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · simp [pow_zero, hk0]
  | q + 1, k, hk => by
      -- Rewrite the next power by the Cauchy product and compare each antidiagonal term.
      calc
        ‖PowerSeries.coeff k (φ ^ (q + 1))‖ = ‖∑ a ∈ Finset.antidiagonal k,
            PowerSeries.coeff a.1 (φ ^ q) * PowerSeries.coeff a.2 φ‖ := by
              rw [pow_succ, PowerSeries.coeff_mul]
        _ ≤ ∑ a ∈ Finset.antidiagonal k,
              ‖PowerSeries.coeff a.1 (φ ^ q) * PowerSeries.coeff a.2 φ‖ := by
                exact norm_sum_le _ _
        _ = ∑ a ∈ Finset.antidiagonal k,
              ‖PowerSeries.coeff a.1 (φ ^ q)‖ * ‖PowerSeries.coeff a.2 φ‖ := by
                simp
        _ ≤ ∑ a ∈ Finset.antidiagonal k,
              ((PowerSeries.coeff a.1 (Φ ^ q) : NNReal) : ℝ) *
                ((PowerSeries.coeff a.2 Φ : NNReal) : ℝ) := by
                  refine Finset.sum_le_sum ?_
                  intro a ha
                  have ha' : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha
                  have ha1_le : a.1 ≤ n := by omega
                  have ha2_le : a.2 ≤ n := by omega
                  exact mul_le_mul
                    (coeff_pow_le_of_coeff_le_upto hcoeff q a.1 ha1_le)
                    (hcoeff a.2 ha2_le)
                    (norm_nonneg _)
                    (by positivity)
        _ = ((∑ a ∈ Finset.antidiagonal k,
              PowerSeries.coeff a.1 (Φ ^ q) * PowerSeries.coeff a.2 Φ : NNReal) : ℝ) := by
                simp [NNReal.coe_mul]
        _ = ((PowerSeries.coeff k (Φ ^ (q + 1)) : NNReal) : ℝ) := by
              rw [pow_succ, PowerSeries.coeff_mul]

/-- Helper for Proposition 3.1: if the coefficients of `φ` are dominated through degree `n`,
then the same holds for the degree-`n` coefficient of the two ODE right-hand sides. -/
private theorem ode_rhs_coeff_le_of_coeff_le_upto {f : ℂ⟦X,Y⟧} {F : NNReal⟦X,Y⟧}
    (hF : MvPowerSeries.IsMajorantSeries f F) {φ : ℂ⟦X⟧} {Φ : NNReal⟦X⟧} {n : ℕ}
    (hcoeff : ∀ m ≤ n, ‖PowerSeries.coeff m φ‖ ≤ ((PowerSeries.coeff m Φ : NNReal) : ℝ)) :
    ‖∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ ≤
      ((∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (Φ ^ q) : NNReal) : ℝ) := by
  -- First bound the complex triangular sum by the sum of the norms of its summands.
  calc
    ‖∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ ≤
      ∑ p ∈ Finset.range (n + 1), ‖∑ q ∈ Finset.range (n + 1 - p),
        MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          ‖MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact norm_sum_le _ _
    _ = ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          ‖MvPowerSeries.coeffXY f p q‖ * ‖PowerSeries.coeff (n - p) (φ ^ q)‖ := by
            simp
    _ ≤ ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          ((MvPowerSeries.coeffXY F p q : NNReal) : ℝ) *
            ((PowerSeries.coeff (n - p) (Φ ^ q) : NNReal) : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro p hp
              refine Finset.sum_le_sum ?_
              intro q hq
              exact mul_le_mul (hF.coeff_le p q)
                (coeff_pow_le_of_coeff_le_upto hcoeff q (n - p) (Nat.sub_le _ _))
                (norm_nonneg _)
                (by positivity)
    _ = ((∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
          MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (Φ ^ q) : NNReal) : ℝ) := by
            simp [NNReal.coe_mul]

/-- Helper for Proposition 3.1: the formal solution of the majorant equation dominates every
coefficient of the original formal solution degree by degree. -/
private theorem formal_solution_coeff_le_upto {f : ℂ⟦X,Y⟧} {F : NNReal⟦X,Y⟧}
    (hF : MvPowerSeries.IsMajorantSeries f F) {φ : ℂ⟦X⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ f) {Φ : NNReal⟦X⟧}
    (hΦ : PowerSeries.IsFormalFirstOrderOdeSolution Φ F) :
    ∀ n m, m ≤ n → ‖PowerSeries.coeff m φ‖ ≤ ((PowerSeries.coeff m Φ : NNReal) : ℝ)
  | 0, m, hm => by
      -- At degree `0`, both formal solutions have the prescribed vanishing constant term.
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      simp [PowerSeries.IsFormalFirstOrderOdeSolution.coeff_zero hφ,
        PowerSeries.IsFormalFirstOrderOdeSolution.coeff_zero hΦ]
  | n + 1, m, hm => by
      by_cases hmn : m ≤ n
      · -- The inductive prefix already controls all earlier coefficients.
        exact formal_solution_coeff_le_upto hF hφ hΦ n m hmn
      · -- The new step comes from comparing the degree-`n` coefficients of the two derivatives.
        have hm_eq : m = n + 1 := by omega
        subst hm_eq
        have hprefix : ∀ k ≤ n, ‖PowerSeries.coeff k φ‖ ≤ ((PowerSeries.coeff k Φ : NNReal) : ℝ) :=
          fun k hk ↦ formal_solution_coeff_le_upto hF hφ hΦ n k hk
        have hrhs :
            ‖∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
                MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ ≤
              ((∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
                  MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (Φ ^ q) :
                    NNReal) : ℝ) :=
          ode_rhs_coeff_le_of_coeff_le_upto hF hprefix
        have hderiv :
            ‖PowerSeries.coeff n (d⁄dX ℂ φ)‖ ≤
              ((PowerSeries.coeff n (d⁄dX NNReal Φ) : NNReal) : ℝ) := by
          -- Rewrite both derivative coefficients using the defining coefficient equations.
          calc
            ‖PowerSeries.coeff n (d⁄dX ℂ φ)‖ = ‖∑ p ∈ Finset.range (n + 1),
                ∑ q ∈ Finset.range (n + 1 - p),
                  MvPowerSeries.coeffXY f p q * PowerSeries.coeff (n - p) (φ ^ q)‖ := by
                    rw [hφ.equation]
            _ ≤ ((∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1 - p),
                    MvPowerSeries.coeffXY F p q * PowerSeries.coeff (n - p) (Φ ^ q) :
                      NNReal) : ℝ) := hrhs
            _ = ((PowerSeries.coeff n (d⁄dX NNReal Φ) : NNReal) : ℝ) := by
                  rw [← hΦ.equation]
        have hmul :
            ‖(n + 1 : ℂ)‖ * ‖PowerSeries.coeff (n + 1) φ‖ ≤
              (n + 1 : ℝ) * ((PowerSeries.coeff (n + 1) Φ : NNReal) : ℝ) := by
          -- `coeff_derivative` rewrites the derivative bound into the next-coefficient step.
          simpa [PowerSeries.coeff_derivative, NNReal.coe_mul,
            mul_comm, mul_left_comm, mul_assoc] using hderiv
        have hnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
          simpa using Complex.norm_natCast (n + 1)
        have hmul' :
            (n + 1 : ℝ) * ‖PowerSeries.coeff (n + 1) φ‖ ≤
              (n + 1 : ℝ) * ((PowerSeries.coeff (n + 1) Φ : NNReal) : ℝ) := by
          simpa [hnorm] using hmul
        exact le_of_mul_le_mul_left hmul' (by positivity)

/-- Proposition 3.1: let `F(x, y)` be a majorant series of the complex power series `f(x, y)`,
and let `Φ` be a formal
solution with vanishing constant term of `dy/dx = F(x, y)`. Then `Φ` is a majorant series of any
formal solution `φ` with vanishing constant term of `dy/dx = f(x, y)`. The comparison is
coefficientwise, using the derivative coefficient formula and the majorant inequalities for `f`
and `F`. -/
theorem formal_majorant_solution
    {f : ℂ⟦X,Y⟧} {F : NNReal⟦X,Y⟧} (hF : MvPowerSeries.IsMajorantSeries f F) {φ : ℂ⟦X⟧}
    (hφ : PowerSeries.IsFormalFirstOrderOdeSolution φ f)
    {Φ : NNReal⟦X⟧} (hΦ : PowerSeries.IsFormalFirstOrderOdeSolution Φ F) :
    PowerSeries.IsMajorantSeries φ Φ := by
  refine ⟨hφ.constantCoeff_eq_zero, hΦ.constantCoeff_eq_zero, ?_⟩
  intro n
  -- The stronger prefix lemma already gives the required positive-degree coefficient bound.
  exact formal_solution_coeff_le_upto hF hφ hΦ (n + 1) (n + 1) le_rfl
