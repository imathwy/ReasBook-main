import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
import cartan.I.section02.«0004_Definition_I_2_extra_3»
import cartan.I.section02.«0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FormalMultilinearSeries Polynomial
open scoped PowerSeries

-- Domain sampling / source-core-bridge triage:
-- * primary domain: second-order linear recurrences and their scalar generating series.
-- * core/canonical owners sampled: `LinearRecurrence.mkSol`, `LinearRecurrence.is_sol_mkSol`,
--   `FormalMultilinearSeries.ofScalars`, `FormalMultilinearSeries.ofScalars_apply_eq`, and
--   `Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero`.
-- * primitive source-facing data here: the specific recurrence with initial values `0, 1`, and
--   the quadratic polynomial `β X^2 + α X - 1`.
-- * derived API here: the associated scalar formal power series, its radius/sum formulas, and the
--   closed-form statements obtained from the roots of the source-facing quadratic.

/- Exercise 8 is source-facing at the level of a specific second-order sequence. The canonical
owner for the recurrence law itself is `LinearRecurrence`; the sequence below is the canonical
solution with initial values `0, 1`. -/

section LinearRecurrence

variable {R : Type*} [CommSemiring R]

/-- The canonical `LinearRecurrence` underlying Exercise 8. -/
def secondOrderRecurrenceRel (α β : R) : LinearRecurrence R where
  order := 2
  coeffs := ![β, α]

/-- The coefficient sequence defined by the second-order recurrence in Exercise 8. -/
def secondOrderRecurrence (α β : R) : ℕ → R :=
  (secondOrderRecurrenceRel α β).mkSol ![0, 1]

/-- `secondOrderRecurrence` is the canonical solution of `secondOrderRecurrenceRel`. -/
theorem secondOrderRecurrence_isSolution (α β : R) :
    (secondOrderRecurrenceRel α β).IsSolution (secondOrderRecurrence α β) :=
  (secondOrderRecurrenceRel α β).is_sol_mkSol ![0, 1]

@[simp] theorem secondOrderRecurrence_zero (α β : R) :
    secondOrderRecurrence α β 0 = 0 := by
  simpa [secondOrderRecurrence] using
    (secondOrderRecurrenceRel α β).mkSol_eq_init ![0, 1] (0 : Fin 2)

@[simp] theorem secondOrderRecurrence_one (α β : R) :
    secondOrderRecurrence α β 1 = 1 := by
  simpa [secondOrderRecurrence] using
    (secondOrderRecurrenceRel α β).mkSol_eq_init ![0, 1] (1 : Fin 2)

/-- The defining second-order recursion for `secondOrderRecurrence`. -/
theorem secondOrderRecurrence_succ_succ (α β : R) (n : ℕ) :
    secondOrderRecurrence α β (n + 2) =
      α * secondOrderRecurrence α β (n + 1) + β * secondOrderRecurrence α β n := by
  have h := secondOrderRecurrence_isSolution α β n
  rw [secondOrderRecurrenceRel, Fin.sum_univ_two] at h
  simpa [secondOrderRecurrence, add_assoc, add_comm, add_left_comm] using h

end LinearRecurrence

section ScalarSeries

universe u

section CompleteAnalyticBridge

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂]

/-- Helper for Exercise 8: the quadratic denominator of the generating-function identity, viewed as
a scalar power series. -/
private noncomputable def secondOrderRecurrenceDenominatorSeries (α β : 𝕂) : 𝕂⟦X⟧ :=
  (1 : 𝕂⟦X⟧) - PowerSeries.C α * PowerSeries.X - PowerSeries.C β * PowerSeries.X ^ 2

/-- Helper for Exercise 8: a scalar sequence packaged as a scalar power series. -/
private noncomputable def secondOrderRecurrenceSolutionSeries (a : ℕ → 𝕂) : 𝕂⟦X⟧ :=
  PowerSeries.mk a

/-- Helper for Exercise 8: the denominator series has no coefficients above degree `2`. -/
private theorem secondOrderRecurrenceDenominatorSeries_coeff_eq_zero_of_three_le
    (α β : 𝕂) {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff n (secondOrderRecurrenceDenominatorSeries α β) = 0 := by
  -- The denominator only has constant, linear, and quadratic terms.
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have hone : PowerSeries.coeff n (1 : 𝕂⟦X⟧) = 0 := by
    simp [PowerSeries.coeff_one, h0]
  have hαX : PowerSeries.coeff n (PowerSeries.C α * PowerSeries.X : 𝕂⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X, h1]
  have hβX : PowerSeries.coeff n (PowerSeries.C β * PowerSeries.X ^ 2 : 𝕂⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X_pow, h2]
  simp [secondOrderRecurrenceDenominatorSeries, hone, hαX, hβX]

/-- Helper for Exercise 8: the formal variable `X` has no coefficients above degree `1`. -/
private theorem secondOrderRecurrence_X_coeff_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff n (PowerSeries.X : 𝕂⟦X⟧) = 0 := by
  -- The series `X` is supported exactly in degree `1`.
  have h1 : n ≠ 1 := by omega
  simp [PowerSeries.coeff_X, h1]

/-- Helper for Exercise 8: multiplying by the quadratic denominator sends the coefficient series to
the formal variable `X`. -/
private theorem secondOrderRecurrence_formal_series_mul_identity
    (α β : 𝕂) (a : ℕ → 𝕂) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hrec : ∀ n : ℕ, a (n + 2) = α * a (n + 1) + β * a n) :
    secondOrderRecurrenceDenominatorSeries α β * secondOrderRecurrenceSolutionSeries a =
      PowerSeries.X := by
  let S : 𝕂⟦X⟧ := secondOrderRecurrenceSolutionSeries a
  ext n
  rcases n with _ | (_ | n)
  · -- The constant coefficient vanishes because `a₀ = 0`.
    simp [secondOrderRecurrenceDenominatorSeries, secondOrderRecurrenceSolutionSeries, ha0]
  · -- The linear coefficient is normalized by `a₁ = 1`.
    have hα :
        PowerSeries.coeff 1 ((PowerSeries.C α * PowerSeries.X) * S) = α * a 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [pow_one, S, secondOrderRecurrenceSolutionSeries] using
        congrArg (fun x ↦ α * x) (PowerSeries.coeff_X_pow_mul S 1 0)
    have hβ :
        PowerSeries.coeff 1 ((PowerSeries.C β * PowerSeries.X ^ 2) * S) = 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      have hcoeff : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * S) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']
        norm_num
      rw [hcoeff]
      simp
    have hα' :
        PowerSeries.coeff 1
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk a) = α * a 0 := by
      simpa [S, secondOrderRecurrenceSolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff 1
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk a) = 0 := by
      simpa [S, secondOrderRecurrenceSolutionSeries] using hβ
    rw [secondOrderRecurrenceDenominatorSeries, sub_mul, sub_mul, one_mul]
    simp [sub_eq_add_neg, secondOrderRecurrenceSolutionSeries]
    rw [hα', hβ', ha0]
    simp [ha1]
  · -- Route correction: for coefficients `n + 2`, the Cauchy product is exactly the recurrence.
    have hα :
        PowerSeries.coeff (n + 2) ((PowerSeries.C α * PowerSeries.X) * S) =
          α * a (n + 1) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [pow_one, S, secondOrderRecurrenceSolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ α * x) (PowerSeries.coeff_X_pow_mul S 1 (n + 1))
    have hβ :
        PowerSeries.coeff (n + 2) ((PowerSeries.C β * PowerSeries.X ^ 2) * S) =
          β * a n := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [S, secondOrderRecurrenceSolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ β * x) (PowerSeries.coeff_X_pow_mul S 2 n)
    have hα' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk a) =
          α * a (n + 1) := by
      simpa [S, secondOrderRecurrenceSolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk a) =
          β * a n := by
      simpa [S, secondOrderRecurrenceSolutionSeries] using hβ
    rw [secondOrderRecurrenceDenominatorSeries, sub_mul, sub_mul, one_mul]
    simp [sub_eq_add_neg, secondOrderRecurrenceSolutionSeries]
    rw [hα', hβ', hrec n]
    ring_nf
    have hneq : 2 + n ≠ 1 := by omega
    simp [PowerSeries.coeff_X, hneq]

/-- Helper for Exercise 8: the quadratic denominator has infinite radius because it is a
polynomial. -/
private theorem secondOrderRecurrenceDenominatorSeries_radius_eq_top (α β : 𝕂) :
    (secondOrderRecurrenceDenominatorSeries α β).radius = ⊤ := by
  -- The coefficient sequence vanishes identically above degree `2`.
  rw [PowerSeries.radius]
  apply (ofScalars 𝕂
    (fun n ↦ PowerSeries.coeff n (secondOrderRecurrenceDenominatorSeries α β))
    ).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨3, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕂)
    (c := fun m ↦ PowerSeries.coeff m (secondOrderRecurrenceDenominatorSeries α β))
    (hc := secondOrderRecurrenceDenominatorSeries_coeff_eq_zero_of_three_le α β hn)

/-- Helper for Exercise 8: the formal variable has infinite radius because it is a polynomial of
degree `1`. -/
private theorem secondOrderRecurrence_X_radius_eq_top :
    (PowerSeries.X : 𝕂⟦X⟧).radius = ⊤ := by
  -- The coefficient sequence of `X` vanishes above degree `1`.
  rw [PowerSeries.radius]
  apply (ofScalars 𝕂 fun n ↦ PowerSeries.coeff n (PowerSeries.X : 𝕂⟦X⟧)
    ).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕂)
    (c := fun m ↦ PowerSeries.coeff m (PowerSeries.X : 𝕂⟦X⟧))
    (hc := secondOrderRecurrence_X_coeff_eq_zero_of_two_le hn)

/-- Helper for Exercise 8: evaluating the quadratic denominator series at `z` gives
`1 - α z - β z²`. -/
private theorem secondOrderRecurrenceDenominatorSeries_sum (α β z : 𝕂) :
    PowerSeries.sum (secondOrderRecurrenceDenominatorSeries α β) z =
      (1 : 𝕂) - α * z - β * z ^ 2 := by
  -- Finite support reduces the sum to the first three coefficients.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 3)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [secondOrderRecurrenceDenominatorSeries, pow_two]
    ring
  · intro n hn
    have hthree : 3 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (secondOrderRecurrenceDenominatorSeries α β) = 0 :=
      secondOrderRecurrenceDenominatorSeries_coeff_eq_zero_of_three_le α β hthree
    simp [hcoeff]

/-- Helper for Exercise 8: evaluating the formal variable at `z` gives `z`. -/
private theorem secondOrderRecurrence_X_sum (z : 𝕂) :
    PowerSeries.sum (PowerSeries.X : 𝕂⟦X⟧) z = z := by
  -- Finite support reduces the sum to the constant and linear coefficients.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [PowerSeries.coeff_X]
  · intro n hn
    have htwo : 2 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (PowerSeries.X : 𝕂⟦X⟧) = 0 :=
      secondOrderRecurrence_X_coeff_eq_zero_of_two_le htwo
    simp [hcoeff]

section

variable [CompleteSpace 𝕂]

/-- Helper for Exercise 8: over a complete field, the textbook generating-function identity follows
from the formal relation `(1 - αX - βX²) S(X) = X`. -/
private theorem secondOrderRecurrenceSeries_sum_mul_quadratic_complete
    (α β : 𝕂) (a : ℕ → 𝕂) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hrec : ∀ n : ℕ, a (n + 2) = α * a (n + 1) + β * a n) {z : 𝕂}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕂 a).radius) :
    (1 - α * z - β * z ^ 2) * (ofScalars 𝕂 a).sum z = z := by
  let D : 𝕂⟦X⟧ := secondOrderRecurrenceDenominatorSeries α β
  let S : 𝕂⟦X⟧ := secondOrderRecurrenceSolutionSeries a
  have hzS : (‖z‖₊ : ENNReal) < S.radius := by
    simpa [S, secondOrderRecurrenceSolutionSeries, PowerSeries.radius] using hz
  have hDtop : D.radius = ⊤ := by
    simpa [D] using secondOrderRecurrenceDenominatorSeries_radius_eq_top (α := α) (β := β)
  have hD_norm : Summable (fun n : ℕ ↦ ‖PowerSeries.coeff n D * z ^ n‖) := by
    have hDlt : (‖z‖₊ : ENNReal) < D.radius := by
      simp [hDtop]
    refine (summable_norm_coeff_mul_pow_of_lt_radius D (r := ‖z‖₊) hDlt).of_norm_bounded ?_
    intro n
    simp [norm_mul, norm_pow]
  have hS_norm : Summable (fun n : ℕ ↦ ‖PowerSeries.coeff n S * z ^ n‖) := by
    refine (summable_norm_coeff_mul_pow_of_lt_radius S (r := ‖z‖₊) hzS).of_norm_bounded ?_
    intro n
    simp [norm_mul, norm_pow]
  have hD :
      Summable (fun n : ℕ ↦ PowerSeries.coeff n D * z ^ n) := by
    have hD_hasSum :
        HasSum (fun n : ℕ ↦ PowerSeries.coeff n D * z ^ n) (PowerSeries.sum D z) := by
      simpa
        [PowerSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        (FormalMultilinearSeries.hasSum
          (p := ofScalars 𝕂 fun n ↦ PowerSeries.coeff n D)
          (x := z)
          (mem_eball_zero_iff.mpr <| by simp [hDtop]))
    exact hD_hasSum.summable
  have hS :
      Summable (fun n : ℕ ↦ PowerSeries.coeff n S * z ^ n) := by
    have hS_hasSum :
        HasSum (fun n : ℕ ↦ PowerSeries.coeff n S * z ^ n) (PowerSeries.sum S z) := by
      simpa
        [PowerSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        (FormalMultilinearSeries.hasSum
          (p := ofScalars 𝕂 fun n ↦ PowerSeries.coeff n S)
          (x := z)
          (mem_eball_zero_iff.mpr <| by simpa using hzS))
    exact hS_hasSum.summable
  have hmul :
      PowerSeries.sum (D * S) z = PowerSeries.sum D z * PowerSeries.sum S z :=
    sum_mul_eq_mul_sum D S z hD_norm hD hS_norm hS
  have hDsum : PowerSeries.sum D z = (1 : 𝕂) - α * z - β * z ^ 2 := by
    simpa [D] using secondOrderRecurrenceDenominatorSeries_sum (α := α) (β := β) z
  have hSsum : PowerSeries.sum S z = (ofScalars 𝕂 a).sum z := by
    simp [S, secondOrderRecurrenceSolutionSeries, PowerSeries.sum,
      FormalMultilinearSeries.ofScalarsSum]
  have hformal : D * S = (PowerSeries.X : 𝕂⟦X⟧) := by
    simpa [D, S] using
      secondOrderRecurrence_formal_series_mul_identity (α := α) (β := β) (a := a) ha0 ha1 hrec
  -- Evaluate the formal identity termwise and rewrite the finite series explicitly.
  calc
    (1 - α * z - β * z ^ 2) * (ofScalars 𝕂 a).sum z
        = PowerSeries.sum D z * PowerSeries.sum S z := by rw [hDsum, hSsum]
    _ = PowerSeries.sum (D * S) z := hmul.symm
    _ = PowerSeries.sum (PowerSeries.X : 𝕂⟦X⟧) z := by rw [hformal]
    _ = z := secondOrderRecurrence_X_sum z

end

end CompleteAnalyticBridge

/- The associated scalar power series is the canonical owner
`FormalMultilinearSeries.ofScalars 𝕜 (secondOrderRecurrence α β)`. Its pointwise evaluation is
given directly by `FormalMultilinearSeries.ofScalars_apply_eq`, so no local wrapper is kept here. -/

section SeminormedCommRing

variable {𝕜 : Type u} [SeminormedCommRing 𝕜] [NormOneClass 𝕜]

/-- Helper for Exercise 8: the shifted recurrence coefficients satisfy a uniform geometric bound. -/
lemma secondOrderRecurrence_norm_le_geometric_bound_succ (α β : 𝕜) (n : ℕ) :
    ‖secondOrderRecurrence α β (n + 1)‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ n := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  have hcα : ‖α‖ ≤ c := by
    -- The single constant `c` simultaneously dominates both recurrence coefficients.
    dsimp [c]
    exact (le_max_left ‖α‖ ‖β‖).trans (le_max_left _ _)
  have hcβ : ‖β‖ ≤ c := by
    -- The same domination applies to the second coefficient.
    dsimp [c]
    exact (le_max_right ‖α‖ ‖β‖).trans (le_max_left _ _)
  have hhalf : (1 / 2 : ℝ) ≤ c := by
    -- The lower bound `c ≥ 1 / 2` makes the geometric factor at least `1`.
    dsimp [c]
    exact le_max_right _ _
  have hc_nonneg : 0 ≤ c := by
    linarith
  have hone_le : 1 ≤ 2 * c := by
    linarith
  induction n using Nat.twoStepInduction with
  | zero =>
      -- The initial value is `a₁ = 1`, so the shifted bound starts exactly at `1`.
      simp [secondOrderRecurrence_one]
  | one =>
      -- The first recurrence step is controlled by the triangle inequality and `c ≥ 1 / 2`.
      rw [secondOrderRecurrence_succ_succ]
      calc
        ‖α * secondOrderRecurrence α β 1 + β * secondOrderRecurrence α β 0‖
            ≤ ‖α * secondOrderRecurrence α β 1‖ + ‖β * secondOrderRecurrence α β 0‖ := by
              exact norm_add_le _ _
        _ ≤ ‖α‖ * ‖secondOrderRecurrence α β 1‖ + ‖β‖ * ‖secondOrderRecurrence α β 0‖ := by
              gcongr
              · exact norm_mul_le _ _
              · exact norm_mul_le _ _
        _ = ‖α‖ := by simp
        _ ≤ c := hcα
        _ ≤ 2 * c := by linarith
        _ = (2 * c) ^ 1 := by rw [pow_one]
  | more n hn hn_succ =>
      -- The recurrence reduces `a_{n+3}` to the previous two shifted terms,
      -- which are already bounded.
      rw [secondOrderRecurrence_succ_succ α β (n + 1)]
      calc
        ‖α * secondOrderRecurrence α β (n + 2) + β * secondOrderRecurrence α β (n + 1)‖
            ≤ ‖α * secondOrderRecurrence α β (n + 2)‖
              + ‖β * secondOrderRecurrence α β (n + 1)‖ := by
                exact norm_add_le _ _
        _ ≤ ‖α‖ * ‖secondOrderRecurrence α β (n + 2)‖
              + ‖β‖ * ‖secondOrderRecurrence α β (n + 1)‖ := by
                gcongr
                · exact norm_mul_le _ _
                · exact norm_mul_le _ _
        _ ≤ ‖α‖ * (2 * c) ^ (n + 1) + ‖β‖ * (2 * c) ^ n := by
              gcongr
        _ ≤ c * (2 * c) ^ (n + 1) + ‖β‖ * (2 * c) ^ n := by
              gcongr
        _ ≤ c * (2 * c) ^ (n + 1) + c * (2 * c) ^ n := by
              gcongr
        _ ≤ c * (2 * c) ^ (n + 1) + c * (2 * c) ^ (n + 1) := by
              gcongr
              exact Nat.le_succ _
        _ = (2 * c) ^ (n + 2) := by
              rw [pow_succ']
              ring

/-- Exercise 8 (1): the recurrence coefficients satisfy the geometric bound
`‖a_n‖ ≤ (2c)^(n-1)` for all `n`, with `c = max (‖α‖, ‖β‖, 1 / 2)`. -/
theorem secondOrderRecurrence_norm_le_geometric_bound (α β : 𝕜) (n : ℕ) :
    ‖secondOrderRecurrence α β n‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ (n - 1) := by
  cases n with
  | zero =>
      -- The initial coefficient vanishes, so the unshifted bound is immediate.
      simp
  | succ n =>
      -- For positive indices, the shifted helper lemma is exactly the required estimate.
      simpa using secondOrderRecurrence_norm_le_geometric_bound_succ (α := α) (β := β) n

end SeminormedCommRing

section NontriviallyNormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Helper for Exercise 8: the completion of a nontrivially normed field is again nontrivially
normed. -/
private noncomputable instance completionNontriviallyNormedField :
    NontriviallyNormedField (UniformSpace.Completion 𝕜) := by
  refine NontriviallyNormedField.ofNormNeOne ?_
  rcases NontriviallyNormedField.non_trivial (α := 𝕜) with ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))
  refine ⟨(x : UniformSpace.Completion 𝕜), ?_, ?_⟩
  · simpa [UniformSpace.Completion.coe_eq_zero_iff] using hx0
  · simpa using (ne_of_gt hx)

/-- Helper for Exercise 8: coercing the coefficient series to the completion preserves its radius
because the coefficient norms do not change. -/
private theorem secondOrderRecurrenceSeries_radius_eq_completion_radius (α β : 𝕜) :
    (ofScalars (UniformSpace.Completion 𝕜)
      (fun n ↦ ((secondOrderRecurrence α β n : 𝕜) : UniformSpace.Completion 𝕜))).radius =
      (ofScalars 𝕜 (secondOrderRecurrence α β)).radius := by
  apply le_antisymm
  · simpa [FormalMultilinearSeries.ofScalars_norm] using
      (FormalMultilinearSeries.radius_le_of_le
        (p := ofScalars 𝕜 (secondOrderRecurrence α β))
        (q := ofScalars (UniformSpace.Completion 𝕜)
          (fun n ↦ ((secondOrderRecurrence α β n : 𝕜) : UniformSpace.Completion 𝕜)))
        (fun n ↦ by simp))
  · simpa [FormalMultilinearSeries.ofScalars_norm] using
      (FormalMultilinearSeries.radius_le_of_le
        (p := ofScalars (UniformSpace.Completion 𝕜)
          (fun n ↦ ((secondOrderRecurrence α β n : 𝕜) : UniformSpace.Completion 𝕜)))
        (q := ofScalars 𝕜 (secondOrderRecurrence α β))
        (fun n ↦ by simp))

/-- Helper for Exercise 8: descending the complete-space sum identity from `Completion 𝕜`
produces the expected rational sum in the base field. -/
lemma secondOrderRecurrenceSeries_hasSum_rat (α β : 𝕜) {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius) :
    HasSum (fun n : ℕ ↦ secondOrderRecurrence α β n * z ^ n)
      (z / (1 - α * z - β * z ^ 2)) := by
  let aCompl : ℕ → UniformSpace.Completion 𝕜 :=
    fun n ↦ ((secondOrderRecurrence α β n : 𝕜) : UniformSpace.Completion 𝕜)
  let ACompl :
      FormalMultilinearSeries
        (UniformSpace.Completion 𝕜) (UniformSpace.Completion 𝕜) (UniformSpace.Completion 𝕜) :=
    FormalMultilinearSeries.ofScalars
      (𝕜 := UniformSpace.Completion 𝕜) (E := UniformSpace.Completion 𝕜) aCompl
  have hz_compl :
      ENNReal.ofReal ‖((z : 𝕜) : UniformSpace.Completion 𝕜)‖ <
        ACompl.radius := by
    simpa [aCompl, ACompl,
      secondOrderRecurrenceSeries_radius_eq_completion_radius (α := α) (β := β)] using hz
  have hrec_compl :
      ∀ n : ℕ, aCompl (n + 2) =
        (α : UniformSpace.Completion 𝕜) * aCompl (n + 1) +
          (β : UniformSpace.Completion 𝕜) * aCompl n := by
    intro n
    have hrec_cast :
        aCompl (n + 2) =
          (((α * secondOrderRecurrence α β (n + 1) +
              β * secondOrderRecurrence α β n : 𝕜) : 𝕜) :
            UniformSpace.Completion 𝕜) := by
      exact congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : UniformSpace.Completion 𝕜))
        (secondOrderRecurrence_succ_succ (α := α) (β := β) n)
    have hcast :
        ((((α * secondOrderRecurrence α β (n + 1) +
            β * secondOrderRecurrence α β n : 𝕜) : 𝕜) :
          UniformSpace.Completion 𝕜)) =
          (α : UniformSpace.Completion 𝕜) * aCompl (n + 1) +
            (β : UniformSpace.Completion 𝕜) * aCompl n := by
      rw [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.coe_mul]
    exact hrec_cast.trans hcast
  have ha0_compl : aCompl 0 = 0 := by
    simp [aCompl]
  have ha1_compl : aCompl 1 = 1 := by
    simp [aCompl]
  have hmul_compl :
      (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
          (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2) *
          ACompl.sum (z : UniformSpace.Completion 𝕜) =
        (z : UniformSpace.Completion 𝕜) := by
    exact secondOrderRecurrenceSeries_sum_mul_quadratic_complete
      (α := (α : UniformSpace.Completion 𝕜)) (β := (β : UniformSpace.Completion 𝕜))
      (a := aCompl) (ha0 := ha0_compl) (ha1 := ha1_compl) (hrec := hrec_compl) (hz := hz_compl)
  have hden_compl :
      1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
        (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2 ≠ 0 := by
    intro hzero
    have hz_zero : (z : UniformSpace.Completion 𝕜) = 0 := by
      simpa [hzero] using hmul_compl.symm
    have : (1 : UniformSpace.Completion 𝕜) = 0 := by
      calc
        (1 : UniformSpace.Completion 𝕜)
            = 1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
                (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2 := by
                simp [hz_zero]
        _ = 0 := hzero
    exact one_ne_zero this
  have hsum_compl :
      ACompl.sum (z : UniformSpace.Completion 𝕜) =
        (z : UniformSpace.Completion 𝕜) /
          (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
            (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2) := by
    apply (eq_div_iff hden_compl).2
    simpa [mul_comm] using hmul_compl
  have hs_compl :
      HasSum (fun n : ℕ ↦ aCompl n * (z : UniformSpace.Completion 𝕜) ^ n)
        ((z : UniformSpace.Completion 𝕜) /
          (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
            (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2)) := by
    have hs_owner :
        HasSum
          (fun n : ℕ ↦ ACompl n
            fun _ ↦ (z : UniformSpace.Completion 𝕜))
          (ACompl.sum (z : UniformSpace.Completion 𝕜)) := by
      exact FormalMultilinearSeries.hasSum
        (p := ACompl)
        (x := (z : UniformSpace.Completion 𝕜))
        (mem_eball_zero_iff.mpr <| by simpa using hz_compl)
    simpa [aCompl, ACompl, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm,
      hsum_compl]
      using hs_owner
  have hs_base_expanded :
      HasSum
        (UniformSpace.Completion.toCompl ∘
          fun n : ℕ ↦ secondOrderRecurrence α β n * z ^ n)
        ((z : UniformSpace.Completion 𝕜) /
          (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
            (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2)) := by
    convert hs_compl using 1
    ext n
    change (((secondOrderRecurrence α β n * z ^ n : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
      aCompl n * (z : UniformSpace.Completion 𝕜) ^ n
    rw [UniformSpace.Completion.coe_mul]
    dsimp [aCompl]
    have hzpow :
        (((z ^ n : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
          (z : UniformSpace.Completion 𝕜) ^ n :=
        (UniformSpace.Completion.coeRingHom : 𝕜 →+* UniformSpace.Completion 𝕜).map_pow z n
    rw [hzpow]
  have hs_base :
      HasSum
        (UniformSpace.Completion.toCompl ∘
          fun n : ℕ ↦ secondOrderRecurrence α β n * z ^ n)
        (((z / (1 - α * z - β * z ^ 2) : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) := by
    have hrat :
        (((z / (1 - α * z - β * z ^ 2) : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
          ((z : UniformSpace.Completion 𝕜) /
            (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
              (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2)) := by
      have hzpow :
          (((z ^ 2 : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
            (z : UniformSpace.Completion 𝕜) ^ 2 :=
        (UniformSpace.Completion.coeRingHom : 𝕜 →+* UniformSpace.Completion 𝕜).map_pow z 2
      rw [div_eq_mul_inv, div_eq_mul_inv, UniformSpace.Completion.coe_mul,
        ← UniformSpace.Completion.coe_inv]
      congr 1
      rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_mul]
      simp [hzpow]
    rw [hrat]
    exact hs_base_expanded
  exact
    (hasSum_iff_hasSum_compl
      (fun n : ℕ ↦ secondOrderRecurrence α β n * z ^ n)
      (z / (1 - α * z - β * z ^ 2) : 𝕜)).1 <|
      hs_base

/-- Helper for Exercise 8: the quadratic denominator does not vanish strictly inside the
convergence disk. -/
lemma secondOrderRecurrenceSeries_denominator_ne_zero (α β : 𝕜) {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius) :
    1 - α * z - β * z ^ 2 ≠ 0 := by
  let aCompl : ℕ → UniformSpace.Completion 𝕜 :=
    fun n ↦ ((secondOrderRecurrence α β n : 𝕜) : UniformSpace.Completion 𝕜)
  let ACompl :
      FormalMultilinearSeries
        (UniformSpace.Completion 𝕜) (UniformSpace.Completion 𝕜) (UniformSpace.Completion 𝕜) :=
    FormalMultilinearSeries.ofScalars
      (𝕜 := UniformSpace.Completion 𝕜) (E := UniformSpace.Completion 𝕜) aCompl
  have hz_compl :
      ENNReal.ofReal ‖((z : 𝕜) : UniformSpace.Completion 𝕜)‖ <
        ACompl.radius := by
    simpa [aCompl, ACompl,
      secondOrderRecurrenceSeries_radius_eq_completion_radius (α := α) (β := β)] using hz
  have hrec_compl :
      ∀ n : ℕ, aCompl (n + 2) =
        (α : UniformSpace.Completion 𝕜) * aCompl (n + 1) +
          (β : UniformSpace.Completion 𝕜) * aCompl n := by
    intro n
    have hrec_cast :
        aCompl (n + 2) =
          (((α * secondOrderRecurrence α β (n + 1) +
              β * secondOrderRecurrence α β n : 𝕜) : 𝕜) :
            UniformSpace.Completion 𝕜) := by
      exact congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : UniformSpace.Completion 𝕜))
        (secondOrderRecurrence_succ_succ (α := α) (β := β) n)
    have hcast :
        ((((α * secondOrderRecurrence α β (n + 1) +
            β * secondOrderRecurrence α β n : 𝕜) : 𝕜) :
          UniformSpace.Completion 𝕜)) =
          (α : UniformSpace.Completion 𝕜) * aCompl (n + 1) +
            (β : UniformSpace.Completion 𝕜) * aCompl n := by
      rw [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.coe_mul]
    exact hrec_cast.trans hcast
  have ha0_compl : aCompl 0 = 0 := by
    simp [aCompl]
  have ha1_compl : aCompl 1 = 1 := by
    simp [aCompl]
  have hmul_compl :
      (1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
          (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2) *
          ACompl.sum (z : UniformSpace.Completion 𝕜) =
        (z : UniformSpace.Completion 𝕜) := by
    exact secondOrderRecurrenceSeries_sum_mul_quadratic_complete
      (α := (α : UniformSpace.Completion 𝕜)) (β := (β : UniformSpace.Completion 𝕜))
      (a := aCompl) (ha0 := ha0_compl) (ha1 := ha1_compl) (hrec := hrec_compl) (hz := hz_compl)
  intro hzero
  have hzero_compl :
      1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
        (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2 = 0 := by
    have hcast :
        (((1 - α * z - β * z ^ 2 : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
          1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
            (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2 := by
      have hzpow :
          (((z ^ 2 : 𝕜) : 𝕜) : UniformSpace.Completion 𝕜) =
            (z : UniformSpace.Completion 𝕜) ^ 2 :=
        (UniformSpace.Completion.coeRingHom : 𝕜 →+* UniformSpace.Completion 𝕜).map_pow z 2
      rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_mul]
      simp [hzpow]
    exact hcast.symm.trans <|
      congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : UniformSpace.Completion 𝕜)) hzero
  have hz_zero : (z : UniformSpace.Completion 𝕜) = 0 := by
    simpa [hzero_compl] using hmul_compl.symm
  have : (1 : UniformSpace.Completion 𝕜) = 0 := by
    calc
      (1 : UniformSpace.Completion 𝕜)
          = 1 - (α : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) -
              (β : UniformSpace.Completion 𝕜) * (z : UniformSpace.Completion 𝕜) ^ 2 := by
              simp [hz_zero]
      _ = 0 := hzero_compl
  exact one_ne_zero this

/-- Exercise 8 (2): the associated scalar power series has positive radius of convergence. -/
theorem secondOrderRecurrenceSeries_radius_pos (α β : 𝕜) :
    0 < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  let r0 : ℝ := (4 * c)⁻¹
  have hc_half : (1 / 2 : ℝ) ≤ c := by
    -- The same lower bound on `c` gives a concrete positive comparison radius.
    dsimp [c]
    exact le_max_right _ _
  have hc_pos : 0 < c := by
    linarith
  have hr0_pos : 0 < r0 := by
    -- The explicit radius is positive because `c > 0`.
    dsimp [r0]
    positivity
  have hr0_nonneg : 0 ≤ r0 := le_of_lt hr0_pos
  have hratio : (2 * c) * r0 = (1 / 2 : ℝ) := by
    -- Choosing `r = (4c)⁻¹` makes the geometric ratio exactly `1 / 2`.
    dsimp [r0]
    field_simp [hc_pos.ne']
    ring
  have hgeom : Summable (fun n : ℕ ↦ r0 * (1 / 2 : ℝ) ^ n) := by
    -- The comparison series is a convergent geometric series.
    exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hsummable_real :
      Summable (fun n : ℕ ↦ ‖ofScalars 𝕜 (secondOrderRecurrence α β) n‖ * r0 ^ n) := by
    -- After dropping the first term, the coefficient bound compares the series
    -- to the geometric one.
    simp_rw [FormalMultilinearSeries.ofScalars_norm]
    refine (summable_nat_add_iff 1).1 <|
      Summable.of_nonneg_of_le
        (f := fun n : ℕ ↦ r0 * (1 / 2 : ℝ) ^ n)
        (g := fun n : ℕ ↦ ‖secondOrderRecurrence α β (n + 1)‖ * r0 ^ (n + 1))
        (fun n ↦ by positivity) ?_ hgeom
    intro n
    have hbound := secondOrderRecurrence_norm_le_geometric_bound_succ (α := α) (β := β) n
    calc
      ‖secondOrderRecurrence α β (n + 1)‖ * r0 ^ (n + 1)
          ≤ (2 * c) ^ n * r0 ^ (n + 1) := by
            gcongr
      _ = (2 * c) ^ n * (r0 ^ n * r0) := by
            rw [pow_succ', mul_comm r0]
      _ = ((2 * c) ^ n * r0 ^ n) * r0 := by ring
      _ = ((2 * c) * r0) ^ n * r0 := by
            rw [← mul_pow]
      _ = r0 * (1 / 2 : ℝ) ^ n := by rw [hratio, mul_comm]
  let r : NNReal := ⟨r0, hr0_nonneg⟩
  have hr_le : (r : ENNReal) ≤ (ofScalars 𝕜 (secondOrderRecurrence α β)).radius := by
    exact (ofScalars 𝕜 (secondOrderRecurrence α β)).le_radius_of_summable
      (r := r) hsummable_real
  exact lt_of_lt_of_le (by exact_mod_cast hr0_pos) hr_le

/-- Exercise 8 (3): on the disk of convergence, the analytic sum of the recurrence series satisfies
the functional equation `(1 - α z - β z^2) S(z) = z`. -/
theorem secondOrderRecurrenceSeries_sum_mul_quadratic (α β : 𝕜) {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius) :
    (1 - α * z - β * z ^ 2) * (ofScalars 𝕜 (secondOrderRecurrence α β)).sum z = z := by
  -- Route correction: descend the complete-space generating-function identity from `Completion 𝕜`
  -- to get the exact rational sum first, then clear the denominator in the base field.
  have hs := secondOrderRecurrenceSeries_hasSum_rat (α := α) (β := β) hz
  have hsum :
      (ofScalars 𝕜 (secondOrderRecurrence α β)).sum z = z / (1 - α * z - β * z ^ 2) := by
    calc
      (ofScalars 𝕜 (secondOrderRecurrence α β)).sum z
          = ∑' n : ℕ, secondOrderRecurrence α β n * z ^ n := by
              simpa [FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
                (FormalMultilinearSeries.ofScalars_sum_eq
                  (E := 𝕜) (c := secondOrderRecurrence α β) z)
      _ = z / (1 - α * z - β * z ^ 2) := hs.tsum_eq
  have hden_ne := secondOrderRecurrenceSeries_denominator_ne_zero (α := α) (β := β) hz
  -- Clear the nonvanishing denominator in the explicit sum formula.
  calc
    (1 - α * z - β * z ^ 2) * (ofScalars 𝕜 (secondOrderRecurrence α β)).sum z
        = (1 - α * z - β * z ^ 2) * (z / (1 - α * z - β * z ^ 2)) := by rw [hsum]
    _ = z := by
      calc
        (1 - α * z - β * z ^ 2) * (z / (1 - α * z - β * z ^ 2))
            = z * ((1 - α * z - β * z ^ 2) / (1 - α * z - β * z ^ 2)) := by ring
        _ = z * 1 := by rw [div_self hden_ne]
        _ = z := by simp

/-- Exercise 8 (4): on the disk of convergence, the analytic sum of the recurrence series is the
rational function `z / (1 - α z - β z^2)`. -/
theorem secondOrderRecurrenceSeries_sum_eq_rat (α β : 𝕜) {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius) :
    (ofScalars 𝕜 (secondOrderRecurrence α β)).sum z = z / (1 - α * z - β * z ^ 2) := by
  have hmul := secondOrderRecurrenceSeries_sum_mul_quadratic (α := α) (β := β) hz
  have hden_ne : 1 - α * z - β * z ^ 2 ≠ 0 := by
    -- If the denominator vanished inside the disk, the functional equation would force `z = 0`,
    -- but then the denominator would evaluate to `1`, a contradiction.
    intro hzero
    have hz_zero : z = 0 := by
      simpa [hzero] using hmul.symm
    have : (1 : 𝕜) = 0 := by
      calc
        (1 : 𝕜) = 1 - α * z - β * z ^ 2 := by simp [hz_zero]
        _ = 0 := hzero
    exact one_ne_zero this
  -- Divide the functional equation by the non-vanishing quadratic factor.
  apply (eq_div_iff hden_ne).2
  simpa [mul_comm] using hmul

end NontriviallyNormedField

section RootPolynomial

variable {𝕜 : Type u} [CommRing 𝕜]

/-- The source-facing quadratic polynomial `β X^2 + α X - 1` whose roots appear in parts (5)
and (6). -/
def secondOrderRecurrenceRootPolynomial (α β : 𝕜) : 𝕜[X] :=
  C β * X ^ 2 + C α * X - 1

end RootPolynomial

section ClosedForm

variable {𝕜 : Type u} [Field 𝕜]

/-- Helper for Exercise 8: if `β X^2 + α X - 1` has roots `z₁` and `z₂`, then the quadratic
coefficient `β` is nonzero. -/
lemma secondOrderRecurrenceRootPolynomial_beta_ne_zero (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂}) :
    β ≠ 0 := by
  intro hβ
  have hdeg :
      (secondOrderRecurrenceRootPolynomial α β).natDegree ≤ 1 := by
    -- With `β = 0` the source polynomial is only linear.
    simpa [secondOrderRecurrenceRootPolynomial, hβ, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using (Polynomial.natDegree_linear_le (a := α) (b := (-1 : 𝕜)))
  have hcard_le : (secondOrderRecurrenceRootPolynomial α β).roots.card ≤ 1 :=
    (Polynomial.card_roots' (secondOrderRecurrenceRootPolynomial α β)).trans hdeg
  have : 2 ≤ 1 := by
    rw [hroots] at hcard_le
    simp at hcard_le
  exact (Nat.not_succ_le_self 1) this

/-- Helper for Exercise 8: the root data give Vieta's relations, the pointwise root equations,
and show that both roots are nonzero. -/
lemma root_polynomial_root_eq_and_vieta (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂}) :
    β ≠ 0 ∧ α = -β * (z₁ + z₂) ∧ (-1 : 𝕜) = β * z₁ * z₂ ∧
      1 = α * z₁ + β * z₁ ^ 2 ∧ 1 = α * z₂ + β * z₂ ^ 2 ∧ z₁ ≠ 0 ∧ z₂ ≠ 0 :=
by
  have hβ : β ≠ 0 := secondOrderRecurrenceRootPolynomial_beta_ne_zero (α := α) (β := β) hroots
  have hα :
      α = -β * (z₁ + z₂) := by
    -- Vieta's formula gives the linear coefficient from the two roots.
    have hroots' : (C β * X ^ 2 + C α * X + C (-1 : 𝕜)).roots = {z₁, z₂} := by
      simpa [secondOrderRecurrenceRootPolynomial, sub_eq_add_neg] using hroots
    simpa using
      (Polynomial.eq_neg_mul_add_of_roots_quadratic_eq_pair
        (a := β) (b := α) (c := (-1 : 𝕜)) (x1 := z₁) (x2 := z₂) hroots')
  have hconst :
      (-1 : 𝕜) = β * z₁ * z₂ := by
    -- The constant term records the product of the roots.
    have hroots' : (C β * X ^ 2 + C α * X + C (-1 : 𝕜)).roots = {z₁, z₂} := by
      simpa [secondOrderRecurrenceRootPolynomial, sub_eq_add_neg] using hroots
    simpa using
      (Polynomial.eq_mul_mul_of_roots_quadratic_eq_pair
        (a := β) (b := α) (c := (-1 : 𝕜)) (x1 := z₁) (x2 := z₂) hroots')
  have hz₁_mem : z₁ ∈ (secondOrderRecurrenceRootPolynomial α β).roots := by
    rw [hroots]
    simp
  have hz₂_mem : z₂ ∈ (secondOrderRecurrenceRootPolynomial α β).roots := by
    rw [hroots]
    simp
  have hz₁_eval :
      (secondOrderRecurrenceRootPolynomial α β).eval z₁ = 0 :=
    Polynomial.isRoot_of_mem_roots hz₁_mem
  have hz₂_eval :
      (secondOrderRecurrenceRootPolynomial α β).eval z₂ = 0 :=
    Polynomial.isRoot_of_mem_roots hz₂_mem
  have hz₁_eq :
      1 = α * z₁ + β * z₁ ^ 2 := by
    -- Evaluating the defining quadratic at `z₁` gives the source root equation.
    have hz₁_eval' : β * z₁ ^ 2 + α * z₁ - 1 = 0 := by
      simpa only [secondOrderRecurrenceRootPolynomial, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_one, sub_eq_add_neg, pow_two, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hz₁_eval
    have hz₁_sum : β * z₁ ^ 2 + α * z₁ = 1 := by
      have := congrArg (fun t : 𝕜 => t + 1) hz₁_eval'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₁_sum.symm
  have hz₂_eq :
      1 = α * z₂ + β * z₂ ^ 2 := by
    -- The same evaluation at `z₂` gives the second root equation.
    have hz₂_eval' : β * z₂ ^ 2 + α * z₂ - 1 = 0 := by
      simpa only [secondOrderRecurrenceRootPolynomial, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_one, sub_eq_add_neg, pow_two, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hz₂_eval
    have hz₂_sum : β * z₂ ^ 2 + α * z₂ = 1 := by
      have := congrArg (fun t : 𝕜 => t + 1) hz₂_eval'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₂_sum.symm
  have hz₁0 : z₁ ≠ 0 := by
    -- The constant term `-1` excludes `0` as a root.
    intro hz₁_zero
    have hconst' := hconst
    rw [hz₁_zero] at hconst'
    simp at hconst'
  have hz₂0 : z₂ ≠ 0 := by
    -- The same constant-term argument excludes `z₂ = 0`.
    intro hz₂_zero
    have hconst' := hconst
    rw [hz₂_zero] at hconst'
    simp at hconst'
  exact ⟨hβ, hα, hconst, hz₁_eq, hz₂_eq, hz₁0, hz₂0⟩

/-- Helper for Exercise 8: rewriting the root equation through inversion gives the quadratic
relation satisfied by the inverse root. -/
lemma inverse_square_eq_of_root_equation {α β z : 𝕜}
    (hz : 1 = α * z + β * z ^ 2) (hz0 : z ≠ 0) :
    z⁻¹ ^ 2 = α * z⁻¹ + β := by
  -- Clearing denominators turns the source root equation into the inverse relation.
  exact (mul_right_cancel₀ (pow_ne_zero 2 hz0)) <| by
    calc
      z⁻¹ ^ 2 * z ^ 2 = 1 := by
        field_simp [hz0]
      _ = α * z + β * z ^ 2 := hz
      _ = (α * z⁻¹ + β) * z ^ 2 := by
        field_simp [hz0]

/-- Helper for Exercise 8: the inverse-root geometric progression solves the source recurrence. -/
lemma inverse_geometric_isSolution (α β z : 𝕜)
    (hz : 1 = α * z + β * z ^ 2) (hz0 : z ≠ 0) :
    (secondOrderRecurrenceRel α β).IsSolution (fun n ↦ z⁻¹ ^ n) :=
by
  -- Route correction: use the characteristic-polynomial API instead of a manual recurrence chase.
  rw [(secondOrderRecurrenceRel α β).geom_sol_iff_root_charPoly (q := z⁻¹)]
  -- The inverse-root identity is exactly the characteristic-polynomial equation.
  rw [LinearRecurrence.charPoly, Polynomial.IsRoot.def, Polynomial.eval, secondOrderRecurrenceRel,
    Fin.sum_univ_two]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_monomial, RingHom.id_apply, one_mul]
  exact sub_eq_zero.mpr <| by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      inverse_square_eq_of_root_equation (α := α) (β := β) hz hz0

/-- Exercise 8 (5): if `z₁` and `z₂` are the two roots of `β X^2 + α X - 1`, then the recurrence
coefficients admit the corresponding closed form obtained from the partial-fraction decomposition of
`z / (1 - α z - β z^2)`.

This is the source-facing distinct-root formula from the text. -/
theorem secondOrderRecurrence_closed_form (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ ≠ z₂)
    (n : ℕ) :
    secondOrderRecurrence α β n =
      (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ n - z₂⁻¹ ^ n) :=
by
  rcases root_polynomial_root_eq_and_vieta (α := α) (β := β) hroots with
    ⟨_, _, _, hz₁_root, hz₂_root, hz₁0, hz₂0⟩
  let u : ℕ → 𝕜 := fun m ↦
    (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ m - z₂⁻¹ ^ m)
  have hu_sol : (secondOrderRecurrenceRel α β).IsSolution u := by
    have hz₁_inv :
        z₁⁻¹ ^ 2 = α * z₁⁻¹ + β :=
      inverse_square_eq_of_root_equation (α := α) (β := β) hz₁_root hz₁0
    have hz₂_inv :
        z₂⁻¹ ^ 2 = α * z₂⁻¹ + β :=
      inverse_square_eq_of_root_equation (α := α) (β := β) hz₂_root hz₂0
    have hsol₁' : ∀ m : ℕ, z₁⁻¹ ^ (m + 2) = α * z₁⁻¹ ^ (m + 1) + β * z₁⁻¹ ^ m := by
      intro m
      calc
        z₁⁻¹ ^ (m + 2) = z₁⁻¹ ^ m * z₁⁻¹ ^ 2 := by rw [pow_add]
        _ = z₁⁻¹ ^ m * (α * z₁⁻¹ + β) := by rw [hz₁_inv]
        _ = α * z₁⁻¹ ^ (m + 1) + β * z₁⁻¹ ^ m := by
              rw [pow_succ', mul_add]
              ring
    have hsol₂' : ∀ m : ℕ, z₂⁻¹ ^ (m + 2) = α * z₂⁻¹ ^ (m + 1) + β * z₂⁻¹ ^ m := by
      intro m
      calc
        z₂⁻¹ ^ (m + 2) = z₂⁻¹ ^ m * z₂⁻¹ ^ 2 := by rw [pow_add]
        _ = z₂⁻¹ ^ m * (α * z₂⁻¹ + β) := by rw [hz₂_inv]
        _ = α * z₂⁻¹ ^ (m + 1) + β * z₂⁻¹ ^ m := by
              rw [pow_succ', mul_add]
              ring
    intro m
    -- The candidate is a scalar multiple of the difference of two geometric solutions.
    rw [secondOrderRecurrenceRel, Fin.sum_univ_two]
    dsimp [u]
    rw [hsol₁' m, hsol₂' m]
    ring
  have hu_init : ∀ i : Fin 2, u i = ![0, 1] i := by
    intro i
    fin_cases i
    · -- The constant term vanishes because the two geometric terms cancel.
      simp [u]
    · -- The linear term is normalized to `1` by the partial-fraction coefficient.
      dsimp [u]
      simp only [pow_one]
      have hz21 : z₂ ≠ z₁ := by
        intro h
        exact hz h.symm
      calc
        z₁ * z₂ / (z₂ - z₁) * (z₁⁻¹ - z₂⁻¹)
            = z₂ * (z₂ - z₁)⁻¹ - z₁ * (z₂ - z₁)⁻¹ := by
                field_simp [hz, hz₁0, hz₂0]
        _ = (z₂ - z₁) * (z₂ - z₁)⁻¹ := by ring
        _ = 1 := by
              exact mul_inv_cancel₀ (sub_ne_zero.mpr hz21)
  have hu_eq : u = secondOrderRecurrence α β := by
    -- Recurrence uniqueness identifies the candidate with the canonical solution.
    simpa [secondOrderRecurrence] using
      (secondOrderRecurrenceRel α β).eq_mk_of_is_sol_of_eq_init' hu_sol hu_init
  simpa [u] using congrArg (fun f : ℕ → 𝕜 => f n) hu_eq.symm

/-- Repeated-root companion to Exercise 8 (5). -/
theorem secondOrderRecurrence_closed_form_of_eq (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ = z₂)
    (n : ℕ) :
    secondOrderRecurrence α β n =
      (n : 𝕜) * z₁⁻¹ ^ (n - 1) :=
by
  rcases root_polynomial_root_eq_and_vieta (α := α) (β := β) hroots with
    ⟨_, _, hconst, hz₁_root, _, hz₁0, _⟩
  have hconst' : (-1 : 𝕜) = β * z₁ * z₁ := by
    simpa [hz] using hconst
  have hβ_eq : β = -(z₁⁻¹) ^ 2 := by
    -- The repeated-root product identity determines `β`.
    exact (mul_right_cancel₀ (pow_ne_zero 2 hz₁0)) <| by
      calc
        β * z₁ ^ 2 = -1 := by
          simpa [pow_two, mul_assoc] using hconst'.symm
        _ = (-(z₁⁻¹) ^ 2) * z₁ ^ 2 := by
          field_simp [hz₁0]
  have hα_eq : α = 2 * z₁⁻¹ := by
    -- Combining the root equation with the product identity determines `α`.
    exact (mul_right_cancel₀ hz₁0) <| by
      calc
        α * z₁ = 1 - β * z₁ ^ 2 := by
          rw [hz₁_root]
          ring
        _ = 2 := by
          rw [show β * z₁ ^ 2 = (-1 : 𝕜) by simpa [pow_two, mul_assoc] using hconst'.symm]
          ring
        _ = (2 * z₁⁻¹) * z₁ := by
          field_simp [hz₁0]
  let u : ℕ → 𝕜 := fun m ↦ (m : 𝕜) * z₁⁻¹ ^ (m - 1)
  have hu_sol : (secondOrderRecurrenceRel α β).IsSolution u := by
    intro m
    rw [secondOrderRecurrenceRel, Fin.sum_univ_two]
    cases m with
    | zero =>
      -- The first recurrence step is a direct algebraic check.
      simp [u, hα_eq, hβ_eq]
    | succ m =>
        -- For positive indices, rewrite every term with the same power of `z₁⁻¹`.
        simp [u, hα_eq, hβ_eq, pow_succ, mul_assoc, mul_left_comm, mul_comm]
        ring
  have hu_init : ∀ i : Fin 2, u i = ![0, 1] i := by
    intro i
    fin_cases i
    · -- The zeroth term vanishes because of the prefactor `n`.
      simp [u]
    · -- The first term is exactly `1`.
      simp [u]
  have hu_eq : u = secondOrderRecurrence α β := by
    -- Recurrence uniqueness identifies the repeated-root candidate.
    simpa [secondOrderRecurrence] using
      (secondOrderRecurrenceRel α β).eq_mk_of_is_sol_of_eq_init' hu_sol hu_init
  simpa [u] using congrArg (fun f : ℕ → 𝕜 => f n) hu_eq.symm

end ClosedForm

section RadiusFromRoots

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Helper for Exercise 8: a nonzero root of `1 - α z - β z²` cannot lie strictly inside the disk
of convergence. -/
lemma secondOrderRecurrenceSeries_radius_le_norm_root (α β : 𝕜) {z : 𝕜}
    (hzroot : 1 = α * z + β * z ^ 2) (hz0 : z ≠ 0) :
    (ofScalars 𝕜 (secondOrderRecurrence α β)).radius ≤ ENNReal.ofReal ‖z‖ := by
  by_contra hlt
  have hzrad : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (secondOrderRecurrence α β)).radius :=
    lt_of_not_ge hlt
  have hmul := secondOrderRecurrenceSeries_sum_mul_quadratic (α := α) (β := β) hzrad
  have hden : 1 - α * z - β * z ^ 2 = 0 := by
    calc
      1 - α * z - β * z ^ 2 = 1 - (α * z + β * z ^ 2) := by ring
      _ = 0 := by rw [hzroot]; ring
  have : z = 0 := by
    simpa [hden] using hmul.symm
  exact hz0 this

/-- Helper for Exercise 8: in the distinct-root case, every smaller weighted norm series is
dominated by a sum of two geometric series. -/
lemma secondOrderRecurrenceSeries_summable_distinct_of_lt_min_norm (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ ≠ z₂) {r : NNReal} (hr : (r : ℝ) < min ‖z₁‖ ‖z₂‖) :
    Summable (fun n : ℕ => ‖secondOrderRecurrence α β n‖ * (r : ℝ) ^ n) := by
  -- Route correction: use the source closed form to compare termwise with two geometric series.
  rcases root_polynomial_root_eq_and_vieta (α := α) (β := β) hroots with
    ⟨_, _, _, _, _, hz₁0, hz₂0⟩
  let C : 𝕜 := z₁ * z₂ / (z₂ - z₁)
  have hz₁pos : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁0
  have hz₂pos : 0 < ‖z₂‖ := norm_pos_iff.mpr hz₂0
  have hr₁ : (r : ℝ) < ‖z₁‖ := lt_of_lt_of_le hr (min_le_left _ _)
  have hr₂ : (r : ℝ) < ‖z₂‖ := lt_of_lt_of_le hr (min_le_right _ _)
  have hq₁_lt : (r : ℝ) / ‖z₁‖ < 1 := by
    exact (div_lt_one hz₁pos).2 hr₁
  have hq₂_lt : (r : ℝ) / ‖z₂‖ < 1 := by
    exact (div_lt_one hz₂pos).2 hr₂
  have hq₁_norm : ‖(r : ℝ) / ‖z₁‖‖ < 1 := by
    have hq₁_nonneg : 0 ≤ (r : ℝ) / ‖z₁‖ := div_nonneg r.2 hz₁pos.le
    simpa [Real.norm_eq_abs, abs_of_nonneg hq₁_nonneg] using hq₁_lt
  have hq₂_norm : ‖(r : ℝ) / ‖z₂‖‖ < 1 := by
    have hq₂_nonneg : 0 ≤ (r : ℝ) / ‖z₂‖ := div_nonneg r.2 hz₂pos.le
    simpa [Real.norm_eq_abs, abs_of_nonneg hq₂_nonneg] using hq₂_lt
  have hgeom :
      Summable
        (fun n : ℕ => ‖C‖ * (((r : ℝ) / ‖z₁‖) ^ n + ((r : ℝ) / ‖z₂‖) ^ n)) := by
    -- Each inverse-root contribution is geometric because `r / ‖zᵢ‖ < 1`.
    exact ((summable_geometric_of_norm_lt_one hq₁_norm).add
        (summable_geometric_of_norm_lt_one hq₂_norm)).mul_left ‖C‖
  refine Summable.of_nonneg_of_le (g := fun n : ℕ => ‖secondOrderRecurrence α β n‖ * (r : ℝ) ^ n)
    (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_ hgeom
  intro n
  -- Rewrite the coefficient by the distinct-root closed form,
  -- then separate the two geometric terms.
  calc
    ‖secondOrderRecurrence α β n‖ * (r : ℝ) ^ n
        = ‖C * (z₁⁻¹ ^ n - z₂⁻¹ ^ n)‖ * (r : ℝ) ^ n := by
            rw [secondOrderRecurrence_closed_form (α := α) (β := β) (hroots := hroots)
              (hz := hz) (n := n)]
    _ = (‖C‖ * ‖z₁⁻¹ ^ n - z₂⁻¹ ^ n‖) * (r : ℝ) ^ n := by rw [norm_mul]
    _ ≤ (‖C‖ * (‖z₁⁻¹ ^ n‖ + ‖z₂⁻¹ ^ n‖)) * (r : ℝ) ^ n := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖C‖ * (‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ n + ‖z₂⁻¹ ^ n‖ * (r : ℝ) ^ n) := by ring
    _ = ‖C‖ * (((r : ℝ) / ‖z₁‖) ^ n + ((r : ℝ) / ‖z₂‖) ^ n) := by
          congr
          · rw [norm_pow, norm_inv, ← mul_pow]
            simp [div_eq_mul_inv, mul_comm]
          · rw [norm_pow, norm_inv, ← mul_pow]
            simp [div_eq_mul_inv, mul_comm]

/-- Helper for Exercise 8: in the repeated-root case, every smaller weighted norm series is
dominated by an arithmetic-geometric series. -/
lemma secondOrderRecurrenceSeries_summable_repeated_of_lt_norm (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ = z₂) {r : NNReal} (hr : (r : ℝ) < ‖z₁‖) :
    Summable (fun n : ℕ => ‖secondOrderRecurrence α β n‖ * (r : ℝ) ^ n) := by
  rcases root_polynomial_root_eq_and_vieta (α := α) (β := β) hroots with
    ⟨_, _, _, _, _, hz₁0, _⟩
  have hz₁pos : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁0
  have hq_lt : (r : ℝ) / ‖z₁‖ < 1 := by
    exact (div_lt_one hz₁pos).2 hr
  have hq_norm : ‖(r : ℝ) / ‖z₁‖‖ < 1 := by
    have hq_nonneg : 0 ≤ (r : ℝ) / ‖z₁‖ := div_nonneg r.2 hz₁pos.le
    simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt
  have harith :
      Summable (fun n : ℕ => (r : ℝ) * ((n + 1 : ℝ) * (((r : ℝ) / ‖z₁‖) ^ n))) := by
    -- Shifting by one turns the repeated-root formula into an arithmetic-geometric series.
    have hbase : Summable (fun n : ℕ => (n + 1 : ℝ) * (((r : ℝ) / ‖z₁‖) ^ n)) := by
      convert summable_descFactorial_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq_norm using 1 with n
      simp
    exact hbase.mul_left (r : ℝ)
  refine (summable_nat_add_iff 1).1 <|
    Summable.of_nonneg_of_le
      (f := fun n : ℕ => (r : ℝ) * ((n + 1 : ℝ) * (((r : ℝ) / ‖z₁‖) ^ n)))
      (g := fun n : ℕ => ‖secondOrderRecurrence α β (n + 1)‖ * (r : ℝ) ^ (n + 1))
      (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_ harith
  intro n
  -- Rewrite the shifted coefficient by the repeated-root closed form, then compare with the
  -- standard arithmetic-geometric series.
  calc
    ‖secondOrderRecurrence α β (n + 1)‖ * (r : ℝ) ^ (n + 1)
        = ‖((n + 1 : 𝕜) * z₁⁻¹ ^ n)‖ * (r : ℝ) ^ (n + 1) := by
            rw [secondOrderRecurrence_closed_form_of_eq (α := α) (β := β) (hroots := hroots)
              (hz := hz) (n := n + 1)]
            simp
    _ = ‖(n + 1 : 𝕜)‖ * ‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ (n + 1) := by rw [norm_mul]
    _ ≤ (n + 1 : ℝ) * ‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ (n + 1) := by
          have hnat :
              ‖(n + 1 : 𝕜)‖ ≤ (n + 1 : ℝ) := by
            have hnat' : ‖(n + 1) • (1 : 𝕜)‖ ≤ ((n : ℝ) + 1) * ‖(1 : 𝕜)‖ := by
              simpa [Nat.cast_add] using (norm_nsmul_le (a := (1 : 𝕜)) (n := n + 1))
            simpa [nsmul_eq_mul, one_mul, Nat.cast_add, add_comm, add_left_comm, add_assoc] using
              hnat'
          have hnonneg : 0 ≤ ‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ (n + 1) := by
            positivity
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hnat hnonneg
    _ = (n + 1 : ℝ) * (‖z₁‖⁻¹ ^ n) * ((r : ℝ) ^ n * (r : ℝ)) := by
          rw [norm_pow, norm_inv, pow_succ']
          ring
    _ = ((n + 1 : ℝ) * ((‖z₁‖⁻¹ ^ n) * (r : ℝ) ^ n)) * (r : ℝ) := by ring
    _ = ((n + 1 : ℝ) * (((r : ℝ) / ‖z₁‖) ^ n)) * (r : ℝ) := by
          congr 1
          rw [← mul_pow]
          simp [div_eq_mul_inv, mul_comm]
    _ = (r : ℝ) * ((n + 1 : ℝ) * (((r : ℝ) / ‖z₁‖) ^ n)) := by ring

/-- Helper for Exercise 8: the closed-form comparisons give the lower radius bound
`min (‖z₁‖, ‖z₂‖) ≤ ρ(S)`. -/
lemma secondOrderRecurrenceSeries_min_root_norm_le_radius (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂}) :
    ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) ≤ (ofScalars 𝕜 (secondOrderRecurrence α β)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hsummable :
      Summable (fun n : ℕ => ‖ofScalars 𝕜 (secondOrderRecurrence α β) n‖ * (r : ℝ) ^ n) := by
    by_cases hz : z₁ = z₂
    · have hr' : (r : ℝ) < ‖z₁‖ := by
        have hmin : (r : ℝ) < min ‖z₁‖ ‖z₂‖ := by simpa using hr
        simpa [hz] using hmin
      -- In the repeated-root branch, compare with an arithmetic-geometric series.
      simpa [FormalMultilinearSeries.ofScalars_norm] using
        secondOrderRecurrenceSeries_summable_repeated_of_lt_norm (α := α) (β := β)
          (hroots := hroots) hz hr'
    · have hr' : (r : ℝ) < min ‖z₁‖ ‖z₂‖ := by
        simpa using hr
      -- In the distinct-root branch, compare with two geometric series.
      simpa [FormalMultilinearSeries.ofScalars_norm] using
        secondOrderRecurrenceSeries_summable_distinct_of_lt_min_norm (α := α) (β := β)
          (hroots := hroots) hz hr'
  -- Convert the weighted norm summability into a lower bound on the radius.
  exact (ofScalars 𝕜 (secondOrderRecurrence α β)).le_radius_of_summable (r := r) hsummable

/-- Exercise 8 (6): if `z₁` and `z₂` are the two roots of `β X^2 + α X - 1`, then the radius of
convergence is `min (‖z₁‖, ‖z₂‖)`. -/
theorem secondOrderRecurrenceSeries_radius_eq_min_norm_root (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (secondOrderRecurrenceRootPolynomial α β).roots = {z₁, z₂}) :
    (ofScalars 𝕜 (secondOrderRecurrence α β)).radius = ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) :=
by
  rcases root_polynomial_root_eq_and_vieta (α := α) (β := β) hroots with
    ⟨_, _, _, hz₁_root, hz₂_root, hz₁0, hz₂0⟩
  have hupper₁ :
      (ofScalars 𝕜 (secondOrderRecurrence α β)).radius ≤ ENNReal.ofReal ‖z₁‖ :=
    secondOrderRecurrenceSeries_radius_le_norm_root (α := α) (β := β) hz₁_root hz₁0
  have hupper₂ :
      (ofScalars 𝕜 (secondOrderRecurrence α β)).radius ≤ ENNReal.ofReal ‖z₂‖ :=
    secondOrderRecurrenceSeries_radius_le_norm_root (α := α) (β := β) hz₂_root hz₂0
  have hupper :
      (ofScalars 𝕜 (secondOrderRecurrence α β)).radius ≤ ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) := by
    -- Each root excludes radii strictly larger than its norm, so the radius is bounded by the min.
    rw [ENNReal.ofReal_min]
    exact le_min hupper₁ hupper₂
  have hlower :
      ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) ≤ (ofScalars 𝕜 (secondOrderRecurrence α β)).radius :=
    secondOrderRecurrenceSeries_min_root_norm_le_radius (α := α) (β := β) hroots
  exact le_antisymm hupper hlower

end RadiusFromRoots

end ScalarSeries
