import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»
import DifferentialForms_Cartan_1970.cartan.I.section02.«frozen_0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped ENNReal NNReal PowerSeries

/- Source-facing layer: the recurrence and its coefficient sequence are owned by
`LinearRecurrence`. The analytic generating series is the downstream scalar-series bridge from
`exercise8Coeffs` to `FormalMultilinearSeries.ofScalars`. -/

section Algebraic

variable {R : Type*} [CommSemiring R]

/-- The order-two linear recurrence governing the coefficients in Exercise 8. -/
def exercise8Rec (α β : R) : LinearRecurrence R where
  order := 2
  coeffs := ![β, α]

/-- The recursively defined coefficients in Exercise 8, realized through the canonical solution of
the governing linear recurrence with initial values `0, 1`. -/
def exercise8Coeffs (α β : R) : ℕ → R :=
  (exercise8Rec α β).mkSol ![0, 1]

/-- The coefficient sequence in Exercise 8 is a solution of the canonical order-two linear
recurrence with coefficients `β, α`. -/
theorem exercise8Coeffs_isSolution (α β : R) :
    (exercise8Rec α β).IsSolution (exercise8Coeffs α β) := by
  simpa [exercise8Coeffs] using (exercise8Rec α β).is_sol_mkSol ![0, 1]

/-- The coefficients in Exercise 8 satisfy the stated second-order linear recurrence. -/
theorem exercise8Coeffs_succ_succ (α β : R) (n : ℕ) :
    exercise8Coeffs α β (n + 2) =
      α * exercise8Coeffs α β (n + 1) + β * exercise8Coeffs α β n := by
  have h := exercise8Coeffs_isSolution α β n
  change exercise8Coeffs α β (n + 2) =
      ∑ i : Fin 2, ![β, α] i * exercise8Coeffs α β (n + ↑i) at h
  simpa [Fin.sum_univ_two, add_comm] using h

/-- Helper for Exercise 8: the canonical recurrence solution starts with the initial values
`a₀ = 0` and `a₁ = 1`. -/
theorem exercise8_coeffs_zero_one (α β : R) :
    exercise8Coeffs α β 0 = 0 ∧ exercise8Coeffs α β 1 = 1 := by
  constructor
  · -- The zeroth coefficient is the first prescribed initial datum of `mkSol`.
    simpa [exercise8Coeffs, exercise8Rec] using
      (exercise8Rec α β).mkSol_eq_init ![0, 1] ⟨0, by simp [exercise8Rec]⟩
  · -- The first coefficient is the second prescribed initial datum of `mkSol`.
    simpa [exercise8Coeffs, exercise8Rec] using
      (exercise8Rec α β).mkSol_eq_init ![0, 1] ⟨1, by simp [exercise8Rec]⟩

end Algebraic

section RootPolynomial

variable {K : Type*} [CommRing K]

open Polynomial

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the quadratic polynomial whose roots
govern the recurrence denominator. -/
noncomputable def exercise8RootPolynomial (α β : K) : K[X] :=
  C β * X ^ 2 + C α * X + C (-1)

end RootPolynomial

section ClosedFormHelpers

variable {K : Type*} [Field K]

open Polynomial

/-- Helper for Cartan section04 frozen_0023_Exercise_8: if `β X^2 + α X - 1` has roots `z₁` and
`z₂`, then the quadratic coefficient `β` is nonzero. -/
lemma exercise8RootPolynomial_beta_ne_zero (α β : K) {z₁ z₂ : K}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂}) :
    β ≠ 0 := by
  intro hβ
  have hdeg : (exercise8RootPolynomial α β).natDegree ≤ 1 := by
    -- With `β = 0`, the polynomial degenerates to the linear term `α X - 1`.
    simpa [exercise8RootPolynomial, hβ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.natDegree_linear_le (a := α) (b := (-1 : K)))
  have hcard_le : (exercise8RootPolynomial α β).roots.card ≤ 1 :=
    (Polynomial.card_roots' (exercise8RootPolynomial α β)).trans hdeg
  have : 2 ≤ 1 := by
    rw [hroots] at hcard_le
    simp at hcard_le
  exact (Nat.not_succ_le_self 1) this

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the quadratic root data package Vieta's
relations, the pointwise root equations, and the nonvanishing of both roots. -/
lemma exercise8_rootEqAndVieta (α β : K) {z₁ z₂ : K}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂}) :
    β ≠ 0 ∧ α = -β * (z₁ + z₂) ∧ (-1 : K) = β * z₁ * z₂ ∧
      1 = α * z₁ + β * z₁ ^ 2 ∧ 1 = α * z₂ + β * z₂ ^ 2 ∧ z₁ ≠ 0 ∧ z₂ ≠ 0 := by
  have hβ : β ≠ 0 := exercise8RootPolynomial_beta_ne_zero (α := α) (β := β) hroots
  have hα : α = -β * (z₁ + z₂) := by
    -- Vieta's relation recovers the linear coefficient from the two roots.
    have hroots' : (C β * X ^ 2 + C α * X + C (-1 : K)).roots = {z₁, z₂} := by
      simpa [exercise8RootPolynomial, sub_eq_add_neg] using hroots
    simpa using
      (Polynomial.eq_neg_mul_add_of_roots_quadratic_eq_pair
        (a := β) (b := α) (c := (-1 : K)) (x1 := z₁) (x2 := z₂) hroots')
  have hconst : (-1 : K) = β * z₁ * z₂ := by
    -- The constant term gives the product of the two roots.
    have hroots' : (C β * X ^ 2 + C α * X + C (-1 : K)).roots = {z₁, z₂} := by
      simpa [exercise8RootPolynomial, sub_eq_add_neg] using hroots
    simpa using
      (Polynomial.eq_mul_mul_of_roots_quadratic_eq_pair
        (a := β) (b := α) (c := (-1 : K)) (x1 := z₁) (x2 := z₂) hroots')
  have hz₁_mem : z₁ ∈ (exercise8RootPolynomial α β).roots := by
    rw [hroots]
    simp
  have hz₂_mem : z₂ ∈ (exercise8RootPolynomial α β).roots := by
    rw [hroots]
    simp
  have hz₁_eval : (exercise8RootPolynomial α β).eval z₁ = 0 :=
    Polynomial.isRoot_of_mem_roots hz₁_mem
  have hz₂_eval : (exercise8RootPolynomial α β).eval z₂ = 0 :=
    Polynomial.isRoot_of_mem_roots hz₂_mem
  have hz₁_eq : 1 = α * z₁ + β * z₁ ^ 2 := by
    -- Evaluating the quadratic at `z₁` gives the first source root equation.
    have hz₁_eval' : β * z₁ ^ 2 + α * z₁ - 1 = 0 := by
      simpa only [exercise8RootPolynomial, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_one, sub_eq_add_neg, pow_two, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hz₁_eval
    have hz₁_sum : β * z₁ ^ 2 + α * z₁ = 1 := by
      have := congrArg (fun t : K => t + 1) hz₁_eval'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₁_sum.symm
  have hz₂_eq : 1 = α * z₂ + β * z₂ ^ 2 := by
    -- The same evaluation gives the second source root equation.
    have hz₂_eval' : β * z₂ ^ 2 + α * z₂ - 1 = 0 := by
      simpa only [exercise8RootPolynomial, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_one, sub_eq_add_neg, pow_two, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hz₂_eval
    have hz₂_sum : β * z₂ ^ 2 + α * z₂ = 1 := by
      have := congrArg (fun t : K => t + 1) hz₂_eval'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₂_sum.symm
  have hz₁0 : z₁ ≠ 0 := by
    -- The constant term excludes `0` as a root.
    intro hz₁_zero
    have hconst' := hconst
    rw [hz₁_zero] at hconst'
    simp at hconst'
  have hz₂0 : z₂ ≠ 0 := by
    -- The same constant-term argument excludes `0` for `z₂`.
    intro hz₂_zero
    have hconst' := hconst
    rw [hz₂_zero] at hconst'
    simp at hconst'
  exact ⟨hβ, hα, hconst, hz₁_eq, hz₂_eq, hz₁0, hz₂0⟩

/-- Helper for Cartan section04 frozen_0023_Exercise_8: rewriting the root equation through
inversion gives the quadratic relation satisfied by the inverse root. -/
lemma exercise8_inverseSquareEqOfRootEquation {α β z : K}
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

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the inverse-root geometric progression
solves the governing recurrence. -/
lemma exercise8_inverseGeometricIsSolution (α β z : K)
    (hz : 1 = α * z + β * z ^ 2) (hz0 : z ≠ 0) :
    (exercise8Rec α β).IsSolution (fun n ↦ z⁻¹ ^ n) := by
  -- Route correction: use the characteristic-polynomial API rather than a manual recurrence chase.
  rw [(exercise8Rec α β).geom_sol_iff_root_charPoly (q := z⁻¹)]
  -- The inverse-root identity is exactly the characteristic-polynomial equation.
  rw [LinearRecurrence.charPoly, Polynomial.IsRoot.def, Polynomial.eval, exercise8Rec,
    Fin.sum_univ_two]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_monomial, RingHom.id_apply, one_mul]
  exact sub_eq_zero.mpr <| by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      exercise8_inverseSquareEqOfRootEquation (α := α) (β := β) hz hz0

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the distinct-root closed form for the
recurrence coefficients follows from recurrence uniqueness. -/
theorem exercise8_coeff_closed_form_of_distinct_roots_aux
    {α β z₁ z₂ : K}
    (hz₁ : β * z₁ ^ 2 + α * z₁ - 1 = 0)
    (hz₂ : β * z₂ ^ 2 + α * z₂ - 1 = 0)
    (hneq : z₁ ≠ z₂) (n : ℕ) :
    exercise8Coeffs α β n = (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ n - z₂⁻¹ ^ n) := by
  have hz₁_root : 1 = α * z₁ + β * z₁ ^ 2 := by
    -- Rearranging the first quadratic equation gives the root identity used by the recurrence API.
    have hz₁_sum : β * z₁ ^ 2 + α * z₁ = 1 := by
      have := congrArg (fun t : K => t + 1) hz₁
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₁_sum.symm
  have hz₂_root : 1 = α * z₂ + β * z₂ ^ 2 := by
    -- The same rearrangement works for the second root.
    have hz₂_sum : β * z₂ ^ 2 + α * z₂ = 1 := by
      have := congrArg (fun t : K => t + 1) hz₂
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hz₂_sum.symm
  have hz₁0 : z₁ ≠ 0 := by
    -- The equation `β z₁² + α z₁ - 1 = 0` excludes the zero root.
    intro hz₁_zero
    rw [hz₁_zero] at hz₁
    simp at hz₁
  have hz₂0 : z₂ ≠ 0 := by
    -- The same constant-term argument excludes `z₂ = 0`.
    intro hz₂_zero
    rw [hz₂_zero] at hz₂
    simp at hz₂
  let u : ℕ → K := fun m ↦
    (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ m - z₂⁻¹ ^ m)
  have hu_sol : (exercise8Rec α β).IsSolution u := by
    have hz₁_inv :
        z₁⁻¹ ^ 2 = α * z₁⁻¹ + β :=
      exercise8_inverseSquareEqOfRootEquation (α := α) (β := β) hz₁_root hz₁0
    have hz₂_inv :
        z₂⁻¹ ^ 2 = α * z₂⁻¹ + β :=
      exercise8_inverseSquareEqOfRootEquation (α := α) (β := β) hz₂_root hz₂0
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
    rw [exercise8Rec, Fin.sum_univ_two]
    dsimp [u]
    rw [hsol₁' m, hsol₂' m]
    ring
  have hu_init : ∀ i : Fin 2, u i = ![0, 1] i := by
    intro i
    fin_cases i
    · -- At `0`, the two geometric terms cancel.
      simp [u]
    · -- At `1`, the normalization factor gives the prescribed initial value.
      dsimp [u]
      simp only [pow_one]
      have hz21 : z₂ ≠ z₁ := by
        intro h
        exact hneq h.symm
      calc
        z₁ * z₂ / (z₂ - z₁) * (z₁⁻¹ - z₂⁻¹)
            = z₂ * (z₂ - z₁)⁻¹ - z₁ * (z₂ - z₁)⁻¹ := by
                field_simp [hneq, hz₁0, hz₂0]
        _ = (z₂ - z₁) * (z₂ - z₁)⁻¹ := by ring
        _ = 1 := by
              exact mul_inv_cancel₀ (sub_ne_zero.mpr hz21)
  have hu_eq : u = exercise8Coeffs α β := by
    -- Recurrence uniqueness identifies the candidate with the canonical solution.
    simpa [exercise8Coeffs] using
      (exercise8Rec α β).eq_mk_of_is_sol_of_eq_init' hu_sol hu_init
  simpa [u] using congrArg (fun f : ℕ → K => f n) hu_eq.symm

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the repeated-root branch of the closed
form becomes an arithmetic-geometric expression. -/
theorem exercise8_coeff_closed_form_of_eq
    {α β z₁ z₂ : K}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ = z₂)
    (n : ℕ) :
    exercise8Coeffs α β n = (n : K) * z₁⁻¹ ^ (n - 1) := by
  rcases exercise8_rootEqAndVieta (α := α) (β := β) hroots with
    ⟨_, _, hconst, hz₁_root, _, hz₁0, _⟩
  have hconst' : (-1 : K) = β * z₁ * z₁ := by
    simpa [hz] using hconst
  have hβ_eq : β = -(z₁⁻¹) ^ 2 := by
    -- The repeated-root product relation determines `β`.
    exact (mul_right_cancel₀ (pow_ne_zero 2 hz₁0)) <| by
      calc
        β * z₁ ^ 2 = -1 := by
          simpa [pow_two, mul_assoc] using hconst'.symm
        _ = (-(z₁⁻¹) ^ 2) * z₁ ^ 2 := by
          field_simp [hz₁0]
  have hα_eq : α = 2 * z₁⁻¹ := by
    -- The root equation and the product identity together determine `α`.
    exact (mul_right_cancel₀ hz₁0) <| by
      calc
        α * z₁ = 1 - β * z₁ ^ 2 := by
          rw [hz₁_root]
          ring
        _ = 2 := by
          rw [show β * z₁ ^ 2 = (-1 : K) by simpa [pow_two, mul_assoc] using hconst'.symm]
          ring
        _ = (2 * z₁⁻¹) * z₁ := by
          field_simp [hz₁0]
  let u : ℕ → K := fun m ↦ (m : K) * z₁⁻¹ ^ (m - 1)
  have hu_sol : (exercise8Rec α β).IsSolution u := by
    intro m
    rw [exercise8Rec, Fin.sum_univ_two]
    cases m with
    | zero =>
        -- The first recurrence step is a direct algebraic check.
        simp [u, hα_eq, hβ_eq]
    | succ m =>
        -- For positive indices, rewrite every term with the same inverse power.
        simp [u, hα_eq, hβ_eq, pow_succ, mul_assoc, mul_left_comm, mul_comm]
        ring
  have hu_init : ∀ i : Fin 2, u i = ![0, 1] i := by
    intro i
    fin_cases i
    · -- The zeroth term vanishes because of the prefactor `n`.
      simp [u]
    · -- The first term is exactly `1`.
      simp [u]
  have hu_eq : u = exercise8Coeffs α β := by
    -- Recurrence uniqueness again identifies the repeated-root candidate.
    simpa [exercise8Coeffs] using
      (exercise8Rec α β).eq_mk_of_is_sol_of_eq_init' hu_sol hu_init
  simpa [u] using congrArg (fun f : ℕ → K => f n) hu_eq.symm

end ClosedFormHelpers

section CoefficientBound

variable {𝕜 : Type*} [SeminormedCommRing 𝕜] [NormOneClass 𝕜]

/-- Helper for Exercise 8: after shifting by one index, the recursive coefficients are dominated by
the geometric majorant `(2c)^n`, where `c = max (|α|, |β|, 1 / 2)`. -/
theorem exercise8_coeff_norm_succ_le_geometric (α β : 𝕜) (n : ℕ) :
    ‖exercise8Coeffs α β (n + 1)‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ n := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
  have hone : exercise8Coeffs α β 1 = 1 := (exercise8_coeffs_zero_one α β).2
  have hα : ‖α‖ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hβ : ‖β‖ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hone_le_two_c : (1 : ℝ) ≤ 2 * c := by
    have hhalf : (1 / 2 : ℝ) ≤ c := by
      dsimp [c]
      exact le_max_right _ _
    nlinarith
  have hpair :
      ∀ m : ℕ,
        ‖exercise8Coeffs α β (m + 1)‖ ≤ (2 * c) ^ m ∧
        ‖exercise8Coeffs α β (m + 2)‖ ≤ (2 * c) ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
        constructor
        · -- The first shifted coefficient is `1`, which matches the geometric majorant at `0`.
          simp [hone, c]
        · -- The recurrence at `n = 0` reduces the second shifted coefficient to `α`.
          rw [exercise8Coeffs_succ_succ α β 0, hone, hzero, mul_one, mul_zero, add_zero]
          calc
            ‖α‖ ≤ c := hα
            _ ≤ 2 * c := by nlinarith
            _ = (2 * c) ^ (0 + 1) := by ring
    | succ m ihm =>
        rcases ihm with ⟨hm, hm_succ⟩
        constructor
        · -- The first half of the next pair is exactly the second half of the previous one.
          simpa [Nat.succ_eq_add_one, add_assoc, c] using hm_succ
        · -- Apply the recurrence and estimate each term by the induction hypotheses.
          rw [show m + 1 + 2 = m + 3 by omega]
          rw [exercise8Coeffs_succ_succ α β (m + 1)]
          calc
            ‖α * exercise8Coeffs α β (m + 2) + β * exercise8Coeffs α β (m + 1)‖
                ≤ ‖α * exercise8Coeffs α β (m + 2)‖ +
                    ‖β * exercise8Coeffs α β (m + 1)‖ := norm_add_le _ _
            _ ≤ ‖α‖ * ‖exercise8Coeffs α β (m + 2)‖ +
                    ‖β‖ * ‖exercise8Coeffs α β (m + 1)‖ := by
                  gcongr
                  · exact norm_mul_le _ _
                  · exact norm_mul_le _ _
            _ ≤ c * (2 * c) ^ (m + 1) + c * (2 * c) ^ m := by
                  gcongr
            _ ≤ (2 * c) ^ m * (2 * c) ^ 2 := by
                  have hmajor : c * (2 * c) + c ≤ (2 * c) ^ 2 := by
                    nlinarith [hc_nonneg, hone_le_two_c]
                  have hpow_nonneg : 0 ≤ (2 * c) ^ m := by positivity
                  have hfactor :
                      c * (2 * c) ^ (m + 1) + c * (2 * c) ^ m =
                        (2 * c) ^ m * (c * (2 * c) + c) := by
                    rw [pow_succ', ← mul_assoc]
                    ring
                  rw [hfactor]
                  gcongr
            _ = (2 * c) ^ (m + 2) := by rw [← pow_add]
  -- The requested estimate is the first component of the paired induction.
  simpa [c] using (hpair n).1

-- Proof sketch: prove the estimate by induction on `n` using the recurrence and the choice
-- `c = max (|α|, |β|, 1 / 2)`.
/-- The coefficients of the recurrence in Exercise 8 satisfy the geometric bound from part (a). -/
theorem exercise8_coeff_norm_le (α β : 𝕜) (n : ℕ) :
    ‖exercise8Coeffs α β n‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ (n - 1) := by
  rcases n with _ | n
  · -- The constant term vanishes, so the textbook bound is immediate.
    simp [(exercise8_coeffs_zero_one α β).1]
  · -- For positive indices, rewrite the statement into the stable shifted estimate.
    simpa [Nat.succ_sub_one] using exercise8_coeff_norm_succ_le_geometric α β n

end CoefficientBound

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

open Polynomial

-- Proof sketch: use the coefficient bound from `exercise8_coeff_norm_le` together with
-- `FormalMultilinearSeries.le_radius_of_bound`.
/-- The series attached to Exercise 8 has strictly positive radius of convergence. -/
theorem exercise8_radius_pos (α β : 𝕜) :
    0 < (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  have hc_half : (1 / 2 : ℝ) ≤ c := by
    dsimp [c]
    exact le_max_right _ _
  have h_two_c_pos : 0 < 2 * c := by
    nlinarith
  have hr_nonneg : 0 ≤ (2 * c)⁻¹ := by positivity
  let r : NNReal := ⟨(2 * c)⁻¹, hr_nonneg⟩
  have h_two_c_ne_zero : (2 * c) ≠ 0 := ne_of_gt h_two_c_pos
  have hradius :
      (r : ENNReal) ≤ (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
    -- The geometric bound makes `‖aₙ‖ rⁿ` uniformly bounded by `r`.
    refine (ofScalars 𝕜 (exercise8Coeffs α β)).le_radius_of_bound ((2 * c)⁻¹) ?_
    intro n
    rcases n with _ | n
    · -- The constant coefficient is zero, so the scaled norm is zero as well.
      simp [r, c, (exercise8_coeffs_zero_one α β).1]
    · -- For positive indices, cancel the matching geometric powers.
      calc
        ‖ofScalars 𝕜 (exercise8Coeffs α β) (n + 1)‖ * (r : ℝ) ^ (n + 1)
            = ‖exercise8Coeffs α β (n + 1)‖ * ((2 * c)⁻¹) ^ (n + 1) := by
                rw [FormalMultilinearSeries.ofScalars_norm
                  (E := 𝕜) (c := exercise8Coeffs α β) (n := n + 1)]
                rfl
        _ ≤ (2 * c) ^ n * ((2 * c)⁻¹) ^ (n + 1) := by
              have hpow_nonneg : 0 ≤ ((2 * c)⁻¹) ^ (n + 1) := by positivity
              nlinarith [exercise8_coeff_norm_succ_le_geometric α β n]
        _ = (2 * c)⁻¹ := by
              have hcancel : (2 * c) ^ n * ((2 * c)⁻¹) ^ n = 1 := by
                rw [← mul_pow, mul_inv_cancel₀ h_two_c_ne_zero, one_pow]
              rw [pow_succ']
              calc
                (2 * c) ^ n * ((2 * c)⁻¹ * ((2 * c)⁻¹) ^ n)
                    = ((2 * c) ^ n * ((2 * c)⁻¹) ^ n) * (2 * c)⁻¹ := by
                        ac_rfl
                _ = (2 * c)⁻¹ := by rw [hcancel, one_mul]
  have hrpos : (0 : ENNReal) < (r : ENNReal) := by
    exact ENNReal.coe_pos.2 (by
      change 0 < (2 * c)⁻¹
      positivity)
  exact lt_of_lt_of_le hrpos hradius

end Analytic

section AnalyticSum

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

open Polynomial

/-- Helper for Exercise 8: the recurrence denominator packaged as a scalar power series. -/
private noncomputable def exercise8DenominatorSeries (α β : 𝕜) : 𝕜⟦X⟧ :=
  (1 : 𝕜⟦X⟧) - PowerSeries.C α * PowerSeries.X - PowerSeries.C β * PowerSeries.X ^ 2

/-- Helper for Exercise 8: the recurrence coefficients packaged as a scalar power series. -/
private noncomputable def exercise8SolutionSeries (α β : 𝕜) : 𝕜⟦X⟧ :=
  PowerSeries.mk (exercise8Coeffs α β)

/-- Helper for Exercise 8: the denominator series has no coefficients above degree `2`. -/
private theorem exercise8_denominatorSeries_coeff_eq_zero_of_three_le
    (α β : 𝕜) {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff n (exercise8DenominatorSeries α β) = 0 := by
  -- All three summands are supported in degrees `0`, `1`, and `2`.
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have hone : PowerSeries.coeff n (1 : 𝕜⟦X⟧) = 0 := by
    simp [PowerSeries.coeff_one, h0]
  have hαX : PowerSeries.coeff n (PowerSeries.C α * PowerSeries.X : 𝕜⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X, h1]
  have hβX : PowerSeries.coeff n (PowerSeries.C β * PowerSeries.X ^ 2 : 𝕜⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X_pow, h2]
  simp [exercise8DenominatorSeries, hone, hαX, hβX]

/-- Helper for Exercise 8: the formal variable has no coefficients above degree `1`. -/
private theorem exercise8_X_coeff_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧) = 0 := by
  -- The series `X` is supported exactly in degree `1`.
  have h1 : n ≠ 1 := by omega
  simp [PowerSeries.coeff_X, h1]

/-- Helper for Exercise 8: multiplying the coefficient series by the recurrence polynomial gives the
formal variable `X`. -/
private theorem exercise8_formal_series_mul_identity (α β : 𝕜) :
    exercise8DenominatorSeries α β * exercise8SolutionSeries α β = PowerSeries.X := by
  let S : 𝕜⟦X⟧ := exercise8SolutionSeries α β
  ext n
  rcases n with _ | (_ | n)
  · -- The constant coefficient vanishes because the initial datum is `a₀ = 0`.
    have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
    simp [exercise8DenominatorSeries, exercise8SolutionSeries, hzero]
  · -- The linear coefficient is `a₁ = 1`, and the shifted terms still vanish at this degree.
    have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
    have hone : exercise8Coeffs α β 1 = 1 := (exercise8_coeffs_zero_one α β).2
    have hα :
        PowerSeries.coeff 1 ((PowerSeries.C α * PowerSeries.X) * S) =
          α * exercise8Coeffs α β 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [S, exercise8SolutionSeries] using
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
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β)) =
          α * exercise8Coeffs α β 0 := by
      simpa [S, exercise8SolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff 1
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk (exercise8Coeffs α β)) = 0 := by
      simpa [S, exercise8SolutionSeries] using hβ
    rw [exercise8DenominatorSeries, sub_mul, sub_mul, one_mul]
    suffices
        exercise8Coeffs α β 1 +
            -(PowerSeries.coeff 1
                (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β))) +
          -(PowerSeries.coeff 1
              (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk (exercise8Coeffs α β))) =
          1 by
      simpa [sub_eq_add_neg, exercise8SolutionSeries]
    rw [hα', hβ', hzero]
    simp [hone]
  · -- Route correction: for degrees `n + 2`, the coefficient identity is exactly the recurrence.
    have hα :
        PowerSeries.coeff (n + 2) ((PowerSeries.C α * PowerSeries.X) * S) =
          α * exercise8Coeffs α β (n + 1) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [pow_one, S, exercise8SolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ α * x) (PowerSeries.coeff_X_pow_mul S 1 (n + 1))
    have hβ :
        PowerSeries.coeff (n + 2) ((PowerSeries.C β * PowerSeries.X ^ 2) * S) =
          β * exercise8Coeffs α β n := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [S, exercise8SolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ β * x) (PowerSeries.coeff_X_pow_mul S 2 n)
    have hrec := exercise8Coeffs_succ_succ α β n
    have hα' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β)) =
          α * exercise8Coeffs α β (n + 1) := by
      simpa [S, exercise8SolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk (exercise8Coeffs α β)) =
          β * exercise8Coeffs α β n := by
      simpa [S, exercise8SolutionSeries] using hβ
    rw [exercise8DenominatorSeries, sub_mul, sub_mul, one_mul]
    suffices
        exercise8Coeffs α β (n + 1 + 1) +
            -(PowerSeries.coeff (n + 1 + 1)
                (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β))) +
          -(PowerSeries.coeff (n + 1 + 1)
              (PowerSeries.C β * PowerSeries.X ^ 2 *
                PowerSeries.mk (exercise8Coeffs α β))) =
          PowerSeries.coeff (n + 1 + 1) PowerSeries.X by
      simpa [sub_eq_add_neg, exercise8SolutionSeries]
    rw [hα', hβ', hrec]
    ring_nf
    have hneq : 2 + n ≠ 1 := by omega
    simp [PowerSeries.coeff_X, hneq]

/-- Helper for Exercise 8: the denominator power series has infinite radius because it is a
quadratic polynomial. -/
private theorem exercise8_denominatorSeries_radius_eq_top (α β : 𝕜) :
    (exercise8DenominatorSeries α β).radius = ⊤ := by
  -- The denominator coefficients are eventually zero above degree `2`.
  let coeffs : ℕ → 𝕜 := fun n ↦ PowerSeries.coeff n (exercise8DenominatorSeries α β)
  rw [PowerSeries.radius]
  change (ofScalars 𝕜 coeffs).radius = ⊤
  apply (ofScalars 𝕜 coeffs).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨3, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕜)
    (c := coeffs)
    (hc := exercise8_denominatorSeries_coeff_eq_zero_of_three_le α β hn)

/-- Helper for Exercise 8: the formal variable `X` has infinite radius because it is a polynomial
of degree `1`. -/
private theorem exercise8_X_radius_eq_top :
    (PowerSeries.X : 𝕜⟦X⟧).radius = ⊤ := by
  -- The coefficient sequence of `X` vanishes above degree `1`.
  let coeffs : ℕ → 𝕜 := fun n ↦ PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧)
  rw [PowerSeries.radius]
  change (ofScalars 𝕜 coeffs).radius = ⊤
  apply (ofScalars 𝕜 coeffs).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕜)
    (c := coeffs)
    (hc := exercise8_X_coeff_eq_zero_of_two_le hn)

/-- Helper for Exercise 8: evaluating the denominator polynomial series recovers
`1 - α z - β z^2`. -/
private theorem exercise8_denominatorSeries_sum (α β z : 𝕜) :
    PowerSeries.sum (exercise8DenominatorSeries α β) z = (1 : 𝕜) - α * z - β * z ^ 2 := by
  -- Finite support reduces the scalar series to the first three coefficients.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 3)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [exercise8DenominatorSeries, pow_two]
    ring
  · intro n hn
    have hthree : 3 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (exercise8DenominatorSeries α β) = 0 :=
      exercise8_denominatorSeries_coeff_eq_zero_of_three_le α β hthree
    simp [hcoeff]

/-- Helper for Exercise 8: evaluating the formal variable `X` at `z` gives `z`. -/
private theorem exercise8_X_sum (z : 𝕜) :
    PowerSeries.sum (PowerSeries.X : 𝕜⟦X⟧) z = z := by
  -- Finite support reduces the scalar series to the constant and linear terms.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [PowerSeries.coeff_X]
  · intro n hn
    have htwo : 2 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧) = 0 :=
      exercise8_X_coeff_eq_zero_of_two_le htwo
    simp [hcoeff]

-- Proof sketch: compare coefficients after multiplying the series by `1 - α z - β z^2`;
-- the recurrence makes every coefficient vanish except the linear term.
section CompleteAnalytic

variable [CompleteSpace 𝕜]

/-- Multiplying the sum of the Exercise 8 series by `1 - α z - β z^2` gives `z` on the disk of
convergence. -/
theorem exercise8_recurrence_polynomial_mul_sum
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ((1 : 𝕜) - α * z - β * z ^ 2) * ofScalarsSum (exercise8Coeffs α β) z = z := by
  -- Route correction: package the recurrence as a formal identity and then evaluate it through the
  -- chapter Cauchy-product theorem on a finite radius strictly between `‖z‖₊` and the radius.
  let D : 𝕜⟦X⟧ := exercise8DenominatorSeries α β
  let S : 𝕜⟦X⟧ := exercise8SolutionSeries α β
  have hz' : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
    exact (mem_scalarSeriesDiscOfConvergence_iff (𝕜 := 𝕜) (a := exercise8Coeffs α β)).1 hz
  obtain ⟨ρ, hzρ, hρS_lt⟩ :
      ∃ ρ : ℝ≥0, ‖z‖₊ < ρ ∧ (ρ : ℝ≥0∞) < S.radius := by
    simpa [S, exercise8SolutionSeries, PowerSeries.radius] using
      ENNReal.lt_iff_exists_nnreal_btwn.1 hz'
  have hρD : (ρ : ℝ≥0∞) ≤ D.radius := by
    have hDtop : D.radius = ⊤ := by
      simpa [D] using exercise8_denominatorSeries_radius_eq_top (α := α) (β := β)
    rw [hDtop]
    exact le_top
  have hρS : (ρ : ℝ≥0∞) ≤ S.radius := hρS_lt.le
  have hmul :
      PowerSeries.sum (D * S) z = PowerSeries.sum D z * PowerSeries.sum S z :=
    scalar_series_cauchy_product_eval_eq_mul D S ρ hρD hρS hzρ
  have hDsum : PowerSeries.sum D z = (1 : 𝕜) - α * z - β * z ^ 2 := by
    simpa [D] using exercise8_denominatorSeries_sum α β z
  have hSsum : PowerSeries.sum S z = ofScalarsSum (exercise8Coeffs α β) z := by
    simp [S, exercise8SolutionSeries, PowerSeries.sum]
  have hformal : D * S = (PowerSeries.X : 𝕜⟦X⟧) := by
    simpa [D, S] using exercise8_formal_series_mul_identity (α := α) (β := β)
  -- Rewrite both sides using the formal identity and the explicit polynomial evaluations.
  calc
    ((1 : 𝕜) - α * z - β * z ^ 2) * ofScalarsSum (exercise8Coeffs α β) z
        = PowerSeries.sum D z * PowerSeries.sum S z := by
            rw [hDsum, hSsum]
    _ = PowerSeries.sum (D * S) z := by rw [hmul]
    _ = PowerSeries.sum (PowerSeries.X : 𝕜⟦X⟧) z := by rw [hformal]
    _ = z := exercise8_X_sum z

/-- Helper for Exercise 8: the quadratic denominator does not vanish inside the convergence disc of
the coefficient series. -/
private theorem exercise8_denominator_ne_zero_of_mem_radius
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ((1 : 𝕜) - α * z - β * z ^ 2) ≠ 0 := by
  -- The evaluated formal identity would force `z = 0`, contradicting the denominator value there.
  intro hden
  have hmul := exercise8_recurrence_polynomial_mul_sum (α := α) (β := β) hz
  rw [hden, zero_mul] at hmul
  have hz0 : z = 0 := by simpa using hmul.symm
  have hone_zero : (1 : 𝕜) = 0 := by
    rw [hz0] at hden
    simp at hden
  exact one_ne_zero hone_zero

-- Proof sketch: combine the previous identity with the fact that the denominator does not vanish
-- on the open disk of convergence.
/-- Exercise 8: on the open disk of convergence, the sum of the recursive power series is
`z / (1 - α z - β z^2)`. -/
theorem exercise8_sum_eq_rational_function
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ofScalarsSum (exercise8Coeffs α β) z = z / ((1 : 𝕜) - α * z - β * z ^ 2) := by
  -- Divide the evaluated recurrence identity by the nonvanishing quadratic denominator.
  have hden :
      ((1 : 𝕜) - α * z - β * z ^ 2) ≠ 0 :=
    exercise8_denominator_ne_zero_of_mem_radius (α := α) (β := β) hz
  have hmul := exercise8_recurrence_polynomial_mul_sum (α := α) (β := β) hz
  exact (eq_div_iff hden).2 (by simpa [mul_comm] using hmul)

/-- Helper for Cartan section04 frozen_0023_Exercise_8: any root of `1 - α z - β z²` bounds the
radius of convergence from above. -/
lemma exercise8_radius_le_norm_root (α β : 𝕜) {z : 𝕜}
    (hzroot : 1 = α * z + β * z ^ 2) :
    (ofScalars 𝕜 (exercise8Coeffs α β)).radius ≤ ENNReal.ofReal ‖z‖ := by
  by_contra hlt
  have hzrad : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 (exercise8Coeffs α β)).radius :=
    lt_of_not_ge hlt
  have hzmem : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
    have hzrad' : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
      simpa using hzrad
    exact (mem_scalarSeriesDiscOfConvergence_iff (𝕜 := 𝕜) (a := exercise8Coeffs α β)).2 hzrad'
  have hden_ne :=
    exercise8_denominator_ne_zero_of_mem_radius (α := α) (β := β) hzmem
  have hden : (1 : 𝕜) - α * z - β * z ^ 2 = 0 := by
    calc
      (1 : 𝕜) - α * z - β * z ^ 2 = 1 - (α * z + β * z ^ 2) := by ring
      _ = 0 := by rw [hzroot]; ring
  exact hden_ne hden

end CompleteAnalytic

/-- Helper for Cartan section04 frozen_0023_Exercise_8: in the distinct-root case, every smaller
weighted norm series is dominated by a sum of two geometric series. -/
lemma exercise8_summable_distinct_of_lt_min_norm (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ ≠ z₂) {r : NNReal} (hr : (r : ℝ) < min ‖z₁‖ ‖z₂‖) :
    Summable (fun n : ℕ => ‖exercise8Coeffs α β n‖ * (r : ℝ) ^ n) := by
  rcases exercise8_rootEqAndVieta (α := α) (β := β) hroots with
    ⟨_, _, _, hz₁_root, hz₂_root, hz₁0, hz₂0⟩
  let C : 𝕜 := z₁ * z₂ / (z₂ - z₁)
  have hz₁_eq : β * z₁ ^ 2 + α * z₁ - 1 = 0 := by
    calc
      β * z₁ ^ 2 + α * z₁ - 1 = (α * z₁ + β * z₁ ^ 2) - 1 := by ring
      _ = 0 := by rw [hz₁_root]; ring
  have hz₂_eq : β * z₂ ^ 2 + α * z₂ - 1 = 0 := by
    calc
      β * z₂ ^ 2 + α * z₂ - 1 = (α * z₂ + β * z₂ ^ 2) - 1 := by ring
      _ = 0 := by rw [hz₂_root]; ring
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
    -- Both inverse-root contributions are geometric because `r / ‖zᵢ‖ < 1`.
    exact ((summable_geometric_of_norm_lt_one hq₁_norm).add
        (summable_geometric_of_norm_lt_one hq₂_norm)).mul_left ‖C‖
  refine Summable.of_nonneg_of_le
      (g := fun n : ℕ => ‖exercise8Coeffs α β n‖ * (r : ℝ) ^ n)
      (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_ hgeom
  intro n
  -- Rewrite the coefficient by the distinct-root closed form and separate the two geometric terms.
  calc
    ‖exercise8Coeffs α β n‖ * (r : ℝ) ^ n
        = ‖C * (z₁⁻¹ ^ n - z₂⁻¹ ^ n)‖ * (r : ℝ) ^ n := by
            rw [exercise8_coeff_closed_form_of_distinct_roots_aux
              (hz₁ := hz₁_eq) (hz₂ := hz₂_eq) (hneq := hz) (n := n)]
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

/-- Helper for Cartan section04 frozen_0023_Exercise_8: in the repeated-root case, every smaller
weighted norm series is dominated by an arithmetic-geometric series. -/
lemma exercise8_summable_repeated_of_lt_norm (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂})
    (hz : z₁ = z₂) {r : NNReal} (hr : (r : ℝ) < ‖z₁‖) :
    Summable (fun n : ℕ => ‖exercise8Coeffs α β n‖ * (r : ℝ) ^ n) := by
  rcases exercise8_rootEqAndVieta (α := α) (β := β) hroots with
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
      (g := fun n : ℕ => ‖exercise8Coeffs α β (n + 1)‖ * (r : ℝ) ^ (n + 1))
      (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_ harith
  intro n
  -- Rewrite the shifted coefficient by the repeated-root formula and compare with the model series.
  calc
    ‖exercise8Coeffs α β (n + 1)‖ * (r : ℝ) ^ (n + 1)
        = ‖((n + 1 : 𝕜) * z₁⁻¹ ^ n)‖ * (r : ℝ) ^ (n + 1) := by
            rw [exercise8_coeff_closed_form_of_eq (α := α) (β := β) (hroots := hroots)
              (hz := hz) (n := n + 1)]
            simp
    _ = ‖(n + 1 : 𝕜)‖ * ‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ (n + 1) := by rw [norm_mul]
    _ ≤ (n + 1 : ℝ) * ‖z₁⁻¹ ^ n‖ * (r : ℝ) ^ (n + 1) := by
          have hnat : ‖(n + 1 : 𝕜)‖ ≤ (n + 1 : ℝ) := by
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

/-- Helper for Cartan section04 frozen_0023_Exercise_8: the closed-form comparisons give the lower
radius bound `min (‖z₁‖, ‖z₂‖) ≤ ρ(S)`. -/
lemma exercise8_minRootNorm_le_radius (α β : 𝕜) {z₁ z₂ : 𝕜}
    (hroots : (exercise8RootPolynomial α β).roots = {z₁, z₂}) :
    ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) ≤ (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hsummable :
      Summable (fun n : ℕ => ‖ofScalars 𝕜 (exercise8Coeffs α β) n‖ * (r : ℝ) ^ n) := by
    by_cases hz : z₁ = z₂
    · have hr' : (r : ℝ) < ‖z₁‖ := by
        have hmin : (r : ℝ) < min ‖z₁‖ ‖z₂‖ := by simpa using hr
        simpa [hz] using hmin
      -- In the repeated-root branch, compare with an arithmetic-geometric series.
      simpa [FormalMultilinearSeries.ofScalars_norm] using
        exercise8_summable_repeated_of_lt_norm (α := α) (β := β) (hroots := hroots) hz hr'
    · have hr' : (r : ℝ) < min ‖z₁‖ ‖z₂‖ := by
        simpa using hr
      -- In the distinct-root branch, compare with two geometric series.
      simpa [FormalMultilinearSeries.ofScalars_norm] using
        exercise8_summable_distinct_of_lt_min_norm (α := α) (β := β) (hroots := hroots) hz hr'
  -- Weighted norm summability converts directly into a lower bound on the radius.
  exact (ofScalars 𝕜 (exercise8Coeffs α β)).le_radius_of_summable (r := r) hsummable

-- Proof sketch: use the rational expression of the sum and compare the singularities coming from
-- the two roots of `β X^2 + α X - 1`.
section CompleteAnalytic

variable [CompleteSpace 𝕜]

/-- Cartan section04 frozen_0023_Exercise_8: the radius of convergence in Exercise 8 is the
minimum of the norms of the two roots of `β X^2 + α X - 1`, when `z₁, z₂` are the full quadratic
root pair. -/
theorem exercise8_radius_eq_min_root_norm
    {α β z₁ z₂ : 𝕜}
    (hroots : (C β * X ^ 2 + C α * X - 1).roots = {z₁, z₂}) :
    (ofScalars 𝕜 (exercise8Coeffs α β)).radius = ↑(min ‖z₁‖₊ ‖z₂‖₊) := by
  rcases exercise8_rootEqAndVieta (α := α) (β := β) (z₁ := z₁) (z₂ := z₂)
      (by simpa [exercise8RootPolynomial] using hroots) with
    ⟨_, _, _, hz₁_root, hz₂_root, _, _⟩
  have hupper₁ :
      (ofScalars 𝕜 (exercise8Coeffs α β)).radius ≤ ENNReal.ofReal ‖z₁‖ :=
    exercise8_radius_le_norm_root (α := α) (β := β) hz₁_root
  have hupper₂ :
      (ofScalars 𝕜 (exercise8Coeffs α β)).radius ≤ ENNReal.ofReal ‖z₂‖ :=
    exercise8_radius_le_norm_root (α := α) (β := β) hz₂_root
  have hupper :
      (ofScalars 𝕜 (exercise8Coeffs α β)).radius ≤ ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) := by
    -- Each root excludes radii strictly larger than its norm, so the radius is bounded by the
    -- minimum.
    rw [ENNReal.ofReal_min]
    exact le_min hupper₁ hupper₂
  have hlower :
      ENNReal.ofReal (min ‖z₁‖ ‖z₂‖) ≤ (ofScalars 𝕜 (exercise8Coeffs α β)).radius :=
    exercise8_minRootNorm_le_radius (α := α) (β := β) (z₁ := z₁) (z₂ := z₂)
      (by simpa [exercise8RootPolynomial] using hroots)
  simpa using le_antisymm hupper hlower

end CompleteAnalytic

end AnalyticSum

section ClosedForm

variable {K : Type*} [Field K]

-- Proof sketch: factor the denominator with the two distinct roots and read off the coefficients
-- from the partial fraction decomposition.
/-- Distinct roots of `β X^2 + α X - 1` give the closed formula for the coefficients from part
(c). -/
theorem exercise8_coeff_closed_form_of_distinct_roots
    {α β z₁ z₂ : K}
    (hz₁ : β * z₁ ^ 2 + α * z₁ - 1 = 0)
    (hz₂ : β * z₂ ^ 2 + α * z₂ - 1 = 0)
    (hneq : z₁ ≠ z₂) (n : ℕ) :
    exercise8Coeffs α β n = (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ n - z₂⁻¹ ^ n) := by
  -- The file-local recurrence-uniqueness helper already proves the distinct-root closed form.
  simpa using
    exercise8_coeff_closed_form_of_distinct_roots_aux
      (hz₁ := hz₁) (hz₂ := hz₂) (hneq := hneq) (n := n)

end ClosedForm
