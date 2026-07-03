import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_24_30 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The sum of the parameters strictly following the `i`th stick-breaking factor. -/
def stickBreakingTailSum {n : ℕ} (θ : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ i.castSucc < j), θ j

/-- A finite stick-breaking input vector extended by the terminal value `1`. -/
def extendWithTerminalOne {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 : ℝ) v

/-- The finite stick-breaking map sending break proportions to the associated mass vector. -/
def stickBreakingMap {n : ℕ} (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦ (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i), (1 - v j)) * v i

/-- The product Beta input measure for the finite stick-breaking construction. -/
def stickBreakingBetaInputMeasure {n : ℕ} (θ : Fin (n + 1) → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i : Fin n ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)

/-- The finite-dimensional Dirichlet measure defined by the Beta stick-breaking construction. -/
def dirichletMeasure {n : ℕ} (θ : Fin (n + 1) → ℝ) : Measure (Fin (n + 1) → ℝ) :=
  Measure.map (fun v ↦ stickBreakingMap (extendWithTerminalOne v)) (stickBreakingBetaInputMeasure θ)

-- Proof sketch: unfold `dirichletMeasure`; it is defined as the pushforward of the product Beta
-- input measure under the finite stick-breaking map with terminal factor `1`.
/-- The Dirichlet measure is the pushforward of the Beta stick-breaking input measure under the
finite stick-breaking map. -/
theorem dirichletMeasure_eq_map_stickBreakingBetaInputMeasure
    {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    dirichletMeasure θ =
      Measure.map (fun v ↦ stickBreakingMap (extendWithTerminalOne v))
        (stickBreakingBetaInputMeasure θ) := sorry

-- Proof sketch: use `iIndepFun_iff_map_fun_eq_pi_map` together with the coordinate laws `hV_law`
-- to identify the law of the Beta stick-breaking input vector with the corresponding product
-- measure, then compose with the measurable stick-breaking map.
/-- Corollary 24.30: an independent finite stick-breaking family of Beta variables, extended by a
terminal value `1`, has the associated Dirichlet law under the stick-breaking map. -/
theorem stickBreaking_hasLaw_dirichletMeasure
    (P : Measure Ω) {n : ℕ} (θ : Fin (n + 1) → ℝ) {V : Fin n → Ω → ℝ}
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : Fin n,
      HasLaw (V i) (betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)) P) :
    HasLaw
      (fun ω ↦ stickBreakingMap (extendWithTerminalOne (fun i : Fin n ↦ V i ω)))
      (dirichletMeasure θ) P := sorry
