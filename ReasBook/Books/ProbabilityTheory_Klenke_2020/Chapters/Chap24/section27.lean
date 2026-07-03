import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_24_27 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The open-simplex density on the first `n` coordinates used to define the Dirichlet law with
parameter vector `θ : Fin (n + 1) → ℝ`. -/
def dirichletDensity {n : ℕ} (θ : Fin (n + 1) → ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <|
    if (∀ i : Fin n, 0 < x i) ∧ ((∑ i : Fin n, x i) < 1) then
      (Real.Gamma (∑ i : Fin (n + 1), θ i) / ∏ i : Fin (n + 1), Real.Gamma (θ i)) *
        (∏ i : Fin n, x i ^ (θ i.castSucc - 1)) *
        (1 - ∑ i : Fin n, x i) ^ (θ (Fin.last n) - 1)
    else 0

-- Proof sketch: unfold `dirichletDensity`; it is exactly the indicated Gamma-normalized density on
-- the open simplex chart of the first `n` coordinates.
/-- The defining density formula for the chart model of the Dirichlet distribution. -/
theorem dirichletDensity_def {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    dirichletDensity θ =
      fun x : Fin n → ℝ ↦
        ENNReal.ofReal <|
          if (∀ i : Fin n, 0 < x i) ∧ ((∑ i : Fin n, x i) < 1) then
            (Real.Gamma (∑ i : Fin (n + 1), θ i) / ∏ i : Fin (n + 1), Real.Gamma (θ i)) *
              (∏ i : Fin n, x i ^ (θ i.castSucc - 1)) *
              (1 - ∑ i : Fin n, x i) ^ (θ (Fin.last n) - 1)
          else 0 := sorry

/-- The Dirichlet law on `Fin (n + 1) → ℝ`, obtained by pushing forward the open-simplex density
on the first `n` coordinates and recovering the last coordinate from the sum-to-one constraint. -/
def dirichletMeasure {n : ℕ} (θ : Fin (n + 1) → ℝ) : Measure (Fin (n + 1) → ℝ) :=
  ((volume : Measure (Fin n → ℝ)).withDensity (dirichletDensity θ)).map
    (fun x ↦ Fin.snoc x (1 - ∑ i : Fin n, x i))

-- Proof sketch: unfold `dirichletMeasure`; by definition it is the pushforward of the chart
-- density along `x ↦ Fin.snoc x (1 - ∑ i, x i)`.
/-- The Dirichlet law is the pushforward of its open-simplex density under the map that adds the
last coordinate `1 - ∑ i, x i`. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    dirichletMeasure θ =
      ((volume : Measure (Fin n → ℝ)).withDensity (dirichletDensity θ)).map
        (fun x ↦ Fin.snoc x (1 - ∑ i : Fin n, x i)) := sorry

-- Proof sketch: write the Dirichlet law in the open-simplex chart on the first `n` coordinates,
-- take the product with the independent Gamma law `gammaMeasure (∑ i, θ i) 1`, and transport this
-- joint law along `(x, z) ↦ z • Fin.snoc x (1 - ∑ i, x i)`. The Jacobian computation from the
-- source shows that the transformed density factors as the product of the unit-rate Gamma densities
-- with shapes `θ i`.
/-- Theorem 24.27: if `X` has Dirichlet law with parameter vector `θ` and `Z` is an independent
unit-rate Gamma variable with shape `∑ i, θ i`, then the scaled vector `Z • X` has the product
law of independent unit-rate Gamma variables with shapes `θ i`. -/
theorem dirichlet_smul_gamma_hasLaw_pi
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) :
    HasLaw
      (fun ω ↦ Z ω • X ω)
      (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1) P := sorry

-- Proof sketch: apply the main product-law statement and use the standard characterization of a
-- finite family as independent when its joint law is the corresponding product measure.
/-- The scaled coordinates `ω ↦ Z ω * X ω i` form an independent family. -/
theorem dirichlet_smul_gamma_iIndepFun
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) :
    iIndepFun (fun i : Fin (n + 1) ↦ fun ω ↦ Z ω * X ω i) P := sorry

-- Proof sketch: project the joint product-law statement to the `i`th coordinate and identify the
-- corresponding marginal of the product measure.
/-- Each scaled coordinate `ω ↦ Z ω * X ω i` has the unit-rate Gamma law with shape `θ i`. -/
theorem dirichlet_smul_gamma_coordinate_hasLaw
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) (i : Fin (n + 1)) :
    HasLaw (fun ω ↦ Z ω * X ω i) (gammaMeasure (θ i) 1) P := sorry

end ProbabilityTheory
