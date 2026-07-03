import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_24_29 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

namespace ProbabilityTheory

/-- The Dirichlet law with parameter vector `θ` on a finite coordinate set is the pushforward of
independent Gamma laws by normalization with the total mass. -/
def dirichletMeasure {n : ℕ} (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: this is just the defining normalized-Gamma pushforward formula for
-- `dirichletMeasure`.
/-- The Dirichlet measure is the pushforward of the independent Gamma product law by the
normalization map. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin n → ℝ) :
    dirichletMeasure θ =
      (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j) := sorry

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: project the normalized-Gamma realization of the Dirichlet law onto the first
-- coordinate and identify the resulting ratio law with the Beta distribution having parameters
-- `θ 0` and the sum of the remaining coordinates.
/-- Corollary 24.29 (1): for a Dirichlet-distributed `(n + 1)`-tuple, the first coordinate has
Beta law with parameters `θ 0` and `∑ i, θ i.succ`. -/
theorem hasLaw_fst_beta_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω ↦ X ω 0) (betaMeasure (θ 0) (∑ i : Fin n, θ i.succ)) μ := sorry

-- Proof sketch: rewrite the residual coordinates as the normalized tail of the Gamma realization
-- from the Dirichlet law, then remove the first Gamma coordinate and apply the same normalized
-- Gamma description to the remaining parameter vector.
/-- Corollary 24.29 (2): after dividing the remaining coordinates by `1 - X₁`, the residual
vector again has Dirichlet law with the tail parameter vector. -/
theorem hasLaw_tail_dirichlet_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ X ω i.succ / (1 - X ω 0))
      (dirichletMeasure fun i : Fin n ↦ θ i.succ) μ := sorry

-- Proof sketch: in the normalized-Gamma model, the first ratio depends only on the first Gamma
-- variable and the remaining total mass, while the residual vector depends only on the normalized
-- tail; the independent Gamma coordinates then give the claimed independence.
/-- Corollary 24.29 (3): the first Dirichlet coordinate is independent of the renormalized tail
vector. -/
theorem indepFun_fst_tail_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    IndepFun (fun ω ↦ X ω 0) (fun ω ↦ fun i : Fin n ↦ X ω i.succ / (1 - X ω 0)) μ := sorry

end ProbabilityTheory
