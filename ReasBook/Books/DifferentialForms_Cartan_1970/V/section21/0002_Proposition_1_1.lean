import Mathlib
import cartan.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch` tool was available in this runner, so the statement
-- surface was checked directly against the local owner `analyticFunctionSubring`, the section
-- predicate `UniformlyBoundedOnCompacta`, and mathlib's `AnalyticOnNhd.deriv_of_isOpen` API.

/-- The derivative image of a holomorphic family on `D`, represented by restricting ambient
analytic extensions and their derivatives to `D`. -/
def HolomorphicDerivativeImage (D : Set ℂ) (A : Set (analyticFunctionSubring ℂ D)) :
    Set (analyticFunctionSubring ℂ D) :=
  { g | ∃ f ∈ A, ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F D ∧
      D.restrict F = (f : D → ℂ) ∧
      D.restrict (deriv F) = (g : D → ℂ) }

/-- Proposition 1.1. For an open set `D`, if a family `A ⊆ ℋ(D)` is uniformly bounded on every
compact subset of `D`, then the family of derivatives of its members is again uniformly bounded on
every compact subset of `D`. Here the derivative family is represented by
`HolomorphicDerivativeImage D A`. -/
theorem holomorphic_derivative_image_uniformly_bounded_on_compacts
    {D : Set ℂ} (hD_open : IsOpen D) {A : Set (analyticFunctionSubring ℂ D)}
    (hA : UniformlyBoundedOnCompacta D A) :
    UniformlyBoundedOnCompacta D (HolomorphicDerivativeImage D A) := by
  intro K hK hKD
  -- Enlarge the test compact set to a compact closed thickening still contained in `D`.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hD_open hKD
  obtain ⟨M, hM⟩ := hA hK.cthickening hKδ
  refine ⟨M / δ, ?_⟩
  intro g hg z hz
  -- Unpack one ambient analytic extension whose derivative restricts to `g`.
  rcases hg with ⟨f, hf, F, hF, hF_eq, hg_eq⟩
  have hF_eval : ∀ w (hw : w ∈ D), F w = f ⟨w, hw⟩ := by
    intro w hw
    exact congrArg (fun h : D → ℂ ↦ h ⟨w, hw⟩) hF_eq
  have hg_eval : ∀ w (hw : w ∈ D), deriv F w = g ⟨w, hw⟩ := by
    intro w hw
    exact congrArg (fun h : D → ℂ ↦ h ⟨w, hw⟩) hg_eq
  -- Apply the Cauchy derivative estimate on the radius-`δ` ball around `z`.
  have hball : Metric.closedBall z δ ⊆ D :=
    (Metric.closedBall_subset_cthickening hz δ).trans hKδ
  have hdiff : DiffContOnCl ℂ F (Metric.ball z δ) :=
    hF.differentiableOn.diffContOnCl_ball hball
  have hsphere : ∀ w ∈ Metric.sphere z δ, ‖F w‖ ≤ M := by
    intro w hw
    have hwD : w ∈ D := hball (Metric.sphere_subset_closedBall hw)
    have hwthick : w ∈ Metric.cthickening δ K :=
      Metric.closedBall_subset_cthickening hz δ (Metric.sphere_subset_closedBall hw)
    calc
      ‖F w‖ = ‖f ⟨w, hwD⟩‖ := by rw [hF_eval w hwD]
      _ = ‖f ⟨w, hKδ hwthick⟩‖ := by rfl
      _ ≤ M := hM f hf w hwthick
  have hderiv : ‖deriv F z‖ ≤ M / δ :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdiff hsphere
  -- Rewrite the ambient derivative back to the restricted function `g`.
  calc
    ‖g ⟨z, hKD hz⟩‖ = ‖deriv F z‖ := by rw [← hg_eval z (hKD hz)]
    _ ≤ M / δ := hderiv
