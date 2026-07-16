import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Definition_8_54_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

-- Domain sampling pass:
-- * primary domain: rough and smooth vector fields acting on smooth scalar-valued functions;
-- * source-facing layer: Lee's test-function smoothness criterion for a rough vector field;
-- * core/canonical owners inspected: `VectorField.apply` for the pointwise action on smooth
--   functions, `VectorField.mpullback` for restriction to open subsets, and
--   `ContMDiffMap.restrictRingHom` for restricting smooth functions to an open subset;
-- * project bridges checked for the local-to-global step:
--   `smooth_on_chart_iff_smooth_components`,
--   `exists_smooth_bump_function_for`, and
--   `exists_supported_contMDiffMap_extension_of_isClosed`.
-- Primitive data is only the rough field `X : ∀ p, TangentSpace I p`; smoothness of the
-- action on test functions is derived via `VectorField.apply`, and the open-subset condition is
-- expressed using the canonical pullback owner `VectorField.mpullback`.
-- The chapter proof route is finite-dimensional and uses ambient bump/extension machinery, so the
-- source-facing criterion is stated under `[FiniteDimensional ℝ E] [T2Space M]
-- [SigmaCompactSpace M]` rather than for an arbitrary modeled manifold.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

open VectorField

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯

/-- Proposition 8.14 (1): on a finite-dimensional smooth manifold with the ambient bump/extension
hypotheses, a rough vector field on `M` is smooth exactly when it sends every global smooth
real-valued function on `M` to a smooth real-valued function on `M`. -/
theorem roughVectorField_smooth_iff_forall_smooth_apply_smooth
    (X : ∀ p : M, TangentSpace I p) :
    ContMDiff I I.tangent ∞ (T% X) ↔
      ∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f) := sorry

/-- Proposition 8.14 (2): the global test-function condition for a rough vector field is
equivalent to the corresponding local condition on every open subset, where the ambient vector
field is pulled back along the open-subset inclusion. The nontrivial global-to-local direction uses
the same finite-dimensional ambient bump/extension hypotheses as part (1). -/
theorem roughVectorField_forall_smooth_apply_smooth_iff_forall_open_forall_smooth_apply_smooth
    (X : ∀ p : M, TangentSpace I p) :
    (∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f)) ↔
      ∀ U : Opens M, ∀ f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯,
        ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply (mpullback I I (Subtype.val : U → M) X) f) := sorry

end
