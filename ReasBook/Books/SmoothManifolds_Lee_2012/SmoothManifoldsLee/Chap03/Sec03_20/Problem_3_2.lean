import Mathlib.Geometry.Manifold.IsManifold.Basic

open scoped Manifold

noncomputable section

section

universe u𝕜 uE uH uM uE' uH' uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']
variable [IsManifold I' 1 M']

-- Semantic recall note: `lean_leansearch` surfaced the canonical product-tangent-bundle API
-- around `contMDiff_equivTangentBundleProd`; local Chapter 3 precedent uses
-- `equivTangentBundleProd`, and this item keeps the source-facing fiberwise linear equivalence
-- coming from the definitional product identification.

/-- Problem 3-2: the tangent space to the product manifold `M × M'` at `p` is canonically the
product `TangentSpace I p.1 × TangentSpace I' p.2`. -/
def tangentSpaceProdEquiv (p : M × M') :
    TangentSpace (I.prod I') p ≃ₗ[𝕜] TangentSpace I p.1 × TangentSpace I' p.2 :=
  (LinearEquiv.refl 𝕜 (E × E') :
    TangentSpace (I.prod I') p ≃ₗ[𝕜] TangentSpace I p.1 × TangentSpace I' p.2)

/-- The product tangent-space equivalence is definitionally
`LinearEquiv.refl` on the model fiber. -/
theorem tangentSpaceProdEquiv_def (p : M × M') :
    ((tangentSpaceProdEquiv p) :
      TangentSpace (I.prod I') p ≃ₗ[𝕜] TangentSpace I p.1 × TangentSpace I' p.2) =
      (LinearEquiv.refl 𝕜 (E × E') :
        TangentSpace (I.prod I') p ≃ₗ[𝕜] TangentSpace I p.1 × TangentSpace I' p.2) := by
  -- The definition already chooses the identity equivalence on the model fiber.
  rfl

/-- The canonical product tangent-space equivalence is the identity on the model fiber. -/
@[simp] theorem tangentSpaceProdEquiv_apply (p : M × M')
    (v : TangentSpace (I.prod I') p) :
    tangentSpaceProdEquiv p v = v := by
  -- Reduce to the explicit `LinearEquiv.refl` description and evaluate it on `v`.
  rfl

end

end
