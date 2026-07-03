import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open scoped Manifold ContDiff

universe u v

variable {n : ℕ}
variable {H : Type u} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]

-- `lean_leansearch` was unavailable in this session, so this file uses the local Section 3.16
-- tangent-bundle precedent together with the canonical mathlib tangent-bundle API.

#synth TopologicalSpace (TangentBundle I M)
#synth ChartedSpace (ModelProd H (EuclideanSpace ℝ (Fin n))) (TangentBundle I M)
#synth IsManifold I.tangent (∞ : ℕ∞ω) (TangentBundle I M)

/-- Proposition 3.18: mathlib's canonical tangent bundle `TangentBundle I M` carries its natural
topology and smooth manifold structure modeled on `I.tangent`, which corresponds to the textbook's
`2n`-dimensional smooth structure when `M` is an `n`-manifold, and its projection to `M` is
smooth. -/
theorem tangentBundle_contMDiff_proj :
    ContMDiff I.tangent I (∞ : ℕ∞ω) (TotalSpace.proj : TangentBundle I M → M) := sorry
