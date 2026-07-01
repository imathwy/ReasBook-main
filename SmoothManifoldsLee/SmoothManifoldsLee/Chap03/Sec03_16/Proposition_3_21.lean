import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' (∞ : ℕ∞ω) N]
variable {F : M → N}

/- Proposition 3.21: if `F : M → N` is smooth, then its global differential
`tangentMap I I' F : TangentBundle I M → TangentBundle I' N` is smooth. This is the `∞`-smooth
specialization of mathlib's canonical owner theorem `ContMDiff.contMDiff_tangentMap`. -/
#check
  (fun hF : ContMDiff I I' (∞ : ℕ∞ω) F ↦ hF.contMDiff_tangentMap le_rfl :
    ContMDiff I I' (∞ : ℕ∞ω) F →
      ContMDiff I.tangent I'.tangent (∞ : ℕ∞ω) (tangentMap I I' F))
