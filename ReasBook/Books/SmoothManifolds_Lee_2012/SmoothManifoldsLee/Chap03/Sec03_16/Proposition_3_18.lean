import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open scoped Manifold ContDiff

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]

-- Domain sampling pass: this item lies in the smooth-manifold tangent-bundle API. The inspected
-- core/canonical owners are mathlib's `TangentBundle`, `ModelWithCorners.tangent`, and the
-- generic bundle-projection theorem `Bundle.contMDiff_proj`, together with this chapter's earlier
-- tangent-bundle recall in `Definition_3_16_extra_1` and the tangent-map recall in
-- `Proposition_3_21`. Primitive data is the canonical tangent bundle with its induced topology
-- and manifold structure; smoothness of the projection is derived API from `Bundle.contMDiff_proj`
-- and should not be repackaged as a separate local owner.

#synth TopologicalSpace (TangentBundle I M)
#synth ChartedSpace (ModelProd H E) (TangentBundle I M)
#synth IsManifold I.tangent (∞ : ℕ∞ω) (TangentBundle I M)

/- Proposition 3.18: the canonical tangent bundle `TangentBundle I M` carries its natural
topology and smooth manifold structure modeled on `I.tangent`, with chart model `ModelProd H E`;
in the textbook's real `n`-manifold case this is the familiar `2n`-dimensional tangent-bundle
model. Smoothness of the bundle projection `π : TM → M` is the generic theorem
`Bundle.contMDiff_proj` specialized to `TangentSpace I`. -/
#check (Bundle.contMDiff_proj (TangentSpace I) :
  ContMDiff I.tangent I (∞ : ℕ∞ω) (TotalSpace.proj : TangentBundle I M → M))

end
