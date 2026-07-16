import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Definition_4_26_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note:
-- `lean_leansearch` was unavailable in this session, so local inspection was used.

open scoped Manifold ContDiff

universe u𝕜 uE uE' uH uH' uM uM'

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
variable {π : M → M'}

/- Every smooth covering map is already a smooth local diffeomorphism via
the defining field `IsSmoothCoveringMap.isLocalDiffeomorph`. -/
#check Manifold.IsSmoothCoveringMap.isLocalDiffeomorph

namespace Manifold.IsSmoothCoveringMap

/-- Proposition 4.33 (1): every smooth covering map between smooth manifolds is a smooth
submersion. -/
-- Proof sketch: for each point of the source, use the local inverse branch coming from the local
-- diffeomorphism field of the smooth covering map; this gives the smooth local section required by
-- `Manifold.IsSmoothSubmersion`.
theorem isSmoothSubmersion [IsManifold I ∞ M] [IsManifold I' ∞ M']
    (hπ : Manifold.IsSmoothCoveringMap I I' π) : Manifold.IsSmoothSubmersion I I' π := sorry

/-- Proposition 4.33 (2): every smooth covering map is an open map. -/
-- Proof sketch: forget to the local diffeomorphism field and apply
-- `IsLocalDiffeomorph.isOpenMap`.
theorem isOpenMap (hπ : Manifold.IsSmoothCoveringMap I I' π) : IsOpenMap π := sorry

/-- Proposition 4.33 (3): every smooth covering map is a quotient map. -/
-- Proof sketch: use the covering-map field together with the surjectivity field and apply
-- `IsCoveringMap.isQuotientMap`.
theorem isQuotientMap (hπ : Manifold.IsSmoothCoveringMap I I' π) : Topology.IsQuotientMap π := sorry

/-- Proposition 4.33 (4): an injective smooth covering map is a diffeomorphism. -/
-- Proof sketch: combine injectivity with the surjectivity field to get bijectivity, then apply
-- `IsLocalDiffeomorph.diffeomorphOfBijective` to the local diffeomorphism field.
noncomputable def diffeomorphOfInjective (hπ : Manifold.IsSmoothCoveringMap I I' π)
    (h_inj : Function.Injective π) : M ≃ₘ⟮I, I'⟯ M' :=
  hπ.isLocalDiffeomorph.diffeomorphOfBijective ⟨h_inj, hπ.surjective⟩

/-- The diffeomorphism produced by `diffeomorphOfInjective` has underlying map `π`. -/
theorem diffeomorphOfInjective_apply (hπ : Manifold.IsSmoothCoveringMap I I' π)
    (h_inj : Function.Injective π) (x : M) :
    diffeomorphOfInjective hπ h_inj x = π x := sorry

end Manifold.IsSmoothCoveringMap

namespace IsCoveringMap

/-- Proposition 4.33 (5): a surjective topological covering map is a smooth covering map exactly
when it is a local diffeomorphism. -/
-- Proof sketch: one direction is the defining local-diffeomorphism field of
-- `IsSmoothCoveringMap`; the converse packages the assumed covering-map and surjectivity data with
-- the local diffeomorphism hypothesis.
theorem isSmoothCoveringMap_iff_isLocalDiffeomorph (hπ : IsCoveringMap π)
    (h_surj : Function.Surjective π) :
    Manifold.IsSmoothCoveringMap I I' π ↔ IsLocalDiffeomorph I I' ∞ π := sorry

end IsCoveringMap

end
