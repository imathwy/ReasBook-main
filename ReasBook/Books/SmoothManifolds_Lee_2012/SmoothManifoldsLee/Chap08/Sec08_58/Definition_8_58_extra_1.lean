import Mathlib.Geometry.Manifold.Immersion
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Notation_5_35_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section

universe u𝕜 uE uH uM uE' uH'

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item uses
-- the local submanifold tangent-space notation `T[J; p]` from Chapter 5 and follows the Chapter 8
-- `VectorField.f_related` precedent for a pointwise property together with its global version.

variable (X : ∀ p : M, TangentSpace I p)

/-- Definition 8.58-extra-1 (1): if `S ⊆ M` is given a smooth immersed-submanifold structure,
then a vector field `X` on `M` is tangent to `S` at `p : S` when the ambient vector `X p`
lies in the tangent subspace `TₚS ⊆ TₚM`, represented in Lean as the range of the differential of
the subtype inclusion. -/
def IsTangentToSubmanifoldAt
    (J : ModelWithCorners 𝕜 E' H') (X : ∀ p : M, TangentSpace I p) (p : S) : Prop :=
  X p ∈ T[J; p]

/- Pointwise tangency to a submanifold is equivalent to being the image of some intrinsic tangent
vector under the differential of the inclusion `S ↪ M`. -/
omit [IsManifold I ∞ M] [IsManifold J ∞ S] in
theorem isTangentToSubmanifoldAt_iff_exists (p : S) :
    IsTangentToSubmanifoldAt J X p ↔
      ∃ v : TangentSpace J p, mfderiv J I (Subtype.val : S → M) p v = X p := by
  change X p ∈ (mfderiv J I (Subtype.val : S → M) p).range ↔
      ∃ v : TangentSpace J p, mfderiv J I (Subtype.val : S → M) p v = X p
  exact LinearMap.mem_range

/-- Definition 8.58-extra-1 (2): a vector field `X` on `M` is tangent to the immersed submanifold
`S` if it is tangent to `S` at every point of `S`. -/
def IsTangentToSubmanifold
    (S : Set M) [ChartedSpace H' S] (J : ModelWithCorners 𝕜 E' H')
    [IsManifold J ∞ S]
    (X : ∀ p : M, TangentSpace I p) : Prop :=
  ∀ p : S, IsTangentToSubmanifoldAt J X p

end VectorField

end
