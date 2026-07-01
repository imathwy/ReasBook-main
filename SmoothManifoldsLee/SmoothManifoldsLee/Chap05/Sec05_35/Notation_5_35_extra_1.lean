import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH'

section TangentSpaceToSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

namespace Manifold

/-- Notation 5.35-extra-1: once the smooth manifold structure on the subtype `S` is fixed, its
tangent space at `p`, viewed inside the ambient tangent space, is the range of the differential of
the subtype inclusion `S ↪ M`. -/
noncomputable abbrev submanifoldTangentSpace
    (J : ModelWithCorners 𝕜 E' H') (p : S) : Submodule 𝕜 (TangentSpace I (p : M)) :=
  (mfderiv J I (Subtype.val : S → M) p).range

scoped notation "T[" J "; " p "]" => submanifoldTangentSpace J p

end Manifold

end TangentSpaceToSubmanifold
