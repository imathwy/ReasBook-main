import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff

section

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {F : M → N}

namespace Manifold

/-- Definition 4.22-extra-1: a smooth local diffeomorphism is exactly a `C^∞` local
diffeomorphism in mathlib's manifold API. This keeps the source-facing notion aligned with the
canonical owner predicate. -/
abbrev IsSmoothLocalDiffeomorphism
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H') (F : M → N) : Prop :=
  IsLocalDiffeomorph I J ∞ F

/-- Helper for Definition 4.22-extra-1: the source-facing smooth local-diffeomorphism condition is
pointwise because the owner predicate `IsLocalDiffeomorph` is pointwise. -/
theorem isSmoothLocalDiffeomorphism_iff_forall_isLocalDiffeomorphAt :
    IsSmoothLocalDiffeomorphism I J F ↔ ∀ x : M, IsLocalDiffeomorphAt I J ∞ F x := by
  -- Unfold the source-facing alias so the owner theorem can express the per-point condition.
  simpa [IsSmoothLocalDiffeomorphism] using
    (isLocalDiffeomorph_iff (I := I) (J := J) (n := (∞ : WithTop ℕ∞)) (f := F))

end Manifold

end
