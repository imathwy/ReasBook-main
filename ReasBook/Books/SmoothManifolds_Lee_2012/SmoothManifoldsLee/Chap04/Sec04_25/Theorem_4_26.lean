import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv` from
-- `Definition_4_21_extra_1` and `Manifold.IsSmoothSubmersion` from `Proposition_4_28`.

open scoped ContDiff Manifold

namespace Manifold

section

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}

/-- A smooth local section of `π : M → N` over an open subset `U ⊆ N` is a smooth map
`σ : U → M` whose composite with `π` is the identity on `U`. -/
def IsSmoothLocalSection (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (π : M → N) (U : TopologicalSpace.Opens N) (σ : U → M) : Prop :=
  ContMDiff J I ∞ σ ∧ ∀ x : U, π (σ x) = x

namespace IsSmoothLocalSection

-- Proof sketch: evaluate the defining right-inverse equation in
-- `Manifold.IsSmoothLocalSection` at the chosen point of the open subset.
/-- A smooth local section satisfies the section equation at each point of its domain. -/
theorem apply_eq {π : M → N} {U : TopologicalSpace.Opens N} {σ : U → M}
    (hσ : IsSmoothLocalSection I J π U σ) (x : U) :
    π (σ x) = x := sorry

end IsSmoothLocalSection

end

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Proof sketch: for the forward implication, apply the rank theorem in local coordinates to write
-- `π` near each `p` as a coordinate projection and take the coordinate inclusion as a smooth local
-- section through `p`. For the reverse implication, differentiate the identity `π ∘ σ = id` at
-- `q = π p`; then `mfderiv I J π p ∘ mfderiv J I σ q = ContinuousLinearMap.id ℝ _`, so
-- `mfderiv I J π p` is surjective.
/-- Theorem 4.26 (Local Section Theorem): a smooth map between finite-dimensional smooth manifolds
is a smooth submersion exactly when each point of the source lies on a smooth local section
through its image. -/
theorem smooth_submersion_iff_exists_smooth_local_section_through_every_point {π : M → N}
    (hπ : ContMDiff I J ∞ π) :
    (∀ p : M, Function.Surjective (mfderiv I J π p)) ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens N, ∃ hq : π p ∈ U, ∃ σ : U → M,
        IsSmoothLocalSection I J π U σ ∧ σ ⟨π p, hq⟩ = p := sorry

end

end Manifold
