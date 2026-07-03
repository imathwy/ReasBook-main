import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_28 (from Chap04/Sec04_25) -/
open scoped Topology ContDiff

namespace Manifold

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {π : M → N}

/-- In the finite-dimensional setting, a smooth submersion is a smooth map whose manifold
derivative is surjective at every point. -/
structure IsSmoothSubmersion (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (π : M → N) : Prop where
  /-- A smooth submersion is smooth as a map of manifolds. -/
  contMDiff : ContMDiff I J ∞ π
  /-- The manifold derivative of a smooth submersion is surjective at every point. -/
  surjective_mfderiv (x : M) : Function.Surjective (mfderiv I J π x)

namespace IsSmoothSubmersion

variable {π : M → N}

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] in
/-- A smooth submersion is continuous. -/
theorem continuous (hπ : IsSmoothSubmersion I J π) : Continuous π :=
  hπ.contMDiff.continuous

section RealFiniteDimensional

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {π : M → N}

/-- A smooth submersion canonically determines a topological submersion. -/
def toTopologicalSubmersion (hπ : IsSmoothSubmersion I J π) :
    Topology.IsTopologicalSubmersion π where
  continuous := hπ.continuous
  local_section x := by
    have hsections :
        ∀ x : M,
          ∃ U : TopologicalSpace.Opens N, ∃ hxU : π x ∈ U, ∃ σ : U → M,
            IsSmoothLocalSection I J π U σ ∧ σ ⟨π x, hxU⟩ = x :=
      (smooth_submersion_iff_exists_smooth_local_section_through_every_point hπ.contMDiff).mp
        hπ.surjective_mfderiv
    rcases hsections x with ⟨U, hxU, σ, hσ, hx⟩
    refine ⟨U, hxU, ⟨σ, hσ.1.continuous⟩, hσ.apply_eq, ?_⟩
    simpa using hx

/-- Proposition 4.28: A smooth submersion is an open map. -/
theorem isOpenMap (hπ : IsSmoothSubmersion I J π) : IsOpenMap π :=
  hπ.toTopologicalSubmersion.isOpenMap

/-- A surjective smooth submersion is a quotient map. -/
theorem isQuotientMap (hπ : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) :
    Topology.IsQuotientMap π :=
  hπ.toTopologicalSubmersion.isQuotientMap h_surj

end RealFiniteDimensional

end IsSmoothSubmersion

end Manifold
