import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_44.Definition_6_44_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_44.Definition_6_44_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Set Manifold

universe u𝕜 uE uE' uH uH' uN uM uS uES uHS

section StableMapClasses

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]

-- Domain sampling pass: the chapter-level owner for smooth parameter families is
-- `IsSmoothFamily`, and the map classes used below come from the upstream owners
-- `Manifold.IsImmersion`, `Manifold.IsSmoothSubmersion`, `IsLocalDiffeomorph`,
-- `IsTransverseToSubmanifold`, and `≃ₘ⟮I, J⟯`.

/-- A class `C` of smooth maps `N → M` is stable when membership persists locally in any smooth
family `F : S → N → M` after it holds at one parameter value. -/
def IsStableMapClass
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H') (C : Set (N → M)) : Prop :=
  ∀ {S : Type uS} {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
      {HS : Type uHS} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
      {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S] {F : S → N → M},
    IsSmoothFamily J IS I F →
    ∀ {s0 : S}, F s0 ∈ C →
      ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, F s ∈ C

end StableMapClasses

section Problem616Local

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]

/-- Problem 6-16 (1): if `N` is compact, then the class of immersions `N → M` is stable. -/
theorem immersions_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsImmersion I J ∞ f} := sorry

/-- Problem 6-16 (2): if `N` is compact, then the class of smooth submersions `N → M` is
stable. -/
theorem submersions_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsSmoothSubmersion I J f} := sorry

/-- Problem 6-16 (5): if `N` is compact, then the class of local diffeomorphisms `N → M` is
stable. -/
theorem local_diffeomorphisms_are_stable_under_smooth_families_from_compact_source
    [CompactSpace N] :
    IsStableMapClass I J {f : N → M | IsLocalDiffeomorph I J ∞ f} := sorry

/-- Problem 6-16 (6): for compact `N`, a properly embedded submanifold `X ⊆ M` has a
stable class of transverse maps `N → M`. -/
theorem transverse_maps_are_stable_under_smooth_families_from_compact_source [CompactSpace N]
    {X : Set M} {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type*} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X]
    [IsEmbeddedSubmanifold J JX X] (hXproper : X.IsProperlyEmbedded) :
    IsStableMapClass I J
      {f : N → M | IsTransverseToSubmanifold J I JX X f} := sorry

end Problem616Local

section Problem616Embedding

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]

/-- Problem 6-16 (3): if `N` is compact, then the class of smooth embeddings `N → M` is stable. -/
theorem embeddings_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsSmoothEmbedding I J ∞ f} := sorry

/-- Problem 6-16 (4): if `N` is compact, then the class of diffeomorphisms `N → M` is stable. -/
theorem diffeomorphisms_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J (range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :=
  sorry

end Problem616Embedding
