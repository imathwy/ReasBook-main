import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Topology.Homotopy.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_44.Definition_6_44_extra_1

open scoped ContDiff Manifold

-- Semantic search note: `lean_leansearch` only surfaced the homotopy core
-- `ContinuousMap.HomotopicRel`, not a transversality-homotopy theorem, so the statement below
-- uses the local owner `IsTransverseToSubmanifold` together with the chapter's
-- `ContinuousMap.Homotopic` view on the underlying maps.

section TransversalityHomotopy

universe uEM uEN uEX uHM uHN uHX uM uN

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {EX : Type uEX} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HX : Type uHX} [TopologicalSpace HX]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {X : Set M}
variable {JX : ModelWithCorners ℝ EX HX}
variable [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold IM JX X]

/-- Theorem 6.36 (Transversality Homotopy Theorem): every smooth map `f : N → M` is homotopic to
a smooth map `g : N → M` that is transverse to the embedded submanifold `X ⊆ M`. -/
theorem exists_homotopic_to_smooth_map_transverse_to_submanifold
    (f : C^∞⟮IN, N; IM, M⟯) :
    ∃ g : C^∞⟮IN, N; IM, M⟯,
      (f : C(N, M)).Homotopic (g : C(N, M)) ∧
        IsTransverseToSubmanifold IM IN JX X g := sorry

end TransversalityHomotopy
