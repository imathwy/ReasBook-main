import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

-- Semantic search note: the `lean_leansearch` tool requested by the statement policy was
-- unavailable in this session, so the statement surface below reuses the source-facing
-- transversality owners from `Definition_6_44_extra_1` together with the local
-- `IsEmbeddedSubmanifold` codimension API.

section TransversePreimage

universe uEN uEM uES uHN uHM uHS uN uM

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {S : Set M}
variable {JS : ModelWithCorners ℝ ES HS}
variable [ChartedSpace HS S] [IsManifold JS ∞ S] [hS : IsEmbeddedSubmanifold IM JS S]

/-- Theorem 6.30 (1): if `F : N → M` is a smooth map transverse to the embedded submanifold `S`,
then `F ⁻¹' S` admits an embedded submanifold structure in `N` whose codimension is the
codimension of `S` in `M`. -/
theorem transverse_preimage_has_embedded_submanifold_structure
    {F : N → M} (htrans : IsTransverseToSubmanifold IM IN JS S F) :
    let T : Set N := F ⁻¹' S
    let L :=
      modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension)))
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T,
      ∃ hs : IsManifold L ∞ T,
        let _ : ChartedSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T := cs
        let _ : IsManifold L ∞ T := hs
        ∃ hT : IsEmbeddedSubmanifold IN L T,
          hT.codimension = hS.codimension := sorry

end TransversePreimage

section TransverseIntersection

universe uEM uES uES' uHM uHS uHS' uM

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {ES' : Type uES'} [NormedAddCommGroup ES'] [NormedSpace ℝ ES']
  [FiniteDimensional ℝ ES']
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {HS' : Type uHS'} [TopologicalSpace HS']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {S : Set M} {S' : Set M}
variable {JS : ModelWithCorners ℝ ES HS} {JS' : ModelWithCorners ℝ ES' HS'}
variable [ChartedSpace HS S] [IsManifold JS ∞ S] [hS : IsEmbeddedSubmanifold IM JS S]
variable [ChartedSpace HS' S'] [IsManifold JS' ∞ S'] [hS' : IsEmbeddedSubmanifold IM JS' S']

/-- Theorem 6.30 (2): if the embedded submanifolds `S` and `S'` intersect transversely, then
`S ∩ S'` admits an embedded submanifold structure in `M` whose codimension is the sum of the
codimensions of `S` and `S'`. -/
theorem transverse_intersection_has_embedded_submanifold_structure
    (htrans : SubmanifoldsIntersectTransversely IM JS S JS' S') :
    let T : Set M := S ∩ S'
    let L :=
      modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension))))
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension)))) T,
      ∃ hs : IsManifold L ∞ T,
        let _ : ChartedSpace
            (EuclideanSpace ℝ
              (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension)))) T := cs
        let _ : IsManifold L ∞ T := hs
        ∃ hT : IsEmbeddedSubmanifold IM L T,
          hT.codimension = hS.codimension + hS'.codimension := sorry

end TransverseIntersection
