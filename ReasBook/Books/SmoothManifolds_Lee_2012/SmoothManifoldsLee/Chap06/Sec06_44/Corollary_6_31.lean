import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_44.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section SubmersionPreimages

universe uEN uEM uES uHN uHM uHS uN uM

open Manifold

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
variable {K : ModelWithCorners ℝ ES HS}
variable [ChartedSpace HS S] [IsManifold K ∞ S]

/-- Corollary 6.31: if `S ⊆ M` is an embedded submanifold and `F : N → M` is a smooth
submersion, then `F ⁻¹' S` carries an embedded submanifold structure in `N` with the same
codimension as `S`. -/
theorem smooth_submersion_preimage_has_embedded_submanifold_structure
    {F : N → M} (hF : IsSmoothSubmersion IN IM F)
    (hS : IsEmbeddedSubmanifold IM K S) :
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
          hT.codimension = hS.codimension := by
  let _ : IsEmbeddedSubmanifold IM K S := hS
  simpa using
    transverse_preimage_has_embedded_submanifold_structure
      (Manifold.IsSmoothSubmersion.isTransverseToSubmanifold hF)

end SubmersionPreimages
