module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.ShrinkingLemma

public section

universe u v

namespace TopologicalSpace.IsOpenCover

/-- Lemma 41.6. Every indexed open cover of a paracompact Hausdorff space admits a
locally finite indexed open cover whose pointwise closures lie in the original sets. -/
theorem exists_locallyFinite_closure_subset {ι : Type u} {X : Type v}
    [TopologicalSpace X] [ParacompactSpace X] [T2Space X] {U : ι → Opens X}
    (hU : IsOpenCover U) :
    ∃ V : ι → Opens X,
      LocallyFinite (fun i ↦ (V i : Set X)) ∧ IsOpenCover V ∧
        ∀ i, closure (V i : Set X) ⊆ U i := by
  -- First replace the original cover by a locally finite precise refinement.
  obtain ⟨W, hWopen, hWcover, hWlocallyFinite, hWsubsetU⟩ :=
    precise_refinement (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen)
      hU.iSup_set_eq_univ
  have hWpointFinite : ∀ x, {i | x ∈ W i}.Finite := hWlocallyFinite.point_finite
  -- Normality shrinks the point-finite cover while controlling every closure.
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset hWopen hWpointFinite hWcover
  have hVsubsetW : ∀ i, V i ⊆ W i :=
    fun i ↦ subset_closure.trans (hVclosure i)
  have hVlocallyFinite : LocallyFinite V := hWlocallyFinite.subset hVsubsetW
  let V' : ι → Opens X := fun i ↦ ⟨V i, hVopen i⟩
  -- Bundle the shrunken sets as opens and compose the two refinement inclusions.
  refine ⟨V', hVlocallyFinite, IsOpenCover.of_sets hVopen hVcover, ?_⟩
  intro i
  exact (hVclosure i).trans (hWsubsetU i)

end TopologicalSpace.IsOpenCover
