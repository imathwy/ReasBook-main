module

public import Topology_Munkres_2000.Book.Exercise_36_4.PointFinite
import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.OpenCover

public section

open Set TopologicalSpace

universe u v

namespace TopologicalSpace.IsOpenCover

/-- A point-finite open cover of a normal space has an open shrinking whose
closures refine the original cover. -/
theorem exists_shrinking {ι : Type u} {X : Type v} [TopologicalSpace X] [NormalSpace X]
    {U : ι → Opens X} (hU : IsOpenCover U)
    (hUfinite : PointFinite (fun i ↦ (U i : Set X))) :
    ∃ V : ι → Opens X, IsOpenCover V ∧ ∀ i, closure (V i : Set X) ⊆ U i := by
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset (fun i ↦ (U i).2)
      (fun x ↦ hUfinite.finite x) hU.iSup_set_eq_univ
  exact ⟨fun i ↦ ⟨V i, hVopen i⟩, IsOpenCover.of_sets hVopen hVcover, hVclosure⟩

end TopologicalSpace.IsOpenCover
