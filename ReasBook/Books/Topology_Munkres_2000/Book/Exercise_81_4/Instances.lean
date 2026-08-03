module

public import Topology_Munkres_2000.Book.Definition_81_6.ProperlyDiscontinuous

public section

open Filter Set
open scoped Topology

universe u v

namespace Finite

/-- A finite free continuous group action on a Hausdorff space is properly discontinuous
in the neighborhood-disjointness sense. -/
instance toProperlyDiscontinuousMulAction {G : Type u} {X : Type v} [Group G] [Finite G]
    [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    [IsCancelSMul G X] : ProperlyDiscontinuousMulAction G X := by
  refine { exists_nhds_disjoint_image := ?_ }
  intro x
  -- Freeness lets Hausdorff separation distinguish every nonidentity translate of `x` from `x`.
  have hmove : ∀ γ : {g : G // g ≠ 1}, γ.1 • x ≠ x := by
    intro γ hfixed
    exact γ.2 (IsCancelSMul.eq_one_of_smul hfixed)
  choose u v hu hv huv using fun γ : {g : G // g ≠ 1} ↦ t2_separation_nhds (hmove γ)
  let U : Set X := ⋂ γ : {g : G // g ≠ 1}, (γ.1 • ·) ⁻¹' u γ ∩ v γ
  refine ⟨U, ?_, ?_⟩
  · -- Finiteness makes the intersection of all pulled-back separating neighborhoods a neighborhood.
    unfold U
    refine iInter_mem.mpr fun γ ↦ ?_
    exact inter_mem ((continuous_const_smul γ.1).continuousAt (hu γ)) (hv γ)
  · intro g hg
    let γ : {h : G // h ≠ 1} := ⟨g, hg⟩
    -- The component indexed by `g` controls both the image of `U` and `U` itself.
    have hcomponent : U ⊆ (g • ·) ⁻¹' u γ ∩ v γ := by
      unfold U
      exact iInter_subset _ γ
    have himage : (g • ·) '' U ⊆ u γ := by
      calc
        (g • ·) '' U ⊆ (g • ·) '' ((g • ·) ⁻¹' u γ ∩ v γ) := image_mono hcomponent
        _ ⊆ (g • ·) '' ((g • ·) ⁻¹' u γ) := image_mono inter_subset_left
        _ ⊆ u γ := image_preimage_subset _ _
    have hsource : U ⊆ v γ := hcomponent.trans inter_subset_right
    exact (huv γ).mono himage hsource

end Finite
