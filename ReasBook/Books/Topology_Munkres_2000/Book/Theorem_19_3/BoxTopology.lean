module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Constructions

universe u v w

public section

namespace Pi

/-- Coordinatewise inducing maps induce the box topology on their dependent product. -/
theorem induced_boxMap {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) (hf : ∀ i, Topology.IsInducing (f i)) :
    TopologicalSpace.induced (Pi.map f) (boxTopologicalSpace B) = boxTopologicalSpace A := by
  classical
  -- Pull back each ambient box coordinatewise and lift domain boxes using induction.
  have hpreimage : Set.preimage (Pi.map f) '' boxBasis B = boxBasis A := by
    apply Set.Subset.antisymm
    · rintro _ ⟨S, hS, rfl⟩
      obtain ⟨U, hU, rfl⟩ := (mem_boxBasis S).mp hS
      refine (mem_boxBasis _).mpr
        ⟨fun i ↦ f i ⁻¹' U i,
          fun i ↦ Continuous.isOpen_preimage (hf i).continuous (U i) (hU i), ?_⟩
      exact Set.preimage_pi Set.univ U f
    · rintro S hS
      obtain ⟨U, hU, rfl⟩ := (mem_boxBasis S).mp hS
      choose V hVopen hVpre using fun i ↦ (hf i).isOpen_iff.mp (hU i)
      refine ⟨Set.pi Set.univ V, (mem_boxBasis _).mpr ⟨V, hVopen, rfl⟩, ?_⟩
      calc
        Pi.map f ⁻¹' Set.pi Set.univ V = Set.pi Set.univ (fun i ↦ f i ⁻¹' V i) :=
          Set.preimage_pi Set.univ V f
        _ = Set.pi Set.univ U := congrArg (Set.pi Set.univ) (funext hVpre)
  rw [induced_generateFrom_eq, hpreimage]

end Pi
