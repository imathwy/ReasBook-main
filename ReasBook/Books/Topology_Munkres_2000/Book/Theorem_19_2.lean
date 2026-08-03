module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Bases

universe u v

public section

namespace Pi

/-- Theorem 19.2 (1): coordinatewise basis elements form a basis of full coordinate
boxes for the box topology. -/
theorem isTopologicalBasis_box {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] {B : (i : ι) → Set (Set (X i))}
    (hB : ∀ i, TopologicalSpace.IsTopologicalBasis (B i)) :
    (boxTopologicalSpace X).IsTopologicalBasis
      {S | ∃ U : (i : ι) → Set (X i),
        (∀ i, U i ∈ B i) ∧ S = Set.pi Set.univ U} := by
  classical
  letI : TopologicalSpace ((i : ι) → X i) := boxTopologicalSpace X
  -- First identify the generating open boxes as a basis of the box topology.
  have hOpenBoxes :
      (boxTopologicalSpace X).IsTopologicalBasis (boxBasis X) := by
    have hGenerated :
        boxTopologicalSpace X = TopologicalSpace.generateFrom (boxBasis X) := rfl
    have hWithUniv := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter hGenerated
      (fun _ hs _ ht ↦ inter_mem_boxBasis hs ht)
    simpa only [Set.insert_eq_of_mem (univ_mem_boxBasis X)] using hWithUniv
  -- Refine every open box coordinatewise by the supplied coordinate bases.
  refine hOpenBoxes.isTopologicalBasis_of_exists_subset ?_ ?_
  · rintro S ⟨U, hU, rfl⟩
    exact isOpen_box U fun i ↦ (hB i).isOpen (hU i)
  · rintro S hS x hx
    obtain ⟨U, hU, rfl⟩ := (mem_boxBasis S).mp hS
    have hRefinement :
        ∀ i, ∃ V ∈ B i, x i ∈ V ∧ V ⊆ U i := fun i ↦
      (hB i).exists_subset_of_mem_open (hx i (Set.mem_univ i)) (hU i)
    choose V hVB hxV hVU using hRefinement
    -- The coordinate choices assemble into a basis box inside the original box.
    refine ⟨Set.pi Set.univ V, ⟨V, hVB, rfl⟩, ?_, ?_⟩
    · intro i hi
      exact hxV i
    · exact Set.pi_mono fun i _ ↦ hVU i

end Pi

/- Theorem 19.2 (2): coordinatewise basis elements with finite support form a basis
for the product topology. -/
#check isTopologicalBasis_pi
