module

public import Topology_Munkres_2000.Book.Example_12_4
public import Mathlib.Topology.WithTopology

public section

open Set

universe u

/-- A type synonym equipped with the topology whose open sets are empty or have countable
complement. -/
abbrev CocountableTopology (X : Type u) : Type u :=
  WithTopology X (TopologicalSpace.cocountable X)

namespace CocountableTopology

/-- The identity equivalence between `X` and `CocountableTopology X`. -/
def of {X : Type u} : X ≃ CocountableTopology X :=
  (WithTopology.equiv X (TopologicalSpace.cocountable X)).symm

/-- Helper for Example 12.4: an injective image is countable exactly when its source set is. -/
lemma countable_image_iff_of_injective {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {s : Set α} : (f '' s).Countable ↔ s.Countable := by
  -- Countability moves forward under every map and backward under injectivity.
  constructor
  · exact Set.countable_of_injective_of_countable_image hf.injOn
  · intro hs
    exact hs.image f

/-- A set in `CocountableTopology X` is open exactly when it is empty or has countable
complement. -/
theorem isOpen_iff' {X : Type u} {s : Set (CocountableTopology X)} :
    IsOpen s ↔ s = ∅ ∨ sᶜ.Countable := by
  -- Reduce to the defining topology and transport both clauses through the identity wrapper.
  refine (WithTopology.isOpen_iff (t := TopologicalSpace.cocountable X)).trans ?_
  refine TopologicalSpace.cocountable_isOpen.trans ?_
  simp_rw [← Set.preimage_compl,
    WithTopology.preimage_toTopology, Set.image_eq_empty,
    countable_image_iff_of_injective (WithTopology.ofTopology_injective _)]

/-- A set in `CocountableTopology X` is open exactly when every nonempty such set has countable
complement. -/
theorem isOpen_iff {X : Type u} {s : Set (CocountableTopology X)} :
    IsOpen s ↔ s.Nonempty → sᶜ.Countable := by
  -- Rewrite the empty-set alternative as the implication required by the textbook formulation.
  simp only [isOpen_iff', nonempty_iff_ne_empty, or_iff_not_imp_left]

end CocountableTopology
