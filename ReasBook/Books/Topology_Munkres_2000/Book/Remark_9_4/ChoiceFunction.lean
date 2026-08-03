module

public import Topology_Munkres_2000.Book.Definition_9_1.ChoiceFunction

@[expose] public section

open Set

universe u

namespace Set

/-- The collection of all nonempty subsets of `A`. -/
def nonemptySubsetsOf {α : Type u} (A : Set α) : Set (Set α) :=
  {B | B ⊆ A ∧ B.Nonempty}

/-- Membership in the collection of nonempty subsets of `A`. -/
theorem mem_nonemptySubsetsOf_iff {α : Type u} {A B : Set α} :
    B ∈ A.nonemptySubsetsOf ↔ B ⊆ A ∧ B.Nonempty := by
  rfl

/-- The collection of all nonempty subsets of a type. -/
def nonemptySubsets (X : Type u) : Set (Set X) :=
  {s | s.Nonempty}

/-- Membership in the collection of nonempty subsets of a type. -/
theorem mem_nonemptySubsets_iff {X : Type u} {s : Set X} :
    s ∈ nonemptySubsets X ↔ s.Nonempty := by
  rfl

/-- The nonempty subsets of a type are the nonempty subsets of its universal set. -/
theorem nonemptySubsets_eq_univ_nonemptySubsetsOf (X : Type u) :
    nonemptySubsets X = (Set.univ : Set X).nonemptySubsetsOf := by
  ext s
  simp [mem_nonemptySubsets_iff, mem_nonemptySubsetsOf_iff]

end Set

/-- A choice function for the collection of all nonempty subsets of `X`. -/
abbrev SetChoice (X : Type u) :=
  {c : Set.nonemptySubsets X → ⋃₀ Set.nonemptySubsets X //
    (Set.nonemptySubsets X).IsChoiceFunction c}

namespace SetChoice

/-- Build a choice function on all nonempty subsets from a selector and its membership proof. -/
def ofFun {X : Type u} (choose : (s : Set X) → s.Nonempty → X)
    (choose_mem : ∀ (s : Set X) (hs : s.Nonempty), choose s hs ∈ s) : SetChoice X :=
  ⟨fun (s : Set.nonemptySubsets X) ↦
      ⟨choose s s.property, mem_sUnion_of_mem (choose_mem s s.property) s.property⟩,
    Set.IsChoiceFunction.of_mem fun (s : Set.nonemptySubsets X) ↦ choose_mem s s.property⟩

/-- A choice function on nonempty subsets can be applied to a set and its nonemptiness proof. -/
instance instCoeFun {X : Type u} : CoeFun (SetChoice X)
    (fun _ ↦ (s : Set X) → s.Nonempty → X) where
  coe c s hs := (c.1 ⟨s, hs⟩).1

/-- A choice function on nonempty subsets selects an element of the given set. -/
theorem mem {X : Type u} (c : SetChoice X) (s : Set X) (hs : s.Nonempty) : c s hs ∈ s := by
  exact c.property.mem ⟨s, hs⟩

end SetChoice
