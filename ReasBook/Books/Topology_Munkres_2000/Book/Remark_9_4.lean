module

public import Topology_Munkres_2000.Book.Lemma_9_2
public import Topology_Munkres_2000.Book.Remark_9_4.ChoiceFunction

public section

open Set

universe u

/-- Remark 9.4. The collection of all nonempty subsets of a set admits a choice
function; no disjointness hypothesis is required. -/
theorem existsChoiceFunction_nonemptySubsetsOf {α : Type u} (A : Set α) :
    ∃ c : A.nonemptySubsetsOf → ⋃₀ A.nonemptySubsetsOf,
      A.nonemptySubsetsOf.IsChoiceFunction c := by
  exact existsChoiceFunction A.nonemptySubsetsOf fun B hB ↦ hB.2
