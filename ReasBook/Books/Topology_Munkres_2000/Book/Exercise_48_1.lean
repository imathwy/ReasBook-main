module

public import Mathlib.Topology.Baire.Lemmas

public section

open Set

universe u

/-- Exercise 48.1: In a countable cover of a nonempty Baire space, the closure of
one member has nonempty interior. -/
theorem exists_nonempty_interior_closure_of_iUnion_eq_univ
    {X : Type u} [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    (B : ℕ → Set X) (hB : ⋃ n, B n = Set.univ) :
    ∃ n, (interior (closure (B n))).Nonempty := by
  have hclosed : ∀ n, IsClosed (closure (B n)) := fun _ ↦ isClosed_closure
  have hcover : ⋃ n, closure (B n) = Set.univ := by
    apply top_unique
    exact hB.ge.trans (iUnion_mono fun _ ↦ subset_closure)
  exact nonempty_interior_of_iUnion_of_closed hclosed hcover
