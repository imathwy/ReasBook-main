module

public import Mathlib.SetTheory.Cardinal.SchroederBernstein

public section

/-- Exercise 7.6 (1): If `B ⊆ A` and there is an injection from `A` to `B`, then
`A` and `B` have the same cardinality. -/
theorem Set.existsBijection_of_subset_of_injective {α : Type u} {A B : Set α}
    (hBA : B ⊆ A) (f : A → B) (hf : Function.Injective f) :
    ∃ h : A → B, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf (Set.inclusion_injective hBA)

/- Exercise 7.6 (2), the Schröder–Bernstein theorem: If there are injections
`A → C` and `C → A`, then `A` and `C` have the same cardinality. -/
#check Function.Embedding.schroeder_bernstein
