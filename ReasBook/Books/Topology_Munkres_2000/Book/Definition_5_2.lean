module

public import Mathlib.Data.Set.Operations

public section

/- Definition 5.2: The canonical indexing function `Set.rangeFactorization A`
is surjective onto the collection `Set.range A`. It is injective exactly when
the family `A` is injective, so repeated values `A α = A β` are permitted. -/
#check Set.rangeFactorization_surjective
#check Set.rangeFactorization_injective

/-- A family can have a surjective indexing function without distinct indices
denoting distinct sets. -/
theorem exists_surjective_indexing_not_injective :
    ∃ A : Bool → Set Unit,
      Function.Surjective (Set.rangeFactorization A) ∧
        ¬ Function.Injective (Set.rangeFactorization A) := by
  refine ⟨fun _ ↦ Set.univ, Set.rangeFactorization_surjective, ?_⟩
  intro h
  have htf : true = false := h rfl
  contradiction
