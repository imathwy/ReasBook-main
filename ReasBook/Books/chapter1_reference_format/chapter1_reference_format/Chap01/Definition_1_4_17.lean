import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped BigOperators

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V]

/- Definition 1.4.17: for a family `Vᵢ` of subspaces of a `K`-vector space `V`, their sum is the
lattice supremum `⨆ i, Vᵢ i`, whose elements are precisely finite sums of vectors drawn from the
given subspaces; when the index type is finite, the statement `V = ⊕ i, Vᵢ i` is the canonical
mathlib proposition `DirectSum.IsInternal Vᵢ`. -/
#check (fun Vᵢ : ι → Submodule K V ↦ (⨆ i, Vᵢ i : Submodule K V))

section

variable [DecidableEq ι]

/- For a finite family of subspaces, the internal direct-sum condition is the canonical
mathlib proposition `DirectSum.IsInternal Vᵢ`. -/
#check (DirectSum.IsInternal : (ι → Submodule K V) → Prop)

end

/-- The supremum of a family of subspaces consists exactly of the values of the canonical map from
their external direct sum, so its elements are precisely finite sums of vectors drawn from the
given subspaces. -/
-- Proof sketch: combine `DirectSum.range_coeLinearMap` with `LinearMap.mem_range`; the carrier of
-- `DirectSum ι (fun i ↦ Vᵢ i)` already enforces finite support, which matches the textbook's
-- finite-sum description.
theorem mem_iSup_iff_exists_directSum [DecidableEq ι] (Vᵢ : ι → Submodule K V) (x : V) :
    x ∈ ⨆ i, Vᵢ i ↔
      ∃ l : DirectSum ι (fun i ↦ Vᵢ i), DirectSum.coeLinearMap Vᵢ l = x := by
  rw [← DirectSum.range_coeLinearMap]
  exact LinearMap.mem_range

/-- The canonical owner proposition `DirectSum.IsInternal Vᵢ` says exactly that the recomposition
map from the external direct sum onto `V` has a unique preimage over each vector. -/
theorem directSum_isInternal_iff_existsUnique
    [DecidableEq ι] (Vᵢ : ι → Submodule K V) :
    DirectSum.IsInternal Vᵢ ↔
      ∀ x : V, ∃! l : DirectSum ι (fun i ↦ Vᵢ i), DirectSum.coeLinearMap Vᵢ l = x := by
  change Function.Bijective (DirectSum.coeLinearMap Vᵢ) ↔ _
  constructor
  · intro h x
    exact h.existsUnique x
  · intro h
    exact (Function.bijective_iff_existsUnique _).2 h

/-- A finite family of subspaces is an internal direct sum exactly when every vector admits a
unique decomposition as a sum of components lying in the given subspaces. -/
-- Proof sketch: over a finite index type, identify the external direct sum with the space of
-- tuples `xs : ∀ i, Vᵢ i`; then translate the bijectivity in `DirectSum.IsInternal Vᵢ` into
-- existence and uniqueness of a coordinate tuple summing to a given vector.
theorem directSum_isInternal_iff_existsUnique_decomposition [Fintype ι] [DecidableEq ι]
    (Vᵢ : ι → Submodule K V) :
    DirectSum.IsInternal Vᵢ ↔
      ∀ x : V, ∃! xs : ∀ i, Vᵢ i, x = ∑ i, ((xs i : Vᵢ i) : V) := by
  let e := DirectSum.linearEquivFunOnFintype K ι (fun i ↦ Vᵢ i)
  have hsum (xs : ∀ i, Vᵢ i) :
      DirectSum.coeLinearMap Vᵢ (e.symm xs) = ∑ i, ((xs i : Vᵢ i) : V) := by
    classical
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum]
    exact (DFinsupp.sum_eq_sum_fintype (e.symm xs) (fun i ↦ rfl) :
      DFinsupp.sum (e.symm xs) (fun i x ↦ ((x : Vᵢ i) : V)) = _)
  constructor
  · intro h x
    let p : (∀ i, Vᵢ i) → Prop := fun xs ↦ DirectSum.coeLinearMap Vᵢ (e.symm xs) = x
    have hp : (∃! xs : ∀ i, Vᵢ i, p xs) ↔ ∃! l : DirectSum ι (fun i ↦ Vᵢ i), p (e l) :=
      e.bijective.existsUnique_iff
    have h' := (directSum_isInternal_iff_existsUnique Vᵢ).mp h x
    have h'_e : ∃! l : DirectSum ι (fun i ↦ Vᵢ i), p (e l) := by
      simpa [p, e] using h'
    have h'' : ∃! xs : ∀ i, Vᵢ i, p xs := hp.2 h'_e
    simpa [p, hsum, eq_comm] using h''
  · intro h
    refine (directSum_isInternal_iff_existsUnique Vᵢ).2 ?_
    intro x
    let p : (∀ i, Vᵢ i) → Prop := fun xs ↦ DirectSum.coeLinearMap Vᵢ (e.symm xs) = x
    have hp : (∃! xs : ∀ i, Vᵢ i, p xs) ↔ ∃! l : DirectSum ι (fun i ↦ Vᵢ i), p (e l) :=
      e.bijective.existsUnique_iff
    have h' : ∃! xs : ∀ i, Vᵢ i, p xs := by
      simpa [p, hsum, eq_comm] using h x
    have h'' : ∃! l : DirectSum ι (fun i ↦ Vᵢ i), p (e l) := hp.1 h'
    simpa [p, e] using h''
