import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
The core owner theorem is the lattice-theoretic characterization `isCompl_iff`.
-/
recall isCompl_iff {α : Type u} [PartialOrder α] [BoundedOrder α] {a b : α} :
    IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b

section

variable {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Proposition 1.4.18: two subspaces `V₁` and `V₂` of `V` are complementary
exactly when their sum is the whole space and their intersection is trivial. -/
theorem subspace_isCompl_iff_sup_eq_top_and_inf_eq_bot (V₁ V₂ : Subspace K V) :
    IsCompl V₁ V₂ ↔ V₁ ⊔ V₂ = ⊤ ∧ V₁ ⊓ V₂ = ⊥ := by
  -- Rewrite complementarity into disjointness and codisjointness in the lattice of subspaces.
  -- Then identify those lattice conditions with trivial intersection and whole-space sum.
  rw [isCompl_iff, disjoint_iff, codisjoint_iff, and_comm]

end
