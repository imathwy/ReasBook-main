import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X]

/-- A subset of a topological space is a finite union of locally closed subsets. -/
def IsFiniteUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ Z ∈ S, IsLocallyClosed Z) ∧ E = ⋃₀ S

/-- A locally closed subset is a finite union of locally closed subsets, with one piece. -/
theorem IsLocallyClosed.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed E := by
  refine ⟨{E}, Set.finite_singleton E, ?_, by simp⟩
  intro Z hZ
  exact hZ ▸ hE

namespace Topology

-- Proof sketch: constructible sets are generated from open retrocompact sets by finite unions and
-- complements. Open retrocompact sets are open, hence locally closed, and the class of finite
-- unions of locally closed sets is stable under the finite Boolean operations used in the
-- constructible induction.
/-- Any constructible subset is a finite union of locally closed subsets. -/
theorem IsConstructible.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsConstructible E) :
    IsFiniteUnionOfLocallyClosed E := sorry

end Topology

namespace IsFiniteUnionOfLocallyClosed

-- Proof sketch: choose a finite enumeration of the finite family of locally closed pieces.
/-- Unpack a finite union of locally closed subsets into finitely many locally closed pieces. -/
theorem exists_eq_iUnion {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    ∃ n : ℕ, ∃ S : Fin n → Set X, (∀ i, IsLocallyClosed (S i)) ∧ E = ⋃ i, S i := sorry

end IsFiniteUnionOfLocallyClosed

end
