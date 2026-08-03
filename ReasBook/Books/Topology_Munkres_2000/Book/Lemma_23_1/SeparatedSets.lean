module

public import Mathlib.Topology.DerivedSet

public section

open Set

universe u

namespace Set

/-- Two subsets of a topological space are separated when neither meets the closure of the other. -/
def AreSeparated {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  Disjoint (closure A) B ∧ Disjoint A (closure B)

/-- Sets whose closures avoid the other set are separated. -/
theorem areSeparated_of_disjoint_closure {X : Type u} [TopologicalSpace X] {A B : Set X}
    (hAB : Disjoint (closure A) B) (hBA : Disjoint A (closure B)) : AreSeparated A B :=
  ⟨hAB, hBA⟩

/-- If `A` and `B` are separated, then the closure of `A` is disjoint from `B`. -/
theorem AreSeparated.disjoint_closure_left {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : AreSeparated A B) : Disjoint (closure A) B :=
  h.1

/-- If `A` and `B` are separated, then `A` is disjoint from the closure of `B`. -/
theorem AreSeparated.disjoint_closure_right {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : AreSeparated A B) : Disjoint A (closure B) :=
  h.2

/-- Separated sets are disjoint. -/
theorem AreSeparated.disjoint {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : AreSeparated A B) : Disjoint A B :=
  h.disjoint_closure_left.mono subset_closure Subset.rfl

/-- Two sets are separated exactly when they are disjoint and neither contains a limit point of
the other. -/
theorem areSeparated_iff_disjoint_derivedSet {X : Type u} [TopologicalSpace X] {A B : Set X} :
    AreSeparated A B ↔
      Disjoint A B ∧ Disjoint A (derivedSet B) ∧ Disjoint B (derivedSet A) := by
  rw [AreSeparated, closure_eq_self_union_derivedSet A, closure_eq_self_union_derivedSet B,
    disjoint_union_left, disjoint_union_right]
  constructor
  · rintro ⟨⟨hAB, hA'B⟩, -, hAB'⟩
    exact ⟨hAB, hAB', hA'B.symm⟩
  · rintro ⟨hAB, hAB', hBA'⟩
    exact ⟨⟨hAB, hBA'.symm⟩, hAB, hAB'⟩

/-- The relation of being separated is symmetric. -/
theorem AreSeparated.symm {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : AreSeparated A B) : AreSeparated B A :=
  areSeparated_of_disjoint_closure h.disjoint_closure_right.symm
    h.disjoint_closure_left.symm

end Set
