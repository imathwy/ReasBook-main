module

public import Topology_Munkres_2000.Book.Remark_9_4.ChoiceFunction
public import Mathlib.Order.RelClasses

@[expose] public section

open Set

universe u

namespace Tower

/-- The ambient set of strict predecessors of `x` in `T` under `r`. -/
def predecessors {X : Type u} (T : Set X) (r : T → T → Prop) (x : T) : Set X :=
  {z | ∃ y : T, r y x ∧ z = y}

/-- Membership in the ambient strict-predecessor section. -/
theorem mem_predecessors_iff {X : Type u} {T : Set X} {r : T → T → Prop}
    {x : T} {z : X} :
    z ∈ predecessors T r x ↔ ∃ y : T, r y x ∧ z = y := by
  rfl

/-- The complement in `X` of the strict-predecessor section of `x`. -/
def remaining {X : Type u} (T : Set X) (r : T → T → Prop) (x : T) : Set X :=
  Set.univ \ predecessors T r x

/-- Membership in the complement of a strict-predecessor section. -/
theorem mem_remaining_iff {X : Type u} {T : Set X} {r : T → T → Prop}
    {x : T} {z : X} :
    z ∈ remaining T r x ↔ z ∉ predecessors T r x := by
  simp [remaining]

/-- The complement of the strict-predecessor section of an element of a well-order is nonempty. -/
theorem remaining_nonempty {X : Type u} {T : Set X} {r : T → T → Prop}
    (h : IsWellOrder T r) (x : T) : (remaining T r x).Nonempty := by
  refine ⟨x, ?_⟩
  rw [mem_remaining_iff]
  rintro ⟨y, hyx, hxy⟩
  have : y = x := SetCoe.ext hxy.symm
  subst y
  exact (WellFounded.irrefl h.toIsWellFounded.wf).irrefl x hyx

end Tower

/-- A tower for an explicit choice function consists of a well-ordered subset whose
elements are chosen from the complements of their strict-predecessor sections. -/
structure Tower (X : Type u) (c : SetChoice X) where
  carrier : Set X
  rel : carrier → carrier → Prop
  wellOrder : IsWellOrder carrier rel
  choose_remaining : ∀ x : carrier,
    x.1 = c (Tower.remaining carrier rel x) (Tower.remaining_nonempty wellOrder x)

namespace Tower

/-- A tower coerces to its carrier type. -/
instance instCoeSort {X : Type u} {c : SetChoice X} : CoeSort (Tower X c) (Type u) where
  coe T := T.carrier

/-- The strict order on a tower is its stored relation. -/
instance instLT {X : Type u} {c : SetChoice X} (T : Tower X c) : LT T where
  lt := T.rel

/-- The stored strict order of a tower is a well-order. -/
instance instIsWellOrder {X : Type u} {c : SetChoice X} (T : Tower X c) :
    IsWellOrder T (· < ·) := T.wellOrder

/-- The strict section of a tower at `x`, viewed as a subset of the ambient type. -/
def strictSection {X : Type u} {c : SetChoice X} (T : Tower X c) (x : T) : Set X :=
  predecessors T.carrier T.rel x

/-- Membership in a tower section is strict precedence inside the tower. -/
theorem mem_strictSection_iff {X : Type u} {c : SetChoice X} {T : Tower X c}
    {x : T} {z : X} :
    z ∈ T.strictSection x ↔ ∃ y : T, y < x ∧ z = y := by
  rfl

/-- An element of a tower is selected from the complement of its section. -/
theorem choice_eq {X : Type u} {c : SetChoice X} (T : Tower X c) (x : T) :
    x.1 = c (Set.univ \ T.strictSection x) (remaining_nonempty T.wellOrder x) := by
  exact T.choose_remaining x

/-- The defining well-order and choice conditions of a tower. -/
theorem spec {X : Type u} {c : SetChoice X} (T : Tower X c) :
    IsWellOrder T (· < ·) ∧
      ∀ x : T,
        x.1 = c (Set.univ \ T.strictSection x)
          (remaining_nonempty T.wellOrder x) := by
  exact ⟨T.wellOrder, T.choice_eq⟩

end Tower
