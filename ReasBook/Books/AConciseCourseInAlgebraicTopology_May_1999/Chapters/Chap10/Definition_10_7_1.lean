import Mathlib.Data.Set.Basic

universe u

/-- Definition 10.7.1: a triad on `X` consists of two distinguished subspaces `A` and `B`
of `X`, represented in Lean as subsets of `X`; unlike a chain `B ⊆ A ⊆ X`, no containment
relation between them is part of the data of a triad. -/
structure Triad (X : Type u) where
  /-- The distinguished subspace `A` of the triad. -/
  subspaceA : Set X
  /-- The distinguished subspace `B` of the triad. -/
  subspaceB : Set X
deriving Inhabited

attribute [ext] Triad

namespace Triad

variable {X : Type u}

/-- The intersection `A ∩ B` of the distinguished subspaces of a triad `(X; A, B)`. -/
abbrev intersection (T : Triad X) : Set X :=
  T.subspaceA ∩ T.subspaceB

/-- The union `A ∪ B` of the distinguished subspaces of a triad `(X; A, B)`. -/
abbrev union (T : Triad X) : Set X :=
  T.subspaceA ∪ T.subspaceB

/-- Membership in `T.intersection` is exactly simultaneous membership in the two distinguished
subspaces of the triad. -/
@[simp]
theorem mem_intersection {T : Triad X} {x : X} :
    x ∈ T.intersection ↔ x ∈ T.subspaceA ∧ x ∈ T.subspaceB :=
  Iff.rfl

/-- Membership in `T.union` is exactly membership in one of the two distinguished subspaces of
the triad. -/
@[simp]
theorem mem_union {T : Triad X} {x : X} :
    x ∈ T.union ↔ x ∈ T.subspaceA ∨ x ∈ T.subspaceB :=
  Iff.rfl

/-- The intersection `C = A ∩ B`, regarded as a subspace of `A`. -/
abbrev leftIntersectionSubspace (T : Triad X) : Set T.subspaceA :=
  { a | a.1 ∈ T.subspaceB }

/-- The intersection `C = A ∩ B`, regarded as a subspace of `B`. -/
abbrev rightIntersectionSubspace (T : Triad X) : Set T.subspaceB :=
  { b | b.1 ∈ T.subspaceA }

/-- Helper for Definition 10.7.1: the copy of `A ∩ B` inside `A` is the preimage of `B`
under the subtype map `A → X`. -/
@[simp] theorem leftIntersectionSubspace_eq_preimage (T : Triad X) :
    T.leftIntersectionSubspace = Subtype.val ⁻¹' T.subspaceB := by
  -- Both sides reduce to the same subtype-membership predicate on points of `A`.
  rfl

/-- Helper for Definition 10.7.1: the copy of `A ∩ B` inside `B` is the preimage of `A`
under the subtype map `B → X`. -/
@[simp] theorem rightIntersectionSubspace_eq_preimage (T : Triad X) :
    T.rightIntersectionSubspace = Subtype.val ⁻¹' T.subspaceA := by
  -- Both sides reduce to the same subtype-membership predicate on points of `B`.
  rfl

/-- A point of `A` lies in the copy of `C = A ∩ B` inside `A` exactly when its ambient point lies
in `B`. -/
@[simp] theorem mem_leftIntersectionSubspace {T : Triad X} {a : T.subspaceA} :
    a ∈ T.leftIntersectionSubspace ↔ (a : X) ∈ T.subspaceB :=
  Iff.rfl

/-- Helper for Definition 10.7.1: a point of `A` has ambient point in `A ∩ B` exactly when it lies
in the copy of the intersection inside `A`. -/
@[simp] theorem coe_mem_intersection_iff_mem_leftIntersectionSubspace {T : Triad X}
    {a : T.subspaceA} :
    (a : X) ∈ T.intersection ↔ a ∈ T.leftIntersectionSubspace := by
  -- Rewrite both predicates into ambient membership conditions in `A` and `B`.
  rw [mem_intersection, mem_leftIntersectionSubspace]
  constructor
  · -- From ambient intersection membership, only the `B`-condition remains to check.
    intro ha
    exact ha.2
  · -- Conversely, the subtype point already carries its `A`-membership.
    intro ha
    exact ⟨a.2, ha⟩

/-- A point of `B` lies in the copy of `C = A ∩ B` inside `B` exactly when its ambient point lies
in `A`. -/
@[simp] theorem mem_rightIntersectionSubspace {T : Triad X} {b : T.subspaceB} :
    b ∈ T.rightIntersectionSubspace ↔ (b : X) ∈ T.subspaceA :=
  Iff.rfl

/-- Helper for Definition 10.7.1: a point of `B` has ambient point in `A ∩ B` exactly when it lies
in the copy of the intersection inside `B`. -/
@[simp] theorem coe_mem_intersection_iff_mem_rightIntersectionSubspace {T : Triad X}
    {b : T.subspaceB} :
    (b : X) ∈ T.intersection ↔ b ∈ T.rightIntersectionSubspace := by
  -- Rewrite both predicates into ambient membership conditions in `A` and `B`.
  rw [mem_intersection, mem_rightIntersectionSubspace]
  constructor
  · -- From ambient intersection membership, only the `A`-condition remains to check.
    intro hb
    exact hb.1
  · -- Conversely, the subtype point already carries its `B`-membership.
    intro hb
    exact ⟨hb, b.2⟩

/-- Helper for Definition 10.7.1: an actual point of the copy of `A ∩ B` inside `A`
coerces to an ambient point of `A ∩ B`. -/
@[simp] theorem coe_mem_intersection_of_mem_leftIntersectionSubspace {T : Triad X}
    (a : T.leftIntersectionSubspace) :
    ((a : T.subspaceA) : X) ∈ T.intersection := by
  -- Regard `a` as a point of `A` and use the earlier bridge characterization.
  exact
    (coe_mem_intersection_iff_mem_leftIntersectionSubspace (a := (a : T.subspaceA))).2 a.2

/-- Helper for Definition 10.7.1: an actual point of the copy of `A ∩ B` inside `B`
coerces to an ambient point of `A ∩ B`. -/
@[simp] theorem coe_mem_intersection_of_mem_rightIntersectionSubspace {T : Triad X}
    (b : T.rightIntersectionSubspace) :
    ((b : T.subspaceB) : X) ∈ T.intersection := by
  -- Regard `b` as a point of `B` and use the symmetric bridge characterization.
  exact
    (coe_mem_intersection_iff_mem_rightIntersectionSubspace (b := (b : T.subspaceB))).2 b.2

/-- Helper for Definition 10.7.1: the left-hand copy of `A ∩ B` maps canonically into the
ambient intersection by forgetting only subtype layers. -/
def leftIntersectionInclusion (T : Triad X) : T.leftIntersectionSubspace → T.intersection :=
  fun a => ⟨((a : T.subspaceA) : X), coe_mem_intersection_of_mem_leftIntersectionSubspace a⟩

/-- Helper for Definition 10.7.1: the right-hand copy of `A ∩ B` maps canonically into the
ambient intersection by forgetting only subtype layers. -/
def rightIntersectionInclusion (T : Triad X) : T.rightIntersectionSubspace → T.intersection :=
  fun b => ⟨((b : T.subspaceB) : X), coe_mem_intersection_of_mem_rightIntersectionSubspace b⟩

/-- Applying the left inclusion does not change the ambient point, only the subtype wrapper. -/
@[simp] theorem coe_leftIntersectionInclusion (T : Triad X) (a : T.leftIntersectionSubspace) :
    ((T.leftIntersectionInclusion a : T.intersection) : X) = ((a : T.subspaceA) : X) := by
  -- Both sides are definitionally the same ambient point of `X`.
  rfl

/-- Helper for Definition 10.7.1: the left inclusion is injective because it only forgets
subtype layers and does not change the ambient point. -/
theorem leftIntersectionInclusion_injective (T : Triad X) :
    Function.Injective T.leftIntersectionInclusion := by
  -- Equality after forgetting subtype layers forces equality of the underlying ambient points.
  intro a b h
  -- Each nested subtype is determined by its underlying ambient point.
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : T.intersection => (z : X)) h

/-- Applying the right inclusion does not change the ambient point, only the subtype wrapper. -/
@[simp] theorem coe_rightIntersectionInclusion (T : Triad X) (b : T.rightIntersectionSubspace) :
    ((T.rightIntersectionInclusion b : T.intersection) : X) = ((b : T.subspaceB) : X) := by
  -- Both sides are definitionally the same ambient point of `X`.
  rfl

/-- Helper for Definition 10.7.1: the right inclusion is injective because it only forgets
subtype layers and does not change the ambient point. -/
theorem rightIntersectionInclusion_injective (T : Triad X) :
    Function.Injective T.rightIntersectionInclusion := by
  -- Equality after forgetting subtype layers forces equality of the underlying ambient points.
  intro a b h
  -- Each nested subtype is determined by its underlying ambient point.
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : T.intersection => (z : X)) h

end Triad
