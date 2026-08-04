module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_22_2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.Constructions

public section

namespace DiskBoundaryQuotient

open ClosedUnitDisk

/-- Two disk points are related when they are equal or both lie on the boundary circle. -/
def rel (x y : ClosedUnitDisk) : Prop :=
  x = y ∨ (IsBoundary x ∧ IsBoundary y)

/-- The boundary-collapse relation has its explicit equality-or-boundary description. -/
theorem rel_iff (x y : ClosedUnitDisk) :
    rel x y ↔ x = y ∨ (IsBoundary x ∧ IsBoundary y) := by
  rfl

/-- Collapsing the entire boundary circle defines an equivalence relation on the disk. -/
theorem relEquivalence : Equivalence rel where
  refl x := Or.inl rfl
  symm := by
    rintro x y (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hy, hx⟩
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, hy⟩
    · exact hyz
    · rcases hyz with rfl | ⟨hy', hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

/-- The setoid that identifies all boundary points and leaves interior points distinct. -/
def setoid : Setoid ClosedUnitDisk where
  r := rel
  iseqv := relEquivalence

/-- The disk setoid relates exactly equal points and pairs of boundary points. -/
theorem setoid_rel_iff (x y : ClosedUnitDisk) :
    setoid x y ↔ x = y ∨ (IsBoundary x ∧ IsBoundary y) := by
  rfl

/-- The quotient of the closed disk obtained by collapsing its boundary circle to one point. -/
abbrev Space : Type :=
  Quotient setoid

/-- The canonical projection from the closed disk to its boundary-collapse quotient. -/
def quotientMap : ClosedUnitDisk → Space :=
  Quotient.mk setoid

/-- Two disk points have equal quotient images exactly when they are equal or both lie on the
boundary circle. -/
theorem quotientMap_eq_iff (x y : ClosedUnitDisk) :
    quotientMap x = quotientMap y ↔ x = y ∨ (IsBoundary x ∧ IsBoundary y) := by
  change Quotient.mk setoid x = Quotient.mk setoid y ↔ _
  rw [Quotient.eq]
  rfl

/-- A subset of the disk is saturated exactly when containing one boundary point forces it to
contain every boundary point. -/
theorem isSaturated_iff (U : Set ClosedUnitDisk) :
    Set.IsSaturated quotientMap U ↔
      ∀ ⦃x y : ClosedUnitDisk⦄, x ∈ U → IsBoundary x → IsBoundary y → y ∈ U := by
  rw [Set.isSaturated_iff_mem_of_eq]
  constructor
  · intro h x y hx hbx hby
    exact h hx ((quotientMap_eq_iff y x).2 (Or.inr ⟨hby, hbx⟩))
  · intro h x y hx hxy
    rcases (quotientMap_eq_iff y x).1 hxy with rfl | ⟨hby, hbx⟩
    · exact hx
    · exact h hx hbx hby

/-- The canonical projection gives `Space` its quotient topology. -/
theorem quotientMap_isQuotientMap :
    Topology.IsQuotientMap quotientMap := by
  exact isQuotientMap_quotient_mk'

end DiskBoundaryQuotient


end
