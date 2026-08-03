module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk

public section

namespace DiskAntipodalQuotient

open ClosedUnitDisk

/-- Two disk points are related when they are equal, or are antipodes on the boundary. -/
def rel (x y : B²) : Prop :=
  y = x ∨ (IsBoundary x ∧ y = -x)

/-- The disk relation has the explicit equality-or-boundary-antipode description. -/
theorem rel_iff (x y : B²) :
    rel x y ↔ y = x ∨ (IsBoundary x ∧ y = -x) := by
  rfl

/-- The boundary-antipodal relation on the closed disk is an equivalence relation. -/
theorem relEquivalence : Equivalence rel where
  refl x := Or.inl rfl
  symm := by
    rintro x y (rfl | ⟨hx, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨isBoundary_neg x |>.2 hx, by simp⟩
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, rfl⟩
    · exact hyz
    · rcases hyz with rfl | ⟨hy, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩
      · exact Or.inl (by simp)

/-- The setoid identifying antipodal pairs precisely on the boundary of the disk. -/
def setoid : Setoid B² where
  r := rel
  iseqv := relEquivalence

/-- The disk setoid relates exactly equal points and antipodal boundary points. -/
theorem setoid_rel_iff (x y : B²) :
    setoid x y ↔ y = x ∨ (IsBoundary x ∧ y = -x) := by
  rfl

/-- The quotient of `B²` identifying each boundary point with its antipode. -/
abbrev Space : Type :=
  Quotient setoid

/-- The canonical map from the closed disk to its boundary-antipodal quotient. -/
def quotientMap : B² → Space :=
  Quotient.mk setoid

/-- Two disk points have equal quotient images exactly when the setoid relates them. -/
theorem quotientMap_eq_iff (x y : B²) :
    quotientMap x = quotientMap y ↔ y = x ∨ (IsBoundary x ∧ y = -x) := by
  change Quotient.mk setoid x = Quotient.mk setoid y ↔ _
  rw [Quotient.eq]
  rfl

/-- The quotient map identifies a boundary point with its antipode. -/
theorem quotientMap_neg (x : B²) (hx : IsBoundary x) :
    quotientMap (-x) = quotientMap x := by
  exact ((quotientMap_eq_iff x (-x)).2 (Or.inr ⟨hx, rfl⟩)).symm

/-- The canonical map gives `Space` its quotient topology. -/
theorem quotientMap_isQuotientMap :
    Topology.IsQuotientMap quotientMap := by
  exact isQuotientMap_quotient_mk'

end DiskAntipodalQuotient
