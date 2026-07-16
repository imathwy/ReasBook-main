import Mathlib.AlgebraicGeometry.ResidueField
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall: `lean_leansearch` surfaced the canonical point map
`Scheme.fromSpecResidueField`; Chapter 29 already records “of finite type” for scheme morphisms by
the canonical owner `Scheme.Hom.FiniteType`. We therefore keep the source-facing point predicate
while reusing that morphism owner on `S.fromSpecResidueField s`. -/

/-- Definition 29.16.3: a point `s` of a scheme `S` is a finite type point if the canonical
morphism `Spec (κ(s)) ⟶ S` is of finite type; Chapter 29 records this on
`S.fromSpecResidueField s` via the canonical morphism owner `Scheme.Hom.FiniteType`. -/
class IsFiniteTypePoint {S : Scheme.{u}} (s : S) : Prop where
  finiteType_fromSpecResidueField :
    Scheme.Hom.FiniteType (S.fromSpecResidueField s)

/-- Unfold `IsFiniteTypePoint` into the canonical finite-type condition on the residue-field point
morphism. -/
theorem isFiniteTypePoint_iff {S : Scheme.{u}} (s : S) :
    IsFiniteTypePoint s ↔ Scheme.Hom.FiniteType (S.fromSpecResidueField s) := by
  constructor
  · intro h
    exact h.finiteType_fromSpecResidueField
  · intro h
    exact ⟨h⟩

/-- A finite type point gives the canonical finite type structure on `Spec (κ(s)) ⟶ S`. -/
instance instFiniteTypeFromIsFiniteTypePoint {S : Scheme.{u}} (s : S)
    [h : IsFiniteTypePoint s] : Scheme.Hom.FiniteType (S.fromSpecResidueField s) :=
  h.finiteType_fromSpecResidueField

/-- A finite type point gives the canonical locally finite type structure on
`Spec (κ(s)) ⟶ S`. -/
instance instLocallyOfFiniteTypeFromIsFiniteTypePoint {S : Scheme.{u}} (s : S)
    [h : IsFiniteTypePoint s] : LocallyOfFiniteType (S.fromSpecResidueField s) :=
  h.finiteType_fromSpecResidueField.toLocallyOfFiniteType

/-- The set of finite type points of a scheme. -/
def finiteTypePoints (S : Scheme.{u}) : Set S :=
  { s | IsFiniteTypePoint s }

/-- Membership in `finiteTypePoints S` is exactly the finite type point property. -/
theorem mem_finiteTypePoints_iff (S : Scheme.{u}) (s : S) :
    s ∈ finiteTypePoints S ↔ IsFiniteTypePoint s :=
  Iff.rfl

end AlgebraicGeometry
