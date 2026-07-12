import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- Representation choice: mathlib exposes rational maps through `Scheme.functionField`,
-- `Scheme.RationalMap.fromFunctionField`, and `Scheme.RationalMap.equivFunctionFieldOver`.

/-- Definition 29.49.11 (1): two irreducible schemes are birational if their function fields are
isomorphic. -/
def Birational (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic X.functionField Y.functionField

/-- Birationality of irreducible schemes is symmetric. -/
theorem Birational.symm {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y] :
    Birational X Y → Birational Y X
  | ⟨e⟩ => ⟨e.symm⟩

/-- Birationality of irreducible schemes is symmetric. -/
theorem birational_comm (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] :
    Birational X Y ↔ Birational Y X :=
  ⟨Birational.symm, Birational.symm⟩

/-- The generic-point `S`-scheme attached to an irreducible `S`-scheme. -/
noncomputable abbrev genericPointOver
    (S X : Scheme) [X.Over S] [IrreducibleSpace X] : Over S :=
  Over.mk (X.fromSpecStalk (genericPoint X) ≫ (X ↘ S))

/-- Definition 29.49.11 (2): two irreducible `S`-schemes are `S`-birational if their generic-point
schemes are isomorphic over `S`. -/
def BirationalOver (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic (genericPointOver S X) (genericPointOver S Y)

/-- `S`-birationality of irreducible `S`-schemes is symmetric. -/
theorem BirationalOver.symm {S X Y : Scheme} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y → BirationalOver S Y X
  | ⟨e⟩ => ⟨e.symm⟩

/-- `S`-birationality is symmetric. -/
theorem birationalOver_comm (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y ↔ BirationalOver S Y X :=
  ⟨BirationalOver.symm, BirationalOver.symm⟩

end AlgebraicGeometry
