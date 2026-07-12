import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `QuasiSeparatedSpace`,
-- `Scheme.IsSeparated`, `QuasiCompact`, `QuasiSeparated`, `IsSeparated`, and the affine
-- quasi-separated/separated instances. The Stacks tag evidence is consistent for tag `0816`.

/-- The four basic scheme separation properties used in this file. -/
inductive SchemeSeparationProperty : Type
  /-- The scheme is quasi-separated. -/
  | quasiSeparated
  /-- The scheme is separated. -/
  | separated
  /-- The scheme is quasi-compact and quasi-separated. -/
  | quasiCompactQuasiSeparated
  /-- The scheme is quasi-compact and separated. -/
  | quasiCompactSeparated

namespace SchemeSeparationProperty

/-- The absolute scheme property associated to a basic separation property. -/
def Holds (P : SchemeSeparationProperty) (X : Scheme.{u}) : Prop :=
  match P with
  | quasiSeparated => QuasiSeparatedSpace X.carrier
  | separated => X.IsSeparated
  | quasiCompactQuasiSeparated => CompactSpace X.carrier ∧ QuasiSeparatedSpace X.carrier
  | quasiCompactSeparated => CompactSpace X.carrier ∧ X.IsSeparated

/-- The morphism property associated to a basic separation property. -/
def HomHolds (P : SchemeSeparationProperty) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  match P with
  | quasiSeparated => QuasiSeparated f
  | separated => IsSeparated f
  | quasiCompactQuasiSeparated => QuasiCompact f ∧ QuasiSeparated f
  | quasiCompactSeparated => QuasiCompact f ∧ IsSeparated f

/-- Remark 26.21.18 (1): any affine scheme has each of the four listed separation
properties. -/
@[stacks 0816]
theorem holds_of_isAffine (P : SchemeSeparationProperty) (X : Scheme.{u}) [IsAffine X] :
    P.Holds X := sorry

/-- Remark 26.21.18 (2): over a target with one of the four listed separation properties, a
morphism has that property if and only if its source has it. -/
@[stacks 0816]
theorem homHolds_iff_holds_source_of_holds_target (P : SchemeSeparationProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : P.Holds Y) :
    P.HomHolds f ↔ P.Holds X := sorry

/-- Remark 26.21.18 (3): the fibre product of schemes with one of the four listed separation
properties again has that property. -/
@[stacks 0816]
theorem holds_pullback_of_holds (P : SchemeSeparationProperty) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : P.Holds X) (hY : P.Holds Y) (hZ : P.Holds Z) :
    P.Holds (pullback f g) := sorry

end SchemeSeparationProperty

end AlgebraicGeometry
