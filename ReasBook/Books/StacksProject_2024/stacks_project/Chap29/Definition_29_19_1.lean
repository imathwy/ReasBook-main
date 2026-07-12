import Mathlib
import StacksProject_2024.Chap28.Definition_28_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced the canonical scheme-morphism owner `LocallyOfFiniteType` together
-- with the local-Noetherian transfer theorem `LocallyOfFiniteType.isLocallyNoetherian`. Local
-- Chapter 28/29 precedent already fixes `Scheme.regularLocus` as the scheme-side owner of the
-- regular locus and `UniversallyCatenary` as the nearby “every locally finite type scheme over the
-- base has property P” pattern.

/-- Definition 29.19.1: a locally Noetherian scheme `X` is `J-2` if for every morphism
`Y ⟶ X` which is locally of finite type, the regular locus `Reg(Y)` is open in `Y`. -/
@[stacks 07R3]
class IsJ2 (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  /-- For every scheme locally of finite type over `X`, the regular locus is open. -/
  regularLocus_isOpen_of_locallyOfFiniteType {Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f] :
    IsOpen (Reg(Y))

variable (X : Scheme.{u})

/-- For a locally Noetherian scheme, the `J-2` condition is exactly openness of the regular locus
for every scheme locally of finite type over it. -/
@[stacks 07R3]
theorem isJ2_iff_forall_regularLocus_isOpen_of_locallyOfFiniteType [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X) [LocallyOfFiniteType f],
        IsOpen (Reg(Y)) :=
  ⟨fun h _ f ↦
      h.regularLocus_isOpen_of_locallyOfFiniteType f,
    fun h ↦
      { toIsLocallyNoetherian := inferInstance
        regularLocus_isOpen_of_locallyOfFiniteType := fun f ↦ h f }⟩

/-- On a `J-2` scheme, every locally finite type `X`-scheme has open regular locus. -/
@[stacks 07R3]
theorem regularLocus_isOpen_of_locallyOfFiniteType
    (X : Scheme.{u}) [IsJ2 X] {Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f] :
    IsOpen (Reg(Y)) :=
  IsJ2.regularLocus_isOpen_of_locallyOfFiniteType f

/-- A `J-2` scheme has open regular locus. -/
@[stacks 07R3]
theorem regularLocus_isOpen (X : Scheme.{u}) [IsJ2 X] :
    IsOpen (Reg(X)) := by
  let hX : IsJ2 X := inferInstance
  simpa using hX.regularLocus_isOpen_of_locallyOfFiniteType (CategoryTheory.CategoryStruct.id X)

end AlgebraicGeometry.Scheme
