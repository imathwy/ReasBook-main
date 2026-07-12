import Mathlib
import Mathlib.CategoryTheory.Subobject.Lattice

-- Auxiliary Chapter 12 subquotient constructions used for later `E_∞`-style statements.

open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section QuotientMap

variable [HasZeroMorphisms C] [HasCokernels C]

-- The inclusion `X ≤ Y` identifies `X.arrow` with `Subobject.ofLE X Y hXY ≫ Y.arrow`, so the
-- cokernel projection of `Y.arrow` annihilates `X.arrow`.
private theorem subobjectQuotientMapCondition {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    X.arrow ≫ cokernel.π Y.arrow = 0 := sorry

/-- The canonical morphism `A / X ⟶ A / Y` induced by an inclusion `X ≤ Y` of subobjects. -/
def subobjectQuotientMap {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    cokernel X.arrow ⟶ cokernel Y.arrow :=
  cokernel.desc X.arrow (cokernel.π Y.arrow) (subobjectQuotientMapCondition hXY)

end QuotientMap

section Subquotients

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

/-- The subquotient `Y / X`, realized as the kernel subobject of the canonical map
`A / X ⟶ A / Y`. -/
def subobjectSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) : C :=
  kernelSubobject (subobjectQuotientMap hXY)

/-- The canonical subobject of `A / X` whose underlying object is the subquotient
`subobjectSubquotient hXY = Y / X`. -/
abbrev subobjectSubquotientSubobject {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject (cokernel X.arrow) :=
  kernelSubobject (subobjectQuotientMap hXY)

end Subquotients

section IsSubquotient

variable [Abelian C]

/-- An object `X` is a subquotient of `Y` if it is isomorphic to `Y₂ / Y₁` for some subobjects
`Y₁ ≤ Y₂ ≤ Y`. -/
def IsSubquotient (X Y : C) : Prop :=
  ∃ (Y₁ Y₂ : Subobject Y) (hY₁Y₂ : Y₁ ≤ Y₂), Nonempty (X ≅ subobjectSubquotient hY₁Y₂)

namespace IsSubquotient

/-- Transport `IsSubquotient` along an isomorphism on the left object. -/
theorem of_iso {X X' Y : C} (e : X ≅ X') :
    IsSubquotient X' Y → IsSubquotient X Y := by
  rintro ⟨Y₁, Y₂, hY₁Y₂, ⟨i⟩⟩
  exact ⟨Y₁, Y₂, hY₁Y₂, ⟨e ≪≫ i⟩⟩

end IsSubquotient

-- Proof sketch: inside the ambient quotient `A / W`, the subquotients `X / W` and `Y / W`
-- define nested subobjects of `Z / W`; the quotient of these two stages recovers `Y / X`.
/-- If `W ≤ X ≤ Y ≤ Z` are subobjects of `A`, then the intermediate quotient `Y / X` is a
subquotient of the larger quotient `Z / W`. -/
theorem subobjectSubquotient_isSubquotient_of_le_chain {A : C} {W X Y Z : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    IsSubquotient (subobjectSubquotient hXY)
      (subobjectSubquotient (hWX.trans <| hXY.trans hYZ)) := by
  sorry

end IsSubquotient

end CategoryTheory
