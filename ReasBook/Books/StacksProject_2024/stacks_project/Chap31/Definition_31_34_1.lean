import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

open CategoryTheory
open Scheme.IdealSheafData

-- Semantic recall note: the owner choices below were checked against nearby Chapter 31 ideal-sheaf
-- files and mathlib's `Scheme.IdealSheafData.comap` / `subschemeι` API.

section

variable {X X' : Scheme.{u}} {I : X.IdealSheafData}

/-- A morphism `f : X' ⟶ X` is a blowup of `X` in the closed subscheme defined by the ideal sheaf
`I` if the inverse-image center is an effective Cartier divisor and `f` is terminal among
morphisms to `X` with that property. -/
class IsBlowup (f : X' ⟶ X) (I : X.IdealSheafData) : Prop where
  /-- The inverse-image center on the blowup is an effective Cartier divisor. -/
  toIsEffectiveCartierDivisor [MonoidalCategory (RingedSpace.Modules X'.toRingedSpace)] :
    (I.comap f).IsEffectiveCartierDivisor
  /-- The blowup is terminal among morphisms to `X` whose inverse-image center is an effective
  Cartier divisor. -/
  lift_unique {Y : Scheme.{u}} [MonoidalCategory (RingedSpace.Modules Y.toRingedSpace)]
      (g : Y ⟶ X) (_ : (I.comap g).IsEffectiveCartierDivisor) :
    ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

instance {f : X' ⟶ X} [MonoidalCategory (RingedSpace.Modules X'.toRingedSpace)] [h : IsBlowup f I] :
    (I.comap f).IsEffectiveCartierDivisor :=
  h.toIsEffectiveCartierDivisor

/-- The blowup universal property produces a unique factorization through the blowup for every
map to `X` whose inverse-image center is an effective Cartier divisor. -/
theorem IsBlowup.existsUnique_lift {f : X' ⟶ X} [h : IsBlowup f I]
    {Y : Scheme.{u}} [MonoidalCategory (RingedSpace.Modules Y.toRingedSpace)] (g : Y ⟶ X)
    (hg : (I.comap g).IsEffectiveCartierDivisor) :
    ExistsUnique fun h' : Y ⟶ X' ↦ h' ≫ f = g :=
  h.lift_unique g hg

/-- A center for a `U`-admissible blowup is a finitely presented closed subscheme of `X` disjoint
from the open subscheme `U`, together with a blowup structure on the morphism. -/
class IsAdmissibleBlowupCenter (U : X.Opens) (f : X' ⟶ X) (I : X.IdealSheafData) : Prop
    extends IsBlowup f I where
  /-- The closed subscheme defining the center is locally of finite presentation over `X`. -/
  locallyOfFinitePresentation_subschemeι :
    LocallyOfFinitePresentation I.subschemeι
  /-- The center is disjoint from the open subscheme `U`. -/
  disjoint_support :
    Disjoint (I.support : Set X) U

/-- An admissible center is locally of finite presentation over the base scheme. -/
theorem IsAdmissibleBlowupCenter.locallyOfFinitePresentation {U : X.Opens} {f : X' ⟶ X}
    [h : IsAdmissibleBlowupCenter U f I] :
    LocallyOfFinitePresentation I.subschemeι :=
  h.locallyOfFinitePresentation_subschemeι

/-- An admissible center exhibits the given morphism as a blowup in that center. -/
theorem IsAdmissibleBlowupCenter.isBlowup {U : X.Opens} {f : X' ⟶ X}
    [h : IsAdmissibleBlowupCenter U f I] :
    IsBlowup f I :=
  h.toIsBlowup

/-- A center is admissible exactly when it is a blowup center of finite presentation disjoint from
the chosen open subscheme. -/
theorem isAdmissibleBlowupCenter_iff (U : X.Opens) (f : X' ⟶ X) (I : X.IdealSheafData) :
    IsAdmissibleBlowupCenter U f I ↔
      IsBlowup f I ∧
        LocallyOfFinitePresentation I.subschemeι ∧
        Disjoint (I.support : Set X) U := by
  constructor
  · intro h
    exact ⟨h.toIsBlowup, h.locallyOfFinitePresentation_subschemeι, h.disjoint_support⟩
  · rintro ⟨hblowup, hfp, hdisjoint⟩
    exact
      { toIsBlowup := hblowup
        locallyOfFinitePresentation_subschemeι := hfp
        disjoint_support := hdisjoint }

/-- Definition 31.34.1: let `X` be a scheme and let `U ⊆ X` be an open subscheme. A morphism
`f : X' ⟶ X` is a `U`-admissible blowup if there exists a finitely presented closed subscheme of
`X` disjoint from `U` such that `f` is a blowup of `X` in that center. -/
@[stacks 080K]
def IsAdmissibleBlowup (U : X.Opens) (f : X' ⟶ X) : Prop :=
  ∃ I : X.IdealSheafData, IsAdmissibleBlowupCenter U f I

/-- A `U`-admissible blowup is obtained from any admissible center. -/
theorem IsAdmissibleBlowup.mk {U : X.Opens} {f : X' ⟶ X}
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U f I] :
    IsAdmissibleBlowup U f :=
  ⟨I, inferInstance⟩

/-- An admissible blowup comes equipped with an admissible center. -/
theorem IsAdmissibleBlowup.exists_center {U : X.Opens} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ I : X.IdealSheafData, IsAdmissibleBlowupCenter U f I :=
  hf

/-- A `U`-admissible blowup admits a center that is finitely presented, disjoint from `U`, and
for which the morphism is a blowup. -/
theorem IsAdmissibleBlowup.exists_center_spec {U : X.Opens} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ I : X.IdealSheafData,
      IsBlowup f I ∧
        LocallyOfFinitePresentation I.subschemeι ∧
        Disjoint (I.support : Set X) U := by
  rcases hf with ⟨I, hI⟩
  exact ⟨I, hI.toIsBlowup, hI.locallyOfFinitePresentation_subschemeι, hI.disjoint_support⟩

/-- A morphism is `U`-admissible exactly when it admits a finitely presented center disjoint from
`U` for which it satisfies the blowup universal property. -/
theorem isAdmissibleBlowup_iff (U : X.Opens) (f : X' ⟶ X) :
    IsAdmissibleBlowup U f ↔
      ∃ I : X.IdealSheafData,
        IsBlowup f I ∧
          LocallyOfFinitePresentation I.subschemeι ∧
          Disjoint (I.support : Set X) U := by
  constructor
  · exact IsAdmissibleBlowup.exists_center_spec
  · rintro ⟨I, hblowup, hfp, hdisjoint⟩
    exact ⟨I, (isAdmissibleBlowupCenter_iff U f I).2 ⟨hblowup, hfp, hdisjoint⟩⟩

end

end AlgebraicGeometry
