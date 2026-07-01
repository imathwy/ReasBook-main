import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C}
variable {JC' : GrothendieckTopology C'}
variable {JD : GrothendieckTopology D}

/-- Abelian sheaves on `\mathcal C'`. -/
abbrev sourceAbelianSheafCat (JC' : GrothendieckTopology C') :=
  Sheaf JC' AddCommGrpCat.{max u v}

/-- Abelian sheaves on `\mathcal C`. -/
abbrev targetAbelianSheafCat (JC : GrothendieckTopology C) :=
  Sheaf JC AddCommGrpCat.{max u v}

/-- Abelian sheaves on the base site `\mathcal D`. -/
abbrev baseAbelianSheafCat (JD : GrothendieckTopology D) :=
  Sheaf JD AddCommGrpCat.{max u v}

/-- The derived category of abelian sheaves on `\mathcal C'`. -/
abbrev sourceDerived (JC' : GrothendieckTopology C') :=
  DerivedCategory (sourceAbelianSheafCat JC')

/-- The derived category of abelian sheaves on `\mathcal C`. -/
abbrev targetDerived (JC : GrothendieckTopology C) :=
  DerivedCategory (targetAbelianSheafCat JC)

/-- The derived category of abelian sheaves on `\mathcal D`. -/
abbrev baseDerived (JD : GrothendieckTopology D) :=
  DerivedCategory (baseAbelianSheafCat JD)

/-- The degree-zero embedding of abelian sheaves on `\mathcal C'` into the derived category. -/
abbrev sourceSingleZero (JC' : GrothendieckTopology C') :
    sourceAbelianSheafCat JC' ⥤ sourceDerived JC' :=
  DerivedCategory.singleFunctor (sourceAbelianSheafCat JC') (0 : ℤ)

/-- The degree-zero embedding of abelian sheaves on `\mathcal C` into the derived category. -/
abbrev targetSingleZero (JC : GrothendieckTopology C) :
    targetAbelianSheafCat JC ⥤ targetDerived JC :=
  DerivedCategory.singleFunctor (targetAbelianSheafCat JC) (0 : ℤ)

/-- Remark 21.38.7: with notation as in Situation `21.38.3`, if
`g^{-1} : \operatorname{Ab}(\mathcal C) \to \operatorname{Ab}(\mathcal C')` admits a left adjoint
`g_!`, `L\pi'_!` is identified with `Lg_! ⋙ L\pi_!`, `t : \mathcal F' \to g^{-1}\mathcal F` is a
map of abelian sheaves, and one has the canonical comparison
`Lg_!(\mathcal F') \to g_!\mathcal F'` in degree zero, then there is the induced canonical map
`L\pi'_!(\mathcal F') \to L\pi_!(\mathcal F)`. -/
abbrev derivedProjectionLowerShriekMap
    (gInverse : targetAbelianSheafCat JC ⥤ sourceAbelianSheafCat JC')
    (gLowerShriek : sourceAbelianSheafCat JC' ⥤ targetAbelianSheafCat JC)
    (adj_g : gLowerShriek ⊣ gInverse)
    (LgShriek : sourceDerived JC' ⥤ targetDerived JC)
    (LpiShriek : targetDerived JC ⥤ baseDerived JD)
    (Lpi'Shriek : sourceDerived JC' ⥤ baseDerived JD)
    (hcomp : Lpi'Shriek ≅ LgShriek ⋙ LpiShriek)
    {F : targetAbelianSheafCat JC} {F' : sourceAbelianSheafCat JC'}
    (t : F' ⟶ gInverse.obj F)
    (lgComparison :
      LgShriek.obj ((sourceSingleZero JC').obj F') ⟶
        (targetSingleZero JC).obj (gLowerShriek.obj F')) :
    Lpi'Shriek.obj ((sourceSingleZero JC').obj F') ⟶
      LpiShriek.obj ((targetSingleZero JC).obj F) :=
  (hcomp.app ((sourceSingleZero JC').obj F')).hom ≫
    LpiShriek.map
      (lgComparison ≫
        (targetSingleZero JC).map ((adj_g.homEquiv F' F).symm t))

-- Proof sketch: unfold `derivedProjectionLowerShriekMap`. The map is the composite of the
-- identification `L\pi'_! ≅ Lg_! ⋙ L\pi_!`, the degree-zero comparison
-- `Lg_!(\mathcal F') → g_!\mathcal F'`, and the image under `L\pi_!` of the adjoint transpose
-- `g_!\mathcal F' → \mathcal F` of `t`.
/-- The canonical map `derivedProjectionLowerShriekMap` is exactly the composite described in the
remark. -/
theorem derivedProjectionLowerShriekMap_def
    (gInverse : targetAbelianSheafCat JC ⥤ sourceAbelianSheafCat JC')
    (gLowerShriek : sourceAbelianSheafCat JC' ⥤ targetAbelianSheafCat JC)
    (adj_g : gLowerShriek ⊣ gInverse)
    (LgShriek : sourceDerived JC' ⥤ targetDerived JC)
    (LpiShriek : targetDerived JC ⥤ baseDerived JD)
    (Lpi'Shriek : sourceDerived JC' ⥤ baseDerived JD)
    (hcomp : Lpi'Shriek ≅ LgShriek ⋙ LpiShriek)
    {F : targetAbelianSheafCat JC} {F' : sourceAbelianSheafCat JC'}
    (t : F' ⟶ gInverse.obj F)
    (lgComparison :
      LgShriek.obj ((sourceSingleZero JC').obj F') ⟶
        (targetSingleZero JC).obj (gLowerShriek.obj F')) :
    derivedProjectionLowerShriekMap gInverse gLowerShriek adj_g
        LgShriek LpiShriek Lpi'Shriek hcomp t lgComparison =
      (hcomp.app ((sourceSingleZero JC').obj F')).hom ≫
        LpiShriek.map
          (lgComparison ≫
            (targetSingleZero JC).map ((adj_g.homEquiv F' F).symm t)) := sorry

end

end CategoryTheory
