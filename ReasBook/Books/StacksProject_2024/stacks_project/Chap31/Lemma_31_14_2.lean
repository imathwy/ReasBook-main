import Mathlib
import StacksProject_2024.Chap29.Lemma_29_31_2
import StacksProject_2024.Chap31.Definition_31_14_1
import StacksProject_2024.Chap31.Definition_31_21_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced only the ambient closed-immersion / ideal-sheaf
-- owners (`IsClosedImmersion.overEquivIdealSheafData`, `Scheme.IdealSheafData.ker_subschemeι`)
-- rather than a ready-made Chapter 31 statement. The source-facing API below therefore follows
-- the local owners already used in `Chap29/Lemma_29_31_2`, `Chap31/Definition_31_14_1`, and
-- `Chap31/Definition_31_21_1`.

variable {S : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules S.ringCatSheaf)]
variable [SymmetricCategory (SheafOfModules S.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules S.ringCatSheaf)]

local notation "ModS" => SheafOfModules S.ringCatSheaf
local notation "𝒪S" => (SheafOfModules.unit S.ringCatSheaf : ModS)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪S ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

/-- Lemma 31.14.2 (1): if `D ⊆ S` is an effective Cartier divisor, formalized here by the
invertibility of the closed-immersion ideal subobject of `D.subschemeι`, then the conormal sheaf
`\mathcal C_{D/S}` is the restriction `\mathcal I_D|_D = \mathcal O_S(-D)|_D`. Here
`\mathcal O_S(-D)` is `effectiveCartierDivisorNegSheaf` for the ideal subobject of
`D.subschemeι`. -/
@[stacks 0B3P]
theorem effectiveCartierDivisor_conormalSheaf_iso_pullbackNegSheaf
    (D : S.IdealSheafData)
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Limits.HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u})]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D.subschemeι))] :
    Nonempty
      (((Scheme.Modules.pullback D.subschemeι).obj
          (effectiveCartierDivisorNegSheaf
            (closedImmersionIdealSubobject D.subschemeι))) ≅
        immersionConormalSheaf D.subschemeι) := sorry

/-- Lemma 31.14.2 (2): if `D ⊆ S` is an effective Cartier divisor, formalized here by the
invertibility of the closed-immersion ideal subobject of `D.subschemeι`, then the normal sheaf
`\mathcal N_{D/S}`, i.e. the dual of the conormal sheaf on `D`, is the restriction
`\mathcal O_S(D)|_D`. -/
@[stacks 0B3P]
theorem effectiveCartierDivisor_normalSheaf_iso_pullbackAssociatedSheaf
    (D : S.IdealSheafData)
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Limits.HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u})]
    [MonoidalCategory D.subscheme.Modules]
    [MonoidalClosed D.subscheme.Modules]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D.subschemeι))] :
    Nonempty
      (((Scheme.Modules.pullback D.subschemeι).obj
          (effectiveCartierDivisorAssociatedSheaf
            (closedImmersionIdealSubobject D.subschemeι))) ≅
        (ihom (immersionConormalSheaf D.subschemeι)).obj
          (SheafOfModules.unit D.subscheme.ringCatSheaf :
            D.subscheme.Modules)) := sorry

end AlgebraicGeometry.Scheme
