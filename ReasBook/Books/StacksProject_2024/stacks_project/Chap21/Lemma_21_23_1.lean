import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_6
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

variable (J : GrothendieckTopology C)
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)]
variable [IsGrothendieckAbelian.{max u v}
  (SequentialInverseSystem (SiteAbelianSheafCat J))]
variable [CountableAB4Star (SiteAbelianSheafCat J)]

local notation "AbSheaf" => SiteAbelianSheafCat J
local notation "AbSheafSeq" => SequentialInverseSystem AbSheaf
local notation "DAbSheaf" => DerivedCategory AbSheaf
local notation "DAbSheafSeq" => DerivedCategory AbSheafSeq
local notation:max "R" " lim(" K ")" =>
  Functor.obj
    (additiveFunctorTotalRightDerived (lim : AbSheafSeq ⥤ AbSheaf) :
      DAbSheafSeq ⥤ DAbSheaf)
    K

-- Limits in the sheaf category are computed objectwise from the ambient presheaf category, so
-- the inverse-limit functor preserves zero morphisms and addition componentwise.
local instance : (lim : AbSheafSeq ⥤ AbSheaf).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π Y j = (limMap f + limMap g) ≫ limit.π Y j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

/-- Lemma 21.23.1: let `(C, J)` be a site and let
`K : DerivedCategory (SequentialInverseSystem (SiteAbelianSheafCat J))`. If `K_n` denotes the
stagewise restriction of `K` to `C`, then the chosen object `R lim(K)` is a derived limit of the
tower `(K_n)_n`. Equivalently, `R lim(K)` computes `R lim_n K_n` in
`DerivedCategory (SiteAbelianSheafCat J)`. -/
@[stacks 0941]
theorem siteAbelianDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DAbSheafSeq) :
    IsDerivedLimit
      (stagewiseDerivedInverseLimitTower K)
      (R lim(K)) := by
  simpa using derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation K

end

end CategoryTheory
