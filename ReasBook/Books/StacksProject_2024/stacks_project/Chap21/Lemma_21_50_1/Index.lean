import Mathlib
import StacksProject_2024.Chap20.«20_54_2_1»
import StacksProject_2024.Chap21.Lemma_21_19_1_impl
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [HasBinaryProducts Y.carrier]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : Y, (localizedRestriction Y U).Additive]
variable [∀ U : Y, PreservesFiniteLimits (localizedRestriction Y U)]
variable [∀ U : Y, PreservesFiniteColimits (localizedRestriction Y U)]
variable [CategoryWithHomology (ModuleCat Y)]
variable [∀ U : Y, CategoryWithHomology (ModuleCat (Y.localization U))]

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable [f.modulePushforward.Additive]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable (modulePullbackDerived_pushforward_adjunction : modulePullbackDerived f ⊣ R(f)_*)

variable
  (modulePullbackDerivedTensorIso :
    ∀ L : DModY,
      (tensoringRight DModY).obj L ⋙ modulePullbackDerived f ≅
        modulePullbackDerived f ⋙ (tensoringRight DModX).obj ((modulePullbackDerived f).obj L))

/-- Helper for Lemma 21.50.1: after the adjunction unit has been factored off, the relative cup
product is natural in the right/source variable specialized to the projection-formula setting. -/
lemma projection_formula_cup_right_commSq
    (E : DModX) {K L : DModY} (φ : K ⟶ L) :
    (R(f)_*.map ((modulePullbackDerived f).map φ) ▷ (R(f)_*).obj E) ≫
        CategoryTheory.relativeDerivedCupProduct
          (modulePullbackDerived f)
          (R(f)_*)
          modulePullbackDerived_pushforward_adjunction
          (curriedTensor DModX)
          (curriedTensor DModY)
          (fun A B ↦ (modulePullbackDerivedTensorIso B).app A)
          E
          ((modulePullbackDerived f).obj L) =
      CategoryTheory.relativeDerivedCupProduct
          (modulePullbackDerived f)
          (R(f)_*)
          modulePullbackDerived_pushforward_adjunction
          (curriedTensor DModX)
          (curriedTensor DModY)
          (fun A B ↦ (modulePullbackDerivedTensorIso B).app A)
          E
          ((modulePullbackDerived f).obj K) ≫
        (R(f)_*).map (((modulePullbackDerived f).map φ) ▷ E) := by
  -- Transpose both composites across the adjunction so the cup products become their defining
  -- pullback-side maps.
  refine
    ((modulePullbackDerived_pushforward_adjunction.homEquiv
      (((tensoringRight DModY).obj (R(f)_*.obj E)).obj ((R(f)_*.obj ((modulePullbackDerived f).obj K)))
      (((tensoringRight DModX).obj E).obj ((modulePullbackDerived f).obj K))).symm.injective ?_)
  rw [modulePullbackDerived_pushforward_adjunction.homEquiv_naturality_left_symm]
  rw [modulePullbackDerived_pushforward_adjunction.homEquiv_naturality_right_symm]
  rw [CategoryTheory.relativeDerivedCupProduct_spec, CategoryTheory.relativeDerivedCupProduct_spec]
  -- After expanding the two transposes, both sides are the same by naturality of the pullback
  -- tensor comparison and of the adjunction counit.
  simp only [CategoryTheory.relativeDerivedCupProductAdjointMap, Functor.map_comp, Category.assoc]
  aesop_cat

end

end RingedSite.Hom
