import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap18.Lemma_18_20_1
import stacks_project.Chap21.Remark_21_19_3

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- Restriction of `\mathcal O_X`-modules from a ringed site `X` to the localized ringed site
`(X/U, \mathcal O_U)`. -/
abbrev localizedRestriction (X : RingedSite.{u, v}) (U : X) :
    ModuleCat X ⥤ SheafOfModules (X.structureSheaf.over U) :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- The exact functor on derived categories induced by restriction to the localized ringed site
`(X/U, \mathcal O_U)`. -/
abbrev localizedRestrictionDerived
    (X : RingedSite.{u, v}) (U : X)
    [(localizedRestriction X U).Additive]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)] :
    ModuleDerived X ⥤ DerivedCategory (SheafOfModules (X.structureSheaf.over U)) :=
  CategoryTheory.Functor.mapDerivedCategory (localizedRestriction X U)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (V : Y)

variable [f.modulePushforward.Additive]
variable [(RingedSite.Hom.localization f V).modulePushforward.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (RingedSite.Hom.localization f V))
  (ModuleQis (X.localization (f.base.obj V)))]

variable [(localizedRestriction X (f.base.obj V)).Additive]
variable [PreservesFiniteLimits (localizedRestriction X (f.base.obj V))]
variable [PreservesFiniteColimits (localizedRestriction X (f.base.obj V))]

variable [(localizedRestriction Y V).Additive]
variable [PreservesFiniteLimits (localizedRestriction Y V)]
variable [PreservesFiniteColimits (localizedRestriction Y V)]

-- Proof sketch: use the underived identity
-- `(f_* \mathcal F)|_{\mathcal D/V} \cong g_*(\mathcal F|_{\mathcal C/U})`
-- coming from the localization square of Lemma `18.20.1` and Sites, Lemma `7.28.1`. Then pass to
-- unbounded derived functors by representing `E` with a K-injective complex, applying
-- Lemma `21.20.1` to keep the restricted complex K-injective, and comparing the two resulting
-- pushforwards termwise.
/-- Lemma 21.20.4: if `f : X ⟶ Y` is a morphism of ringed sites, `V : Y`, `U = f.base.obj V`,
and `g : X/U ⟶ Y/V` is the localized morphism of ringed sites, then restriction to `Y/V`
commutes with the unbounded derived direct image:
`(Rf_* E)|_{Y/V} \cong Rg_*(E|_{X/U})` for every `E : D(\mathcal O_X)`. -/
theorem modulePushforwardDerived_localizedRestriction_iso
    (E : ModuleDerived X) :
    let U := f.base.obj V
    let g := RingedSite.Hom.localization f V
    ∃ η :
      ((localizedRestrictionDerived Y V).obj ((modulePushforwardDerived f).obj E)) ⟶
        ((modulePushforwardDerived g).obj ((localizedRestrictionDerived X U).obj E)),
      IsIso η := sorry

end

end RingedSite.Hom
