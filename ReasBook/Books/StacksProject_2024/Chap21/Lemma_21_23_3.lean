import Mathlib
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/-- The category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on the ringed site `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves on `X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {A B : Type u} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor induced by pushforward on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived Y :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The unbounded derived direct-image functor `Rf_*` on module sheaves. -/
abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The family of stages underlying a sequential inverse system in `D(\mathcal O_X)`. -/
abbrev inverseSystemFamily {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X) :
    ℕ → ModuleDerived X :=
  fun n ↦ Ksys.obj (op n)

/-- The Milnor difference endomorphism of `\prod_n K_n` attached to a sequential inverse system in
`D(\mathcal O_X)`. -/
def derivedLimitDifferenceMap {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n -
      Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map ((homOfLE (Nat.le_succ n)).op)

/-- A chosen sequential derived limit of a tower `(K_n)` in `D(\mathcal O_X)` is an object `K`
that fits into the standard Milnor distinguished triangle
`K ⟶ \prod_n K_n ⟶ \prod_n K_n ⟶ K[1]`. -/
def IsSequentialDerivedLimit {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang (ModuleDerived X)

-- Proof sketch: represent the inverse system by an object of the derived category of sequential
-- inverse systems, apply the site-theoretic description of `R lim` from Lemma `21.23.1`, and use
-- the commutative square relating `f_*` and the projection from `X × ℕ` to `X`. Equivalently, one
-- can apply `Rf_*` to the Milnor distinguished triangle defining the derived limit and use that
-- `Rf_*` is a right adjoint, hence preserves products.
/-- Lemma 21.23.3: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f : X ⟶ Y`, the derived direct image functor `Rf_*` commutes with derived limits of sequential
inverse systems. Concretely, if `K` is a chosen derived limit of a tower `(K_n)` in
`D(\mathcal O_X)`, then `Rf_* K` is a chosen derived limit of the pushed-forward tower
`(Rf_* K_n)` in `D(\mathcal O_Y)`. -/
theorem modulePushforwardDerived_isSequentialDerivedLimit_of_isSequentialDerivedLimit
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X) {K : ModuleDerived X}
    (hK : IsSequentialDerivedLimit Ksys K) :
    IsSequentialDerivedLimit (Ksys ⋙ modulePushforwardDerived f)
      ((modulePushforwardDerived f).obj K) := sorry

end RingedSite.Hom
