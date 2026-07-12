import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap21.Lemma_21_20_7_core
import StacksProject_2024.Chap21.Lemma_21_37_1

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open RingedSite.Hom
open scoped GrothendieckTopologyDerivedSections

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v

namespace CategoryTheory

section

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{v} JC JD)]
variable [HasWeakSheafify JC AddCommGrpCat.{v}]
variable [HasWeakSheafify JD AddCommGrpCat.{v}]
variable [IsGrothendieckAbelian.{v} (SiteAbelianSheafCat JC)]
variable [IsGrothendieckAbelian.{v} (SiteAbelianSheafCat JD)]

-- Proof sketch: compute the chosen derived inverse image by a K-injective representative of `M`.
-- Lemma `21.37.1` gives acyclicity of inverse images of injective objects for sections over `U`,
-- so `RΓ(U,-)` of the inverse image is computed by ordinary sections. Evaluating the inverse-image
-- sheaf at `U` is the same as evaluating the original sheaf at `u(U)`, giving the comparison.
/-- Objectwise derived sections commute with inverse image on abelian sheaves for a continuous and
cocontinuous functor of sites. -/
@[stacks 0DD8]
theorem inverseImageAbelianDerived_sectionsOverObject_isomorphic
    (U : C)
    (M : DerivedCategory (SiteAbelianSheafCat JD)) :
    IsIsomorphic
      ((RΓ[JC](U)).obj ((siteAbelianInverseImageDerived JC JD u).obj M))
      ((RΓ[JD](u.obj U)).obj M) := sorry

end

section

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{v})
variable [HasWeakSheafify JC AddCommGrpCat.{v}]
variable [HasWeakSheafify JD AddCommGrpCat.{v}]

variable [Functor.Additive ((moduleInverseImageHom JC JD u 𝒪D).modulePushforward)]
variable [IsGrothendieckAbelian.{v}
  (ModuleCat (RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u 𝒪D)))]
variable [IsGrothendieckAbelian.{v} (ModuleCat (RingedSite.ofRingSheaf JD 𝒪D))]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (moduleInverseImageHom JC JD u 𝒪D))
  (ModuleQis (RingedSite.ofRingSheaf JD 𝒪D))]

local notation "SourceSite" => RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u 𝒪D)
local notation "TargetSite" => RingedSite.ofRingSheaf JD 𝒪D
local notation "RΓAbC[" U "]" => moduleSectionsAsAbelianDerived SourceSite U
local notation "RΓAbD[" V "]" => moduleSectionsAsAbelianDerived TargetSite V
local notation "Lg⁻¹" => modulePushforwardDerived (moduleInverseImageHom JC JD u 𝒪D)

-- Proof sketch: represent `M` by a K-injective complex of `𝒪D`-modules. Lemma `21.37.1` shows
-- that inverse images of injective modules are acyclic for sections over `U`, so the left-hand
-- derived sections are computed by ordinary sections of the inverse-image complex. Evaluating the
-- inverse-image module at `U` agrees with evaluating the original complex at `u.obj U`, giving
-- the stated comparison in `DerivedCategory AddCommGrpCat`.
/-- Lemma 21.37.5: let `u : 𝒞 ⥤ 𝒟` be a continuous and cocontinuous functor of sites, let
`g : Sh(𝒞) ⟶ Sh(𝒟)` be the associated morphism of topoi, and let `𝒪C = g⁻¹ 𝒪D`. Then for
`U : 𝒞` and `M : ModuleDerived TargetSite`, the derived sections of the inverse-image complex
`g^* M = g⁻¹ M` over `U`, viewed in `DerivedCategory AddCommGrpCat`, are canonically isomorphic
to the derived sections of `M` over `u.obj U`. This is the statement-stage form of
`RΓ(U, g^* M) = RΓ(u(U), M)`. -/
@[stacks 0DD8]
theorem moduleInverseImageDerived_sectionsOverObject_isomorphic
    (U : C)
    (M : ModuleDerived TargetSite) :
    IsIsomorphic
      ((RΓAbC[U]).obj ((Lg⁻¹).obj M))
      ((RΓAbD[u.obj U]).obj M) := sorry

end

end CategoryTheory
