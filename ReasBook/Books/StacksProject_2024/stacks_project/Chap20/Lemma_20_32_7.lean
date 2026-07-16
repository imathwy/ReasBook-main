import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_6
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Sections_on_open
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped RingedSpaceDerivedPushforward

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.7:
- primary domain: derived comparison between the ringed-space module functors `RΓ(U, -)` and
  `R(f)_*` and the corresponding derived functors after forgetting `𝒪_X`-module structure to
  abelian sheaves;
- sampled owner declarations:
  `sectionsRingOnOpen`,
  `SheafOfModules.evaluation`,
  `sheafSections`,
  `moduleUnderlyingSheaf`,
  `moduleDerivedSectionsAtOpen`,
  `moduleDerivedPushforward`,
  `TopCat.Sheaf.pushforward`,
  `Functor.mapDerivedCategory`,
  `CategoryTheory.additiveFunctorTotalRightDerived`;
- best owner abstraction:
  `source-facing`: the two comparison isomorphism statements of Lemma `20.32.7`;
  `core/canonical`: the Chapter 20 owners `sectionsRingOnOpen`, `SheafOfModules.evaluation`,
    `sheafSections`, `moduleUnderlyingSheaf`, `moduleDerivedSectionsAtOpen`,
    `moduleDerivedPushforward`, the exact codomain-change owner `Functor.mapDerivedCategory`, and
    the abelian-sheaf pushforward owner `TopCat.Sheaf.pushforward AddCommGrpCat`; total right
    derived functors are needed only on the genuinely non-exact abelian-sheaf sections and
    pushforward functors;
  `bridge/view`: the codomain-change bridge `moduleDerivedSectionsAtOpenToAb` and the two
    source-facing comparison lemmas, written directly against those owners rather than through a
    second root owner on abelian sheaves.

Primitive data are only the ringed space `X`, the open subset `U`, the morphism `f : X ⟶ Y`,
and the derived object `K`. The derived comparison functors are not primitive data; they are the
canonical derived owners attached to the underived functors, with
`(moduleUnderlyingSheaf X).mapDerivedCategory` and
`(forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat).mapDerivedCategory` handling the
exact forgetful passage, and total right derived functors used only for the non-exact
abelian-sheaf section and pushforward functors. -/

end AlgebraicGeometry.RingedSpace

open scoped RingedSpaceDerivedSectionsAtOpenToAb

namespace AlgebraicGeometry.RingedSpace

-- Keep the canonical exactness instances for `moduleUnderlyingSheaf` active across this file so
-- the comparison functor expressions elaborate without reintroducing the earlier section-local
-- duplicate pins.
attribute [local instance]
  moduleUnderlyingSheaf_preservesFiniteLimits
  moduleUnderlyingSheaf_preservesFiniteColimits

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)

local instance : HasDerivedCategory (X.carrier.Sheaf AddCommGrpCat.{u}) :=
  HasDerivedCategory.standard (X.carrier.Sheaf AddCommGrpCat.{u})

-- Proof sketch: both derived section functors compute ordinary abelian-valued sections on the
-- same underlying abelian sheaf on `U`; the source comparison is therefore an isomorphism.
/-- Lemma 20.32.7 (1), source-facing form: the derived sections of `K` over `U` are canonically
isomorphic to the derived abelian sections of the underlying abelian sheaf of `K`. -/
@[stacks 0D5Y]
theorem moduleDerivedSectionsAtOpenToAb_underlyingAbelian_isomorphic
    (K : DerivedCategory X.Modules) :
    IsIsomorphic
      ((RΓ[U]).obj K)
      ((moduleSectionsAsAbelianDerived X U).obj K) := by
  rcases moduleDerivedSectionsAtOpenToAb_isomorphic_moduleSectionsAsAbelianDerived X U with ⟨e⟩
  exact ⟨e.app K⟩

end

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [IsGrothendieckAbelian.{u} (X.carrier.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).Additive]

private abbrev abelianSheafDerivedPushforward :
    DerivedCategory (X.carrier.Sheaf AddCommGrpCat) ⥤
      DerivedCategory (Y.carrier.Sheaf AddCommGrpCat) :=
  additiveFunctorTotalRightDerived (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base)

-- Proof sketch: underived pushforward of `𝒪_X`-modules and pushforward of the underlying abelian
-- sheaf agree after forgetting module structure, so the two derived pushforwards are canonically
-- isomorphic.
/-- Functor-level companion to Lemma 20.32.7 (2): after forgetting `𝒪_X`-module structure,
derived pushforward is canonically isomorphic to the derived pushforward of underlying abelian
sheaves. -/
theorem modulePushforwardDerived_underlyingAbelian_functor_isomorphic :
    IsIsomorphic
      (R(f)_* ⋙ (moduleUnderlyingSheaf Y).mapDerivedCategory)
      ((moduleUnderlyingSheaf X).mapDerivedCategory ⋙ abelianSheafDerivedPushforward f) := by
  sorry

/-- Lemma 20.32.7 (2), source-facing form: derived pushforward commutes with passage to the
underlying abelian sheaf. -/
@[stacks 0D5Y]
theorem modulePushforwardDerived_underlyingAbelian_isomorphic
    (K : DerivedCategory X.Modules) :
    IsIsomorphic
      (((R(f)_*) ⋙ (moduleUnderlyingSheaf Y).mapDerivedCategory).obj K)
      (((moduleUnderlyingSheaf X).mapDerivedCategory ⋙ abelianSheafDerivedPushforward f).obj K) := by
  rcases modulePushforwardDerived_underlyingAbelian_functor_isomorphic f with ⟨e⟩
  exact ⟨e.app K⟩

end

end AlgebraicGeometry.RingedSpace
