import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap13.Definition_13_14_10
import stacks_project.Chap13.Lemma_13_16_1
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a site with structure sheaf
`\mathcal O`. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]

local instance instPreadditiveTarget : Preadditive (RingedSiteModules JC 𝒪') :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪')).toPreadditive

local instance instPreadditiveSource : Preadditive (RingedSiteModules JD 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪)).toPreadditive
/-- Lemma 21.18.2: the pullback functor on homotopy categories of module sheaves associated to a
site-presented morphism of ringed topoi admits a total left derived functor, giving the
unbounded derived pullback `Lf^* : D(\mathcal O') \to D(\mathcal O)`. -/
-- Proof sketch: apply Lemma `13.14.15` to the class of quasi-isomorphisms in the homotopy
-- category. Lemma `21.17.11` provides enough K-flat complexes with flat terms, while
-- Lemmas `21.18.1` and `21.17.12` show that pullback sends quasi-isomorphisms between those
-- chosen resolutions to quasi-isomorphisms.
theorem pullbackToDerived_hasLeftDerivedFunctor
    [hadd : (pullbackFunctor F φ).Additive] :
    Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (pullbackFunctor F φ))
      (HomotopyCategory.quasiIso (RingedSiteModules JC 𝒪') (up ℤ)) := sorry

end

end SheafOfModules.RingedSite
