import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap18.Lemma_18_41_1
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Lemma_21_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open RingedSite.Hom
open SheafOfModules
open SheafOfModules.RingedSite
open scoped RingedSite.Hom
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v

namespace CategoryTheory

section

/- Domain-style sampling:
- primary domain: lower-shriek / inverse-image adjunctions for sheaves of modules on ringed sites,
  together with the standard generator objects `j_{U!}\mathcal O_U`;
- inspected owner declarations:
  `inverseImageRingSheaf`,
  `moduleInverseImageHom`,
  `modulePullbackToDerived`,
  `IsLeftAcyclicForAdditiveFunctor`;
- best owner abstraction: the ambient owner categories and inverse-image functor are already
  canonicalized in Chapter 21 by
  `ModuleCat (RingedSite.ofRingSheaf JC (ringSheaf JC ((u.sheafPushforwardContinuous
    CommRingCat JC JD).obj 𝒪D)))`,
  `ModuleCat (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D))`, and
  `RingedSite.Hom.modulePushforward (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D))`; the
  underived lower shriek is already owned by the ringed-site morphism
  `g = moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)` through `g^*`, so no parallel
  site-specific lower-shriek wrapper should appear in the public API; the standard generators
  should be written through the Chapter 18 notation `j![𝒪, U]`;
- primitive data: the continuous/cocontinuous site functor `u`, the pullback structure sheaf
  `g^{-1}\mathcal O_\mathcal D`, the Chapter 18 hypotheses ensuring the canonical underived
  adjunction `g_! ⊣ g^{-1}`, and the chosen derived functors;
- derived API: existence of the total left derived functor, the derived adjunction, and the
  generator calculation.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `21.37.2`;
- `core/canonical`: `inverseImageRingSheaf`, `ModuleCat`, `moduleInverseImageHom`,
  `RingedSite.Hom.modulePushforward`, `RingedSite.Hom.moduleLowerShriek`,
  `modulePullbackToDerived`, `modulePushforwardDerived`, `j![𝒪, U]`,
  `Functor.HasLeftDerivedFunctor`, `IsLeftAcyclicForAdditiveFunctor`, and explicit derived
  adjunction data `adj : modulePullbackDerived g ⊣ modulePushforwardDerived g`;
- `bridge/view`: the inverse-image ring sheaf `g^{-1}\mathcal O_\mathcal D` on the source site,
  kept only as local notation. -/

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{v})
variable [HasWeakSheafify JD AddCommGrpCat.{v}]
variable [∀ U : C, HasWeakSheafify (JD.over (u.obj U)) AddCommGrpCat.{v}]
variable [∀ U : C, ∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}, (Over.post u).op.HasLeftKanExtension F]

local notation "XC" =>
  RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))
local notation "XD" => RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)
private abbrev sourceCommRingSheaf : Sheaf JC CommRingCat.{v} :=
  (u.sheafPushforwardContinuous CommRingCat.{v} JC JD).obj 𝒪D
local notation "g" => moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)

variable
  [Abelian (ModuleCat (RingedSite.ofRingSheaf JC
    (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))]
  [CategoryWithHomology (ModuleCat (RingedSite.ofRingSheaf JC
    (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))]
  [Abelian (ModuleCat (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]
  [CategoryWithHomology (ModuleCat (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]

local instance instModuleQisContainsIdentities :
    (ModuleQis (RingedSite.ofRingSheaf JC
      (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D)))).ContainsIdentities where
  id_mem X := by
    simpa [ModuleQis] using
      (show HomotopyCategory.quasiIso
          (ModuleCat XC)
          (up ℤ) (𝟙 X) from by
        rw [HomotopyCategory.mem_quasiIso_iff]
        intro n
        infer_instance)

-- Proof sketch: use Proposition `13.29.2` with the generating family of modules
-- `j![sourceCommRingSheaf u 𝒪D, U]`. Lemma `18.41.1` gives the left adjoint `g_!`, Lemma
-- `18.28.8` gives
-- enough such generators, and Lemma `21.37.1` supplies the acyclicity needed to verify the
-- adapted-generator criterion for existence of the total left derived functor.
/-- Lemma 21.37.2 (1): for the canonical lower-shriek functor
`g_! : Mod(g⁻¹𝒪D) ⥤ Mod(𝒪D)`, formalized canonically as the pullback owner `g^*` for
`g = moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)`, the canonical Chapter 21 owner
`modulePullbackToDerived g` has a total left derived functor. -/
@[stacks 07AC]
theorem moduleLowerShriek_hasLeftDerivedFunctor
    [(g^*).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis XC) :=
  sorry

variable [((moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D))^*).Additive]

instance instModuleLowerShriekHasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis XC) :=
  moduleLowerShriek_hasLeftDerivedFunctor u 𝒪D

variable [HasWeakSheafify JC AddCommGrpCat.{v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [JC.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{v})]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [JD.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{v})]
variable [((moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D))^*).IsRightAdjoint]
variable [Functor.Additive (modulePushforward (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)))]
variable
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)))
    (ModuleQis (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]

/- Lemma 21.37.2 (2): the canonical Chapter 21 owner for the derived adjunction between the
derived lower shriek `L(g)^*` and derived pushforward `R(g)_*` is
`modulePullbackDerived_pushforward_adjunction g : modulePullbackDerived g ⊣
  modulePushforwardDerived g`. -/
#check modulePullbackDerived_pushforward_adjunction g

/-- Lemma 21.37.2 (3): the standard generator `j![sourceCommRingSheaf u 𝒪D, U]` is left acyclic
for the canonical lower-shriek owner `g_!`, expressed by the Chapter 13 owner
`Functor.ComputesLeftDerivedAt` on the degree-zero complex of
`j![sourceCommRingSheaf u 𝒪D, U]` (equivalently
`IsLeftAcyclicForAdditiveFunctor`). The companion isomorphism
from the Chapter 18 generator calculation identifies the underived image with
`j![𝒪D, u.obj U]`; this file does not repackage that isomorphism as a second public owner. -/
@[stacks 07AC, instance]
instance moduleLowerShriek_isLeftAcyclicForAdditiveFunctor_jShriek
    (U : C) :
    Functor.ComputesLeftDerivedAt
      (modulePullbackToDerived g)
      (ModuleQis XC)
      ((HomotopyCategory.singleFunctor (ModuleCat XC) 0).obj
        (j![(sourceCommRingSheaf u 𝒪D), U])) := by
  sorry

end

end CategoryTheory
