import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_25_1 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [SmallCategory C]
variable {D : Type u₂} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable [HasSheafify JC (Type w)] [HasSheafify JD (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, F.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)]
variable [HasWeakSheafify JD AddCommGrpCat.{w}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [PreservesFiniteLimits (F.sheafPullback (Type w) JC JD)]
variable {𝒪' : Sheaf JC RingCat.{w}} {𝒪 : Sheaf JD RingCat.{w}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪)

-- Proof sketch: use Lemma `18.15.2` together with the closed-immersion pushforward properties of
-- Lemma `7.43.8` to identify the underlying direct image on abelian sheaves as an exact functor;
-- exactness on sheaves of modules follows from the forgetful comparison to abelian sheaves.
/-- For a site presentation of a morphism of ringed topoi whose underlying morphism of topoi is a
closed immersion and whose structure-sheaf map is an epimorphism, the pushforward functor on
module sheaves is exact. -/
theorem ringedToposModulePushforward_exact_of_closedImmersion_of_structureMap_epi
    (hi : (Functor.morphismOfTopoiInOfContinuous F JC JD).IsClosedImmersion) [Epi φ] :
    exactFunctor (SheafOfModules 𝒪) (SheafOfModules 𝒪')
      (SheafOfModules.pushforward φ) := sorry

-- Proof sketch: the direct image on sheaves of sets is fully faithful for a closed immersion of
-- topoi by Lemma `7.43.8`, and the epimorphism hypothesis on `i^♯` upgrades the recovered map of
-- underlying sheaves to an `\mathcal O`-linear morphism by the restriction-of-scalars argument of
-- Lemma `18.11.4`.
/-- For a site presentation of a morphism of ringed topoi whose underlying morphism of topoi is a
closed immersion and whose structure-sheaf map is an epimorphism, the pushforward functor on
module sheaves is fully faithful. -/
noncomputable instance
    ringedToposModulePushforward_fullyFaithful_of_closedImmersion_of_structureMap_epi
    (hi : (Functor.morphismOfTopoiInOfContinuous F JC JD).IsClosedImmersion) [Epi φ] :
    (SheafOfModules.pushforward φ).FullyFaithful := sorry

-- Proof sketch: for a fully faithful right adjoint, an object lies in the essential image exactly
-- when the adjunction unit is an isomorphism. Here the right adjoint is
-- `SheafOfModules.pushforward φ`, and in the surjective closed-immersion situation
-- this is the categorical form of the textbook condition that the kernel ideal
-- `\mathcal I = \ker(i^\sharp)` acts trivially on the target module.
/-- Lemma 18.25.1: if
`i : (\mathit{Sh}(\mathcal C), \mathcal O) \to (\mathit{Sh}(\mathcal D), \mathcal O')` is a
morphism of ringed topoi presented by a continuous functor of sites `F`, whose underlying morphism
of topoi is a closed immersion and whose structure-sheaf map
`i^\sharp : \mathcal O' \to i_* \mathcal O` is surjective, then an `\mathcal O'`-module lies in
the essential image of the pushforward functor on modules exactly when the adjunction unit is an
isomorphism; this is the canonical categorical formulation of the textbook criterion
`\mathcal I \mathcal G = 0` for `\mathcal I = \ker(i^\sharp)`. -/
theorem ringedToposModulePushforward_essImage_iff_unit_isIso_of_closedImmersion_of_structureMap_epi
    (hi : (Functor.morphismOfTopoiInOfContinuous F JC JD).IsClosedImmersion) [Epi φ]
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (𝒢 : SheafOfModules 𝒪') :
    (SheafOfModules.pushforward φ).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app 𝒢) := sorry
