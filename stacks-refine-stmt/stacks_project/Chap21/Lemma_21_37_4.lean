import Mathlib
import stacks_project.Chap21.Definition_21_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable [PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type u) JC JD)]
variable {𝒪D : Sheaf JD RingCat.{u}}

-- Proof sketch: use Lemma `21.13.5` on the underlying abelian sheaf of the inverse-image module.
-- Lemma `21.37.1` supplies the vanishing of higher cohomology over objects of `C`. For the Čech
-- exactness criterion, apply the adjunction between `u.sheafPullback (Type u) JC JD` and
-- `u.sheafPushforwardContinuous (Type u) JC JD`, use that left adjoints preserve surjections, and
-- use the pullback-preservation hypothesis to identify the iterated fibre products after applying
-- `g_!^{Sh}`. Lemma `21.14.1` gives total acyclicity of the injective module `ℐ` on `D`, so the
-- converse direction of Lemma `21.13.5` yields the desired exactness on the source site.
/-- Lemma 21.37.4: let `u : \mathcal C \to \mathcal D` be continuous and cocontinuous, let
`g : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` be the associated morphism of topoi,
let `\mathcal O_\mathcal D` be a sheaf of rings on `\mathcal D`, and let `\mathcal I` be an
injective `\mathcal O_\mathcal D`-module. If the lower shriek on sheaves of sets
`g_!^{Sh}`, formalized by `u.sheafPullback (Type u) JC JD`, commutes with fibre products, then
the inverse image `g^{-1}\mathcal I`, formalized by the module-theoretic inverse-image functor
`SheafOfModules.pushforward (𝟙 ((u.sheafPushforwardContinuous RingCat JC JD).obj 𝒪D))`, is
totally acyclic. -/
theorem moduleInverseImage_isTotallyAcyclicOne_of_injective_of_sheafPullback_preserves_pullbacks
    (ℐ : SheafOfModules 𝒪D) (hℐ : Injective ℐ) :
    IsTotallyAcyclicOne
      ((SheafOfModules.toSheaf ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D)).obj
        ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D))).obj ℐ)) := sorry

end

end CategoryTheory
