import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable {𝒪D : Sheaf JD RingCat.{u}}

-- Proof sketch: for each covering family of `U`, continuity sends it to a covering family of
-- `u(U)`, and cocontinuity identifies the iterated fibre products so that the Čech complexes for
-- `g⁻¹ ℐ` on `C` and for `ℐ` on `D` agree. Lemma `21.12.3` gives vanishing of the positive Čech
-- cohomology of `ℐ`, and Lemma `21.10.9` upgrades this to vanishing of the higher cohomology
-- groups over `U`.
/-- Lemma 21.37.1: if `u : \mathcal C \to \mathcal D` is continuous and cocontinuous, `\mathcal
O_\mathcal D` is a sheaf of rings on `\mathcal D`, and `\mathcal I` is an injective
`\mathcal O_\mathcal D`-module, then the inverse image `g^{-1}\mathcal I`, formalized on sites by
`SheafOfModules.pushforward (𝟙 ((u.sheafPushforwardContinuous RingCat JC JD).obj \mathcal
O_\mathcal D))`, has vanishing higher cohomology over every object `U : \mathcal C`. -/
theorem higherCohomology_isZero_moduleInverseImage_of_injective
    (ℐ : SheafOfModules 𝒪D) (hℐ : Injective ℐ)
    (U : C) (p : ℕ) (hp : 0 < p) :
    Limits.IsZero
      (((SheafOfModules.toSheaf
          ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D)).obj
        ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D))).obj ℐ)).H' p U) := sorry

end
