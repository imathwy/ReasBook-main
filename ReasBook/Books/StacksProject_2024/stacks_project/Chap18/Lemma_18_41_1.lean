import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
variable (𝒪D : Sheaf K CommRingCat.{u})

-- Proof sketch: identify `g^* = g⁻¹` on module sheaves with the functor
-- `SheafOfModules.pushforward` attached to the identity map on the inverse-image ring sheaf.
-- For the generating family
-- `j_{U!}\mathcal O_U`, the Hom-sets into `g^* \mathcal G` are represented by the modules
-- `j_{u(U)!}\mathcal O_{u(U)}` on `D`; then apply the quotient-generating right-adjoint
-- criterion from Lemma `12.29.6` together with the generator result of Lemma `18.28.8`.
/-- Lemma 18.41.1: if `u : \mathcal C \to \mathcal D` is continuous and cocontinuous, `g :
\mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` is the associated morphism of topoi, and
`\mathcal O_\mathcal C = g^{-1}\mathcal O_\mathcal D`, then the inverse-image functor on module
sheaves
`g^* = g^{-1} : \mathrm{Mod}(\mathcal O_\mathcal D) \to \mathrm{Mod}(\mathcal O_\mathcal C)`
admits a left adjoint `g_!`. In the site-level module API this inverse-image functor is the
pushforward functor attached to the identity map on the inverse-image `RingCat`-valued sheaf
`(u.sheafPushforwardContinuous RingCat J K).obj
((sheafCompose K (forget₂ CommRingCat RingCat)).obj \mathcal O_\mathcal D)`. -/
instance moduleInverseImage_isRightAdjoint :
    (SheafOfModules.pushforward.{u}
      (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪D)))).IsRightAdjoint := by
  let R :=
    (u.sheafPushforwardContinuous RingCat.{u} J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪D)
  -- This is the canonical `pushforward` functor for the identity map on the inverse-image
  -- ring sheaf, so the specialized pullback/pushforward adjunction gives the needed instance.
  exact (SheafOfModules.PullbackConstruction.adjunction.{u} (𝟙 R)).isRightAdjoint

end

end SheafOfModules
