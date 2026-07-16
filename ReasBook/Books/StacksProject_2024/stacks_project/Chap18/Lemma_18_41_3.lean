import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_31_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

open CategoryTheory
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]
variable [(SheafOfModules.pushforward g'.structureSheafMap).IsRightAdjoint]
variable [(SheafOfModules.pushforward g.structureSheafMap).IsRightAdjoint]

-- Proof sketch: first use the site-theoretic base-change statement of Lemma `7.28.6` for the
-- square of underlying site functors `g.base`, `f.base`, `f'.base`, and `g'.base`. The
-- assumptions that `g` and `g'` have identity structure maps identify their inverse-image module
-- functors with the underlying inverse-image functors on sheaves, so the sheaf-level comparison
-- upgrades to the stated equality on module categories.
/-- Lemma 18.41.3 (1): for a commutative square of ringed sites whose vertical and horizontal
morphisms come from cocontinuous functors, if the induced costructured-arrow functors are
cofinal and the structure maps of `g` and `g'` are the canonical identifications
`g⁻¹𝒪_Y = 𝒪_Y'` and `(g')⁻¹𝒪_X = 𝒪_X'`, then
`f'_* ⋙ (g')^* = g^* ⋙ f_*` on module sheaves. -/
theorem module_pushforward_pullback_square_eq
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g') :
    g'^* ⋙ f'.modulePushforward =
      f.modulePushforward ⋙ g^* := by
  sorry

/- The lower-shriek comparison clause from the older presentation is currently unused in the
direct Chapter 21 import closure, while its stale adjointness surface is not coherent enough to
keep as canonical API here. The compiling Beck-Chevalley comparison needed downstream is the
direct-image/pullback statement above. -/

end

end RingedSite.Hom
