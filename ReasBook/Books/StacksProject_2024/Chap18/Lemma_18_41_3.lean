import Mathlib
import StacksProject_2024.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The lower shriek functor on module sheaves attached to a morphism of ringed sites whose
inverse-image functor admits a left adjoint. -/
abbrev moduleLowerShriek {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [(f^*).IsRightAdjoint] :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  (f^*).leftAdjoint

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]

-- Proof sketch: first use the site-theoretic base change statement of Lemma `7.28.6` for the
-- square of underlying site functors `g.base`, `f.base`, `f'.base`, and `g'.base`. The
-- assumptions that `g` and `g'` have identity structure maps identify their inverse-image module
-- functors with the underlying inverse-image functors on sheaves, so the sheaf-level comparison
-- upgrades to the stated equality on module categories.
/-- Lemma 18.41.3 (1): for a commutative square of ringed sites whose vertical and horizontal
morphisms come from cocontinuous functors, if the induced costructured-arrow functors are
cofinal and the structure maps of `g` and `g'` are the canonical identifications
`g^{-1}\mathcal O_Y = \mathcal O_{Y'}` and `(g')^{-1}\mathcal O_X = \mathcal O_{X'}`, then
`f'_* \circ (g')^* = g^* \circ f_*` on module sheaves. -/
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
      f.modulePushforward ⋙ g^* := sorry

variable [(g^*).IsRightAdjoint]
variable [(g'^*).IsRightAdjoint]

-- Proof sketch: by the first clause, the two composites `f'_* ∘ (g')^*` and `g^* ∘ f_*` agree
-- on module categories. The functors `g_!` and `g'_!` are defined as left adjoints to `g^*` and
-- `(g')^*`, and uniqueness of left adjoints transports the right-adjoint comparison to the
-- corresponding equality `g'_! ∘ (f')^{-1} = f^{-1} ∘ g_!`.
/-- Lemma 18.41.3 (2): under the same hypotheses, if the inverse-image functors for `g` and `g'`
admit left adjoints `g_!` and `g'_!`, then `g'_! \circ (f')^{-1} = f^{-1} \circ g_!` on module
sheaves. -/
theorem module_lower_shriek_pullback_square_eq
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
    f'^* ⋙ g'.moduleLowerShriek =
      g.moduleLowerShriek ⋙ f^* := sorry

end

end RingedSite.Hom
