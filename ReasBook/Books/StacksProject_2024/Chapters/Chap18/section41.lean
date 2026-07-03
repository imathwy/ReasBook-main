import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_41_1 (from Chap18) -/
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
    (SheafOfModules.pushforward
      (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪D)))).IsRightAdjoint := sorry

end

end SheafOfModules

/-! ### Remark_18_41_2 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (JD.over (u.obj U)) AddCommGrpCat.{u}]
variable [∀ U : C, ∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.post u).op.HasLeftKanExtension F]
variable (𝒪D : Sheaf JD CommRingCat.{u})

/-- The inverse-image structure sheaf `g^{-1} \mathcal O_\mathcal D`, viewed as a
`RingCat`-valued sheaf on `\mathcal C`. -/
abbrev inverseImageRingSheaf : Sheaf JC RingCat.{u} :=
  (u.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪D)

/-- The inverse-image functor on `\mathcal O_\mathcal D`-modules induced by the identity map on
`g^{-1}\mathcal O_\mathcal D`. -/
abbrev moduleInverseImage :
    SheafOfModules (ringSheaf JD 𝒪D) ⥤
      SheafOfModules
        ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
          (ringSheaf JD 𝒪D)) :=
  SheafOfModules.pushforward
    (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
      (ringSheaf JD 𝒪D)))

/-- The chosen lower shriek `g_! : \mathrm{Mod}(g^{-1}\mathcal O_\mathcal D) \to
\mathrm{Mod}(\mathcal O_\mathcal D)`, defined as the left adjoint of the inverse-image functor on
modules from Lemma `18.41.1`. -/
abbrev moduleLowerShriek :
    SheafOfModules
      ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        (ringSheaf JD 𝒪D)) ⥤
      SheafOfModules (ringSheaf JD 𝒪D) :=
  Functor.leftAdjoint (moduleInverseImage u 𝒪D)

/-- The localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1`, viewed in the fixed setup of
this remark. -/
abbrev localizedComparisonOnStructureSheaves (U : C) :
    ((Over.post u).sheafPullback AddCommGrpCat.{u}
        (JC.over U) (JD.over (u.obj U))).obj
      (CategoryTheory.localizedStructureAbelianSheaf JC
        ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
    CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U) :=
  CategoryTheory.compare_on_localizations u 𝒪D U

/-- The local criterion from `18.41.2.1`: every slice-site comparison
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` is an isomorphism. -/
abbrev localizedComparisonMapsAreIso : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves u 𝒪D U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (CategoryTheory.localizedStructureAbelianSheaf JC
            ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
        CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))

/-- The fixed-context local hypothesis that all comparison maps from `18.41.2.1` are
isomorphisms. -/
abbrev localizedComparisonCondition : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves u 𝒪D U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (CategoryTheory.localizedStructureAbelianSheaf JC
            ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
        CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))

-- Proof sketch: the proof of Lemma `18.41.1` constructs the comparison from abelian lower shriek
-- followed by forgetfulness to forgetting after module lower shriek by checking the generating
-- modules `j_{U!}\mathcal O_U`. If each localized comparison map
-- `compare_on_localizations u 𝒪D U` is an isomorphism, then the comparison is an isomorphism on
-- those generators, hence the induced transformation of functors is a natural isomorphism.
/-- Remark 18.41.2: in general the square formed by lower shriek on modules, lower shriek on
underlying abelian sheaves, and the forgetful functors need not commute. However, if for every
object `U` of `\mathcal C` the localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1` is an isomorphism, then the
comparison between `g^{Ab}_! ∘ forget` and `forget ∘ g_!` is a natural isomorphism. -/
theorem lowerShriek_toSheaf_comparison_exists_of_compare_on_localizations
    (hlocal :
      ∀ U : C,
        IsIso
          ((localizedComparisonOnStructureSheaves u 𝒪D U) :
            ((Over.post u).sheafPullback AddCommGrpCat.{u}
                (JC.over U) (JD.over (u.obj U))).obj
              (CategoryTheory.localizedStructureAbelianSheaf JC
                ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
            CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))) :
    ∃ comparison :
      SheafOfModules.toSheaf
        ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
          (ringSheaf JD 𝒪D)) ⋙
        u.sheafPullback AddCommGrpCat.{u} JC JD ⟶
        moduleLowerShriek u 𝒪D ⋙
          SheafOfModules.toSheaf (ringSheaf JD 𝒪D),
      ∀ ℱ, IsIso (comparison.app ℱ) := sorry

end

end SheafOfModules

/-! ### Lemma_18_41_3 (from Chap18) -/
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

/-! ### Lemma_18_41_4 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

/-- A sheaf of commutative rings regarded as a `RingCat`-valued sheaf. -/
abbrev ringSheaf {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} where
  obj := 𝒪.obj ⋙ forget₂ CommRingCat RingCat
  property := by
    simpa using ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).property

section

variable {C' C D' D : Type u}
variable [Category.{u} C'] [Category.{u} C] [Category.{u} D'] [Category.{u} D]
variable {J' : GrothendieckTopology C'} {J : GrothendieckTopology C}
variable {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
variable {u' : D' ⥤ C'} {u : D ⥤ C} {v' : C' ⥤ C} {v : D' ⥤ D}
variable [Functor.IsContinuous u K J]
variable [Functor.IsContinuous u' K' J']
variable [Functor.IsContinuous v K' K] [Functor.IsCocontinuous v K' K]
variable [Functor.IsContinuous v' J' J] [Functor.IsCocontinuous v' J' J]
variable {𝒪D : Sheaf K CommRingCat.{u}} {𝒪C : Sheaf J CommRingCat.{u}}
variable (φ : ringSheaf K 𝒪D ⟶
  (u.sheafPushforwardContinuous RingCat.{u} K J).obj (ringSheaf J 𝒪C))
variable (hcomm : v ⋙ u = u' ⋙ v')

/-- The pullback of the source structure sheaf along `v'`. -/
abbrev sourcePullbackStructureSheaf : Sheaf J' RingCat.{u} :=
  (v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)

/-- The pullback of the target structure sheaf along `v`. -/
abbrev targetPullbackStructureSheaf : Sheaf K' RingCat.{u} :=
  (v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)

/-- The upper horizontal structure-sheaf map induced by the commutative square of sites. -/
noncomputable def upperStructureMap :
    (v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D) ⟶
      (u'.sheafPushforwardContinuous RingCat.{u} K' J').obj
        ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) :=
  letI : Functor.IsContinuous (u' ⋙ v') K' J := Functor.isContinuous_comp u' v' K' J' J
  (v.sheafPushforwardContinuous RingCat.{u} K' K).map φ ≫
    (Functor.sheafPushforwardContinuousComp' (eqToIso hcomm) RingCat.{u} K' K J).hom.app _ ≫
    (Functor.sheafPushforwardContinuousComp u' v' RingCat.{u} K' J' J).inv.app _

/-- The inverse-image functor on modules induced by `g'`. -/
abbrev rightVerticalInverseImage : SheafOfModules (ringSheaf J 𝒪C) ⥤
    SheafOfModules ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) :=
  @SheafOfModules.pushforward C' _ C _ J' J v'
    ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C))
    (ringSheaf J 𝒪C) inferInstance
    (𝟙 ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)))

/-- The inverse-image functor on modules induced by `g`. -/
abbrev lowerVerticalInverseImage : SheafOfModules (ringSheaf K 𝒪D) ⥤
    SheafOfModules ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)) :=
  @SheafOfModules.pushforward D' _ D _ K' K v
    ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D))
    (ringSheaf K 𝒪D) inferInstance
    (𝟙 ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)))

/-- The direct-image functor on modules induced by `f'`. -/
abbrev upperHorizontalDirectImage :
    SheafOfModules ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) ⥤
      SheafOfModules ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)) :=
  @SheafOfModules.pushforward D' _ C' _ K' J' u'
    ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D))
    ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) inferInstance
    (upperStructureMap φ hcomm)

/-- The direct-image functor on modules induced by `f`. -/
abbrev lowerHorizontalDirectImage : SheafOfModules (ringSheaf J 𝒪C) ⥤
    SheafOfModules (ringSheaf K 𝒪D) :=
  @SheafOfModules.pushforward D _ C _ K J u (ringSheaf K 𝒪D) (ringSheaf J 𝒪C)
    inferInstance φ

/-- The lower-shriek functor on modules induced by `g'`. -/
abbrev rightVerticalLowerShriek
    [(@SheafOfModules.pushforward C' _ C _ J' J v' sourcePullbackStructureSheaf
      (ringSheaf J 𝒪C) inferInstance (𝟙 sourcePullbackStructureSheaf)).IsRightAdjoint] :
    SheafOfModules ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) ⥤
      SheafOfModules (ringSheaf J 𝒪C) :=
  @SheafOfModules.pullback C' _ C _ J' J v'
    ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C))
    (ringSheaf J 𝒪C) inferInstance
    (𝟙 ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C))) inferInstance

/-- The lower-shriek functor on modules induced by `g`. -/
abbrev lowerVerticalLowerShriek
    [(@SheafOfModules.pushforward D' _ D _ K' K v targetPullbackStructureSheaf
      (ringSheaf K 𝒪D) inferInstance (𝟙 targetPullbackStructureSheaf)).IsRightAdjoint] :
    SheafOfModules ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)) ⥤
      SheafOfModules (ringSheaf K 𝒪D) :=
  @SheafOfModules.pullback D' _ D _ K' K v
    ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D))
    (ringSheaf K 𝒪D) inferInstance
    (𝟙 ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D))) inferInstance

/-- The inverse-image functor on modules induced by `f'`. -/
abbrev upperHorizontalInverseImage
    [(@SheafOfModules.pushforward D' _ C' _ K' J' u' targetPullbackStructureSheaf
      sourcePullbackStructureSheaf inferInstance (upperStructureMap φ hcomm)).IsRightAdjoint] :
    SheafOfModules ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D)) ⥤
      SheafOfModules ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) :=
  @SheafOfModules.pullback D' _ C' _ K' J' u'
    ((v.sheafPushforwardContinuous RingCat.{u} K' K).obj (ringSheaf K 𝒪D))
    ((v'.sheafPushforwardContinuous RingCat.{u} J' J).obj (ringSheaf J 𝒪C)) inferInstance
    (upperStructureMap φ hcomm) inferInstance

/-- The inverse-image functor on modules induced by `f`. -/
abbrev lowerHorizontalInverseImage
    [(@SheafOfModules.pushforward D _ C _ K J u (ringSheaf K 𝒪D)
      (ringSheaf J 𝒪C) inferInstance φ).IsRightAdjoint] :
    SheafOfModules (ringSheaf K 𝒪D) ⥤ SheafOfModules (ringSheaf J 𝒪C) :=
  @SheafOfModules.pullback D _ C _ K J u (ringSheaf K 𝒪D) (ringSheaf J 𝒪C)
    inferInstance φ inferInstance

-- Proof sketch: rewrite the upper horizontal structure map as the transported pullback of `φ`
-- along the commutative square `v ⋙ u = u' ⋙ v'`. Then both composites are the two
-- pseudofunctorial descriptions of direct image on modules for the same composite morphism, so
-- compare them with `SheafOfModules.pushforwardComp`.
/-- Lemma 18.41.4 (1): for a commuting square of site-presented ringed topoi in which `v` and `v'`
are both continuous and cocontinuous and preserve the structure sheaves, the module direct image
along `f'` after the inverse image along `g'` canonically agrees with the inverse image along `g`
after the direct image along `f`. This is the module-sheaf form of
`f'_* \circ (g')^* = g^* \circ f_*`. -/
theorem module_pushforward_pullback_square_eq :
    (@SheafOfModules.pushforward C' _ C _ J' J v' sourcePullbackStructureSheaf
      (ringSheaf J 𝒪C) inferInstance (𝟙 sourcePullbackStructureSheaf)) ⋙
        (@SheafOfModules.pushforward D' _ C' _ K' J' u' targetPullbackStructureSheaf
          sourcePullbackStructureSheaf inferInstance (upperStructureMap φ hcomm)) =
      (@SheafOfModules.pushforward D _ C _ K J u (ringSheaf K 𝒪D)
        (ringSheaf J 𝒪C) inferInstance φ) ⋙
        (@SheafOfModules.pushforward D' _ D _ K' K v targetPullbackStructureSheaf
          (ringSheaf K 𝒪D) inferInstance (𝟙 targetPullbackStructureSheaf)) := sorry

-- Proof sketch: the two functors are the left adjoints of the two right adjoints compared in
-- `module_pushforward_pullback_square_eq`. Uniqueness of left adjoints, equivalently the pseudofunctorial
-- comparison `SheafOfModules.pullbackComp`, gives the desired identification.
/-- Lemma 18.41.4 (2): with the same hypotheses, once the relevant inverse-image functors on
modules are known to admit left adjoints, the lower shriek along `g'` after inverse image along
`f'` canonically agrees with inverse image along `f` after the lower shriek along `g`. This is the
module-sheaf form of `g'_! \circ (f')^{-1} = f^{-1} \circ g_!`. -/
theorem module_lower_shriek_pullback_square_eq
    [(@SheafOfModules.pushforward C' _ C _ J' J v' sourcePullbackStructureSheaf
      (ringSheaf J 𝒪C) inferInstance (𝟙 sourcePullbackStructureSheaf)).IsRightAdjoint]
    [(@SheafOfModules.pushforward D' _ D _ K' K v targetPullbackStructureSheaf
      (ringSheaf K 𝒪D) inferInstance (𝟙 targetPullbackStructureSheaf)).IsRightAdjoint]
    [(@SheafOfModules.pushforward D _ C _ K J u (ringSheaf K 𝒪D)
      (ringSheaf J 𝒪C) inferInstance φ).IsRightAdjoint]
    [(@SheafOfModules.pushforward D' _ C' _ K' J' u' targetPullbackStructureSheaf
      sourcePullbackStructureSheaf inferInstance (upperStructureMap φ hcomm)).IsRightAdjoint] :
    (@SheafOfModules.pullback D' _ C' _ K' J' u' targetPullbackStructureSheaf
      sourcePullbackStructureSheaf inferInstance (upperStructureMap φ hcomm) inferInstance) ⋙
        (@SheafOfModules.pullback C' _ C _ J' J v' sourcePullbackStructureSheaf
          (ringSheaf J 𝒪C) inferInstance (𝟙 sourcePullbackStructureSheaf) inferInstance) =
      (@SheafOfModules.pullback D' _ D _ K' K v targetPullbackStructureSheaf
        (ringSheaf K 𝒪D) inferInstance (𝟙 targetPullbackStructureSheaf) inferInstance) ⋙
        (@SheafOfModules.pullback D _ C _ K J u (ringSheaf K 𝒪D)
          (ringSheaf J 𝒪C) inferInstance φ inferInstance) := sorry

end

end SheafOfModules
