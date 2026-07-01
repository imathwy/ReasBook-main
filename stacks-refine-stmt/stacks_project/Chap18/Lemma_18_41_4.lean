import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
