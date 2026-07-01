import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {DModX DModX' DModZ DModZ' : Type u}
variable [Category DModX] [Category DModX'] [Category DModZ] [Category DModZ']

/-- The top horizontal map on supported cohomology obtained by first pulling back the ambient
cohomology of `i_* R\mathcal H_Z(K)` and then applying the morphism from Remark `20.34.12`. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_topMap
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (ambientPullbackMap : ambientCohomology ⟶ pullbackDerived ⋙ ambientCohomology')
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    {K : DModX}
    (τ : restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
      sectionsWithSupportDerived'.obj (pullbackDerived.obj K)) :
    ambientCohomology.obj (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ⟶
      ambientCohomology'.obj
        (i'PushforwardDerived.obj (sectionsWithSupportDerived'.obj (pullbackDerived.obj K))) :=
  ambientPullbackMap.app (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ≫
    ambientCohomology'.map
      (baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
        i'PushforwardDerived.map τ)

/-- The left vertical map from supported cohomology to ordinary cohomology induced by the counit
`i_* R\mathcal H_Z(K) ⟶ K`. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_leftMap
    (iPushforwardDerived : DModZ ⥤ DModX)
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (K : DModX) :
    ambientCohomology.obj (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ⟶
      ambientCohomology.obj K :=
  ambientCohomology.map (adjZ.counit.app K)

/-- The right vertical map from supported cohomology on `X'` to ordinary cohomology on `X'`
induced by the supported-subcategory counit. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_rightMap
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    (K' : DModX') :
    ambientCohomology'.obj
        (i'PushforwardDerived.obj (sectionsWithSupportDerived'.obj K')) ⟶
      ambientCohomology'.obj K' :=
  ambientCohomology'.map
    (supportedRightAdjointAmbientIso.inv.app K' ≫ adjSupported.counit.app K')

-- Proof sketch: identify the supported cohomology groups with the ambient cohomology of
-- `i_* R\mathcal H_Z(K)` and `i'_* R\mathcal H_{Z'}(Lf^* K)`. Naturality of the pullback map on
-- ambient cohomology gives the square obtained by pulling back `i_* R\mathcal H_Z(K) ⟶ K`, and
-- the defining relation for `τ` from Remark `20.34.12` identifies the right-hand composite with
-- the pullback of that counit.
/-- Lemma 20.34.13: after identifying `H^p_Z(X, K)` with the ambient cohomology of
`i_* R\mathcal H_Z(K)` and `H^p_{Z'}(X', Lf^* K)` with the ambient cohomology of
`i'_* R\mathcal H_{Z'}(Lf^* K)`, the pullback map on cohomology with support and the natural maps
to ordinary cohomology form a commutative square. -/
theorem closedSubsetPullback_sectionsWithSupportDerived_cohomology_commSq
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (ambientPullbackMap : ambientCohomology ⟶ pullbackDerived ⋙ ambientCohomology')
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    {K : DModX}
    (τ : restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
      sectionsWithSupportDerived'.obj (pullbackDerived.obj K))
    (hτ :
      baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
          i'PushforwardDerived.map τ ≫
          supportedRightAdjointAmbientIso.inv.app (pullbackDerived.obj K) ≫
          adjSupported.counit.app (pullbackDerived.obj K) =
        pullbackDerived.map (adjZ.counit.app K)) :
    CommSq
      (closedSubsetPullback_sectionsWithSupportDerived_topMap
        iPushforwardDerived i'PushforwardDerived
        sectionsWithSupportDerived sectionsWithSupportDerived'
        pullbackDerived restrictedPullbackDerived
        ambientCohomology ambientCohomology' ambientPullbackMap
        baseChangeIso τ)
      (closedSubsetPullback_sectionsWithSupportDerived_leftMap
        iPushforwardDerived sectionsWithSupportDerived ambientCohomology adjZ K)
      (closedSubsetPullback_sectionsWithSupportDerived_rightMap
        i'PushforwardDerived sectionsWithSupportDerived'
        supportedProperty supportedRightAdjoint ambientCohomology'
        adjSupported supportedRightAdjointAmbientIso (pullbackDerived.obj K))
      (ambientPullbackMap.app K) := sorry

end

end AlgebraicGeometry.RingedSpace
