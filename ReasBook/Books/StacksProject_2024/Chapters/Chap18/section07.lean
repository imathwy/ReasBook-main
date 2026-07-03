import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_7_1 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Domain-style sampling for Definition 18.7.1:
- primary domain: ringed sites and ringed topoi presented by sites;
- sampled owner API:
  `RingedSite`,
  `RingedSite.Hom`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `RingedSite.Hom.IsToposEquivalence`,
  `RingedSite.Hom.IsRingedEquivalence`;
- source/core/bridge triage:
  `source-facing`: a ringed topos presented by a site, and its site-presented morphisms;
  `core/canonical`: `RingedSite` for objects and `RingedSite.Hom` for morphisms;
  `bridge/view`: the induced underlying morphism of topoi, when the canonical sheaf-theoretic
  hypotheses needed to build it are available, the bundled bridge owner
    `RingedSite.Hom.IsToposEquivalence`, the stronger ringed bridge owner
    `RingedSite.Hom.IsRingedEquivalence`, and the ring-sheaf pushforward attached to the base
    site morphism.

Primitive data separate cleanly as follows:
- object level: exactly the data already owned by `RingedSite`;
- morphism level: exactly the data already owned by `RingedSite.Hom`, namely a site morphism
  together with the induced map on structure sheaves into the canonical pushforward.

Accordingly, this item should recall the canonical owners `RingedSite` and `RingedSite.Hom`
directly. The underlying morphism of topoi is auxiliary bridge data, and any bridge structure must
reuse the canonical site-level owner rather than duplicating its primitive fields or introducing an
independent ring-sheaf pushforward. -/

/- Definition 18.7.1: a ringed topos presented by a site is just a ringed site, i.e. a site
together with a sheaf of rings. -/
recall RingedSite

/- Definition 18.7.1: a morphism of ringed topoi presented by sites is the canonical owner
`RingedSite.Hom`, i.e. a morphism of sites together with the adjoint pushforward form
`\mathcal O_Y \to f_* \mathcal O_X` of the structure-sheaf map. -/
recall RingedSite.Hom

namespace RingedSite.Hom

variable {X Y Z : RingedSite.{u, v}}

/-- The canonical pushforward functor on ring-valued sheaves attached to a morphism of ringed
sites. -/
abbrev ringPushforward (f : X ⟶ Y) :
    Sheaf X.siteTopology RingCat.{max u v} ⥤ Sheaf Y.siteTopology RingCat.{max u v} :=
  f.base.sheafPushforwardContinuous RingCat.{max u v} Y.siteTopology X.siteTopology

open scoped MorphismOfTopoiIn

/-- Bridge data ensuring that a morphism of ringed sites presents an underlying morphism of topoi
in a specified sheaf-value category. The underlying morphism of topoi uses the special case
`A = Type w`. -/
class HasToposMorphism (A : Type w) [Category A] (f : X ⟶ Y) : Prop where
  /-- The canonical pushforward on set-valued sheaves is a right adjoint. -/
  sheafPushforwardContinuous_isRightAdjoint :
    (f.base.sheafPushforwardContinuous A Y.siteTopology X.siteTopology).IsRightAdjoint
  /-- The canonical pullback on set-valued sheaves preserves finite limits. -/
  sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (f.base.sheafPullback A Y.siteTopology X.siteTopology)

attribute [instance] HasToposMorphism.sheafPushforwardContinuous_isRightAdjoint
attribute [instance] HasToposMorphism.sheafPullback_preservesFiniteLimits

/-- Explicit right-adjoint and left-exactness data package into the bundled bridge owner
`HasToposMorphism`. -/
instance instHasToposMorphismOfSheafFunctorData
    (A : Type w) [Category A] (f : X ⟶ Y)
    [(f.base.sheafPushforwardContinuous A Y.siteTopology X.siteTopology).IsRightAdjoint]
    [PreservesFiniteLimits (f.base.sheafPullback A Y.siteTopology X.siteTopology)] :
    HasToposMorphism A f where
  sheafPushforwardContinuous_isRightAdjoint := inferInstance
  sheafPullback_preservesFiniteLimits := inferInstance

/-- The underlying morphism of topoi attached to a morphism of ringed sites, whenever the
bundled bridge owner `HasToposMorphism` is available. This is a bridge/view from the source-facing
owner `RingedSite.Hom` to the canonical topos-level owner `MorphismOfTopoiIn`. -/
noncomputable abbrev toMorphismOfTopoi (f : X ⟶ Y) [HasToposMorphism (Type w) f] :
    MorphismOfTopoiIn.{u, u, v, v, w} Y.siteTopology X.siteTopology where
  inverseImageFunctor :=
    LeftExactFunctor.of (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)
  pushforward := f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology
  adjunction := f.base.sheafAdjunctionContinuous (Type w) Y.siteTopology X.siteTopology

@[simp] theorem toMorphismOfTopoi_pushforward
    (f : X ⟶ Y) [HasToposMorphism (Type w) f] :
    f.toMorphismOfTopoi _* =
      f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology :=
  rfl

/-- The underlying morphism of topoi of `f` is an equivalence. This keeps the auxiliary
sheaf-theoretic hypotheses needed to build `f.toMorphismOfTopoi` internal to a single bridge
owner, so downstream theorem headers can state only the mathematically primary equivalence
hypothesis. -/
class IsToposEquivalence (f : X ⟶ Y) : Prop extends HasToposMorphism (Type (max u v)) f where
  /-- The inverse-image functor of the canonical underlying morphism of topoi is an equivalence. -/
  inverseImage_isEquivalence :
    Functor.IsEquivalence (f.toMorphismOfTopoi.inverseImage)

attribute [instance] IsToposEquivalence.inverseImage_isEquivalence

/-- The presented ringed topoi underlying `f` are equivalent: the underlying morphism of topoi is
an equivalence, and the structure-sheaf comparison is an isomorphism in the pushforward form
carried by `RingedSite.Hom`. Equivalently, the adjoint inverse-image form of the structure-sheaf
map is an isomorphism. -/
class IsRingedEquivalence (f : X ⟶ Y) : Prop extends IsToposEquivalence f where
  /-- The structure-sheaf map of `f` is an isomorphism. -/
  structureSheafMap_isIso : IsIso f.structureSheafMap

attribute [instance] IsRingedEquivalence.structureSheafMap_isIso

end RingedSite.Hom

/-! ### Lemma_18_7_2 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace CategoryTheory

abbrev underlyingStructureSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J RingCat) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget RingCat)).obj 𝒪

/-- The inverse-image form of the pushforward-form structure-sheaf map of a morphism of topoi. -/
abbrev underlyingInverseImageMap
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {f : MorphismOfTopoiIn.{u, u, v, v, max u v} K J}
    {𝒪C : Sheaf J RingCat} {𝒪D : Sheaf K RingCat}
    (fSharp : underlyingStructureSheaf K 𝒪D ⟶ (f _*).obj (underlyingStructureSheaf J 𝒪C)) :
    (f⁻¹).obj (underlyingStructureSheaf K 𝒪D) ⟶ underlyingStructureSheaf J 𝒪C :=
  ((f.adjunction.homEquiv _ _).symm) fSharp

namespace RingedSite.Hom

/-- The inverse-image form of the underlying set-valued structure-sheaf map of a morphism of
ringed sites. -/
abbrev underlyingInverseImageMap
    {X Y : RingedSite.{u, v}} (φ : X ⟶ Y) :
    (φ.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology).obj
        (_root_.RingedSite.Hom.underlyingStructureSheaf Y) ⟶
      _root_.RingedSite.Hom.underlyingStructureSheaf X :=
  ((φ.base.sheafAdjunctionContinuous (Type (max u v)) Y.siteTopology X.siteTopology).homEquiv _ _
      ).symm
    ((sheafCompose Y.siteTopology (forget RingCat.{max u v})).map φ.structureSheafMap ≫
      eqToHom (_root_.RingedSite.Hom.structureSheafPushforward_eq φ))

end RingedSite.Hom

/-- A site with a sheaf of rings determines the corresponding ringed site. -/
abbrev ringedSiteOf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J RingCat) :
    _root_.RingedSite where
  carrier := C
  str := inferInstance
  siteTopology := J
  structureSheaf := 𝒪

/- Domain-style sampling for Lemma 18.7.2:
- primary domain: ringed refinements of the Chapter 7 site-theoretic reductions of morphisms of
  topoi;
- sampled owner API:
  `RingedSite`,
  `RingedSite.Hom`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `exists_special_cocontinuous_common_site_factorization_of_isEquivalence`;
- best owner abstraction: the Chapter 7 reduction data now live directly at the owner level through
  dense-subsite functors, sheaf-category equivalences, and the canonical lower morphism of topoi;
  the ringed refinement should therefore be phrased over explicit replacement sites, with only the
  transported structure sheaves and middle morphism of ringed sites added here;
- primitive data vs derived API:
  primitive source data are the underlying morphism of topoi `f` and the underlying
  structure-sheaf map `fSharp`;
  derived data are the transported replacement structure sheaves and the induced middle
  ringed-site factorization;
- source/core/bridge triage:
  `source-facing`: the factorization statement for a morphism of ringed topoi;
  `core/canonical`: the Chapter 7 owner-level reduction data together with `RingedSite`;
  `bridge/view`: the transported structure sheaves on the replacement sites and the comparison of
  the original structure-sheaf map with the middle ringed-site morphism.
-/

namespace RingedToposSiteFactorization

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {C' D' : Type u} [Category.{v} C'] [Category.{v} D']
variable {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
variable {f : MorphismOfTopoiIn.{u, u, v, v, max u v} K J}

/-- The underlying inverse-image map on the middle replacement site attached to a ringed-site
morphism. -/
abbrev middleUnderlyingInverseImageMap
    {𝒪C' : Sheaf J' RingCat} {𝒪D' : Sheaf K' RingCat}
    (φ : ringedSiteOf J' 𝒪C' ⟶ ringedSiteOf K' 𝒪D') :
    let _ : IsMorphismOfSites K' J' φ.base := by
      have hsite :
          IsMorphismOfSites
            (ringedSiteOf K' 𝒪D').siteTopology
            (ringedSiteOf J' 𝒪C').siteTopology φ.base :=
        φ.isMorphismOfSites
      simpa [ringedSiteOf] using hsite
    (φ.base.sheafPullback (Type (max u v)) K' J').obj
        (underlyingStructureSheaf K' 𝒪D') ⟶
      underlyingStructureSheaf J' 𝒪C' := by
  let _ : IsMorphismOfSites K' J' φ.base := by
    have hsite :
        IsMorphismOfSites
          (ringedSiteOf K' 𝒪D').siteTopology
          (ringedSiteOf J' 𝒪C').siteTopology φ.base :=
      φ.isMorphismOfSites
    simpa [ringedSiteOf] using hsite
  simpa using RingedSite.Hom.underlyingInverseImageMap φ

/-- The underlying structure-sheaf map obtained by transporting the middle ringed-site morphism
back along the Chapter 7 topos reduction data. -/
abbrev factorizedUnderlyingInverseImageMap
    (sourceEquiv : Sheaf J (Type (max u v)) ≌ Sheaf J' (Type (max u v)))
    (targetEquiv : Sheaf K (Type (max u v)) ≌ Sheaf K' (Type (max u v)))
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    [HasWeakSheafify J' (Type (max u v))]
    [∀ P : D'ᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u v)) K' J')]
    (_inverseImage_eq :
      f.inverseImage =
        targetEquiv.functor ⋙
          (u.morphismOfTopoiInOfContinuous K' J')⁻¹ ⋙
          sourceEquiv.inverse)
    {𝒪C : Sheaf J RingCat} {𝒪D : Sheaf K RingCat}
    {𝒪C' : Sheaf J' RingCat} {𝒪D' : Sheaf K' RingCat}
    (sourceUnderlying :
      sourceEquiv.functor.obj (underlyingStructureSheaf J 𝒪C) ≅
        underlyingStructureSheaf J' 𝒪C')
    (targetUnderlying :
      targetEquiv.functor.obj (underlyingStructureSheaf K 𝒪D) ≅
        underlyingStructureSheaf K' 𝒪D')
    (φ : ringedSiteOf J' 𝒪C' ⟶ ringedSiteOf K' 𝒪D')
    (hφ : φ.base = u) :
    (targetEquiv.functor ⋙ (u.morphismOfTopoiInOfContinuous K' J')⁻¹ ⋙ sourceEquiv.inverse).obj
        (underlyingStructureSheaf K 𝒪D) ⟶
      underlyingStructureSheaf J 𝒪C :=
  sourceEquiv.inverse.map
      ((u.morphismOfTopoiInOfContinuous K' J').inverseImage.map targetUnderlying.hom ≫
        eqToHom (by simp [hφ]) ≫
        middleUnderlyingInverseImageMap φ ≫
        sourceUnderlying.inv) ≫
    (sourceEquiv.unitIso.app (underlyingStructureSheaf J 𝒪C)).inv

/-- The transported middle ringed-site morphism recovers the original structure-sheaf map after
transport along the owner-level topos reduction data. -/
def FactorsUnderlyingStructureMap
    (sourceEquiv : Sheaf J (Type (max u v)) ≌ Sheaf J' (Type (max u v)))
    (targetEquiv : Sheaf K (Type (max u v)) ≌ Sheaf K' (Type (max u v)))
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    [HasWeakSheafify J' (Type (max u v))]
    [∀ P : D'ᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u v)) K' J')]
    (inverseImage_eq :
      f.inverseImage =
        targetEquiv.functor ⋙
          (u.morphismOfTopoiInOfContinuous K' J')⁻¹ ⋙
          sourceEquiv.inverse)
    {𝒪C : Sheaf J RingCat} {𝒪D : Sheaf K RingCat}
    (fSharp : underlyingStructureSheaf K 𝒪D ⟶ (f _*).obj (underlyingStructureSheaf J 𝒪C))
    {𝒪C' : Sheaf J' RingCat} {𝒪D' : Sheaf K' RingCat}
    (sourceUnderlying :
      sourceEquiv.functor.obj (underlyingStructureSheaf J 𝒪C) ≅
        underlyingStructureSheaf J' 𝒪C')
    (targetUnderlying :
      targetEquiv.functor.obj (underlyingStructureSheaf K 𝒪D) ≅
        underlyingStructureSheaf K' 𝒪D')
    (φ : ringedSiteOf J' 𝒪C' ⟶ ringedSiteOf K' 𝒪D')
    (hφ : φ.base = u) : Prop :=
  underlyingInverseImageMap fSharp =
    eqToHom
        (congrArg
          (fun F ↦ F.obj (underlyingStructureSheaf K 𝒪D))
          inverseImage_eq) ≫
      factorizedUnderlyingInverseImageMap sourceEquiv targetEquiv u inverseImage_eq
        sourceUnderlying targetUnderlying φ hφ

end RingedToposSiteFactorization

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {I G : Type u}

/-- Lemma 18.7.2: for a morphism of ringed topoi
`((Sh(J), 𝒪C) ⟶ (Sh(K), 𝒪D))`, formalized by an underlying morphism of topoi
`f : MorphismOfTopoiIn K J` together with the induced map on the underlying sheaves of sets
`fSharp`, one can apply the canonical Chapter 7 reduction to the underlying topos morphism and
obtain transported structure sheaves on the replacement sites together with a middle morphism of
ringed sites over the canonical site functor `u : D' ⥤ C'`, and these transported data recover
the original structure-sheaf map `fSharp` after transport along the chosen topos factorization. -/
theorem exists_ringed_topos_site_factorization
    (f : MorphismOfTopoiIn.{u, u, v, v, max u v} K J)
    (𝒪C : Sheaf J RingCat) (𝒪D : Sheaf K RingCat)
    (fSharp : underlyingStructureSheaf K 𝒪D ⟶ (f _*).obj (underlyingStructureSheaf J 𝒪C))
    (ℱ : I → Sheaf J (Type (max u v))) (𝒢 : G → Sheaf K (Type (max u v))) :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (sourceFamilyEquiv : Sheaf J (Type (max u v)) ≌ Sheaf J' (Type (max u v))),
      (∀ i : I, ((sourceFamilyEquiv.functor.obj (ℱ i)).obj).IsRepresentable) ∧
      ∃ (D' : Type u) (_ : Category.{v} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K')
        (targetFamilyEquiv : Sheaf K (Type (max u v)) ≌ Sheaf K' (Type (max u v))),
        (∀ j : G, ((targetFamilyEquiv.functor.obj (𝒢 j)).obj).IsRepresentable) ∧
        ∃ (sourceEquiv : Sheaf J (Type (max u v)) ≌ Sheaf J' (Type (max u v)))
          (targetEquiv : Sheaf K (Type (max u v)) ≌ Sheaf K' (Type (max u v)))
          (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : HasWeakSheafify J' (Type (max u v)))
          (_ : ∀ P : D'ᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P)
          (_ : PreservesFiniteLimits (u.sheafPullback (Type (max u v)) K' J'))
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (inverseImage_eq :
            f.inverseImage =
              targetEquiv.functor ⋙
                (u.morphismOfTopoiInOfContinuous K' J')⁻¹ ⋙
                sourceEquiv.inverse),
          ∃ hs :
            (sourceFunctor.sheafPushforwardContinuous RingCat J J').IsRightAdjoint,
          ∃ ht :
            (targetFunctor.sheafPushforwardContinuous RingCat K K').IsRightAdjoint,
          let _ :
              (sourceFunctor.sheafPushforwardContinuous RingCat J J').IsRightAdjoint := hs
          let _ :
              (targetFunctor.sheafPushforwardContinuous RingCat K K').IsRightAdjoint := ht
          ∃ 𝒪C' : Sheaf J' RingCat,
          ∃ 𝒪D' : Sheaf K' RingCat,
          ∃ sourceUnderlying :
              sourceEquiv.functor.obj (underlyingStructureSheaf J 𝒪C) ≅
                underlyingStructureSheaf J' 𝒪C',
          ∃ targetUnderlying :
              targetEquiv.functor.obj (underlyingStructureSheaf K 𝒪D) ≅
                underlyingStructureSheaf K' 𝒪D',
          ∃ sourceTransport :
              (sourceFunctor.sheafPullback RingCat J J').obj 𝒪C ≅ 𝒪C',
          ∃ targetTransport :
              (targetFunctor.sheafPullback RingCat K K').obj 𝒪D ≅ 𝒪D',
          ∃ φ : ringedSiteOf J' 𝒪C' ⟶ ringedSiteOf K' 𝒪D',
          ∃ hφ : φ.base = u,
            RingedToposSiteFactorization.FactorsUnderlyingStructureMap
              sourceEquiv targetEquiv u inverseImage_eq
              fSharp sourceUnderlying targetUnderlying φ hφ := by
  sorry

/-- If the underlying morphism of topoi of a morphism of ringed topoi is an equivalence, the
Chapter 7 factorization may be chosen over a common replacement site with a single common
transported structure sheaf. The middle ringed-site morphism is then literally the identity on
that common ringed site. -/
theorem exists_common_ringed_topos_site_factorization_of_isEquivalence
    (f : MorphismOfTopoiIn.{u, u, v, v, max u v} K J)
    [f.inverseImage.IsEquivalence]
    (𝒪C : Sheaf J RingCat) (𝒪D : Sheaf K RingCat)
    (fSharp : underlyingStructureSheaf K 𝒪D ⟶ (f _*).obj (underlyingStructureSheaf J 𝒪C)) :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : ∀ P : Cᵒᵖ ⥤ Type (max u v), sourceFunctor.op.HasPointwiseRightKanExtension P)
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : ∀ P : Dᵒᵖ ⥤ Type (max u v), targetFunctor.op.HasPointwiseRightKanExtension P)
      (inverseImage_eq :
        let _ :
            (sourceFunctor.sheafPushforwardCocontinuous
              (Type (max u v)) J J').IsEquivalence :=
          Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
            sourceFunctor
        let _ :
            (targetFunctor.sheafPushforwardCocontinuous
              (Type (max u v)) K J').IsEquivalence :=
          Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
            targetFunctor
        f.inverseImage =
          targetFunctor.sheafPushforwardCocontinuous (Type (max u v)) K J' ⋙
            (sourceFunctor.sheafPushforwardCocontinuous
              (Type (max u v)) J J').asEquivalence.inverse),
      ∃ hs :
        (sourceFunctor.sheafPushforwardContinuous RingCat J J').IsRightAdjoint,
      ∃ ht :
        (targetFunctor.sheafPushforwardContinuous RingCat K J').IsRightAdjoint,
      let _ :
          (sourceFunctor.sheafPushforwardContinuous RingCat J J').IsRightAdjoint := hs
      let _ :
          (targetFunctor.sheafPushforwardContinuous RingCat K J').IsRightAdjoint := ht
      ∃ 𝒪' : Sheaf J' RingCat,
      ∃ sourceTransport :
          (sourceFunctor.sheafPullback RingCat J J').obj 𝒪C ≅ 𝒪',
      ∃ targetTransport :
          (targetFunctor.sheafPullback RingCat K J').obj 𝒪D ≅ 𝒪',
      ∃ φ : ringedSiteOf J' 𝒪' ⟶ ringedSiteOf J' 𝒪',
        φ = 𝟙 (ringedSiteOf J' 𝒪') := by
  sorry

end

end CategoryTheory
