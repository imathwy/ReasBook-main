import Mathlib
import StacksProject_2024.Chap07.Remark_7_29_7
import StacksProject_2024.Chap07.Remark_7_29_8
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Definition_18_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace CategoryTheory

open RingedSite.Hom
open Functor.IsDenseSubsite

/- Domain-style sampling for Lemma 18.7.2:
- primary domain: reduction of arbitrary morphisms of ringed topoi to site-presented morphisms of
  ringed sites, built on the Chapter 7 reduction of the underlying morphism of topoi;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `exists_special_cocontinuous_site_factorization`,
  `exists_topos_morphism_reduction`,
  `exists_special_cocontinuous_common_site_factorization_of_isEquivalence`,
  `RingedSite.Hom`,
  `Functor.pushforwardUnderlyingIso`,
  `CommSq`,
  `sheafCompose`;
- best owner abstraction: the source-facing input data should remain an arbitrary morphism of
  topoi `f : MorphismOfTopoiIn K J` together with a `RingCat`-valued realization `𝒪f` of the
  direct image of `𝒪C`, an identification of its forgotten sheaf with the set-valued direct image
  `(f _*).obj (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪C))`, and the actual
  structure-sheaf map `fSharp : 𝒪D ⟶ 𝒪f`; the site-presented `RingedSite.Hom` is the produced
  bridge/view on the replacement sites, not the owner of the original source data;
- primitive data vs derived API:
  primitive source data are the morphism of topoi `f : MorphismOfTopoiIn K J` and the direct-image
  realization data
  `𝒪f : Sheaf K RingCat`,
  `fPushforwardIso :
    (sheafCompose K (forget RingCat)).obj 𝒪f ≅
      (f _*).obj (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪C))`,
  and `fSharp : 𝒪D ⟶ 𝒪f`;
  derived data are the transported ring sheaves on the replacement sites, the middle
  site-presented morphism `ψ : RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D'`,
  the comparison square on underlying structure sheaves expressing compatibility with `fSharp`,
  and, only in the generalized companion theorem below, the dense-subsite representability
  statements for additional chosen families;
- source/core/bridge triage:
  `source-facing`: the factorization statement for an arbitrary morphism of ringed topoi;
  `core/canonical`: `MorphismOfTopoiIn`, the Chapter 7 reduction theorems, and `RingedSite.Hom`;
  `bridge/view`: the produced site-presented morphism `ψ` together with the comparison square on
  direct images of underlying sheaves of sets.
-/

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {I G : Type u}
variable {𝒪C : Sheaf J RingCat} {𝒪D : Sheaf K RingCat}
variable {𝒪f : Sheaf K RingCat}

local instance ofRingSheaf_base_isContinuous
    {C₁ D₁ : Type u} [Category.{v} C₁] [Category.{v} D₁]
    {J₁ : GrothendieckTopology C₁} {K₁ : GrothendieckTopology D₁}
    {𝒪₁ : Sheaf J₁ RingCat} {𝒪₂ : Sheaf K₁ RingCat}
    (f : RingedSite.ofRingSheaf J₁ 𝒪₁ ⟶ RingedSite.ofRingSheaf K₁ 𝒪₂) :
    f.base.IsContinuous K₁ J₁ :=
  f.isMorphismOfSites.toIsContinuous

variable (f : MorphismOfTopoiIn K J)
variable
  (fPushforwardIso :
    (sheafCompose K (forget RingCat.{max u v})).obj 𝒪f ≅
      (f _*).obj (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪C)))
  (fSharp : 𝒪D ⟶ 𝒪f)

/-- Helper for Lemma 18.7.2: the dense-subsite unit identifies the pushed-forward transport of a
ring-valued sheaf with the original sheaf. -/
noncomputable abbrev transport_ring_sheaf_to_dense_subsite_iso
    {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'}
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    (𝒪 : Sheaf J RingCat.{max u v}) :
    (v.sheafPushforwardContinuous RingCat.{max u v} J J').obj
        ((sheafEquiv J J' v RingCat.{max u v}).functor.obj 𝒪) ≅
      𝒪 :=
  ((sheafEquiv J J' v RingCat.{max u v}).unitIso.app 𝒪).symm

/-- Helper for Lemma 18.7.2: a dense-subsite replacement transports a ring-valued sheaf to the
replacement site together with the canonical identification after continuous pushforward. -/
noncomputable def transport_ring_sheaf_to_dense_subsite
    {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'}
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    (𝒪 : Sheaf J RingCat.{max u v}) :
    Σ 𝒪' : Sheaf J' RingCat.{max u v},
      (v.sheafPushforwardContinuous RingCat.{max u v} J J').obj 𝒪' ≅ 𝒪 :=
  ⟨(sheafEquiv J J' v RingCat.{max u v}).functor.obj 𝒪,
    transport_ring_sheaf_to_dense_subsite_iso (J := J) (J' := J') (v := v) 𝒪⟩

/-- Helper for Lemma 18.7.2: the mixed inverse-image square produced by the Chapter 7 reduction
has the required direct-image mate. -/
noncomputable def reductionDirectImageSquare
    {C' : Type u} [Category.{v} C']
    {D' : Type u} [Category.{v} D']
    {J' : GrothendieckTopology C'}
    {K' : GrothendieckTopology D'}
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    (targetFunctor : D ⥤ D') [targetFunctor.IsDenseSubsite K K']
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    (sq :
      CatCommSq
        (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
        (u.sheafPullback (Type (max u v)) K' J')
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')) :
    CatCommSq
      (u.sheafPushforwardContinuous (Type (max u v)) K' J')
      (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
      (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
      (f _*) := sorry

/-- Helper for Lemma 18.7.2: bundling a fixed base functor `u` with a pushforward-form
structure-sheaf map gives the corresponding morphism of ringed sites. -/
private abbrev ringedSiteHomOfBaseStructureSheafMap
    {C' : Type u} [Category.{v} C']
    {D' : Type u} [Category.{v} D']
    {J' : GrothendieckTopology C'}
    {K' : GrothendieckTopology D'}
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    (𝒪C' : Sheaf J' RingCat) (𝒪D' : Sheaf K' RingCat)
    (φ : 𝒪D' ⟶ (u.sheafPushforwardContinuous RingCat K' J').obj 𝒪C') :
    RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D' where
  base := u
  isMorphismOfSites := inferInstance
  structureSheafMap := φ

/-- Helper for Lemma 18.7.2: the underlying direct-image map determined by a pushforward-form
structure-sheaf map over the fixed base functor `u`. -/
private abbrev underlyingDirectImageMapOfBaseStructureSheafMap
    {C' : Type u} [Category.{v} C']
    {D' : Type u} [Category.{v} D']
    {J' : GrothendieckTopology C'}
    {K' : GrothendieckTopology D'}
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    (𝒪C' : Sheaf J' RingCat) (𝒪D' : Sheaf K' RingCat)
    (φ : 𝒪D' ⟶ (u.sheafPushforwardContinuous RingCat K' J').obj 𝒪C') :
    underlyingStructureSheaf (RingedSite.ofRingSheaf K' 𝒪D') ⟶
      (u.sheafPushforwardContinuous (Type (max u v)) K' J').obj
        (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪C')) :=
  (ringedSiteHomOfBaseStructureSheafMap (u := u) 𝒪C' 𝒪D' φ).underlyingDirectImageMap

/-- Helper for Lemma 18.7.2: once the base functor `u` is fixed by the Chapter 7 reduction, it
remains to construct the pushforward-form structure-sheaf map over `u` realizing the displayed
comparison square on underlying sheaves of sets. -/
private theorem existsMiddleStructureSheafMapOfReductionSquare
    {C' : Type u} [Category.{v} C']
    {D' : Type u} [Category.{v} D']
    {J' : GrothendieckTopology C'}
    {K' : GrothendieckTopology D'}
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    (targetFunctor : D ⥤ D') [targetFunctor.IsDenseSubsite K K']
    (u : D' ⥤ C') [IsMorphismOfSites K' J' u]
    (𝒪C' : Sheaf J' RingCat) (𝒪D' : Sheaf K' RingCat)
    (sourceTransport :
      (sourceFunctor.sheafPushforwardContinuous RingCat J J').obj 𝒪C' ≅ 𝒪C)
    (targetTransport :
      (targetFunctor.sheafPushforwardContinuous RingCat K K').obj 𝒪D' ≅ 𝒪D)
    (toposSq :
      CatCommSq
        (u.sheafPushforwardContinuous (Type (max u v)) K' J')
        (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
        (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
        (f _*)) :
    ∃ φ : 𝒪D' ⟶ (u.sheafPushforwardContinuous RingCat K' J').obj 𝒪C',
      CommSq
        (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).inv
        ((sheafCompose K (forget RingCat.{max u v})).map fSharp)
        ((targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K').map
            (underlyingDirectImageMapOfBaseStructureSheafMap (u := u) 𝒪C' 𝒪D' φ) ≫
          (toposSq.iso.app
            (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪C'))).hom ≫
          (f _*).map
            (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom)
        fPushforwardIso.hom := by
  -- Route correction: the site-theoretic factorization is already fixed by `toposSq`; the only
  -- unresolved work is the missing RingCat-valued comparison between `𝒪f` and the transported
  -- direct image of `𝒪C'`.
  -- Route correction: the tempting inverse-image construction via
  -- `u.sheafAdjunctionContinuous RingCat K' J'` is not available from the hypotheses in this
  -- file, so the remaining bridge really has to be built on the pushforward side.
  -- TODO: build the ring-valued comparison `eRing`, define `ψ.structureSheafMap` as its adjoint
  -- mate, and then verify the displayed square after forgetting to `Type`.
  sorry

omit fPushforwardIso fSharp in
/-- Helper for Chap18 Lemma 18 7 2: package the Chapter 7 reduction directly in the
`u.sheafPullback` form needed by the ringed-site factorization theorems, together with the
representability payload for any auxiliary families. -/
private theorem existsToposMorphismReductionCanonicalLocal
    (ℱ : I → Sheaf J (Type (max u v))) (𝒢 : G → Sheaf K (Type (max u v)))
    [HasWeakSheafify J (Type (max u v))]
    [HasWeakSheafify K (Type (max u v))] :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type u) (_ : Category.{v} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (sq :
            CatCommSq
              (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
              (u.sheafPullback (Type (max u v)) K' J')
              (f⁻¹)
              (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')),
          (∀ i : I,
            (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
            ∀ j : G,
              (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable := by
  -- Route correction: the public Chapter 7 theorem only packages a lower morphism of topoi `g`;
  -- this file needs the stronger bridge identifying that lower inverse image with
  -- `u.sheafPullback`, and that canonical comparison is the current structural blocker.
  -- TODO: copy the missing Chapter 7 bridge locally, replacing the `g⁻¹` square from
  -- `exists_topos_morphism_reduction` by the equivalent square with `u.sheafPullback`.
  sorry

omit fPushforwardIso fSharp in
/-- Helper for Chap18 Lemma 18 7 2: the empty-family specialization of the missing canonical
reduction bridge, isolated so the main theorem can keep its existential packaging explicit. -/
private theorem existsToposMorphismReductionCanonicalEmptyLocal
    [HasWeakSheafify J (Type (max u v))]
    [HasWeakSheafify K (Type (max u v))] :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type u) (_ : Category.{v} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (sq :
            CatCommSq
              (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
              (u.sheafPullback (Type (max u v)) K' J')
              (f⁻¹)
              (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')),
          True := by
  -- TODO: this is the empty-family specialization of the same missing Chapter 7 bridge as above.
  sorry

/-- Lemma 18.7.2: for an arbitrary morphism of ringed topoi from
`(Sh(J), 𝒪C)` to `(Sh(K), 𝒪D)`, formalized by a morphism of topoi
`f : MorphismOfTopoiIn K J`, a `RingCat`-valued direct-image realization `𝒪f` of `𝒪C`, an
identification of its forgotten sheaf with the set-valued direct image of the underlying structure
sheaf, and an actual direct-image-form structure-sheaf map `fSharp : 𝒪D ⟶ 𝒪f`, one can apply the
canonical Chapter 7 source-facing factorization to `f` and obtain replacement sites together with
a continuous functor `u : D' ⥤ C'` satisfying the site-theoretic hypotheses from the Chapter 7
factorization, transported ring sheaves on those sites, and a middle morphism of ringed sites
whose base is `u`. The compatibility of the middle structure-sheaf map with the original
`fSharp` is recorded by the canonical commutative square on underlying sheaves of sets. -/
@[stacks 03CR]
theorem exists_ringed_topos_site_factorization
    [HasWeakSheafify J (Type (max u v))]
    [HasWeakSheafify K (Type (max u v))] :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type u) (_ : Category.{v} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D'))),
          ∃ 𝒪C' : Sheaf J' RingCat,
            ∃ 𝒪D' : Sheaf K' RingCat,
            ∃ sourceTransport :
                (sourceFunctor.sheafPushforwardContinuous RingCat J J').obj 𝒪C' ≅ 𝒪C,
            ∃ targetTransport :
                (targetFunctor.sheafPushforwardContinuous RingCat K K').obj 𝒪D' ≅ 𝒪D,
            ∃ ψ : RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D',
              ψ.base = u ∧
                ∃ toposSq :
                    CatCommSq
                      (ψ.base.sheafPushforwardContinuous (Type (max u v)) K' J')
                      (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
                      (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
                      (f _*),
                  CommSq
                    (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).inv
                    ((sheafCompose K (forget RingCat.{max u v})).map fSharp)
                    ((targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K').map
                        ψ.underlyingDirectImageMap ≫
                      (toposSq.iso.app
                        (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪C'))).hom ≫
                      (f _*).map
                        (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom)
                    fPushforwardIso.hom := by
  obtain ⟨C', instC', J', hJ'Subcanonical, hC'FiniteLimits, sourceFunctor, hsource,
      D', instD', K', hK'Subcanonical, hD'FiniteLimits, targetFunctor, htarget,
      u, hu, huPullbacks, huTerminal, sq, _⟩ :=
    existsToposMorphismReductionCanonicalEmptyLocal (f := f)
  obtain ⟨𝒪C', sourceTransport⟩ :=
    transport_ring_sheaf_to_dense_subsite (J := J) (J' := J') (v := sourceFunctor) 𝒪C
  obtain ⟨𝒪D', targetTransport⟩ :=
    transport_ring_sheaf_to_dense_subsite (J := K) (J' := K') (v := targetFunctor) 𝒪D
  let toposSq :=
    reductionDirectImageSquare
      (f := f) (C' := C') (D' := D') (J' := J') (K' := K')
      (sourceFunctor := sourceFunctor) (targetFunctor := targetFunctor) (u := u) sq
  obtain ⟨φ, hφcomm⟩ :=
    existsMiddleStructureSheafMapOfReductionSquare
      (f := f) (fPushforwardIso := fPushforwardIso) (fSharp := fSharp)
      (sourceFunctor := sourceFunctor) (targetFunctor := targetFunctor) (u := u)
      (𝒪C' := 𝒪C') (𝒪D' := 𝒪D')
      sourceTransport targetTransport toposSq
  let ψ : RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D' :=
    ringedSiteHomOfBaseStructureSheafMap (u := u) 𝒪C' 𝒪D' φ
  -- Proof comment: once the middle ringed-site morphism exists, the theorem is just existential
  -- packaging of the Chapter 7 reduction data together with the transported ring sheaves.
  refine ⟨C', instC', J', hJ'Subcanonical, hC'FiniteLimits, sourceFunctor, hsource,
    D', instD', K', hK'Subcanonical, hD'FiniteLimits, targetFunctor, htarget,
    u, hu, huPullbacks, huTerminal, 𝒪C', 𝒪D', sourceTransport, targetTransport,
    ψ, rfl, toposSq, by
      simpa [ψ, underlyingDirectImageMapOfBaseStructureSheafMap] using hφcomm⟩

/-- Generalized companion to Lemma 18.7.2: after choosing additional families of set-valued sheaves
on the source and target topoi, the same factorization may be arranged so that their canonical
dense-subsite transports become representable on the replacement sites. This strengthening is
derived API on top of the source-facing ringed-topos factorization. -/
theorem exists_ringed_topos_site_factorization_with_representable_families
    [HasWeakSheafify J (Type (max u v))]
    [HasWeakSheafify K (Type (max u v))]
    (ℱ : I → Sheaf J (Type (max u v))) (𝒢 : G → Sheaf K (Type (max u v))) :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      (∀ i : I,
        (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
      ∃ (D' : Type u) (_ : Category.{v} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        (∀ j : G,
          (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable) ∧
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D'))),
          ∃ 𝒪C' : Sheaf J' RingCat,
            ∃ 𝒪D' : Sheaf K' RingCat,
            ∃ sourceTransport :
                (sourceFunctor.sheafPushforwardContinuous RingCat J J').obj 𝒪C' ≅ 𝒪C,
            ∃ targetTransport :
                (targetFunctor.sheafPushforwardContinuous RingCat K K').obj 𝒪D' ≅ 𝒪D,
            ∃ ψ : RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D',
              ψ.base = u ∧
                ∃ toposSq :
                    CatCommSq
                      (ψ.base.sheafPushforwardContinuous (Type (max u v)) K' J')
                      (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
                      (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K')
                      (f _*),
                  CommSq
                    (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).inv
                    ((sheafCompose K (forget RingCat.{max u v})).map fSharp)
                    ((targetFunctor.sheafPushforwardContinuous (Type (max u v)) K K').map
                        ψ.underlyingDirectImageMap ≫
                      (toposSq.iso.app
                        (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪C'))).hom ≫
                      (f _*).map
                        (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom)
                    fPushforwardIso.hom := by
  obtain ⟨C', instC', J', hJ'Subcanonical, hC'FiniteLimits, sourceFunctor, hsource,
      D', instD', K', hK'Subcanonical, hD'FiniteLimits, targetFunctor, htarget,
      u, hu, huPullbacks, huTerminal, sq, hrepr⟩ :=
    existsToposMorphismReductionCanonicalLocal (f := f) ℱ 𝒢
  rcases hrepr with ⟨hreprSource, hreprTarget⟩
  obtain ⟨𝒪C', sourceTransport⟩ :=
    transport_ring_sheaf_to_dense_subsite (J := J) (J' := J') (v := sourceFunctor) 𝒪C
  obtain ⟨𝒪D', targetTransport⟩ :=
    transport_ring_sheaf_to_dense_subsite (J := K) (J' := K') (v := targetFunctor) 𝒪D
  let toposSq :=
    reductionDirectImageSquare
      (f := f) (sourceFunctor := sourceFunctor) (targetFunctor := targetFunctor) (u := u) sq
  obtain ⟨φ, hφcomm⟩ :=
    existsMiddleStructureSheafMapOfReductionSquare
      (f := f) (fPushforwardIso := fPushforwardIso) (fSharp := fSharp)
      (sourceFunctor := sourceFunctor) (targetFunctor := targetFunctor) (u := u)
      (𝒪C' := 𝒪C') (𝒪D' := 𝒪D')
      sourceTransport targetTransport toposSq
  let ψ : RingedSite.ofRingSheaf J' 𝒪C' ⟶ RingedSite.ofRingSheaf K' 𝒪D' :=
    ringedSiteHomOfBaseStructureSheafMap (u := u) 𝒪C' 𝒪D' φ
  -- Proof comment: the representability clauses come from the Chapter 7 reduction, while the
  -- shared ringed helper supplies the middle morphism and the compatibility square.
  refine ⟨C', instC', J', hJ'Subcanonical, hC'FiniteLimits, sourceFunctor, hsource,
    hreprSource, D', instD', K', hK'Subcanonical, hD'FiniteLimits, targetFunctor, htarget,
    hreprTarget, u, hu, huPullbacks, huTerminal, 𝒪C', 𝒪D', sourceTransport, targetTransport,
    ψ, rfl, toposSq, by
      simpa [ψ, underlyingDirectImageMapOfBaseStructureSheafMap] using hφcomm⟩

/-- Helper for Lemma 18.7.2: on a common replacement site for an equivalence of topoi, the
remaining gap is to transport the target structure sheaf to the common site so that the identity
ringed-site morphism realizes the original ringed equivalence on underlying direct images. -/
private theorem existsCommonRingedTransportOfCommonSiteFactorization
    {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'}
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    (targetFunctor : D ⥤ C') [targetFunctor.IsDenseSubsite K J']
    (toposIso :
      f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type (max u v)) J J' ≅
        targetFunctor.sheafPushforwardCocontinuous (Type (max u v)) K J')
    (𝒪' : Sheaf J' RingCat)
    (sourceTransport :
      (sourceFunctor.sheafPushforwardContinuous RingCat J J').obj 𝒪' ≅ 𝒪C)
    [Functor.IsEquivalence (f⁻¹)] [IsIso fSharp] :
    ∃ targetTransport :
        (targetFunctor.sheafPushforwardContinuous RingCat K J').obj 𝒪' ≅ 𝒪D,
      ∃ toposSq :
          CatCommSq
            ((RingedSite.Hom.id (RingedSite.ofRingSheaf J' 𝒪')).base.sheafPushforwardContinuous
              (Type (max u v)) J' J')
            (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
            (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K J')
            (f _*),
        CommSq
          (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).inv
          ((sheafCompose K (forget RingCat.{max u v})).map fSharp)
          ((targetFunctor.sheafPushforwardContinuous (Type (max u v)) K J').map
              (underlyingDirectImageMap (RingedSite.Hom.id (RingedSite.ofRingSheaf J' 𝒪'))) ≫
            (toposSq.iso.app
              (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪'))).hom ≫
            (f _*).map
              (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom)
          fPushforwardIso.hom := by
  -- Route correction: the common-site factorization already reduces the underlying equivalence to
  -- one site; what remains is the same missing RingCat-valued comparison, now specialized to the
  -- identity morphism of the common ringed site.
  -- Route correction: the inverse-image-side RingCat adjunction route would need extra
  -- `HasWeakSheafify`/Kan-extension data for `RingCat`, so the missing bridge must instead be a
  -- direct pushforward comparison on `𝒪'`.
  -- TODO: convert `toposIso` to the needed direct-image square, identify the transported target
  -- sheaf with `𝒪'` through the ring-valued comparison, and then simplify the identity map case.
  sorry

/-- If a morphism of ringed topoi is an equivalence, formalized by an equivalence of inverse-image
functors together with a `RingCat`-valued direct-image realization `𝒪f` of `𝒪C`, an isomorphism
`fSharp : 𝒪D ⟶ 𝒪f` on structure sheaves, and the identification of the forgotten sheaf of `𝒪f`
with the set-valued direct image, then the Chapter 7 factorization may be chosen over a common
replacement site with a single common transported structure sheaf. The middle ringed-site morphism
is explicitly the identity on that common ringed site, and the direct-image square on underlying
sheaves is recorded by the canonical commutative square comparing this identity factorization with
the forgotten image of the original `fSharp`. -/
theorem exists_common_ringed_topos_site_factorization_of_isRingedEquivalence
    [(f⁻¹).IsEquivalence] [IsIso fSharp] :
    ∃ (C' : Type u) (_ : Category.{v} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J'),
      ∃ 𝒪' : Sheaf J' RingCat,
      ∃ sourceTransport :
          (sourceFunctor.sheafPushforwardContinuous RingCat J J').obj 𝒪' ≅ 𝒪C,
      ∃ targetTransport :
          (targetFunctor.sheafPushforwardContinuous RingCat K J').obj 𝒪' ≅ 𝒪D,
      ∃ toposSq :
          CatCommSq
            ((RingedSite.Hom.id (RingedSite.ofRingSheaf J' 𝒪')).base.sheafPushforwardContinuous
              (Type (max u v)) J' J')
            (sourceFunctor.sheafPushforwardContinuous (Type (max u v)) J J')
            (targetFunctor.sheafPushforwardContinuous (Type (max u v)) K J')
            (f _*),
        CommSq
          (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).inv
          ((sheafCompose K (forget RingCat.{max u v})).map fSharp)
          ((targetFunctor.sheafPushforwardContinuous (Type (max u v)) K J').map
              (underlyingDirectImageMap (RingedSite.Hom.id (RingedSite.ofRingSheaf J' 𝒪'))) ≫
            (toposSq.iso.app
              (underlyingStructureSheaf (RingedSite.ofRingSheaf J' 𝒪'))).hom ≫
            (f _*).map
              (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom)
          fPushforwardIso.hom := by
  -- Route correction: the intended route is to first obtain the common-site square, then apply the
  -- canonical cocontinuous comparison theorem, and finally use
  -- `existsCommonRingedTransportOfCommonSiteFactorization`.
  -- TODO: the current elaborator timeout occurs while instantiating that common-site comparison,
  -- so the proof is left at the minimal structural blocker.
  sorry

end

end CategoryTheory
