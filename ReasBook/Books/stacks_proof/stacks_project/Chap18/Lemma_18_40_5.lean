import Mathlib
import stacks_proof.stacks_project.Chap07.Definition_7_14_1
import stacks_proof.stacks_project.Chap07.Lemma_7_44_2
import stacks_proof.stacks_project.Chap18.Definition_18_7_1
import stacks_proof.stacks_project.Chap18.Definition_18_31_1
import stacks_proof.stacks_project.Chap18.Lemma_18_40_1
import stacks_proof.stacks_project.Chap18.Lemma_18_40_2
import stacks_proof.stacks_project.Chap18.Definition_18_40_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped RingedSite.Hom

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 18.40.5:
- primary domain: locally ringed commutative ringed sites under inverse image and equivalence;
- sampled owner declarations:
  `IsMorphismOfSites`,
  `IsLocallyRingedSite`,
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.IsRingedEquivalence`,
  `RingedSite.Hom.toMorphismOfTopoi`;
- best owner abstraction:
  the source-facing inverse-image clause belongs on the site-morphism owner
  `IsMorphismOfSites J K F`, while the equivalence case is naturally owned by a bundled morphism
  `f : RingedSite.ofCommRingSheaf J 𝒪 ⟶ RingedSite.ofCommRingSheaf K 𝒪'`
  together with the bundled ringed-equivalence class on `f`, while the raw inverse-image statement
  for a site morphism remains the source-facing owner for the non-equivalence case, and the
  site-presented equivalence statement belongs to the bridge layer only after assuming the induced
  inverse-image functor on sheaves is an equivalence;
- primitive data:
  for part (1), the site morphism `IsMorphismOfSites J K F` and the commutative structure sheaf
  `𝒪`;
  for part (2), the bundled ringed-site morphism `f` and its ringed-equivalence structure;
- derived API:
  transport across a structure-sheaf isomorphism, preservation of local ringedness by inverse
  image, and the site-presented bridge theorem with an equivalence hypothesis on the induced
  inverse-image functor on sheaves.

Source/core/bridge triage:
- `source-facing`: the inverse-image preservation statement of part (1);
- `core/canonical`: `IsLocallyRingedSite`;
- `bridge/view`: `RingedSite.ofCommRingSheaf` and the bundled ringed-equivalence class on a
  ringed-site morphism for the equivalence case, together with the site-presented
  inverse-image-equivalence bridge theorem.
-/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 18.40.5: the sheafification of the empty presheaf is an initial sheaf. -/
private noncomputable def emptySheafification_isInitial :
    Limits.IsInitial
      ((presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) := by
  let S : Sheaf J (Type (max u v)) :=
    (presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  letI : ∀ Y : Sheaf J (Type (max u v)), Unique (S ⟶ Y) :=
    fun Y ↦
      { default :=
          ((sheafificationAdjunction J (Type (max u v))).homEquiv
            (⊥_ (Cᵒᵖ ⥤ Type (max u v))) Y).symm
            (Limits.initial.to ((sheafToPresheaf J (Type (max u v))).obj Y))
        uniq := fun f ↦ by
          apply
            ((sheafificationAdjunction J (Type (max u v))).homEquiv
              (⊥_ (Cᵒᵖ ⥤ Type (max u v))) Y).injective
          exact Limits.IsInitial.hom_ext Limits.initialIsInitial _ _ }
  -- Proof comment: an object with a unique arrow to every target is initial.
  exact Limits.IsInitial.ofUnique S

/-- Helper for Lemma 18.40.5: the underlying sheaf isomorphism of commutative structure sheaves
transports the zero section. -/
private theorem zeroSection_eq_comp_underlyingIso_hom
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    zeroSection 𝒪' =
      zeroSection 𝒪 ≫
        (Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).hom := by
  -- Proof comment: the underlying sheaf isomorphism sends the zero section to the zero section
  -- pointwise on every object.
  ext U x
  change (0 : 𝒪'.obj.obj U) =
    ((Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).hom.hom.app U)
      (0 : 𝒪.obj.obj U)
  symm
  simpa using RingHom.map_zero ((e.hom.hom.app U).hom)

/-- Helper for Lemma 18.40.5: the underlying sheaf isomorphism of commutative structure sheaves
transports the unit section. -/
private theorem oneSection_eq_comp_underlyingIso_hom
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    oneSection 𝒪' =
      oneSection 𝒪 ≫
        (Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).hom := by
  -- Proof comment: the same pointwise argument works for the unit section.
  ext U x
  change (1 : 𝒪'.obj.obj U) =
    ((Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).hom.hom.app U)
      (1 : 𝒪.obj.obj U)
  symm
  simpa using RingHom.map_one ((e.hom.hom.app U).hom)

/-- Helper for Lemma 18.40.5: an isomorphism of commutative structure sheaves identifies the
zero-one equalizers appearing in `18.40.2.1`. -/
private noncomputable def oneNeverZeroEqualizerIso
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    Limits.equalizer (zeroSection 𝒪) (oneSection 𝒪) ≅
      Limits.equalizer (zeroSection 𝒪') (oneSection 𝒪') := by
  refine
    { hom := Limits.equalizer.lift (Limits.equalizer.ι (zeroSection 𝒪) (oneSection 𝒪)) ?_
      inv := Limits.equalizer.lift (Limits.equalizer.ι (zeroSection 𝒪') (oneSection 𝒪')) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Proof comment: the equalizer condition is stable after postcomposing with the
    -- underlying sheaf isomorphism.
    simpa [zeroSection_eq_comp_underlyingIso_hom (J := J) e,
      oneSection_eq_comp_underlyingIso_hom (J := J) e, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).hom)
      (Limits.equalizer.condition (zeroSection 𝒪) (oneSection 𝒪))
  · -- Proof comment: the inverse direction is the same transport applied to `e.symm`.
    simpa [zeroSection_eq_comp_underlyingIso_hom (J := J) e.symm,
      oneSection_eq_comp_underlyingIso_hom (J := J) e.symm, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (Functor.mapIso (sheafCompose J (forget CommRingCat.{max u v})) e).inv)
      (Limits.equalizer.condition (zeroSection 𝒪') (oneSection 𝒪'))
  · -- Proof comment: both composites have the same projection to the equalizer source.
    apply Limits.equalizer.hom_ext
    simp [Category.assoc, Limits.equalizer.lift_ι]
  · -- Proof comment: the opposite composite is checked by the same equalizer-extensionality step.
    apply Limits.equalizer.hom_ext
    simp [Category.assoc, Limits.equalizer.lift_ι]

/-- Helper for Lemma 18.40.5: the locally ringed-site condition is preserved under an isomorphism
of commutative structure sheaves on a fixed site. -/
private theorem isLocallyRingedSite_of_iso
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪')
    [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite 𝒪' := by
  letI : IsIso (oneNeverZeroEqualizerMap 𝒪') := by
    -- Proof comment: the empty sheafification is initial, so the transported equalizer map is the
    -- canonical map for `𝒪'`, and hence inherits `IsIso`.
    have hcomp :
        oneNeverZeroEqualizerMap 𝒪 ≫ (oneNeverZeroEqualizerIso (J := J) e).hom =
          oneNeverZeroEqualizerMap 𝒪' :=
      (emptySheafification_isInitial (J := J)).hom_ext _ _
    have hIso :
        IsIso (oneNeverZeroEqualizerMap 𝒪 ≫ (oneNeverZeroEqualizerIso (J := J) e).hom) := by
      infer_instance
    simpa [hcomp] using hIso
  letI : HasLocalUnitDichotomy J 𝒪' := by
    refine
      { local_unit_dichotomy := fun U f ↦ ?_ }
    let g : 𝒪.obj.obj (op U) := ((e.inv.hom.app (op U)).hom) f
    -- Proof comment: pull the section back along `e.inv`, use the dichotomy on `𝒪`, and then map
    -- the resulting local unit information forward along the ring isomorphism `e.hom`.
    obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) U g
    refine ⟨S, ?_⟩
    intro I
    have hfg :
        ((e.hom.hom.app (op I.Y)).hom) (((𝒪.obj.map I.f.op).hom) g) =
          ((𝒪'.obj.map I.f.op).hom) f := by
      have hnat := congrArg (fun k ↦ k.hom f) (e.hom.hom.naturality I.f.op)
      have hinv :=
        congrArg (fun k ↦ k.hom f) (e.hom_inv_id_app (op U))
      simpa [g] using hnat.trans hinv
    rcases hS I with hI | hI
    · left
      rw [← hfg]
      exact RingHom.isUnit_map ((e.hom.hom.app (op I.Y)).hom) hI
    · right
      have hfgOneSub :
          ((e.hom.hom.app (op I.Y)).hom) (1 - ((𝒪.obj.map I.f.op).hom) g) =
            1 - ((𝒪'.obj.map I.f.op).hom) f := by
        simpa [hfg] using
          RingHom.map_sub ((e.hom.hom.app (op I.Y)).hom) 1 (((𝒪.obj.map I.f.op).hom) g)
      rw [← hfgOneSub]
      exact RingHom.isUnit_map ((e.hom.hom.app (op I.Y)).hom) hI
  -- Proof comment: the two transported owner instances reassemble the locally ringed-site
  -- structure on the fixed site.
  exact instIsLocallyRingedSiteOfConditions (J := J) (𝒪 := 𝒪')

/-- Being locally ringed depends only on the isomorphism class of the commutative structure sheaf
on a fixed site. -/
-- Proof sketch: transport the two defining clauses of `IsLocallyRingedSite` across the sheaf
-- isomorphism. The equalizer/empty-cover condition and the local unit dichotomy are both stated
-- purely in terms of sections and restriction maps, so they are preserved under objectwise ring
-- isomorphisms induced by `e`.
theorem isLocallyRingedSite_iff_of_iso
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := by
  constructor
  · intro h
    letI : IsLocallyRingedSite 𝒪 := h
    -- Proof comment: the forward direction is the dedicated transport helper above.
    exact isLocallyRingedSite_of_iso (J := J) e
  · intro h
    letI : IsLocallyRingedSite 𝒪' := h
    -- Proof comment: the reverse implication is the same transport applied to the inverse isomorphism.
    simpa using (isLocallyRingedSite_of_iso (J := J) e.symm)

end

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [IsMorphismOfSites J K F]
variable [((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).IsRightAdjoint)]

/-- Helper for Lemma 18.40.5: inverse image sends the empty sheafification to an initial sheaf. -/
private noncomputable def pullbackEmptySheafification_isInitial :
    Limits.IsInitial
      ((F.sheafPullback (Type (max u v)) J K).obj
        ((presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))))) := by
  let S : Sheaf J (Type (max u v)) :=
    (presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  let T : Sheaf K (Type (max u v)) :=
    (F.sheafPullback (Type (max u v)) J K).obj S
  letI : ∀ Y : Sheaf K (Type (max u v)), Unique (T ⟶ Y) :=
    fun Y ↦
      { default :=
          ((F.sheafAdjunctionContinuous (Type (max u v)) J K).homEquiv S Y).symm
            ((emptySheafification_isInitial (J := J)).to
              ((F.sheafPushforwardContinuous (Type (max u v)) J K).obj Y))
        uniq := fun f ↦ by
          apply ((F.sheafAdjunctionContinuous (Type (max u v)) J K).homEquiv S Y).injective
          exact (emptySheafification_isInitial (J := J)).hom_ext _ _ }
  -- Proof comment: the inverse-image functor is a left adjoint, so it preserves the initial
  -- sheafification of the empty presheaf.
  exact Limits.IsInitial.ofUnique T

/-- Helper for Lemma 18.40.5: inverse image preserves the `18.40.2.1` equalizer-isomorphism
clause of `IsLocallyRingedSite`. -/
private theorem pullbackOneNeverZeroEqualizerMap_isIso
    {𝒪 : Sheaf J CommRingCat.{max u v}} [IsIso (oneNeverZeroEqualizerMap 𝒪)] :
    IsIso (oneNeverZeroEqualizerMap ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) := by
  -- Proof comment: compare the pulled-back source via the sheafification comparison, compare the
  -- pulled-back target via equalizer preservation, and then use initiality of the empty
  -- sheafification to identify the transported map with the canonical pulled-back equalizer map.
  let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
    F.sheafPullback (Type (max u v)) J K
  letI :
      IsIso (F.pushforwardContinuousSheafificationComparison J K) :=
    Functor.pushforwardContinuousSheafificationComparison_isIso (G := F) (J := J) (K := K)
  let emptyRestrictionIso :
      (F.op ⋙ (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) ≅
        (⊥_ (Dᵒᵖ ⥤ Type (max u v))) :=
    Limits.PreservesInitial.iso
      ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (Type (max u v))).obj F.op)
  let α :
      (presheafToSheaf K (Type (max u v))).obj
          (⊥_ (Dᵒᵖ ⥤ Type (max u v))) ≅
        FType.obj ((presheafToSheaf J (Type (max u v))).obj
          (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) := by
    exact
      (Functor.mapIso (presheafToSheaf K (Type (max u v))) emptyRestrictionIso).symm ≪≫
        (asIso (F.pushforwardContinuousSheafificationComparison J K)).app
          (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  let β :
      FType.obj (Limits.equalizer (zeroSection 𝒪) (oneSection 𝒪)) ≅
        Limits.equalizer
          (zeroSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪))
          (oneSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) := by
    simpa [FType] using
      (Limits.PreservesEqualizer.iso FType (zeroSection 𝒪) (oneSection 𝒪))
  let m :
      (presheafToSheaf K (Type (max u v))).obj
          (⊥_ (Dᵒᵖ ⥤ Type (max u v))) ⟶
        Limits.equalizer
          (zeroSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪))
          (oneSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) :=
    α.hom ≫ FType.map (oneNeverZeroEqualizerMap 𝒪) ≫ β.hom
  have hMap : IsIso (FType.map (oneNeverZeroEqualizerMap 𝒪)) := by
    exact Functor.map_isIso FType (oneNeverZeroEqualizerMap 𝒪)
  have hmIso : IsIso m := by
    dsimp [m]
    infer_instance
  have hm :
      m = oneNeverZeroEqualizerMap ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
    (pullbackEmptySheafification_isInitial (F := F) (J := J) (K := K)).hom_ext _ _
  simpa [m, hm] using hmIso

/-- Helper for Lemma 18.40.5: inverse image transports the public
`binaryFactorizationMap` across the canonical coproduct and product comparison isomorphisms. -/
private theorem pullbackBinaryFactorizationMapComparison
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
      F.sheafPullback (Type (max u v)) J K
    let FComm : Sheaf J CommRingCat.{max u v} ⥤ Sheaf K CommRingCat.{max u v} :=
      F.sheafPullback CommRingCat.{max u v} J K
    let O : Sheaf J (Type (max u v)) :=
      (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪
    let O' : Sheaf K (Type (max u v)) :=
      (sheafCompose K (forget CommRingCat.{max u v})).obj (FComm.obj 𝒪)
    let σ : FType.obj ((O ⨯ O) ⨿ (O ⨯ O)) ≅ (O' ⨯ O') ⨿ (O' ⨯ O') := by
      simpa [FType, FComm, O, O'] using
        (Limits.PreservesColimitPair.iso FType (O ⨯ O) (O ⨯ O)).symm
    let τ : FType.obj (O ⨯ O) ≅ O' ⨯ O' := by
      simpa [FType, FComm, O, O'] using
        (Limits.PreservesLimitPair.iso FType O O)
    FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom =
      σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪) := by
  let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
    F.sheafPullback (Type (max u v)) J K
  let FComm : Sheaf J CommRingCat.{max u v} ⥤ Sheaf K CommRingCat.{max u v} :=
    F.sheafPullback CommRingCat.{max u v} J K
  let O : Sheaf J (Type (max u v)) :=
    (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪
  let O' : Sheaf K (Type (max u v)) :=
    (sheafCompose K (forget CommRingCat.{max u v})).obj (FComm.obj 𝒪)
  let σ : FType.obj ((O ⨯ O) ⨿ (O ⨯ O)) ≅ (O' ⨯ O') ⨿ (O' ⨯ O') := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesColimitPair.iso FType (O ⨯ O) (O ⨯ O)).symm
  let τ : FType.obj (O ⨯ O) ≅ O' ⨯ O' := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesLimitPair.iso FType O O)
  have hcore :
      σ.inv ≫ FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom =
        binaryFactorizationMap (FComm.obj 𝒪) := by
    -- Proof comment: normalize the transported source and target, then check the left and right
    -- branches componentwise.
    apply coprod.hom_ext
    · apply prod.hom_ext
      · ext U x
        simp [σ, τ, binaryFactorizationMap, Category.assoc]
      · ext U x
        rfl
    · apply prod.hom_ext
      · ext U x
        simp [σ, τ, binaryFactorizationMap, Category.assoc]
      · ext U x
        rfl
  -- Proof comment: reinsert the source comparison isomorphism to recover the owner-level
  -- conjugation statement.
  calc
    FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom =
        σ.hom ≫ (σ.inv ≫ FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom) := by
          symm
          simpa [σ, Category.assoc] using
            (Iso.hom_inv_id_assoc σ (FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom))
    _ = σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪) := by rw [hcore]

/-- Helper for Lemma 18.40.5: inverse image preserves the local unit dichotomy by transporting the
categorical witness `binaryFactorizationMap` and its local surjectivity. -/
private theorem pullbackHasLocalUnitDichotomy
    {𝒪 : Sheaf J CommRingCat.{max u v}} [HasLocalUnitDichotomy J 𝒪] :
    HasLocalUnitDichotomy K ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) := by
  let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
    F.sheafPullback (Type (max u v)) J K
  let FComm : Sheaf J CommRingCat.{max u v} ⥤ Sheaf K CommRingCat.{max u v} :=
    F.sheafPullback CommRingCat.{max u v} J K
  let O : Sheaf J (Type (max u v)) :=
    (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪
  let O' : Sheaf K (Type (max u v)) :=
    (sheafCompose K (forget CommRingCat.{max u v})).obj (FComm.obj 𝒪)
  let σ : FType.obj ((O ⨯ O) ⨿ (O ⨯ O)) ≅ (O' ⨯ O') ⨿ (O' ⨯ O') := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesColimitPair.iso FType (O ⨯ O) (O ⨯ O)).symm
  let τ : FType.obj (O ⨯ O) ≅ O' ⨯ O' := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesLimitPair.iso FType O O)
  letI : FType.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_map_exact FType
      (isMorphismOfSites_sheafPullback_exact (u := F))
  have hLoc :
      Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) := by
    -- Proof comment: Lemma `18.40.1` identifies local unit dichotomy with sectionwise local
    -- factorization for `binaryFactorizationMap`.
    rw [isLocallySurjective_binaryFactorizationMap_iff]
    exact local_factorization_of_local_unit_dichotomy (J := J) (𝒪 := 𝒪)
  have hMapComp : Epi (FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom) := by
    letI : Epi (binaryFactorizationMap 𝒪) :=
      (Sheaf.isLocallySurjective_iff_epi (binaryFactorizationMap 𝒪)).1 hLoc
    infer_instance
  have hTransport : Epi (σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪)) := by
    simpa [σ, τ, Category.assoc] using
      (show Epi (FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom) from hMapComp)
  have hPulled : Epi (binaryFactorizationMap (FComm.obj 𝒪)) := by
    have : Epi (σ.inv ≫ (σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪))) := by
      infer_instance
    simpa [Category.assoc] using this
  -- Proof comment: convert the transported epimorphism back to local surjectivity and invoke the
  -- converse direction from Lemma `18.40.2`.
  exact hasLocalUnitDichotomy_of_binaryFactorizationMap_isLocallySurjective
    (J := K) (𝒪 := FComm.obj 𝒪)
    ((Sheaf.isLocallySurjective_iff_epi
      (binaryFactorizationMap (FComm.obj 𝒪))).2 hPulled)

/-- Helper for Lemma 18.40.5: if the pulled-back `18.40.2.1` equalizer map is an isomorphism and
the inverse-image functor is an equivalence, then the original equalizer map is an isomorphism. -/
private theorem reflectOneNeverZeroEqualizerMapIsIso
    [Functor.IsEquivalence (F.sheafPullback (Type (max u v)) J K)]
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [IsIso (oneNeverZeroEqualizerMap ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪))] :
    IsIso (oneNeverZeroEqualizerMap 𝒪) := by
  let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
    F.sheafPullback (Type (max u v)) J K
  letI : FType.ReflectsIsomorphisms := by
    infer_instance
  letI :
      IsIso (F.pushforwardContinuousSheafificationComparison J K) :=
    Functor.pushforwardContinuousSheafificationComparison_isIso (G := F) (J := J) (K := K)
  let emptyRestrictionIso :
      (F.op ⋙ (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) ≅
        (⊥_ (Dᵒᵖ ⥤ Type (max u v))) :=
    Limits.PreservesInitial.iso
      ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (Type (max u v))).obj F.op)
  let α :
      (presheafToSheaf K (Type (max u v))).obj
          (⊥_ (Dᵒᵖ ⥤ Type (max u v))) ≅
        FType.obj ((presheafToSheaf J (Type (max u v))).obj
          (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) := by
    exact
      (Functor.mapIso (presheafToSheaf K (Type (max u v))) emptyRestrictionIso).symm ≪≫
        (asIso (F.pushforwardContinuousSheafificationComparison J K)).app
          (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  let β :
      FType.obj (Limits.equalizer (zeroSection 𝒪) (oneSection 𝒪)) ≅
        Limits.equalizer
          (zeroSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪))
          (oneSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) := by
    simpa [FType] using
      (Limits.PreservesEqualizer.iso FType (zeroSection 𝒪) (oneSection 𝒪))
  let m :
      (presheafToSheaf K (Type (max u v))).obj
          (⊥_ (Dᵒᵖ ⥤ Type (max u v))) ⟶
        Limits.equalizer
          (zeroSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪))
          (oneSection ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) :=
    α.hom ≫ FType.map (oneNeverZeroEqualizerMap 𝒪) ≫ β.hom
  have hm :
      m = oneNeverZeroEqualizerMap ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
    (pullbackEmptySheafification_isInitial (F := F) (J := J) (K := K)).hom_ext _ _
  have hmIso : IsIso m := by
    simpa [m, hm]
  have hMap : IsIso (FType.map (oneNeverZeroEqualizerMap 𝒪)) := by
    have : IsIso (α.inv ≫ m ≫ β.inv) := by
      infer_instance
    simpa [m, Category.assoc] using this
  -- Proof comment: once the mapped equalizer map is an isomorphism, the equivalence reflects it
  -- back to the original site.
  exact isIso_of_reflects_iso (oneNeverZeroEqualizerMap 𝒪) FType

/-- Helper for Lemma 18.40.5: if the pulled-back structure sheaf has the local unit dichotomy and
the inverse-image functor is an equivalence, then the original structure sheaf does too. -/
private theorem reflectHasLocalUnitDichotomy
    [Functor.IsEquivalence (F.sheafPullback (Type (max u v)) J K)]
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [HasLocalUnitDichotomy K ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)] :
    HasLocalUnitDichotomy J 𝒪 := by
  let FType : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)) :=
    F.sheafPullback (Type (max u v)) J K
  let FComm : Sheaf J CommRingCat.{max u v} ⥤ Sheaf K CommRingCat.{max u v} :=
    F.sheafPullback CommRingCat.{max u v} J K
  let O : Sheaf J (Type (max u v)) :=
    (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪
  let O' : Sheaf K (Type (max u v)) :=
    (sheafCompose K (forget CommRingCat.{max u v})).obj (FComm.obj 𝒪)
  let σ : FType.obj ((O ⨯ O) ⨿ (O ⨯ O)) ≅ (O' ⨯ O') ⨿ (O' ⨯ O') := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesColimitPair.iso FType (O ⨯ O) (O ⨯ O)).symm
  let τ : FType.obj (O ⨯ O) ≅ O' ⨯ O' := by
    simpa [FType, FComm, O, O'] using
      (Limits.PreservesLimitPair.iso FType O O)
  letI : FType.ReflectsEpimorphisms := by
    infer_instance
  have hPulled :
      Sheaf.IsLocallySurjective (binaryFactorizationMap (FComm.obj 𝒪)) := by
    -- Proof comment: the pulled-back local unit dichotomy gives the local-surjectivity criterion
    -- from Lemma `18.40.1`.
    rw [isLocallySurjective_binaryFactorizationMap_iff]
    exact local_factorization_of_local_unit_dichotomy (J := K) (𝒪 := FComm.obj 𝒪)
  have hComp : Epi (σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪)) := by
    letI : Epi (binaryFactorizationMap (FComm.obj 𝒪)) :=
      (Sheaf.isLocallySurjective_iff_epi
        (binaryFactorizationMap (FComm.obj 𝒪))).1 hPulled
    infer_instance
  have hMapComp : Epi (FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom) := by
    simpa [σ, τ, Category.assoc] using
      (show Epi (σ.hom ≫ binaryFactorizationMap (FComm.obj 𝒪)) from hComp)
  have hMap : Epi (FType.map (binaryFactorizationMap 𝒪)) := by
    have : Epi ((FType.map (binaryFactorizationMap 𝒪) ≫ τ.hom) ≫ τ.inv) := by
      infer_instance
    simpa [Category.assoc] using this
  have hOrig : Epi (binaryFactorizationMap 𝒪) :=
    Functor.epi_of_epi_map FType hMap
  -- Proof comment: reflect the epi of the mapped categorical witness and translate it back to the
  -- owner `HasLocalUnitDichotomy`.
  exact hasLocalUnitDichotomy_of_binaryFactorizationMap_isLocallySurjective
    (J := J) (𝒪 := 𝒪)
    ((Sheaf.isLocallySurjective_iff_epi (binaryFactorizationMap 𝒪)).2 hOrig)

-- Proof sketch: pull back the two defining clauses of `IsLocallyRingedSite J 𝒪` along the exact
-- inverse-image functor `F.sheafPullback CommRingCat J K`. Exactness preserves the empty sheaf,
-- the terminal sheaf, equalizers, products, isomorphisms, and epimorphisms, so the
-- `0 = 1`-implies-empty condition and the local unit dichotomy descend to the inverse-image
-- structure sheaf.
/-- Lemma 18.40.5 (1): for a site-presented morphism of topoi with inverse image induced by a
site morphism `F : \mathcal C \to \mathcal C'`, if `(\mathcal C, \mathcal O)` is locally ringed,
then `(\mathcal C', F^{-1}\mathcal O)` is locally ringed. -/
@[stacks 04H7]
theorem pullback_isLocallyRingedSite
    {𝒪 : Sheaf J CommRingCat.{max u v}} [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) := by
  -- Route correction: the fixed-site transport theorem above already handles sheaf isomorphisms,
  -- so the remaining work here is owner-level transport along `F.sheafPullback`.
  letI : IsIso (oneNeverZeroEqualizerMap ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)) :=
    pullbackOneNeverZeroEqualizerMap_isIso (F := F)
  letI : HasLocalUnitDichotomy K ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
    pullbackHasLocalUnitDichotomy (F := F)
  -- Proof comment: the transported equalizer clause and the transported local-unit clause are
  -- exactly the two defining ingredients of `IsLocallyRingedSite`.
  exact instIsLocallyRingedSiteOfConditions
    (J := K) (𝒪 := (F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪)

-- Proof sketch: combine the equivalence hypothesis on the induced inverse-image functor on
-- sheaves with the structure-sheaf isomorphism `α`, then apply the bundled owner theorem
-- `RingedSite.Hom.isLocallyRingedSite_iff_of_isRingedEquivalence` after packaging this data into
-- the corresponding site-presented ringed-topos equivalence.
/-- Lemma 18.40.5 (2), bridge form: for a site-presented equivalence of ringed topoi whose
induced inverse-image functor on sheaves is an equivalence and whose inverse-image structure sheaf
`F^{-1}\mathcal O` is identified with `\mathcal O'`, the locally ringed property is equivalent
for `(\mathcal C, \mathcal O)` and `(\mathcal C', \mathcal O')`. -/
@[stacks 04H7]
theorem isLocallyRingedSite_iff_of_inverseImage_isEquivalence
    [Functor.IsEquivalence (F.sheafPullback (Type (max u v)) J K)]
    {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒪' : Sheaf K CommRingCat.{max u v}}
    (α : (F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪 ≅ 𝒪') :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := by
  constructor
  · intro h
    letI : IsLocallyRingedSite 𝒪 := h
    have hPull :
        IsLocallyRingedSite ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
      pullback_isLocallyRingedSite (F := F)
    -- Proof comment: once the inverse image is locally ringed, the fixed-site sheaf isomorphism
    -- `α` transfers the condition to `𝒪'`.
    exact (isLocallyRingedSite_iff_of_iso (J := K) α).1 hPull
  · intro h
    letI : IsLocallyRingedSite 𝒪' := h
    have hPull :
        IsLocallyRingedSite ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
      (isLocallyRingedSite_iff_of_iso (J := K) α).2 h
    letI :
        IsLocallyRingedSite ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) :=
      hPull
    letI : IsIso (oneNeverZeroEqualizerMap 𝒪) :=
      reflectOneNeverZeroEqualizerMapIsIso (F := F)
    letI : HasLocalUnitDichotomy J 𝒪 :=
      reflectHasLocalUnitDichotomy (F := F)
    -- Proof comment: after transferring `𝒪'` to the actual pullback sheaf via `α`, the inverse
    -- image equivalence reflects the two defining clauses back to `𝒪`.
    exact instIsLocallyRingedSiteOfConditions (J := J) (𝒪 := 𝒪)

end

end CategoryTheory

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒪' : Sheaf K CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf K 𝒪'

-- Proof sketch: rewrite the bundled equivalence as the site-presented inverse-image statement for
-- `f.base`, using the inverse-image-form structure-sheaf isomorphism `f^♯`.
/-- Lemma 18.40.5 (2), owner form: a bundled equivalence of commutative ringed sites preserves and
reflects the locally ringed property. -/
@[stacks 04H7]
theorem isLocallyRingedSite_iff_of_isRingedEquivalence
    (f : X ⟶ Y) [f.IsRingedEquivalence] :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := by
  -- Proof comment: this is exactly the site-level inverse-image equivalence theorem applied to the
  -- underlying site morphism `f.base` and the inverse-image-form structure-sheaf isomorphism.
  simpa using
    (CategoryTheory.isLocallyRingedSite_iff_of_inverseImage_isEquivalence
      (F := f.base) (J := K) (K := J)
      (α := asIso (RingedSite.Hom.inverseImageStructureSheafMap f))).symm

end

end RingedSite.Hom
