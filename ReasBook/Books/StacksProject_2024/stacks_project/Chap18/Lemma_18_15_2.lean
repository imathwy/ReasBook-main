import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap07.Proposition_7_44_3
import StacksProject_2024.Chap18.Lemma_18_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v w

namespace CategoryTheory.Functor

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.2:
- primary domain: exactness criteria for direct-image functors on sheaves of abelian groups,
  together with site presentations of morphisms of topoi;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `exactFunctor`,
  `MorphismOfTopoiIn.presentationFunctor_pushforwardIso`;
- best owner abstraction:
  the canonical abelian direct-image owner for a presentation is
  `u.sheafPushforwardContinuous AddCommGrpCat J K`;
- source/core/bridge triage:
  `source-facing`: the Stacks exactness criterion for abelian direct image and its presented form;
  `core/canonical`: `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat J K)`;
  `bridge/view`: the presentation isomorphism on underlying sheaves of sets.
-/

section ExactnessCriterion

variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [HasSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

omit [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})] in
/-- Helper for Lemma 18.15.2: local surjectivity of an additive-sheaf morphism survives after
forgetting the additive structure. -/
lemma underlyingLocallySurjectiveOfAdditiveSheafMap
    {X Y : Sheaf K AddCommGrpCat.{w}} (φ : X ⟶ Y)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Sheaf.IsLocallySurjective ((sheafCompose K (forget AddCommGrpCat.{w})).map φ) := by
  -- Proof comment: forgetting additive structure does not change the underlying image sieve.
  change Presheaf.IsLocallySurjective K
    (Functor.whiskerRight φ.hom (forget AddCommGrpCat.{w}))
  change Presheaf.IsLocallySurjective K φ.hom at hφ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro U s
  simpa [Presheaf.imageSieve] using hφ.imageSieve_mem (U := U) s

/-
Helper for Lemma 18.15.2: on the source site, forgetting additive structure sends epimorphisms of
abelian sheaves to epimorphisms of sheaves of sets.
-/
omit [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}] in
/-- Helper for Lemma 18.15.2: on the source site, forgetting additive structure sends
epimorphisms of abelian sheaves to epimorphisms of sheaves of sets. -/
lemma forgetAddCommGrpEpiOfSheafEpi
    {X Y : Sheaf K AddCommGrpCat.{max u₁ u₂ v}} (φ : X ⟶ Y) [Epi φ] :
    Epi ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ) := by
  -- Proof comment: convert the additive epi to local surjectivity, then forget it to sets.
  have hφ : Epi φ := inferInstance
  let hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (J := K) AddCommGrpCat.{max u₁ u₂ v} φ).2 hφ
  have hUnderlying :
      Sheaf.IsLocallySurjective ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ) :=
    underlyingLocallySurjectiveOfAdditiveSheafMap (K := K) (φ := φ) hloc
  exact
    (Sheaf.isLocallySurjective_iff_epi
      ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ)).1 hUnderlying

/-
Helper for Lemma 18.15.2: forgetting additive structure reflects epimorphisms back to abelian
sheaves.
-/
omit [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}] in
/-- Helper for Lemma 18.15.2: forgetting additive structure reflects epimorphisms back to
abelian sheaves. -/
lemma sheafEpiOfForgetAddCommGrpEpi
    {X Y : Sheaf J AddCommGrpCat.{max u₁ u₂ v}} (φ : X ⟶ Y)
    [Epi ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map φ)] :
    Epi φ := by
  -- Proof comment: faithful forgetting reflects right-cancellability back to additive sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map_injective
  apply (cancel_epi ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map φ)).1
  simpa using congrArg ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map) hgh

/-
Helper for Lemma 18.15.2: after forgetting additive structure, the additive pushforward map is
exactly the set-valued pushforward of the forgotten map.
-/
omit [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}] in
/-- Helper for Lemma 18.15.2: after forgetting additive structure, the additive pushforward map
is exactly the set-valued pushforward of the forgotten map. -/
lemma sheafPushforwardContinuous_forget_map_epi
    {X Y : Sheaf K AddCommGrpCat.{max u₁ u₂ v}} (φ : X ⟶ Y)
    (hmapForget :
      Epi
        ((u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).map
          ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ))) :
    Epi
      ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map
        ((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).map φ)) := by
  let Fadd := u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K
  let Ftype := u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K
  -- Proof comment: `sheaf_pushforward_forget` identifies the forgotten additive pushforward map
  -- with the set-valued pushforward of the forgotten source morphism.
  simpa [Fadd, Ftype, sheaf_pushforward_forget] using hmapForget

omit [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}] in
/-- If the underlying set-valued direct image of the continuous presentation `u` preserves
epimorphisms, then the induced direct image on sheaves of abelian groups also preserves
epimorphisms. -/
theorem sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms := by
  refine ⟨fun {X Y} φ hφ ↦ ?_⟩
  let Fadd := u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K
  let Ftype := u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K
  letI : Ftype.PreservesEpimorphisms := hpush
  -- Proof comment: first forget the source epimorphism to sheaves of sets on `K`.
  have hφForget : Epi ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ) := by
    letI : Epi φ := hφ
    have hloc : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi' (J := K) AddCommGrpCat.{max u₁ u₂ v} φ).2 hφ
    have hUnderlying :
        Sheaf.IsLocallySurjective ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ) :=
      underlyingLocallySurjectiveOfAdditiveSheafMap (K := K) (φ := φ) hloc
    exact
      (Sheaf.isLocallySurjective_iff_epi
        ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ)).1 hUnderlying
  -- Proof comment: the set-valued pushforward preserves that forgotten epi by hypothesis.
  have hmapForget :
      Epi
        (Ftype.map
          ((sheafCompose K (forget AddCommGrpCat.{max u₁ u₂ v})).map φ)) := by
    infer_instance
  -- Proof comment: `sheaf_pushforward_forget` identifies the forgotten pushed-forward map.
  have hmapUnderlying :
      Epi
        ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map
          (Fadd.map φ)) :=
    sheafPushforwardContinuous_forget_map_epi (u := u) (J := J) (K := K) (φ := φ) hmapForget
  -- Proof comment: reflect the target epi back to additive sheaves on `J`.
  letI :
      Epi
        ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map
          (Fadd.map φ)) :=
    hmapUnderlying
  -- Proof comment: faithful forgetting reflects right-cancellability back to additive sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map_injective
  apply (cancel_epi ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map (Fadd.map φ))).1
  simpa using congrArg ((sheafCompose J (forget AddCommGrpCat.{max u₁ u₂ v})).map) hgh

/-
If the direct image on sheaves of abelian groups preserves epimorphisms, then it is exact.
-/
omit [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})] in
/-- If the direct image on sheaves of abelian groups preserves epimorphisms, then it is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms) :
    exactFunctor (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := by
  let F := u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K
  -- Proof comment: the additive sheaf pushforward is a right adjoint, hence preserves finite
  -- limits.
  let _ : F.IsRightAdjoint :=
    (u.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ u₂ v} J K).isRightAdjoint
  let _ : PreservesFiniteLimits F := inferInstance
  let hAbK : Abelian (Sheaf K AddCommGrpCat.{max u₁ u₂ v}) := sheafIsAbelian
  let hAbJ : Abelian (Sheaf J AddCommGrpCat.{max u₁ u₂ v}) := sheafIsAbelian
  let _ : Preadditive (Sheaf K AddCommGrpCat.{max u₁ u₂ v}) := hAbK.toPreadditive
  let _ : Preadditive (Sheaf J AddCommGrpCat.{max u₁ u₂ v}) := hAbJ.toPreadditive
  have hLeft :
      leftExactFunctor (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
        (Sheaf J AddCommGrpCat.{max u₁ u₂ v}) F := by
    -- Proof comment: finite-limit preservation is the left exactness input for the exact-functor
    -- criterion.
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ : F.PreservesEpimorphisms := hpush
  -- Proof comment: in the abelian setting, preserving epimorphisms and kernels upgrades `F` to
  -- preserving homology and hence finite colimits.
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

omit [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})] in
/-- Helper for Lemma 18.15.2: preserving coequalizers on sheaves of sets implies preservation of
epimorphisms. -/
theorem sheafType_preservesEpimorphisms_of_preservesCoequalizers
    {F : Sheaf K (Type (max u₁ u₂ v)) ⥤ Sheaf J (Type (max u₁ u₂ v))}
    [PreservesColimitsOfShape WalkingParallelPair F] :
    F.PreservesEpimorphisms := by
  constructor
  intro X Y φ hφ
  letI : Epi φ := hφ
  letI : IsRegularEpi φ := isRegularEpi_of_regularEpi <| regularEpiOfEpi φ
  -- Route correction: use the canonical regular-epi cofork of `φ` and map its coequalizer
  -- witness through `F`, instead of reconstructing a kernel pair by hand.
  have hcofork :
      IsColimit
        (Cofork.ofπ (F.map φ)
          (by
            simpa only [Functor.map_comp] using congrArg (fun k ↦ F.map k) (IsRegularEpi.w φ))) := by
    -- Proof comment: preservation of the relevant coequalizer shape transports the canonical
    -- regular-epi colimit witness along `F`.
    exact
      isColimitCoforkMapOfIsColimit F (IsRegularEpi.w φ) (IsRegularEpi.isColimit φ)
  -- Proof comment: the cocone map of any colimiting cofork is epi, so `F.map φ` is epi.
  exact Cofork.IsColimit.epi hcofork

/-- Lemma 18.15.2, canonical-owner form: if the direct image on sheaves of abelian groups
preserves epimorphisms, or if its underlying set-valued direct image preserves epimorphisms,
coequalizers, or pushouts, then the abelian direct image is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
    (h :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms ∨
        (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms ∨
          PreservesColimitsOfShape WalkingParallelPair
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K) ∨
            PreservesColimitsOfShape WalkingSpan
              (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K)) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := by
  rcases h with hab | htype | hcoeq | hpushout
  · -- The abelian-epimorphism branch is the direct source-proof endpoint.
    exact sheafPushforwardContinuous_exact_of_preservesEpimorphisms u hab
  · -- Route the underlying-set branch through the epi-upgrade theorem.
    exact sheafPushforwardContinuous_exact_of_preservesEpimorphisms u
      (sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
        u htype)
  · -- Route the coequalizer branch through the dedicated set-valued epi bridge.
    letI : PreservesColimitsOfShape WalkingParallelPair
        (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K) := hcoeq
    exact sheafPushforwardContinuous_exact_of_preservesEpimorphisms u
      (sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms u
        (sheafType_preservesEpimorphisms_of_preservesCoequalizers (J := J)))
  · -- Pushout preservation already implies set-valued epi preservation by the generic owner API.
    letI : PreservesColimitsOfShape WalkingSpan
        (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K) := hpushout
    exact sheafPushforwardContinuous_exact_of_preservesEpimorphisms u
      (sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms u
        inferInstance)

end ExactnessCriterion

section PresentedExactnessCriterion

variable (f : MorphismOfTopoiIn J K)
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasSheafify J AddCommGrpCat.{max u₁ u₂ v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [HasSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

/-- Lemma 18.15.2, bridge form: if `ePush` presents the underlying set-valued direct image of
`f : Sh(K) ⟶ Sh(J)` by the continuous functor `u`, and if `f _*` preserves epimorphisms,
coequalizers, or pushouts, then the induced direct image on abelian sheaves,
`u.sheafPushforwardContinuous AddCommGrpCat J K`, is exact. -/
theorem presented_sheafPushforwardContinuous_exact_of_pushforwardPreservesEpimorphisms_or_coequalizers_or_pushouts
    (ePush :
      u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅
        f _*)
    (h :
      (f _*).PreservesEpimorphisms ∨
        PreservesColimitsOfShape WalkingParallelPair (f _*) ∨
          PreservesColimitsOfShape WalkingSpan (f _*)) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := by
  rcases h with hEpi | hCoeq | hPushout
  · -- Transport the set-valued epimorphism hypothesis across the presentation isomorphism.
    letI : (f _*).PreservesEpimorphisms := hEpi
    exact
      sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
        u (Or.inr <| Or.inl <| Functor.preservesEpimorphisms.of_iso ePush.symm)
  · -- Transport the coequalizer hypothesis across the presentation isomorphism.
    letI : PreservesColimitsOfShape WalkingParallelPair (f _*) := hCoeq
    exact
      sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
        u (Or.inr <| Or.inr <| Or.inl <| preservesColimitsOfShape_of_natIso ePush.symm)
  · -- Transport the pushout hypothesis across the presentation isomorphism.
    letI : PreservesColimitsOfShape WalkingSpan (f _*) := hPushout
    exact
      sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
        u (Or.inr <| Or.inr <| Or.inr <| preservesColimitsOfShape_of_natIso ePush.symm)

end PresentedExactnessCriterion

end CategoryTheory.Functor
