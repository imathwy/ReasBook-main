import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_22_2
import StacksProject_2024.Chap07.Lemma_7_42_5
import StacksProject_2024.Chap18.Lemma_18_15_2
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)

/- Domain-style sampling for Lemma 18.19.3:
- primary domain: exactness of extension by zero and localized restriction for sheaves of modules
  on the localized ringed site `(C/U, J.over U, 𝒪.over U)`;
- sampled owner declarations:
  `ringedSiteLocalizedExtensionByZero`,
  `ringedSiteLocalizedRestriction`,
  `exactFunctor`;
- best owner abstraction: the source-facing chapter owners
  `ringedSiteLocalizedExtensionByZero J 𝒪 U` and
  `ringedSiteLocalizedRestriction J 𝒪 U`.
-/

omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.19.3: after forgetting module structure, localized extension by zero is
definitionally the additive-sheaf pushforward along `Over.star U`. -/
private theorem localizedExtensionByZeroCompToSheaf :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) =
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{max u v} J (J.over U) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.19.3: localized extension by zero preserves finite limits because it is
the right adjoint in the localized adjunction. -/
private theorem localizedExtensionByZeroPreservesFiniteLimitsAux :
    PreservesFiniteLimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  -- Proof comment: the localized extension-by-zero functor is already registered as a right
  -- adjoint, so finite-limit preservation is an instance search step.
  infer_instance

/-- Helper for Lemma 18.19.3: the underlying additive-sheaf extension by zero is exact. -/
private theorem underlying_locally_surjective_of_additive_sheaf_map
    {E : Type u} [Category.{v} E] (L : GrothendieckTopology E)
    [L.HasSheafCompose (forget AddCommGrpCat.{max u v})]
    {F G : Sheaf L AddCommGrpCat.{max u v}} (π : F ⟶ G)
    (hπ : Sheaf.IsLocallySurjective π) :
    Sheaf.IsLocallySurjective ((sheafCompose L (forget AddCommGrpCat.{max u v})).map π) := by
  change Presheaf.IsLocallySurjective L
    (Functor.whiskerRight π.hom (forget AddCommGrpCat.{max u v}))
  change Presheaf.IsLocallySurjective L π.hom at hπ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro V s
  simpa [Presheaf.imageSieve] using hπ.imageSieve_mem (U := V) s

private theorem sheafType_preservesEpimorphisms_of_preservesCoequalizers
    {E E' : Type u} [Category.{v} E] [Category.{v} E']
    {L : GrothendieckTopology E} {L' : GrothendieckTopology E'}
    {F : Sheaf L (Type (max u v)) ⥤ Sheaf L' (Type (max u v))}
    [PreservesColimitsOfShape WalkingParallelPair F] :
    F.PreservesEpimorphisms := by
  constructor
  intro X Y φ hφ
  letI : Epi φ := hφ
  letI : IsRegularEpi φ := isRegularEpi_of_regularEpi <| regularEpiOfEpi φ
  have hcofork :
      IsColimit
        (Cofork.ofπ (F.map φ)
          (by
            simpa only [Functor.map_comp] using congrArg (fun k ↦ F.map k) (IsRegularEpi.w φ))) := by
    exact isColimitCoforkMapOfIsColimit F (IsRegularEpi.w φ) (IsRegularEpi.isColimit φ)
  exact Cofork.IsColimit.epi hcofork

private theorem localizedAdditiveExtensionByZeroExact :
    exactFunctor
      (Sheaf (J.over U) AddCommGrpCat.{max u v})
      (Sheaf J AddCommGrpCat.{max u v})
      ((Over.star U).sheafPushforwardContinuous AddCommGrpCat.{max u v} J (J.over U)) := by
  sorry

/-- Helper for Lemma 18.19.3: localized extension by zero preserves finite colimits after
forgetting to additive sheaves and reflecting finite colimits back through `toSheaf`. -/
private theorem localizedExtensionByZeroPreservesFiniteColimitsAux :
    PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  sorry

/-- Lemma 18.19.3: the localized extension-by-zero functor is exact. -/
theorem ringedSiteLocalizedExtensionByZero_exact :
    exactFunctor _ _ (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  -- Proof comment: exactness follows from the exact-functor criterion once the localized direct
  -- image is known to preserve finite limits and finite colimits.
  exact (exactFunctor_iff (ringedSiteLocalizedExtensionByZero J 𝒪 U)).2
    ⟨localizedExtensionByZeroPreservesFiniteLimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U),
      localizedExtensionByZeroPreservesFiniteColimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)⟩

instance ringedSiteLocalizedExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) :=
  localizedExtensionByZeroPreservesFiniteLimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)

instance ringedSiteLocalizedExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) :=
  localizedExtensionByZeroPreservesFiniteColimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)

instance ringedSiteLocalizedExtensionByZero_additive
    [Abelian (ringedSiteModuleCategory J 𝒪)]
    [Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U))] :
    (ringedSiteLocalizedExtensionByZero J 𝒪 U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  ext V x
  rfl

section RestrictionExact

variable [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

omit [HasBinaryProducts C] in
/-- Lemma 18.19.3: the localized restriction functor is exact. -/
theorem ringedSiteLocalizedRestriction_exact :
    exactFunctor _ _ (ringedSiteLocalizedRestriction J 𝒪 U) := by
  -- Proof comment: `j_U^*` is the module pushforward along `Over.forget U`; exactness follows by
  -- combining the almost-cocontinuous exactness criterion for additive sheaf pushforward with the
  -- generic module-pushforward exactness upgrade.
  let _ : HasWeakSheafify (J.over U) (Type (max u v)) := inferInstance
  let _ : HasWeakSheafify J (Type (max u v)) := inferInstance
  let _ : (J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v}) := inferInstance
  let _ : J.HasSheafCompose (forget AddCommGrpCat.{max u v}) := inferInstance
  let _ : (Over.forget U).IsAlmostCocontinuous (J.over U) J := inferInstance
  let F :
      ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
    SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))
  let Fadd :
      Sheaf J AddCommGrpCat.{max u v} ⥤ Sheaf (J.over U) AddCommGrpCat.{max u v} :=
    (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{max u v} (J.over U) J
  let GC :
      ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
        Sheaf (J.over U) AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))
  let GD :
      ringedSiteModuleCategory J 𝒪 ⥤ Sheaf J AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf (ringSheaf J 𝒪)
  change exactFunctor _ _ F
  have hAddExact :
      exactFunctor
        (Sheaf J AddCommGrpCat.{max u v})
        (Sheaf (J.over U) AddCommGrpCat.{max u v})
        Fadd :=
    CategoryTheory.Functor.sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
      (Over.forget U)
      (Or.inr <| Or.inr <| Or.inr <|
        CategoryTheory.Functor.sheafPushforwardContinuous_preservesPushouts_of_isAlmostCocontinuous
          (Over.forget U) (J.over U) J)
  let _ : F.IsRightAdjoint := by
    simpa [F] using
      (SheafOfModules.instIsRightAdjointPushforward (φ := 𝟙 ((ringSheaf J 𝒪).over U)))
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : Abelian (ringedSiteModuleCategory J 𝒪) := SheafOfModules.instAbelian (ringSheaf J 𝒪)
  let _ : Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U)) :=
    SheafOfModules.instAbelian (ringSheaf (J.over U) (𝒪.over U))
  have hEpiOfToSheafMapEpi
      {M N : ringedSiteModuleCategory (J.over U) (𝒪.over U)} (p : M ⟶ N)
      [Epi (GC.map p)] :
      Epi p := by
    refine ⟨?_⟩
    intro Z g h hgh
    apply GC.map_injective
    apply (cancel_epi (GC.map p)).1
    simpa using congrArg (Functor.map GC) hgh
  have hLeft :
      leftExactFunctor
        (ringedSiteModuleCategory J 𝒪)
        (ringedSiteModuleCategory (J.over U) (𝒪.over U))
        F := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ : PreservesFiniteColimits GD :=
    ((exactFunctor_iff GD).1 (ExactFunctor.of GD).property).2
  let _ : Fadd.PreservesEpimorphisms := by
    let _ : PreservesFiniteColimits Fadd := (exactFunctor_iff Fadd).1 hAddExact |>.2
    infer_instance
  let _ : F.PreservesEpimorphisms := by
    constructor
    intro M N g hg
    have hUnderlying : Epi ((GD ⋙ Fadd).map g) := by
      let _ : Epi g := hg
      infer_instance
    have hMap : Epi (GC.map (F.map g)) := by
      simpa [F, Fadd, GC, GD, SheafOfModules.pushforward, PresheafOfModules.pushforward] using
        hUnderlying
    let _ : Epi (GC.map (F.map g)) := hMap
    exact hEpiOfToSheafMapEpi (F.map g)
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

instance ringedSiteLocalizedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (ringedSiteLocalizedRestriction J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedRestriction J 𝒪 U)).mp
    (ringedSiteLocalizedRestriction_exact J 𝒪 U) |>.1

instance ringedSiteLocalizedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (ringedSiteLocalizedRestriction J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedRestriction J 𝒪 U)).mp
    (ringedSiteLocalizedRestriction_exact J 𝒪 U) |>.2

instance ringedSiteLocalizedRestriction_additive
    [Abelian (ringedSiteModuleCategory J 𝒪)]
    [Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U))] :
    (ringedSiteLocalizedRestriction J 𝒪 U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  ext V x
  rfl

end RestrictionExact

end
