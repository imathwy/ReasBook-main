import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Topology.Sheaves.Abelian
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap06.Lemma_6_32_1
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Definition_17_13_1
import stacks_proof.stacks_project.Chap17.Lemma_17_4_2
import stacks_proof.stacks_project.Chap17.Lemma_17_6_3
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.13.4:
- primary domain: pushforward and pullback of sheaves of modules along a morphism of ringed
  spaces, together with the adjunction and essential-image package for a fully faithful right
  adjoint;
- inspected owner declarations:
  `RingedSpace.IsClosedImmersion`,
  `Topology.IsClosedEmbedding`,
  `Sheaf.IsLocallySurjective`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the source-facing closed-immersion owner `RingedSpace.IsClosedImmersion
  i`, whose module-theoretic consequences are expressed on the canonical pushforward owner `i _*`;
- primitive data: a morphism `i : Z ⟶ X`, the closed-embedding condition on `i.hom.base`, and the
  local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z`;
- derived API: exactness, the canonical `FullyFaithful` structure on `i _*`, the source-facing
  ideal-sheaf annihilation criterion, and its adjunction-theoretic unit-isomorphism
  reformulation.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertions about pushforward of module sheaves along a
  closed immersion of ringed spaces;
- `core/canonical`: `Topology.IsClosedEmbedding i.hom.base`,
  `Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)`,
  `SheafOfModules.pushforward (RingedSpace.Hom.toRingCatSheafHom i)`, and
  `SheafOfModules.pullbackPushforwardAdjunction (RingedSpace.Hom.toRingCatSheafHom i)`;
- `bridge/view`: `RingedSpace.IsClosedImmersion i`, which packages the two hypotheses above with
  extra local-generators data not used in this lemma. -/

namespace AlgebraicGeometry.RingedSpace.Hom

section

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

local notation "φi" => toRingCatSheafHom i
local notation "𝓘" => RingedSpace.closedImmersionIdealSheaf i
local notation "ι𝓘" => kernel.ι (SheafOfModules.unitToPushforwardObjUnit φi)

/-- Helper for Lemma 17.13.4: at every point of the source, the induced map on local rings is
surjective once the structure-sheaf map `\mathcal O_X \to i_* \mathcal O_Z` is locally
surjective and the underlying map is a closed embedding. -/
theorem stalkMap_surjective_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (z : Z) :
    Function.Surjective (PresheafedSpace.Hom.stalkMap i.hom z).hom := by
  let hloc :
      Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    inferInstance
  have hsurj :
      Function.Surjective
        ((TopCat.Presheaf.stalkFunctor CommRingCat (i.hom.base z)).map
          (RingedSpace.Hom.commRingSheafPushforwardMap i).hom) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      (RingedSpace.Hom.commRingSheafPushforwardMap i).hom).1
      (show TopCat.Presheaf.IsLocallySurjective
          (RingedSpace.Hom.commRingSheafPushforwardMap i).hom from hloc)
      (i.hom.base z)
  haveI :
      IsIso (Z.presheaf.stalkPushforward CommRingCat i.hom.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
      hi.isInducing Z.presheaf z
  have hpush :
      Function.Surjective (Z.presheaf.stalkPushforward CommRingCat i.hom.base z) :=
    (ConcreteCategory.bijective_of_isIso _).2
  -- The ringed-space stalk map is definitionally the locally-surjective stalk map followed by the
  -- pushforward stalk comparison isomorphism for the closed embedding.
  simpa using hpush.comp hsurj

/-- Helper for Lemma 17.13.4: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C}
    (hF : exactFunctor A B F) (hG : exactFunctor B C G) :
    exactFunctor A C (F ⋙ G) := by
  -- Proof comment: exactness is preservation of finite limits and finite colimits, both of which
  -- are stable under functor composition.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

private theorem homeomorphismAbelianSheafPushforward_preservesEpimorphisms
    {Y W : TopCat.{u}}
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat]
    [HasWeakSheafify (Opens.grothendieckTopology W) AddCommGrpCat]
    (e : Y ≅ W) :
    (TopCat.Sheaf.pushforward AddCommGrpCat e.hom).PreservesEpimorphisms := by
  -- TODO for Lemma 17.13.4: rebuild the homeomorphism pushforward equivalence using the current
  -- owner-level sheaf API, then transport epimorphy across that equivalence instead of relying on
  -- the missing legacy instance.
  sorry

/-- Helper for Lemma 17.13.4: on additive sheaves, pushforward along the underlying closed
embedding preserves epimorphisms. -/
private theorem abelianSheafPushforward_preservesEpimorphisms_of_isClosedEmbedding
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    (TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base).PreservesEpimorphisms := by
  -- TODO for Lemma 17.13.4: factor `i.hom.base` through its closed image using the repaired
  -- homeomorphism helper and the closed-subset pushforward owner, then compose the resulting
  -- epimorphism-preservation instances.
  sorry

/-- Helper for Lemma 17.13.4: if the underlying additive-sheaf map is epic, then the original
module-sheaf morphism is epic. -/
private theorem module_epi_of_underlying_epi
    {X : RingedSpace.{u}} {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ)
    (hφ : Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)) :
    Epi φ := by
  -- Proof comment: this is exactly the earlier public epi-reflection lemma from Lemma 17.4.2.
  exact AlgebraicGeometry.module_epi_of_underlying_epi (X := X) φ hφ

/-- Helper for Lemma 17.13.4: exact module-sheaf short complexes stay exact after forgetting to
sheaves of abelian groups. -/
private theorem toAbelianSheaf_map_exact
    {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))).Exact := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let stalkAddCommGrpFunctor : X → X.Modules ⥤ AddCommGrpCat.{u} :=
    fun x ↦
      toAbelianSheaf ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : ∀ x : X, (stalkAddCommGrpFunctor x).PreservesZeroMorphisms := by
    intro x
    let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
      TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    letI : G.PreservesZeroMorphisms := by infer_instance
    simpa [stalkAddCommGrpFunctor, G] using
      (inferInstance : (toAbelianSheaf ⋙ G).PreservesZeroMorphisms)
  -- Proof comment: exactness of module sheaves is stalkwise, and forgetting module structure on
  -- each stalk leaves exactness unchanged.
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map toAbelianSheaf)).mpr ?_
  intro x
  have hx : (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  have hx' :
      ((RingedSpace.stalkShortComplex S x).map
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u})).Exact :=
    ((RingedSpace.stalkShortComplex S x).exact_map_iff_of_faithful
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u})).mpr hx
  simpa [stalkAddCommGrpFunctor] using hx'

/-- Helper for Lemma 17.13.4: an epimorphism of `\mathcal O_X`-module sheaves remains epic after
forgetting to sheaves of abelian groups. -/
private theorem underlying_epi_of_module_epi
    {X : RingedSpace.{u}} {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ) [Epi φ] :
    Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf
      (fun S hS ↦ toAbelianSheaf_map_exact (X := X) S hS)
  -- Proof comment: once exactness survives forgetting, `Functor.map_epi` gives the forgotten epi.
  exact Functor.map_epi toAbelianSheaf φ

/-- Helper for Lemma 17.13.4: forgetting module pushforward to additive sheaves is definitionally
the same as first forgetting and then applying additive-sheaf pushforward. -/
private theorem modulePushforward_comp_toSheaf :
    (i _*) ⋙ SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) =
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Z) ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base := by
  rfl

/-- Helper for Lemma 17.13.4: if the underlying additive pushforward preserves epimorphisms, then
the module pushforward preserves epimorphisms as well. -/
private theorem modulePushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    [hpush :
      (TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base).PreservesEpimorphisms] :
    (i _*).PreservesEpimorphisms := by
  refine ⟨?_⟩
  intro 𝒢 ℋ φ hφ
  let toAbelianSheafZ : Z.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} Z :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Z)
  have hφ' : Epi (toAbelianSheafZ.map φ) :=
    underlying_epi_of_module_epi (X := Z) φ
  have hpushφ :
      Epi
        ((TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base).map
          (toAbelianSheafZ.map φ)) := by
    let _ : Epi (toAbelianSheafZ.map φ) := hφ'
    infer_instance
  -- Proof comment: the `toSheaf`/pushforward comparison is definitional, so the forgotten target
  -- map is epic and we reflect epimorphy back to module sheaves on `X`.
  simpa [modulePushforward_comp_toSheaf] using
    (module_epi_of_underlying_epi (X := X) ((i _*).map φ) hpushφ)

/-- Helper for Lemma 17.13.4: exactness of module pushforward along a closed embedding follows
from additive-sheaf epi preservation plus the module-category homology criterion. -/
private theorem pushforwardExact_of_isClosedEmbedding_aux
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    exactFunctor Z.Modules X.Modules (i _*) := by
  let hAb :
      (TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base).PreservesEpimorphisms :=
    abelianSheafPushforward_preservesEpimorphisms_of_isClosedEmbedding i hi
  let _ : (TopCat.Sheaf.pushforward AddCommGrpCat i.hom.base).PreservesEpimorphisms := hAb
  let _ : (i _*).PreservesEpimorphisms :=
    modulePushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms i
  let _ : (i _*).PreservesFiniteLimits := by infer_instance
  let _ : (i _*).PreservesFiniteColimits :=
    Functor.preservesFiniteColimits_of_preservesHomology (i _*)
      (Functor.preservesHomology_of_preservesEpis_and_kernels (i _*))
  -- Proof comment: the module pushforward is already a right adjoint, and the repaired epi bridge
  -- upgrades that to exactness through the standard homology criterion.
  exact (CategoryTheory.exactFunctor_iff (i _*)).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: combine the exactness of pushforward on underlying abelian sheaves for a closed
-- subset inclusion with the exactness of restriction of scalars on sections defining module
-- pushforward.
/-- Lemma 17.13.4 (1): if `i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` has underlying map a
closed embedding, then the pushforward functor on module sheaves is exact. -/
@[stacks 08KS]
theorem pushforward_exact_of_isClosedEmbedding
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    exactFunctor Z.Modules X.Modules (i _*) := by
  -- Route correction: keep the public theorem short and isolate the additive-to-module exactness
  -- upgrade in one dedicated helper theorem.
  exact pushforwardExact_of_isClosedEmbedding_aux i hi

/-- Helper for Lemma 17.13.4: each counit component of `i^* i_* ⟶ 𝟭` is an isomorphism under the
closed-embedding and local-surjectivity hypotheses. -/
private theorem pullbackPushforwardCounit_app_isIso_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (ℱ : Z.Modules) :
    IsIso (((SheafOfModules.pullbackPushforwardAdjunction φi).counit.app ℱ)) := by
  -- TODO for Lemma 17.13.4: check stalks at `z : Z`, rewrite the source stalk using
  -- `RingedSpace.Hom.pullbackStalkIso` and the target using the pushforward-stalk isomorphism for
  -- `i.hom.base`, and then identify the resulting map with the counit of
  -- `ModuleCat.extendRestrictScalarsAdj (i.hom.stalkMap z).hom`.
  sorry

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the canonical exactness statement for pushforward of module sheaves. -/
theorem pushforward_exact_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i] :
    exactFunctor Z.Modules X.Modules (i _*) := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact pushforward_exact_of_isClosedEmbedding i hi.isClosedEmbedding

-- Proof sketch: prove that the counit `i^* i_* ℱ ⟶ ℱ` is an isomorphism on stalks using the
-- closed-embedding hypothesis and the quotient description of local rings; then apply the standard
-- criterion that a right adjoint with isomorphic counit is fully faithful.
/-- Lemma 17.13.4 (2): under the same hypotheses, the pushforward functor on module sheaves is
fully faithful. -/
@[stacks 08KS]
noncomputable instance
    pushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    (i _*).FullyFaithful := by
  have hCounit :
      IsIso (SheafOfModules.pullbackPushforwardAdjunction φi).counit := by
    -- Route correction: reduce full faithfulness to the global counit-isomorphism owner first,
    -- then package the stalkwise component calculations through a dedicated helper theorem.
    let _ :
        ∀ ℱ : Z.Modules,
          IsIso (((SheafOfModules.pullbackPushforwardAdjunction φi).counit.app ℱ)) :=
      fun ℱ ↦
        pullbackPushforwardCounit_app_isIso_of_isClosedEmbedding_of_isLocallySurjective
          i hi ℱ
    exact NatIso.isIso_of_isIso_app
      (SheafOfModules.pullbackPushforwardAdjunction φi).counit
  let _ : IsIso (SheafOfModules.pullbackPushforwardAdjunction φi).counit := hCounit
  exact (SheafOfModules.pullbackPushforwardAdjunction φi).fullyFaithfulROfIsIsoCounit

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the canonical fully faithful structure on pushforward of module sheaves. -/
noncomputable instance pushforward_fullyFaithful_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i] : (i _*).FullyFaithful :=
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  pushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective i hi.isClosedEmbedding

-- Proof sketch: if `𝒢 ≅ i_* ℱ`, then every local section of the kernel ideal sheaf maps to zero
-- in `i_* \mathcal O_Z`, hence acts trivially on local sections of `𝒢`. Conversely, triviality of
-- that ideal action is the source-facing condition allowing the module structure on `𝒢` to
-- descend from `X` to the closed subspace `Z`.
/-- Helper for Lemma 17.13.4: the ideal-sheaf inclusion is the kernel inclusion of
`\mathcal O_X \to i_* \mathcal O_Z`, so its composite with that structure map is zero. -/
theorem closedImmersionIdealSheaf_comp_unitToPushforwardObjUnit_zero :
    ι𝓘 ≫ SheafOfModules.unitToPushforwardObjUnit φi = 0 := by
  -- This is exactly the defining kernel identity.
  exact kernel.condition (SheafOfModules.unitToPushforwardObjUnit φi)

/-- Helper for Lemma 17.13.4: on each open `U`, every section of the closed-immersion ideal sheaf
maps to zero in the pushed-forward structure sheaf `i_* \mathcal O_Z`. -/
theorem closedImmersionIdealSheaf_section_image_zero
    (U : Opens X) (s : (𝓘).val.obj (op U)) :
    ((SheafOfModules.unitToPushforwardObjUnit φi).val.app (op U))
      (((ι𝓘).val.app (op U)) s) = 0 := by
  have hval : (ι𝓘 ≫ SheafOfModules.unitToPushforwardObjUnit φi).val = 0 := by
    -- Pass from the module-sheaf morphism equality to the underlying natural transformations.
    exact congrArg SheafOfModules.Hom.val
      (closedImmersionIdealSheaf_comp_unitToPushforwardObjUnit_zero i)
  have hcomp :
      ((ι𝓘).val.app (op U)) ≫ ((SheafOfModules.unitToPushforwardObjUnit φi).val.app (op U)) = 0 := by
    -- Evaluating the kernel identity at `U` yields the zero composite on sections.
    change ((ι𝓘 ≫ SheafOfModules.unitToPushforwardObjUnit φi).val.app (op U)) = 0
    simpa using congrArg (fun f => f.app (op U)) hval
  -- Applying the zero composite to the chosen section gives the desired vanishing statement.
  simpa using congrArg
    (fun g : (𝓘).val.obj (op U) ⟶
        ((SheafOfModules.pushforward φi).obj (SheafOfModules.unit Z.ringCatSheaf)).val.obj (op U) =>
      ModuleCat.Hom.hom g s)
    hcomp

/-- Helper for Lemma 17.13.4: if `eHom` and `eInv` are inverse morphisms of
`\mathcal O_X`-module sheaves, then their section maps over any open compose to the identity in
the same order. -/
theorem section_map_comp_eq_id
    {ℱ 𝒢 : X.Modules} (eHom : ℱ ⟶ 𝒢) (eInv : 𝒢 ⟶ ℱ)
    (hHomInv : eHom ≫ eInv = 𝟙 ℱ) (U : Opens X) :
    (SheafOfModules.Hom.val eHom).app (op U) ≫ (SheafOfModules.Hom.val eInv).app (op U) =
      𝟙 (ℱ.val.obj (op U)) := by
  -- Evaluate the inverse identity of module-sheaf morphisms on the chosen open.
  simpa using congrArg
    (fun f => (SheafOfModules.Hom.val f).app (op U)) hHomInv

/-- Helper for Lemma 17.13.4: if `eHom` and `eInv` are inverse morphisms of
`\mathcal O_X`-module sheaves, then their section maps over any open compose to the identity in
the opposite order. -/
theorem section_inv_comp_eq_id
    {ℱ 𝒢 : X.Modules} (eHom : ℱ ⟶ 𝒢) (eInv : 𝒢 ⟶ ℱ)
    (hInvHom : eInv ≫ eHom = 𝟙 𝒢) (U : Opens X) :
    (SheafOfModules.Hom.val eInv).app (op U) ≫ (SheafOfModules.Hom.val eHom).app (op U) =
      𝟙 (𝒢.val.obj (op U)) := by
  -- Evaluate the opposite inverse identity of module-sheaf morphisms on the chosen open.
  simpa using congrArg
    (fun f => (SheafOfModules.Hom.val f).app (op U)) hInvHom

/-- Helper for Lemma 17.13.4: on pushed-forward sections, any ambient scalar whose image in
`(i_* \mathcal O_Z)(U)` is zero acts trivially. This packages the restriction-of-scalars action
needed in the forward essential-image implication. -/
theorem pushforward_sections_smul_eq_zero_of_unit_image_zero
    (ℱ : Z.Modules) (U : Opens X)
    (a : (SheafOfModules.unit X.ringCatSheaf).val.obj (op U))
    (ha :
      ((SheafOfModules.unitToPushforwardObjUnit φi).val.app (op U)) a = 0)
    (m : ((i _*).obj ℱ).val.obj (op U)) :
    a • m = 0 := by
  -- Rewrite the scalar in the unit module as an actual ring section of `𝒪_X(U)`.
  change (SheafOfModules.unitSectionToRingSection U a) •
      (show ((SheafOfModules.pushforward φi).obj ℱ).val.obj (op U) from m) = 0
  have hs :
      (((RingedSpace.Hom.commRingSheafPushforwardMap i).hom.app (op U)).hom
        (SheafOfModules.unitSectionToRingSection U a)) = 0 := by
    -- The ringed-space structure map on sections is exactly the unit-module section map.
    change ((SheafOfModules.unitToPushforwardObjUnit φi).val.app (op U)) a = 0
    exact ha
  have hsmul :=
    ModuleCat.restrictScalars.smul_def
      (((RingedSpace.Hom.commRingSheafPushforwardMap i).hom.app (op U)).hom)
      (SheafOfModules.unitSectionToRingSection U a)
      (show ((SheafOfModules.pushforward φi).obj ℱ).val.obj (op U) from m)
  -- After normalizing the hidden restriction-of-scalars action, the vanishing hypothesis kills it.
  rw [hs, zero_smul] at hsmul
  simpa using hsmul

/-- Helper for Lemma 17.13.4: every object already in the essential image of `i_*` is annihilated
sectionwise by the closed-immersion ideal sheaf. -/
theorem closedImmersionIdealSheaf_smul_eq_zero_of_mem_essImage
    {𝒢 : X.Modules} (h𝒢 : (i _*).essImage 𝒢) :
    ∀ U : Opens X,
      ∀ s : (𝓘).val.obj (op U),
      ∀ m : 𝒢.val.obj (op U),
        ((ι𝓘).val.app (op U) s) • m = 0 := by
  obtain ⟨ℱ, ⟨e⟩⟩ := h𝒢
  intro U s m
  let n : ((i _*).obj ℱ).val.obj (op U) :=
    ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.inv).app (op U)) m
  have hm :
      ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app (op U))
        n = m := by
    -- Evaluate the inverse identity on sections and then on the chosen element `m`.
    simpa using congrArg
      (fun g => ModuleCat.Hom.hom g m)
      (section_inv_comp_eq_id e.hom e.inv e.inv_hom_id U)
  -- Transport the section to the pushed-forward model, use the kernel computation there, and map
  -- back along the section map of the essential-image isomorphism.
  rw [← hm]
  calc
    ((ι𝓘).val.app (op U) s) • ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app (op U)) n
        = ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app (op U))
            (((ι𝓘).val.app (op U) s) • n) := by
          symm
          exact ((SheafOfModules.Hom.val e.hom).app (op U)).hom.map_smul _ _
    _ = ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app (op U)) 0 := by
          congr 1
          exact pushforward_sections_smul_eq_zero_of_unit_image_zero i ℱ U
            (((ι𝓘).val.app (op U)) s)
            (closedImmersionIdealSheaf_section_image_zero i U s) n
    _ = 0 := by
          simp

/-- Helper for Lemma 17.13.4: the sectionwise annihilation in the essential image persists on
stalks after passing through the ideal-sheaf inclusion into the structure sheaf. -/
theorem closedImmersionIdealSheaf_stalk_image_smul_eq_zero_of_sectionwise_smul_eq_zero
    {𝒢 : X.Modules}
    (hsec :
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
          ((ι𝓘).val.app (op U) s) • m = 0)
    (x : X) (t : RingedSpace.stalkModuleCat 𝓘 x) (m : RingedSpace.stalkModuleCat 𝒢 x) :
    (RingedSpace.unitStalkLinearMap x
        (RingedSpace.moduleStalkHom x (ι𝓘) t)) • m = 0 := by
  obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.germ_exist (𝓘).val.presheaf x t
  obtain ⟨V, hxV, n, hn⟩ := TopCat.Presheaf.germ_exist 𝒢.val.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let sW : (𝓘).val.obj (op W) := (𝓘).val.map (homOfLE inf_le_left).op s
  let nW : 𝒢.val.obj (op W) := 𝒢.val.map (homOfLE inf_le_right).op n
  have htW :
      t = TopCat.Presheaf.germ (𝓘).val.presheaf W x hxW sW := by
    calc
      t = TopCat.Presheaf.germ (𝓘).val.presheaf U x hxU s := hs.symm
      _ = TopCat.Presheaf.germ (𝓘).val.presheaf W x hxW sW := by
        rw [show sW = (𝓘).val.map (homOfLE inf_le_left).op s by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply (𝓘).val.presheaf (homOfLE inf_le_left) x hxW s
  have hmW :
      m = TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW nW := by
    calc
      m = TopCat.Presheaf.germ 𝒢.val.presheaf V x hxV n := hn.symm
      _ = TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW nW := by
        rw [show nW = 𝒢.val.map (homOfLE inf_le_right).op n by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply 𝒢.val.presheaf (homOfLE inf_le_right) x hxW n
  have hsection_zero :
      (((ι𝓘).val.app (op W)) sW) • nW = 0 := by
    -- This is the raw sectionwise annihilation hypothesis, now applied on the common refinement.
    exact hsec W sW nW
  have hmap :
      RingedSpace.moduleStalkHom x (ι𝓘)
          (TopCat.Presheaf.germ (𝓘).val.presheaf W x hxW sW) =
        TopCat.Presheaf.germ
          (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW
          (((ι𝓘).val.app (op W)) sW) := by
    -- Rewrite the stalk of the ideal-sheaf inclusion by functoriality of germs.
    simpa [RingedSpace.moduleStalkHom] using
      (RingedSpace.moduleStalkMap_germ x (ι𝓘) W hxW sW)
  have hscalar :
      RingedSpace.unitStalkLinearMap x
          (RingedSpace.moduleStalkHom x (ι𝓘)
            (TopCat.Presheaf.germ (𝓘).val.presheaf W x hxW sW)) =
        X.presheaf.germ W x hxW
          (SheafOfModules.unitSectionToRingSection W (((ι𝓘).val.app (op W)) sW)) := by
    -- After the stalk map lands in the unit module, identify it with the corresponding ring germ.
    rw [hmap]
    exact SheafOfModules.unitStalkLinearMap_germ x W hxW (((ι𝓘).val.app (op W)) sW)
  -- Represent both stalk elements on the same neighbourhood and convert stalk scalar action to
  -- the germ of the already-vanishing sectionwise scalar action.
  rw [htW, hmW, hscalar]
  calc
    X.presheaf.germ W x hxW
        (SheafOfModules.unitSectionToRingSection W (((ι𝓘).val.app (op W)) sW)) •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW nW =
      TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((((ι𝓘).val.app (op W)) sW) • nW) := by
        symm
        simpa using
          (PresheafOfModules.germ_smul 𝒢.val x W hxW
            (SheafOfModules.unitSectionToRingSection W (((ι𝓘).val.app (op W)) sW)) nW)
    _ = TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW 0 := by
        exact congrArg (TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW) hsection_zero
    _ = 0 := by
        exact (TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW).hom.map_zero

/-- Helper for Lemma 17.13.4: the sectionwise annihilation in the essential image persists on
stalks after passing through the ideal-sheaf inclusion into the structure sheaf. -/
theorem closedImmersionIdealSheaf_stalk_image_smul_eq_zero_of_mem_essImage
    {𝒢 : X.Modules} (h𝒢 : (i _*).essImage 𝒢) (x : X)
    (t : RingedSpace.stalkModuleCat 𝓘 x) (m : RingedSpace.stalkModuleCat 𝒢 x) :
    (RingedSpace.unitStalkLinearMap x
        (RingedSpace.moduleStalkHom x (ι𝓘) t)) • m = 0 := by
  -- Route correction: reuse the stalk-germ argument through the raw sectionwise annihilation
  -- helper, rather than rebuilding the same common-refinement proof from scratch.
  exact
    closedImmersionIdealSheaf_stalk_image_smul_eq_zero_of_sectionwise_smul_eq_zero i
      (closedImmersionIdealSheaf_smul_eq_zero_of_mem_essImage i h𝒢) x t m

/-- Helper for Lemma 17.13.4: if a stalk element of the closed-immersion ideal sheaf maps to
`1` in the stalk ring, then every stalk element of a module annihilated sectionwise by the ideal
sheaf is zero. -/
theorem stalk_eq_zero_of_closedImmersionIdealSheaf_stalk_contains_one
    {𝒢 : X.Modules}
    (hsec :
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
          ((ι𝓘).val.app (op U) s) • m = 0)
    (x : X)
    (hone :
      ∃ t : RingedSpace.stalkModuleCat 𝓘 x,
        RingedSpace.unitStalkLinearMap x
          (RingedSpace.moduleStalkHom x (ι𝓘) t) = 1)
    (m : RingedSpace.stalkModuleCat 𝒢 x) :
    m = 0 := by
  rcases hone with ⟨t, ht⟩
  -- Use the existing stalk-annihilation lemma, then rewrite the scalar to `1`.
  have hsmul :
      (RingedSpace.unitStalkLinearMap x
          (RingedSpace.moduleStalkHom x (ι𝓘) t)) • m = 0 :=
    closedImmersionIdealSheaf_stalk_image_smul_eq_zero_of_sectionwise_smul_eq_zero i
      hsec x t m
  rw [ht, one_smul] at hsmul
  exact hsmul

/-- Helper for Lemma 17.13.4: if the closed-immersion ideal sheaf contains `1` on a stalk, then
that stalk of any module annihilated by the ideal sheaf is zero. -/
theorem stalk_isZero_of_closedImmersionIdealSheaf_stalk_contains_one
    {𝒢 : X.Modules}
    (hsec :
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
          ((ι𝓘).val.app (op U) s) • m = 0)
    (x : X)
    (hone :
      ∃ t : RingedSpace.stalkModuleCat 𝓘 x,
        RingedSpace.unitStalkLinearMap x
          (RingedSpace.moduleStalkHom x (ι𝓘) t) = 1) :
    IsZero (RingedSpace.stalkModuleCat 𝒢 x) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  intro m n
  -- Once both stalk elements are forced to vanish, the stalk is subsingleton.
  rw [stalk_eq_zero_of_closedImmersionIdealSheaf_stalk_contains_one i hsec x hone m,
    stalk_eq_zero_of_closedImmersionIdealSheaf_stalk_contains_one i hsec x hone n]

/-- Helper for Lemma 17.13.4: off the image of the closed embedding, the ideal-sheaf stalk
contains an element mapping to `1` in the ambient stalk ring. -/
private theorem closedImmersionIdealSheaf_stalk_contains_one_of_not_mem_range
    (hi : Topology.IsClosedEmbedding i.hom.base)
    {x : X} (hx : x ∉ Set.range i.hom.base) :
    ∃ t : RingedSpace.stalkModuleCat 𝓘 x,
      RingedSpace.unitStalkLinearMap x
        (RingedSpace.moduleStalkHom x (ι𝓘) t) = 1 := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk ι𝓘 (SheafOfModules.unitToPushforwardObjUnit φi)
      (kernel.condition (SheafOfModules.unitToPushforwardObjUnit φi))
  have hS : S.Exact := by
    -- Proof comment: the closed-immersion ideal sheaf is the kernel of
    -- `𝒪_X ⟶ i_* 𝒪_Z`, so the defining short complex is exact.
    simpa [S] using
      ShortComplex.exact_kernel (SheafOfModules.unitToPushforwardObjUnit φi)
  have hRange :
      LinearMap.range (RingedSpace.moduleStalkHom x (ι𝓘)).hom =
        LinearMap.ker
          (RingedSpace.moduleStalkHom x
            (SheafOfModules.unitToPushforwardObjUnit φi)).hom := by
    have hxExact : (RingedSpace.stalkShortComplex S x).Exact :=
      (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
    -- Proof comment: exactness on the stalk short complex identifies the image of the ideal
    -- stalk map with the kernel of the stalked structure-sheaf map.
    simpa [S, RingedSpace.stalkShortComplex] using
      ShortComplex.Exact.moduleCat_range_eq_ker hxExact
  let e : Z ≅ TopCat.of (Set.range i.hom.base) :=
    TopCat.isoOfHomeo hi.1.toHomeomorph
  let ℱ' :
      TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Set.range i.hom.base)) :=
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Z)).obj
        (SheafOfModules.unit Z.ringCatSheaf))
  have hZero :
      IsZero
        (RingedSpace.stalkModuleCat
          ((i _*).obj (SheafOfModules.unit Z.ringCatSheaf)) x) := by
    -- Proof comment: away from the image, the underlying additive stalk of the pushed-forward
    -- unit module vanishes by the closed-subset result from Lemma 6.32.1.
    apply isZero_of_reflects_iso _ (forget₂
      (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u})
    simpa [ℱ'] using
      (closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
        (X := X) (Z := Set.range i.hom.base) hi.isClosed_range ℱ' hx)
  have hker :
      (RingedSpace.unitStalkLinearEquiv x).symm (1 : X.presheaf.stalk x) ∈
        LinearMap.ker
          (RingedSpace.moduleStalkHom x
            (SheafOfModules.unitToPushforwardObjUnit φi)).hom := by
    change
      RingedSpace.moduleStalkHom x (SheafOfModules.unitToPushforwardObjUnit φi)
          ((RingedSpace.unitStalkLinearEquiv x).symm (1 : X.presheaf.stalk x)) = 0
    let hsub :
        Subsingleton
          (RingedSpace.stalkModuleCat
            ((i _*).obj (SheafOfModules.unit Z.ringCatSheaf)) x) := by
      simpa [ModuleCat.isZero_iff_subsingleton] using hZero
    exact hsub _ _
  rw [← hRange] at hker
  rcases hker with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- Proof comment: the chosen stalk element maps to the unit-stalk representative of `1`, and
  -- the canonical unit-stalk equivalence identifies that representative with `1` in the stalk
  -- ring.
  change
    RingedSpace.unitStalkLinearMap x
        ((RingedSpace.moduleStalkHom x (ι𝓘)).hom t) = 1
  rw [ht]
  simpa [RingedSpace.unitStalkLinearMap] using
    (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply (1 : X.presheaf.stalk x)

/-- Helper for Lemma 17.13.4: if the closed-immersion ideal acts by zero on all local sections of
`\mathcal G`, then the adjunction unit `𝒢 ⟶ i_* i^* 𝒢` is an isomorphism. -/
private theorem pullbackPushforwardUnit_app_isIso_of_sectionwise_annihilation
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒢 : X.Modules)
    (hsec :
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
          ((ι𝓘).val.app (op U) s) • m = 0) :
    IsIso (((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢)) := by
  -- TODO for Lemma 17.13.4: prove the unit isomorphism stalkwise. On image points, reduce to the
  -- module-category unit for `ModuleCat.extendRestrictScalarsAdj (i.hom.stalkMap z).hom` using the
  -- annihilation of the kernel ideal. Off the image, use the previous helper together with
  -- `stalk_isZero_of_closedImmersionIdealSheaf_stalk_contains_one` and Lemma 6.32.1.
  sorry

/-- Lemma 17.13.4 (3): under the same hypotheses, an `\mathcal O_X`-module sheaf lies in the
essential image of `i_*` exactly when the ideal sheaf of the closed embedding acts trivially on
it, i.e. every local section of `\mathcal I` acts by zero on local sections of `\mathcal G`. -/
@[stacks 08KS]
theorem
    pushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
            ((ι𝓘).val.app (op U) s) • m = 0 := by
  -- Route correction: isolate the sectionwise kernel computation first; the remaining work is to
  -- transport this vanishing across an essential-image isomorphism and to prove the converse by a
  -- stalkwise analysis of the adjunction unit `𝒢 ⟶ i_* i^* 𝒢`.
  constructor
  · -- The forward implication is now the sectionwise transport of the kernel computation.
    exact closedImmersionIdealSheaf_smul_eq_zero_of_mem_essImage i
  · intro hsec
    have hunit :
        IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
      -- Route correction: first isolate the stalkwise unit comparison into a dedicated helper, so
      -- the public theorem only invokes the generic essential-image/unit criterion.
      exact
        pullbackPushforwardUnit_app_isIso_of_sectionwise_annihilation
          i hi 𝒢 hsec
    exact
      (pushforward_essImage_iff_unit_isIso_of_isClosedEmbedding_of_isLocallySurjective i hi 𝒢).2
        hunit

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the essential-image criterion for module pushforward in terms of annihilation by the ideal sheaf
of the closed immersion. -/
theorem
    pushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      ∀ U : Opens X,
        ∀ s : (𝓘).val.obj (op U),
          ∀ m : 𝒢.val.obj (op U),
            ((ι𝓘).val.app (op U) s) • m = 0 := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact
    pushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedEmbedding_of_isLocallySurjective
      i hi.isClosedEmbedding 𝒢

-- Proof sketch: for a fully faithful right adjoint, an object lies in the essential image exactly
-- when the adjunction unit is an isomorphism. The previous theorem is the source-facing
-- closed-immersion translation of that generic adjunction criterion.
/-- Core companion: for the canonical adjunction `i^* ⊣ i_*`, once `i_*` is fully faithful,
membership in the essential image of `i_*` is equivalent to invertibility of the adjunction
unit `\mathcal G \to i_* i^* \mathcal G`. -/
theorem pushforward_essImage_iff_unit_isIso
    (hFF : (i _*).FullyFaithful)
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
  let hFF' : (SheafOfModules.pushforward φi).FullyFaithful := by
    change (i _*).FullyFaithful
    exact hFF
  letI : (SheafOfModules.pushforward φi).Full := hFF'.full
  letI : (SheafOfModules.pushforward φi).Faithful := hFF'.faithful
  simpa using
    (((SheafOfModules.pullbackPushforwardAdjunction φi).isIso_unit_app_iff_mem_essImage :
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) ↔
        (SheafOfModules.pushforward φi).essImage 𝒢)).symm

/-- Helper for Lemma 17.13.4: once the closed-immersion hypotheses give full faithfulness of
`i_*`, essential-image membership is equivalent to the adjunction unit being an isomorphism. -/
theorem pushforward_essImage_iff_unit_isIso_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
  -- Route correction: package the generic adjunction criterion now, so the remaining converse
  -- direction only has to prove the unit isomorphism on stalks.
  exact
    pushforward_essImage_iff_unit_isIso i
      (pushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective i hi) 𝒢

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` also
supplies the canonical adjunction-unit reformulation of the essential-image criterion. -/
theorem pushforward_essImage_iff_unit_isIso_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
  exact
    pushforward_essImage_iff_unit_isIso i
      (pushforward_fullyFaithful_of_isClosedImmersion i) 𝒢

end

end AlgebraicGeometry.RingedSpace.Hom
