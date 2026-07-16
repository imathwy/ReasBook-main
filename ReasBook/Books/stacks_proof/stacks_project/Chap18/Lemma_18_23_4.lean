import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_23_1
import stacks_proof.stacks_project.Chap18.Lemma_18_23_3

open CategoryTheory Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : D ⥤ C) [Functor.IsContinuous F K J]
variable {𝒪C : Sheaf J CommRingCat} {𝒪D : Sheaf K CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify K AddCommGrpCat]
variable [K.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, HasWeakSheafify (K.over V) AddCommGrpCat]
variable [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, (K.over V).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ V : D, ∀ W : Over V, HasWeakSheafify ((K.over V).over W) AddCommGrpCat]
variable [∀ V : D, ∀ W : Over V, ((K.over V).over W).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, ∀ W : Over V, ((K.over V).over W).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

private abbrev ringSheaf
    {E : Type u} [Category.{v} E] (L : GrothendieckTopology E)
    (𝒪 : Sheaf L CommRingCat) :
    Sheaf L RingCat :=
  (sheafCompose L (forget₂ CommRingCat RingCat)).obj 𝒪

/- Domain-style sampling for Lemma 18.23.4:
- primary domain: pullback of sheaves of modules along a morphism of ringed sites/topoi and
  preservation of local module-theoretic properties on the resulting ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  the pullback preservation instances from `Lemma_18_17_2`,
  and the locality criteria from `Lemma_18_23_3`;
- best owner abstraction:
  the inverse-image functor `SheafOfModules.pullback φ` between the chapter owner categories
  `ringedSiteModuleCategory K 𝒪D` and `ringedSiteModuleCategory J 𝒪C`;
- primitive data:
  the underlying `RingCat`-valued structure map
  `φ : ringSheaf K 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat K J).obj (ringSheaf J 𝒪C)`
  presenting the morphism of ringed sites/topoi, together with a module
  `ℱ : ringedSiteModuleCategory K 𝒪D`;
- derived API:
  the seven preservation statements below for local freeness, local finite freeness, local
  generation, finite type, quasi-coherence, and finite presentation.

Source/core/bridge triage:
- `source-facing`: the seven Stacks preservation statements for pullback along a morphism of
  ringed topoi;
- `core/canonical`: `ringedSiteModuleCategory`, `ringSheaf`, `SheafOfModules.pullback`, and the
- `core/canonical`: `ringedSiteModuleCategory`, `SheafOfModules.pullback`, and the owner
  predicates from `Definition_18_23_1`;
- `bridge/view`: the specific structure map `φ`, written using the local `ringSheaf` abbreviation
  for the underlying `RingCat`-valued structure sheaf.

The `let`-bound pullback modules in the theorem statements were therefore only elaboration
scaffolding. The refined public surface below keeps the same source semantics but states the
results directly in the owner categories and with the canonical pullback object. -/

variable
  (φ :
    ringSheaf K 𝒪D ⟶
      (F.sheafPushforwardContinuous RingCat K J).obj
        (ringSheaf J 𝒪C))
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]

local notation "fStar" => SheafOfModules.pullback φ
local notation "ModC" => SheafOfModules (ringSheaf J 𝒪C)
local notation "ModD" => SheafOfModules (ringSheaf K 𝒪D)

/-- Helper for Lemma 18.23.4: a covering family of the terminal object of `D` stays a covering
family after applying the continuous functor `F : D ⥤ C`. -/
private theorem pullbackCoverTargets
    {I : Type (max u v)} (Y : I → D) (hY : K.CoversTop Y) :
    J.CoversTop (fun i ↦ F.obj (Y i)) := by
  -- Proof comment: the local proof needs only the image cover on the target site; this is the
  -- continuity-of-covers step from the source argument.
  sorry

/-- Helper for Lemma 18.23.4: if the restricted source module is free on a chart `V`, then the
restricted pullback module is free on the corresponding chart `F.obj V`. -/
private theorem pullbackFreeChart
    (ℱ : ModD) {V : D} [SheafOfModules.IsFree (ℱ.over V)] :
    SheafOfModules.IsFree (((fStar).obj ℱ).over (F.obj V)) := by
  -- Proof comment: normalize the chart restriction of the pullback to the localized pullback of
  -- `ℱ.over V`, then apply the global free pullback preservation instance.
  sorry

/-- Helper for Lemma 18.23.4: if the restricted source module is finite free on a chart `V`, then
the restricted pullback module is finite free on the corresponding chart `F.obj V`. -/
private theorem pullbackFiniteFreeChart
    (ℱ : ModD) {V : D} [SheafOfModules.IsFiniteFree (ℱ.over V)] :
    SheafOfModules.IsFiniteFree (((fStar).obj ℱ).over (F.obj V)) := by
  -- Proof comment: the same chartwise normalization as in the free case reduces to the global
  -- finite-free pullback preservation instance.
  sorry

/-- Helper for Lemma 18.23.4: globally generating sections on a source chart pull back to globally
generating sections on the corresponding target chart. -/
private theorem pullbackGloballyGeneratedChart
    (ℱ : ModD) {V : D} [Nonempty (ℱ.over V).GeneratingSections] :
    Nonempty ((((fStar).obj ℱ).over (F.obj V)).GeneratingSections) := by
  -- Proof comment: after identifying the target chart with the localized pullback of `ℱ.over V`,
  -- use the global generator-preservation instance from Lemma `18.17.2`.
  sorry

/-- Helper for Lemma 18.23.4: a chart generated by `r` global sections remains generated by `r`
global sections after pullback. -/
private theorem pullbackGeneratedByChart
    (ℱ : ModD) (r : ℕ) {V : D} [SheafOfModules.IsGeneratedBy (ℱ.over V) r] :
    SheafOfModules.IsGeneratedBy (((fStar).obj ℱ).over (F.obj V)) r := by
  -- Proof comment: the chartwise pullback normalization reduces this directly to the fixed-rank
  -- global pullback preservation statement.
  sorry

-- Proof sketch: use Lemma `18.23.3` to test local freeness on a cover by restrictions, then apply
-- Lemma `18.17.2` on each localized ringed-site square to preserve the corresponding global free
-- property after pullback.
/-- Lemma 18.23.4 (1): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves locally free
`\mathcal O_\mathcal D`-modules. -/
@[stacks 03DO]
theorem pullback_isLocallyFree
    (ℱ : ModD)
    [IsLocallyFree ℱ] :
    IsLocallyFree ((fStar).obj ℱ) := by
  -- Proof comment: replace local freeness by a cover whose chart restrictions are globally free,
  -- then pull each chart witness back using the global preservation theorem.
  rcases
      (isLocallyFree_iff_exists_cover_isFree_over (J := K) (𝒪 := 𝒪D) ℱ).1
        (inferInstance : IsLocallyFree ℱ) with
    ⟨I, Y, hY, hfreeY⟩
  refine
    (isLocallyFree_iff_exists_cover_isFree_over (J := J) (𝒪 := 𝒪C) ((fStar).obj ℱ)).2
      ⟨I, fun i ↦ F.obj (Y i), ?_, ?_⟩
  · exact pullbackCoverTargets (F := F) Y hY
  · intro i
    -- Proof comment: the chart `Y i` is globally free on the source side, so its pullback chart
    -- is globally free on the target side by the dedicated chart helper.
    let _ : SheafOfModules.IsFree (ℱ.over (Y i)) := hfreeY i
    exact pullbackFreeChart (F := F) (φ := φ) ℱ

-- Proof sketch: reduce finite local freeness to a covering by finite free restrictions using
-- Lemma `18.23.3`, and preserve each finite free local model under pullback via Lemma `18.17.2`.
/-- Lemma 18.23.4 (2): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves finite locally free
`\mathcal O_\mathcal D`-modules. -/
@[stacks 03DO]
theorem pullback_isFiniteLocallyFree
    (ℱ : ModD)
    [IsFiniteLocallyFree ℱ] :
    IsFiniteLocallyFree ((fStar).obj ℱ) := by
  -- Proof comment: use the global finite-free chart criterion and transport each chart through
  -- pullback.
  rcases
      (isFiniteLocallyFree_iff_exists_cover_isFiniteFree_over (J := K) (𝒪 := 𝒪D) ℱ).1
        (inferInstance : IsFiniteLocallyFree ℱ) with
    ⟨I, Y, hY, hfreeY⟩
  refine
    (isFiniteLocallyFree_iff_exists_cover_isFiniteFree_over
      (J := J) (𝒪 := 𝒪C) ((fStar).obj ℱ)).2
      ⟨I, fun i ↦ F.obj (Y i), pullbackCoverTargets (F := F) Y hY, ?_⟩
  intro i
  -- Proof comment: finite free source charts stay finite free after pullback.
  let _ : SheafOfModules.IsFiniteFree (ℱ.over (Y i)) := hfreeY i
  exact pullbackFiniteFreeChart (F := F) (φ := φ) ℱ

-- Proof sketch: use the local criterion from Lemma `18.23.3` to work on a cover where the
-- restriction is globally generated by sections, and then apply the global pullback-preservation
-- statement from Lemma `18.17.2` on each member of the cover.
/-- Lemma 18.23.4 (3): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves modules locally generated by sections. -/
@[stacks 03DO]
theorem pullback_isLocallyGeneratedBySections
    (ℱ : ModD)
    [IsLocallyGeneratedBySections ℱ] :
    IsLocallyGeneratedBySections ((fStar).obj ℱ) := by
  -- Proof comment: pass to a cover by globally generated restrictions and pull those generators
  -- back chartwise.
  rcases
      (isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
        (J := K) (𝒪 := 𝒪D) ℱ).1
        (inferInstance : IsLocallyGeneratedBySections ℱ) with
    ⟨I, Y, hY, hgenY⟩
  refine
    (isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
      (J := J) (𝒪 := 𝒪C) ((fStar).obj ℱ)).2
      ⟨I, fun i ↦ F.obj (Y i), pullbackCoverTargets (F := F) Y hY, ?_⟩
  intro i
  -- Proof comment: chartwise global generators pull back to global generators.
  let _ : Nonempty (ℱ.over (Y i)).GeneratingSections := hgenY i
  exact pullbackGloballyGeneratedChart (F := F) (φ := φ) ℱ

-- Proof sketch: choose a cover on which `ℱ` is globally generated by exactly `r` sections by
-- Lemma `18.23.3`, and transport each local epimorphism from a rank-`r` free module along the
-- pullback functor using Lemma `18.17.2`.
/-- Lemma 18.23.4 (4): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves the property of being locally generated by
`r` sections. -/
@[stacks 03DO]
theorem pullback_isLocallyGeneratedBy
    (ℱ : ModD)
    (r : ℕ) [IsLocallyGeneratedBy ℱ r] :
    IsLocallyGeneratedBy ((fStar).obj ℱ) r := by
  -- Proof comment: the fixed-rank local criterion reduces to chartwise global generation by `r`
  -- sections, which is preserved by pullback on each chart.
  rcases
      (isLocallyGeneratedBy_iff_exists_cover_isGloballyGeneratedBy_over
        (J := K) (𝒪 := 𝒪D) ℱ r).1
        (inferInstance : IsLocallyGeneratedBy ℱ r) with
    ⟨I, Y, hY, hgenY⟩
  refine
    (isLocallyGeneratedBy_iff_exists_cover_isGloballyGeneratedBy_over
      (J := J) (𝒪 := 𝒪C) ((fStar).obj ℱ) r).2
      ⟨I, fun i ↦ F.obj (Y i), pullbackCoverTargets (F := F) Y hY, ?_⟩
  intro i
  -- Proof comment: the rank-`r` generator witness is transported chartwise by pullback.
  let _ : SheafOfModules.IsGeneratedBy (ℱ.over (Y i)) r := hgenY i
  exact pullbackGeneratedByChart (F := F) (φ := φ) ℱ r

-- Proof sketch: finite type is the local form of finite global generation; apply the cover
-- criterion from Lemma `18.23.3` and then preserve finite global generation on each slice by
-- Lemma `18.17.2`.
/-- Lemma 18.23.4 (5): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves modules of finite type. -/
@[stacks 03DO]
theorem pullback_isFiniteType
    (ℱ : ModD)
    [ℱ.IsFiniteType] :
    ((fStar).obj ℱ).IsFiniteType := by
  -- Proof comment: this clause is already the global finite-type pullback preservation instance
  -- from Lemma `18.17.2`.
  infer_instance

-- Proof sketch: use Lemma `18.23.3` to check quasi-coherence on a cover by restrictions with
-- global presentations, then pull those presentations back locally using Lemma `18.17.2`.
/-- Lemma 18.23.4 (6): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves quasi-coherent modules. -/
@[stacks 03DO]
theorem pullback_isQuasicoherent
    (ℱ : ModD)
    [ℱ.IsQuasicoherent] :
    ((fStar).obj ℱ).IsQuasicoherent := by
  -- Proof comment: quasi-coherence is preserved globally by pullback in Lemma `18.17.2`.
  infer_instance

-- Proof sketch: finite presentation is local through finite global presentations on a cover; use
-- Lemma `18.23.3` to reduce to that form and preserve each finite presentation under pullback by
-- Lemma `18.17.2`.
/-- Lemma 18.23.4 (7): for a morphism of ringed topoi presented by
`F : \mathcal D \to \mathcal C`, pullback preserves modules of finite presentation. -/
@[stacks 03DO]
theorem pullback_isFinitePresentation
    (ℱ : ModD)
    [ℱ.IsFinitePresentation] :
    ((fStar).obj ℱ).IsFinitePresentation := by
  -- Proof comment: finite presentation is preserved globally by pullback in Lemma `18.17.2`.
  infer_instance

end SheafOfModules.RingedSite
