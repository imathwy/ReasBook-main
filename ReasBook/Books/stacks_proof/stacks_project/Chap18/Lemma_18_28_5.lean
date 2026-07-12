import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u v

/-- Helper for Lemma 18.28.5: evaluation functors on a functor category jointly reflect
isomorphisms. -/
private theorem functor_evaluation_jointly_reflects_isomorphisms
    {J C : Type*} [Category J] [Category C] :
    JointlyReflectIsomorphisms
      ((CategoryTheory.evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
  refine ⟨fun {F G} α _ ↦ ?_⟩
  -- A natural transformation is an isomorphism once all of its components are.
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using (inferInstance : IsIso (((CategoryTheory.evaluation J C).obj j).map α))

namespace CategoryTheory.ShortComplex

/-- Helper for Lemma 18.28.5: a short complex in a functor category is short exact precisely when
all of its evaluations are short exact. -/
theorem shortExact_iff_pointwise_shortExact_functor_category
    {J A : Type*} [Category J] [Category A] [Abelian A]
    {S : ShortComplex (J ⥤ A)} :
    S.ShortExact ↔ ∀ j, (S.map ((evaluation J A).obj j)).ShortExact := by
  constructor
  · intro hS j
    -- Exactness, monomorphy, and epimorphy in a functor category can be read on components.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((functor_evaluation_jointly_reflects_isomorphisms (J := J) (C := A)).exact_iff S).1
          hS.exact j
    · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f j
    · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g j
  · intro hS
    -- Route correction: package the pointwise short exact rows once, then reassemble the global
    -- row instead of rebuilding `ShortComplex.functorEquivalence` transports at each use site.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((functor_evaluation_jointly_reflects_isomorphisms (J := J) (C := A)).exact_iff S).2
          fun j ↦ (hS j).exact
    · exact (NatTrans.mono_iff_mono_app S.f).2 fun j ↦ (hS j).mono_f
    · exact (NatTrans.epi_iff_epi_app S.g).2 fun j ↦ (hS j).epi_g

end CategoryTheory.ShortComplex

/-- Helper for Lemma 18.28.5: the stagewise tensor-right images of a short complex assemble into a
diagram of short complexes. -/
private def tensorRight_shortComplexDiagram
    {C : Type*} [Category C] [MonoidalCategory C] [HasZeroMorphisms C]
    {J : Type*} [Category J] (S : ShortComplex C) (F : J ⥤ C) :
    J ⥤ ShortComplex C where
  obj j := S.map (tensorRight (F.obj j))
  map {j j'} f :=
    -- Each diagram map acts termwise by tensoring with the structural map `F.map f`.
    ShortComplex.homMk
      (α_ (S.X₁) (F.map f))
      (α_ (S.X₂) (F.map f))
      (α_ (S.X₃) (F.map f))
      (by simp [Category.assoc])
      (by simp [Category.assoc])
  map_id j := by
    ext <;> simp
  map_comp {j j' j''} f g := by
    ext <;> simp [Category.assoc]

/-- Helper for Lemma 18.28.5: exact colimits in `AddCommGrpCat` induce exact colimits in
`ModuleCat R` through the forgetful functor. -/
private theorem moduleCat_hasExactColimitsOfShape
    {R : Type*} [CommRing R] {J : Type*} [Category J]
    [HasExactColimitsOfShape J AddCommGrpCat.{max u v}]
    :
    HasExactColimitsOfShape J (ModuleCat R) := by
  -- Exactness descends across the faithful forgetful functor to abelian groups.
  let _ : HasColimitsOfShape J (ModuleCat R) := by
    infer_instance
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat R) AddCommGrpCat.{max u v})

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

local instance {J : Type (max u v)} [Category J] :
    HasColimitsOfShape J
      (PresheafOfModules.{max u v, v, u, max u v} (ringPresheaf 𝒪)) := by
  infer_instance

local instance {I : Type (max u v)} :
    HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{max u v, v, u, max u v} (ringPresheaf 𝒪)) := by
  infer_instance

/- Domain-style sampling for Lemma 18.28.5:
- primary domain: closure of flat module objects under filtered colimits and coproducts in
  presheaf and sheaf module categories;
- sampled owner declarations:
  `Module.Flat`,
  `PresheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `PresheafOfModules.hasColimitsOfSize`,
  `#synth HasColimits (Mod(𝒪))`;
- best owner abstraction: flatness is owned by the typeclasses
  `PresheafOfModules.IsFlat` and `SheafOfModules.RingedSite.IsFlat`, while the source-facing
  hypotheses should expose stagewise flatness explicitly; filtered colimits and direct sums should
  use the ambient canonical colimit/coproduct owners rather than carry local existence binders;
- primitive data: a filtered diagram or an indexed family of module objects;
- derived API: the colimit- and coproduct-closure lemmas below.

Source/core/bridge triage:
- `source-facing`: flatness is preserved by filtered colimits and direct sums;
- `core/canonical`: the flatness owner typeclasses on the ambient module categories;
- `bridge/view`: the colimit constructions computing the direct sums and filtered colimits.

This file should therefore keep the source-facing closure statements while reusing the canonical
flatness owners already used upstream, with stagewise flatness exposed as an explicit theorem
hypothesis rather than a parallel wrapper API.
-/

/-- Helper for Lemma 18.28.5: evaluation preserves the chosen colimit of a presheaf-module
diagram. -/
noncomputable def evaluation_colimit_iso {J : Type (max u v)} [Category J]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪)) (X : Cᵒᵖ) :
    (PresheafOfModules.evaluation (ringPresheaf 𝒪) X).obj (colimit F) ≅
      colimit (F ⋙ PresheafOfModules.evaluation (ringPresheaf 𝒪) X) :=
  -- Reuse the canonical comparison isomorphism for a colimit preserved by evaluation.
  preservesColimitIso (PresheafOfModules.evaluation (ringPresheaf 𝒪) X) F

/-- Helper for Lemma 18.28.5: evaluation at a fixed object of the site is exact on presheaves of
modules. -/
private theorem evaluation_exact (X : Cᵒᵖ) :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (ModuleCat (𝒪.obj X))
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) X) := by
  -- Evaluation computes finite limits and colimits pointwise, so it is exact.
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.5: evaluating a short exact row of presheaves of modules at any object
of the site gives a short exact row of modules. -/
private theorem evaluation_shortExact_of_shortExact
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact) (X : Cᵒᵖ) :
    (S.map (PresheafOfModules.evaluation (ringPresheaf 𝒪) X)).ShortExact := by
  let F := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  let G : ModuleCat ((ringPresheaf 𝒪).obj X) ⥤ AddCommGrpCat.{max u v} := forget₂ _ _
  have hToPresheaf :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
        (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)) :=
    (ExactFunctor.of (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).property
  have hUnderlying :
      (S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).ShortExact := by
    -- First forget the module structure, where evaluation is literal functor-category evaluation.
    exact
      (((Functor.exact_tfae (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).out 3 0).1
        (by simpa [exactFunctor_iff] using hToPresheaf)) S hS
  have hForget : ((S.map F).map G).ShortExact := by
    -- After forgetting the module structure, evaluation is the ordinary functor-category
    -- evaluation, so pointwise short exactness follows immediately.
    simpa [F, PresheafOfModules.evaluation] using
      CategoryTheory.ShortComplex.shortExact_iff_pointwise_shortExact_functor_category.1
        (S := S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)))
        hUnderlying X
  -- Faithfulness of the forgetful functor reflects short exactness back to modules.
  exact ShortComplex.reflects_shortExact_of_faithful G hForget

/-- Helper for Lemma 18.28.5: after evaluating at `X`, the stagewise tensor-right images of a
short exact row form the canonical filtered diagram of short complexes over `𝒪(X)`. -/
private noncomputable def evaluated_tensorRight_colimit_shortComplex_iso
    {J : Type (max u v)} [Category J]
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪)) (X : Cᵒᵖ) :
    let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
    let SX := S.map evalX
    let GX := tensorRight_shortComplexDiagram SX (F ⋙ evalX)
    colim.mapShortComplex GX
        (colimit.isColimit GX.X₁)
        (colimit.cocone GX.X₂)
        (colimit.cocone GX.X₃)
        (colim.map GX.f)
        (colim.map GX.g)
        (fun j ↦ by simpa [GX] using colimit.ι_map GX.f j)
        (fun j ↦ by simpa [GX] using colimit.ι_map GX.g j) ≅
      ((S.map (tensorRight (colimit F))).map evalX) :=
  let e₁ :=
    (evaluation_colimit_iso (𝒪 := 𝒪) (F := F ⋙ tensorRight (evalX.obj S.X₁)) X).symm ≪≫
      (preservesColimitIso (tensorRight ((evaluation_colimit_iso (𝒪 := 𝒪) F X).hom))
        (F ⋙ evalX)).symm
  let e₂ :=
    (evaluation_colimit_iso (𝒪 := 𝒪) (F := F ⋙ tensorRight (evalX.obj S.X₂)) X).symm ≪≫
      (preservesColimitIso (tensorRight ((evaluation_colimit_iso (𝒪 := 𝒪) F X).hom))
        (F ⋙ evalX)).symm
  let e₃ :=
    (evaluation_colimit_iso (𝒪 := 𝒪) (F := F ⋙ tensorRight (evalX.obj S.X₃)) X).symm ≪≫
      (preservesColimitIso (tensorRight ((evaluation_colimit_iso (𝒪 := 𝒪) F X).hom))
        (F ⋙ evalX)).symm
  -- Proof comment: compare the explicit colimit row with evaluation of tensor-by-colimit termwise,
  -- then normalize the two structure-map squares on colimit legs.
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · ext j
    -- Proof comment: the first square is the colimit compatibility for `GX.f`, followed by the
    -- two colimit-comparison isomorphisms.
    simp only [e₁, e₂, Iso.trans_hom, Category.assoc]
    rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
    simp only [tensorRight_shortComplexDiagram]
    rw [← Category.assoc, ι_colimMap_assoc]
    simp [Category.assoc]
  · ext j
    -- Proof comment: the second square is identical, now for `GX.g`.
    simp only [e₂, e₃, Iso.trans_hom, Category.assoc]
    rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
    simp only [tensorRight_shortComplexDiagram]
    rw [← Category.assoc, ι_colimMap_assoc]
    simp [Category.assoc]

/-- Helper for Lemma 18.28.5: each evaluated stage of the tensor-right diagram is short exact
because flatness makes tensor-right exact before evaluation. -/
private theorem evaluatedTensorRightStage_shortExact
    {J : Type (max u v)} [Category J]
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))) (hS : S.ShortExact)
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ j, IsFlat (F.obj j)) (X : Cᵒᵖ) (j : J) :
    let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
    let SX := S.map evalX
    let GX := tensorRight_shortComplexDiagram SX (F ⋙ evalX)
    (GX.obj j).ShortExact := by
  let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  let W := tensorRight (F.obj j)
  let hExactW :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        W :=
    (hflat j).exact_tensor
  let _ : PreservesFiniteLimits W := (exactFunctor_iff W).1 hExactW |>.1
  let _ : PreservesFiniteColimits W := (exactFunctor_iff W).1 hExactW |>.2
  have hStagePresheaf : (S.map W).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS W
  -- Proof comment: tensor-right by `F.obj j` is exact, and evaluation at `X` preserves the
  -- resulting short exact row.
  simpa [evalX, W, tensorRight_shortComplexDiagram] using
    evaluation_shortExact_of_shortExact (𝒪 := 𝒪) (S := S.map W) hStagePresheaf X

/-- Helper for Lemma 18.28.5: after evaluating at a fixed object, tensoring by the colimit of a
diagram of flat presheaf modules preserves short exactness. -/
private theorem evaluation_tensorRight_shortExact_of_colimit
    {J : Type (max u v)} [Category J]
    [HasExactColimitsOfShape J AddCommGrpCat.{max u v}]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))) (hS : S.ShortExact)
    (hflat : ∀ j, IsFlat (F.obj j)) (X : Cᵒᵖ) :
    ((S.map (tensorRight (colimit F))).map
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) X)).ShortExact := by
  let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  let SX := S.map evalX
  let GX := tensorRight_shortComplexDiagram SX (F ⋙ evalX)
  let _ : HasExactColimitsOfShape J (ModuleCat ((ringPresheaf 𝒪).obj X)) :=
    moduleCat_hasExactColimitsOfShape (R := (ringPresheaf 𝒪).obj X) (J := J)
  have hGX : ∀ j, (GX.obj j).ShortExact := by
    intro j
    simpa [evalX, SX, GX] using
      evaluatedTensorRightStage_shortExact (𝒪 := 𝒪) S hS F hflat X j
  have hColim :
      (colim.mapShortComplex GX
        (colimit.isColimit GX.X₁)
        (colimit.cocone GX.X₂)
        (colimit.cocone GX.X₃)
        (colim.map GX.f)
        (colim.map GX.g)
        (fun j ↦ by simpa [GX] using colimit.ι_map GX.f j)
        (fun j ↦ by simpa [GX] using colimit.ι_map GX.g j)).ShortExact := by
    -- Proof comment: exactness, mono, and epi all descend through exact colimits in the module
    -- category after assembling the stagewise short exact diagram.
    exact
      shortExact_of_isColimit_of_stagewise_shortExact
        GX
        (colimit.cocone GX)
        (colimit.isColimit GX)
        hGX
  -- Proof comment: transport the colimit short exact row to the tensor-by-colimit row via the
  -- structural comparison isomorphism.
  exact
    ShortComplex.shortExact_of_iso
      (evaluated_tensorRight_colimit_shortComplex_iso (𝒪 := 𝒪) S F X)
      hColim

/-- Helper for Lemma 18.28.5: tensoring a short complex of sheaves by a colimit agrees with the
colimit of the stagewise tensor-right diagram. -/
private noncomputable def tensorRight_colimit_shortComplex_iso
    {K : Type (max u v)} [Category K]
    (F : K ⥤ Mod(𝒪)) (S : ShortComplex (Mod(𝒪))) :
    let G := tensorRight_shortComplexDiagram S F
    colim.mapShortComplex G
        (colimit.isColimit G.X₁)
        (colimit.cocone G.X₂)
        (colimit.cocone G.X₃)
        (colim.map G.f)
        (colim.map G.g)
        (fun k ↦ by simpa [G] using colimit.ι_map G.f k)
        (fun k ↦ by simpa [G] using colimit.ι_map G.g k) ≅
      S.map (tensorRight (colimit F)) := by
  let G := tensorRight_shortComplexDiagram S F
  let e₁ := (preservesColimitIso (tensorRight S.X₁) F).symm
  let e₂ := (preservesColimitIso (tensorRight S.X₂) F).symm
  let e₃ := (preservesColimitIso (tensorRight S.X₃) F).symm
  -- Proof comment: identify the explicit colimit short complex with tensoring by the colimit
  -- termwise, then normalize the two compatibility squares on cocone legs.
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · ext k
    rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
    simpa [G, tensorRight_shortComplexDiagram, Category.assoc] using
      (ι_colimMap_assoc G.f k)
  · ext k
    rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
    simpa [G, tensorRight_shortComplexDiagram, Category.assoc] using
      (ι_colimMap_assoc G.g k)

/-- Helper for Lemma 18.28.5: each stage of the sheaf tensor-right diagram is short exact because
flatness makes tensor-right exact on `Mod(𝒪)`. -/
private theorem tensorRightStage_shortExact
    {K : Type (max u v)} [Category K]
    (F : K ⥤ Mod(𝒪)) (S : ShortComplex (Mod(𝒪))) (hS : S.ShortExact)
    (hflat : ∀ k, IsFlat 𝒪 (F.obj k)) (k : K) :
    let G := tensorRight_shortComplexDiagram S F
    (G.obj k).ShortExact := by
  let W := tensorRight (F.obj k)
  let hExactW : exactFunctor (Mod(𝒪)) (Mod(𝒪)) W := (hflat k).exact_tensor
  let _ : PreservesFiniteLimits W := (exactFunctor_iff W).1 hExactW |>.1
  let _ : PreservesFiniteColimits W := (exactFunctor_iff W).1 hExactW |>.2
  -- Proof comment: tensor-right by the flat stage `F.obj k` is exact, so the stage row is short
  -- exact without any colimit transport.
  simpa [W, tensorRight_shortComplexDiagram] using
    (ShortComplex.ShortExact.map_of_exact hS W)

/-- Helper for Lemma 18.28.5: exact colimits of flat presheaf modules stay flat. -/
private theorem isFlat_colimit_of_hasExactColimits
    {J : Type (max u v)} [Category J]
    [HasExactColimitsOfShape J AddCommGrpCat.{max u v}]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ j, IsFlat (F.obj j)) :
    IsFlat (colimit F) := by
  refine ⟨?_⟩
  -- Route correction: rebuild short exactness globally by forgetting to additive presheaves,
  -- where the pointwise evaluations of the tensor-by-colimit row are already short exact.
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight (colimit F))).2 fun S hS ↦ by
        let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) :=
          S.map (tensorRight (colimit F))
        let U := PresheafOfModules.toPresheaf (ringPresheaf 𝒪)
        have hUnderlyingPointwise :
            ∀ X : Cᵒᵖ,
              ((T.map U).map ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj X)).ShortExact := by
          intro X
          let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
          let G : ModuleCat ((ringPresheaf 𝒪).obj X) ⥤ AddCommGrpCat.{max u v} := forget₂ _ _
          have hTX : (T.map evalX).ShortExact :=
            evaluation_tensorRight_shortExact_of_colimit (𝒪 := 𝒪) F S hS hflat X
          have hForgetX : (((T.map evalX).map G)).ShortExact := by
            simpa using hTX.map_of_exact G
          -- Forgetting module structure identifies evaluation with ordinary functor evaluation.
          simpa [T, U, evalX, PresheafOfModules.evaluation] using hForgetX
        have hUnderlying : (T.map U).ShortExact := by
          -- A short complex of additive presheaves is short exact once all pointwise rows are.
          exact
            (CategoryTheory.ShortComplex.shortExact_iff_pointwise_shortExact_functor_category
              (S := T.map U)).2 hUnderlyingPointwise
        have hT : T.ShortExact := by
          -- The faithful forgetful functor reflects short exactness back to presheaf modules.
          exact ShortComplex.reflects_shortExact_of_faithful U hUnderlying
        exact ⟨(T.exact_iff_exact_toComposableArrows).1 hT.exact, hT.mono_f, hT.epi_g⟩

-- Proof sketch: evaluate the filtered colimit presheaf at each object of `C`. The resulting
-- tensorized short complex is a filtered colimit of short exact complexes after evaluation, so
-- the exact-functor criterion from Lemma `18.28.2` applies directly.
/-- Lemma 18.28.5 (1): a filtered colimit of flat presheaves of modules over a presheaf of
commutative rings is flat. -/
@[stacks 03EU]
theorem isFlat_colimit_of_isFiltered {J : Type (max u v)} [Category J] [IsFiltered J]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ j, IsFlat (F.obj j)) :
    IsFlat (colimit F) := by
  -- Route correction: do not re-enter the abandoned sectionwise-flatness converse. The source
  -- route is to tensor a fixed short exact row stagewise, evaluate only afterwards, and descend
  -- short exactness through the filtered colimit using `Limits.colim.exact_mapShortComplex`.
  -- The new structural helper `evaluated_tensorRight_colimit_shortComplex_iso` isolates the only
  -- transport-heavy step left before applying `Limits.colim.exact_mapShortComplex`.
  let _ : HasExactColimitsOfShape J AddCommGrpCat.{max u v} := by
    infer_instance
  exact isFlat_colimit_of_hasExactColimits (𝒪 := 𝒪) F hflat

-- Proof sketch: a direct sum is the canonical coproduct `∐ fun i ↦ F i`. Evaluate it objectwise,
-- tensorize the short exact row termwise, and then use the exact-functor criterion directly.
/-- Lemma 18.28.5 (2): a direct sum of flat presheaves of modules over a presheaf of commutative
rings is flat. -/
@[stacks 03EU]
theorem isFlat_coproduct {I : Type (max u v)}
    (F : I → PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) := by
  -- A coproduct is the colimit of the corresponding discrete diagram, so reuse the generic
  -- exact-colimit closure theorem rather than the filtered specialization.
  let _ : HasExactColimitsOfShape (Discrete I) AddCommGrpCat.{max u v} := by
    infer_instance
  simpa using
    isFlat_colimit_of_hasExactColimits (𝒪 := 𝒪) (Discrete.functor F)
      (fun i ↦ by simpa using hflat i.as)

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

local instance {K : Type (max u v)} [Category K] :
    HasColimitsOfShape K (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) := by
  infer_instance

local instance {I : Type (max u v)} :
    HasColimitsOfShape (Discrete I) (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) := by
  infer_instance

local instance {I : Type (max u v)}
    (F : I → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :
    HasColimit (Discrete.functor F) := by
  let h :
      HasColimitsOfShape (Discrete I)
        (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) := inferInstance
  exact h.has_colimit (Discrete.functor F)

/-- Helper for Lemma 18.28.5: exactness of the tensor-right functor is stable under any exact
colimit of sheaves of modules. -/
private theorem tensorRight_shortExact_of_colimit
    {K : Type (max u v)} [Category K]
    [HasExactColimitsOfShape K (Mod(𝒪))]
    (F : K ⥤ Mod(𝒪)) (S : ShortComplex (Mod(𝒪))) (hS : S.ShortExact)
    (hflat : ∀ k, IsFlat 𝒪 (F.obj k)) :
    (S.map (tensorRight (colimit F))).ShortExact := by
  let G := tensorRight_shortComplexDiagram S F
  have hG : ∀ k, (G.obj k).ShortExact := by
    intro k
    simpa [G] using tensorRightStage_shortExact (J := J) (𝒪 := 𝒪) F S hS hflat k
  have hColim :
      (colim.mapShortComplex G
        (colimit.isColimit G.X₁)
        (colimit.cocone G.X₂)
        (colimit.cocone G.X₃)
        (colim.map G.f)
        (colim.map G.g)
        (fun k ↦ by simpa [G] using colimit.ι_map G.f k)
        (fun k ↦ by simpa [G] using colimit.ι_map G.g k)).ShortExact := by
    -- Proof comment: the sheaf row is a colimit of stagewise short exact rows in `Mod(𝒪)`.
    exact
      shortExact_of_isColimit_of_stagewise_shortExact
        G
        (colimit.cocone G)
        (colimit.isColimit G)
        hG
  -- Proof comment: transport the colimit short exact row along the canonical tensor/colimit
  -- comparison isomorphism.
  exact ShortComplex.shortExact_of_iso (tensorRight_colimit_shortComplex_iso (𝒪 := 𝒪) F S) hColim

/-- Helper for Lemma 18.28.5: exact colimits of flat sheaves of modules stay flat. -/
private theorem isFlat_colimit_of_hasExactColimits
    {K : Type (max u v)} [Category K]
    [HasExactColimitsOfShape K (Mod(𝒪))]
    (F : K ⥤ Mod(𝒪))
    (hflat : ∀ k, IsFlat 𝒪 (F.obj k)) :
    IsFlat 𝒪 (colimit F) := by
  refine ⟨?_⟩
  -- Use the Chapter 12 exact-functor criterion directly in `Mod(𝒪)`.
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorRight (colimit F))).2 fun S hS ↦ by
        have hT :
            (S.map (tensorRight (colimit F))).ShortExact :=
          tensorRight_shortExact_of_colimit (J := J) (𝒪 := 𝒪) F S hS hflat
        exact ⟨
          ((S.map (tensorRight (colimit F))).exact_iff_exact_toComposableArrows).1 hT.exact,
          hT.mono_f,
          hT.epi_g
        ⟩

-- Proof sketch: pass to underlying presheaves, where filtered colimits are computed objectwise
-- only if needed; the intended proof is to use exactness of tensoring directly in `Mod(𝒪)`.
/-- Lemma 18.28.5 (3): a filtered colimit of flat sheaves of modules over a sheaf of
commutative rings `\mathcal O` on a site is flat. -/
@[stacks 03EU]
theorem isFlat_colimit_of_isFiltered {K : Type (max u v)} [Category K] [IsFiltered K]
    (F : K ⥤ Mod(𝒪))
    (hflat : ∀ k, IsFlat 𝒪 (F.obj k)) :
    IsFlat 𝒪 (colimit F) := by
  let _ : HasExactColimitsOfShape K (Mod(𝒪)) := by
    infer_instance
  exact isFlat_colimit_of_hasExactColimits (J := J) (𝒪 := 𝒪) F hflat

-- Proof sketch: a direct sum is the canonical coproduct `∐ fun i ↦ F i`. Apply the sheaf
-- filtered-colimit statement to the corresponding coproduct computation, equivalently reason on
-- underlying presheaves and use the direct-sum preservation of flatness from part `(2)`.
/-- Lemma 18.28.5 (4): a direct sum of flat sheaves of modules over a sheaf of commutative rings
`\mathcal O` on a site is flat. -/
@[stacks 03EU]
theorem isFlat_coproduct {I : Type (max u v)}
    (F : I → Mod(𝒪))
    (hflat : ∀ i, IsFlat 𝒪 (F i)) :
    IsFlat 𝒪 (∐ F) := by
  let _ : HasExactColimitsOfShape (Discrete I) (Mod(𝒪)) := by
    infer_instance
  simpa using
    isFlat_colimit_of_hasExactColimits (J := J) (𝒪 := 𝒪) (Discrete.functor F)
      (fun i ↦ by simpa using hflat i.as)

end SheafOfModules.RingedSite
