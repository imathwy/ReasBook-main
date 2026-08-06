import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Category.CompactlyGenerated
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_1_14
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15

open CategoryTheory

universe u w

-- Definition 5.2.8 is source-facing, so `wU` and `U` remain full subcategories of `TopCat`.
-- The reusable core owner for the compactly generated side is still mathlib's bundled
-- `CompactlyGenerated`, and the file exposes that bridge explicitly below.

/-- The object property on `TopCat` selecting weak Hausdorff spaces. -/
abbrev weakHausdorffProperty : ObjectProperty TopCat.{w} :=
  fun X ↦ WeaklyHausdorffSpace.{w, w} X

/-- The object property on `TopCat` selecting compactly generated weak Hausdorff spaces. -/
abbrev compactlyGeneratedWeakHausdorffProperty :
    ObjectProperty TopCat.{w} :=
  fun X ↦ CompactlyGeneratedWeakHausdorffSpace.{w, w} X

/-- The category `wU` from Definition 5.2.8 is formalized as the full
subcategory of `TopCat` cut out by `WeaklyHausdorffSpace`. -/
abbrev weakHausdorffSpaceCat :=
  ObjectProperty.FullSubcategory (weakHausdorffProperty.{w})

/-- The canonical inclusion of `wU` into `TopCat`. -/
abbrev weakHausdorffSpaceCatToTop : weakHausdorffSpaceCat.{w} ⥤ TopCat.{w} :=
  weakHausdorffProperty.ι

/-- The book's category `U` of compactly generated weak Hausdorff spaces. -/
abbrev compactlyGeneratedWeakHausdorffSpaceCat :=
  ObjectProperty.FullSubcategory compactlyGeneratedWeakHausdorffProperty

/-- The canonical inclusion of `U` into `TopCat`. -/
abbrev compactlyGeneratedWeakHausdorffSpaceCatToTop :
    compactlyGeneratedWeakHausdorffSpaceCat ⥤ TopCat.{w} :=
  compactlyGeneratedWeakHausdorffProperty.ι

/-- Helper for Definition 5.2.8: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by `TopologicalSpace.compactlyGenerated.{u, w}`. -/
private theorem continuous_compHaus_to_compactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators for the coinduced topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- A continuous map remains continuous after replacing both source and target by their
compactly generated topologies. -/
private theorem continuous_compactlyGenerated_of_continuous
    {X : Type w} [TopologicalSpace X] {Y : Type w} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) :
    @Continuous X Y (TopologicalSpace.compactlyGenerated.{u, w} X)
      (TopologicalSpace.compactlyGenerated.{u, w} Y) f :=
  by
    have hprobe :
        ∀ (S : CompHaus.{u}) (g : C(S, X)),
          @Continuous S Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y) (f ∘ g) := by
      intro S g
      -- Each probe composite stays continuous after replacing the codomain by its k-topology.
      simpa [Function.comp] using
        (continuous_compHaus_to_compactlyGenerated (Y := Y) (f := f ∘ g)
          (hf := hf.comp g.continuous))
    -- It is enough to test continuity after precomposing with compact Hausdorff probes.
    exact
      continuous_from_compactlyGenerated (t := TopologicalSpace.compactlyGenerated.{u, w} Y) f
        hprobe

/-- A carrier-level type synonym used to bundle the k-ification topology. -/
structure Kified (X : Type w) where
  /-- Forget the k-ified carrier back to the underlying point of `X`. -/
  of : X

/-- The k-ified carrier inherits the compactly generated replacement topology from `X`. -/
@[reducible]
def kifiedTopologicalSpace (X : Type w) [TopologicalSpace X] :
    TopologicalSpace (Kified X) :=
  TopologicalSpace.induced Kified.of (TopologicalSpace.compactlyGenerated.{u, w} X)

/-- The default topology on `Kified X` uses compact Hausdorff test spaces in the same universe as
`X`. The more general universe-parameterized k-ification topology remains available as
`kifiedTopologicalSpace.{u, w} X` when needed for categorical comparisons. -/
instance instTopologicalSpaceKified (X : Type w) [TopologicalSpace X] :
    TopologicalSpace (Kified X) :=
  kifiedTopologicalSpace.{w, w} X

/-- Helper for Definition 5.2.8: `Kified.of` embeds the default k-ification into the raw
compactly generated replacement of `X`. -/
private theorem kifiedOf_isEmbedding
    (X : Type w) [TopologicalSpace X] :
    @Topology.IsEmbedding (Kified X) X (kifiedTopologicalSpace.{w, w} X)
      (TopologicalSpace.compactlyGenerated.{w, w} X) Kified.of := by
  -- The default k-ification topology is induced from the raw compactly generated topology.
  have hInjective : Function.Injective (Kified.of : Kified X → X) := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  let tk : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{w, w} X
  let _ : TopologicalSpace X := tk
  simpa [kifiedTopologicalSpace] using
    (hInjective.isEmbedding_induced :
      @Topology.IsEmbedding (Kified X) X
        (TopologicalSpace.induced Kified.of tk) tk Kified.of)

/-- Helper for Definition 5.2.8: the raw compactly generated replacement topology on `X` is
compactly generated in the textbook sense. -/
private theorem rawUCompactlyGeneratedSpaceCompactlyGenerated
    (X : Type w) [t : TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{w} X (TopologicalSpace.compactlyGenerated.{w, w} X) := by
  -- Closedness can be checked against compact Hausdorff probes into the original topology.
  refine @uCompactlyGeneratedSpace_of_isClosed X
    (TopologicalSpace.compactlyGenerated.{w, w} X) ?_
  intro A hA
  refine isClosed_compactlyGenerated_of_compHausClosed (X := X) (A := A) ?_
  intro S f
  have hfk :
      @Continuous S X inferInstance (TopologicalSpace.compactlyGenerated.{w, w} X) (f : S → X) :=
    continuous_compHaus_to_compactlyGenerated (Y := X) (f := f) f.continuous
  let fk : @ContinuousMap S X inferInstance (TopologicalSpace.compactlyGenerated.{w, w} X) :=
    @ContinuousMap.mk S X inferInstance (TopologicalSpace.compactlyGenerated.{w, w} X) f hfk
  -- The compact-Hausdorff detector hypothesis applies to the reinterpreted probe `fk`.
  have hClosedPreimage : IsClosed ((fk : S → X) ⁻¹' A) := hA S fk
  simpa [fk] using hClosedPreimage

/-- Helper for Definition 5.2.8: the raw compactly generated replacement of a weak Hausdorff
space is still weak Hausdorff. -/
private theorem rawWeaklyHausdorffSpaceCompactlyGenerated
    (X : Type w) [t : TopologicalSpace X] [hwh : WeaklyHausdorffSpace.{w, w} X] :
    @WeaklyHausdorffSpace.{w, w} X (TopologicalSpace.compactlyGenerated.{w, w} X) := by
  refine @WeaklyHausdorffSpace.mk.{w, w} X (TopologicalSpace.compactlyGenerated.{w, w} X) ?_
  intro K _ _ _ g hg
  have hgOriginal : @Continuous K X ‹TopologicalSpace K› t g := by
    -- Forgetting the raw k-topology recovers continuity into the original topology on `X`.
    simpa using
      (@Continuous.comp K X X ‹TopologicalSpace K›
        (TopologicalSpace.compactlyGenerated.{w, w} X) t g id
        (continuous_id_compactlyGenerated (X := X) (t := t)) hg)
  have hClosedOriginal : @IsClosed X t (Set.range g) := hwh.isClosed_range g hgOriginal
  -- Closed subsets of the original topology are compactly closed, hence closed in the raw
  -- k-topology.
  exact
    @isClosed_compactlyGenerated_of_isCompactlyClosed X t (Set.range g)
      (@IsClosed.isCompactlyClosed X t (Set.range g) hClosedOriginal)

/-- Helper for Definition 5.2.8: the default `Kified X` topology is coinduced from the raw
compactly generated topology on `X` via `Kified.mk`. -/
private theorem kifiedTopologicalSpace_eq_coinduced
    (X : Type w) [TopologicalSpace X] :
    kifiedTopologicalSpace.{w, w} X =
      TopologicalSpace.coinduced Kified.mk (TopologicalSpace.compactlyGenerated.{w, w} X) := by
  let e : Kified X ≃ X :=
    { toFun := Kified.of
      invFun := Kified.mk
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        rfl }
  -- Rewrite the induced spelling using the equivalence between `Kified X` and `X`.
  simpa [kifiedTopologicalSpace, e] using
    congrArg (fun F ↦ F (TopologicalSpace.compactlyGenerated.{w, w} X)) e.coinduced_symm.symm

/-- Helper for Definition 5.2.8: the default k-ification of `X` is compactly generated. -/
private theorem uCompactlyGeneratedSpaceKified
    (X : Type w) [TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{w} (Kified X) (kifiedTopologicalSpace.{w, w} X) := by
  let t0 : TopologicalSpace X := inferInstance
  have hX :
      @UCompactlyGeneratedSpace.{w} X (TopologicalSpace.compactlyGenerated.{w, w} X) :=
    rawUCompactlyGeneratedSpaceCompactlyGenerated (X := X) (t := t0)
  have hmk :
      @Continuous X (Kified X) (TopologicalSpace.compactlyGenerated.{w, w} X)
        (kifiedTopologicalSpace.{w, w} X) Kified.mk := by
    -- The forward equivalence map is continuous for the coinduced presentation of `Kified X`.
    rw [kifiedTopologicalSpace_eq_coinduced (X := X)]
    exact continuous_coinduced_rng
  -- Transfer compact generation across the coinduced presentation of `Kified X`.
  exact
    @uCompactlyGeneratedSpace_of_coinduced.{w} X (Kified X)
      (TopologicalSpace.compactlyGenerated.{w, w} X) (kifiedTopologicalSpace.{w, w} X)
      hX Kified.mk hmk (kifiedTopologicalSpace_eq_coinduced (X := X))

/-- Helper for Definition 5.2.8: the default k-ification of a weak Hausdorff space is weak
Hausdorff. -/
private theorem weaklyHausdorffSpaceKified
    (X : Type w) [TopologicalSpace X] [WeaklyHausdorffSpace.{w, w} X] :
    @WeaklyHausdorffSpace.{w, w} (Kified X) (kifiedTopologicalSpace.{w, w} X) := by
  let t0 : TopologicalSpace X := inferInstance
  have hX :
      @WeaklyHausdorffSpace.{w, w} X (TopologicalSpace.compactlyGenerated.{w, w} X) :=
    rawWeaklyHausdorffSpaceCompactlyGenerated (X := X) (t := t0)
  -- Pull weak Hausdorffness back along the embedding into the raw compactly generated space.
  exact
    @Topology.IsEmbedding.weaklyHausdorffSpace (Kified X) X
      (kifiedTopologicalSpace.{w, w} X) (TopologicalSpace.compactlyGenerated.{w, w} X)
      hX Kified.of (kifiedOf_isEmbedding X)

/-- Definition 5.2.8: the k-ification of a weak Hausdorff space is compactly generated weak
Hausdorff, providing the object part of the functor `k : wU ⥤ U`. -/
theorem kified_compactlyGeneratedWeakHausdorffSpace
    {X : Type w} [TopologicalSpace X] [WeaklyHausdorffSpace.{w, w} X] :
    let _ : TopologicalSpace (Kified X) := kifiedTopologicalSpace.{w, w} X
    CompactlyGeneratedWeakHausdorffSpace.{w, w} (Kified X) :=
  by
    let _ : TopologicalSpace (Kified X) := kifiedTopologicalSpace.{w, w} X
    -- Package the transported weak Hausdorff and compact-generation structures.
    exact
      @CompactlyGeneratedWeakHausdorffSpace.mk.{w, w} (Kified X)
        (kifiedTopologicalSpace.{w, w} X)
        (weaklyHausdorffSpaceKified X) (uCompactlyGeneratedSpaceKified X)

/-- The default `Kified X` topology is compactly generated weak Hausdorff when `X` is weak
Hausdorff. -/
instance instCompactlyGeneratedWeakHausdorffSpaceKified
    {X : Type w} [TopologicalSpace X] [WeaklyHausdorffSpace.{w, w} X] :
    CompactlyGeneratedWeakHausdorffSpace.{w, w} (Kified X) := by
  simpa using
    (kified_compactlyGeneratedWeakHausdorffSpace :
      let _ : TopologicalSpace (Kified X) := kifiedTopologicalSpace.{w, w} X
      CompactlyGeneratedWeakHausdorffSpace.{w, w} (Kified X))

/-- A continuous map induces a continuous map between the k-ified carrier types. -/
private theorem continuous_kified_of_continuous
    {X : Type w} [TopologicalSpace X] {Y : Type w} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) :
    let _ : TopologicalSpace (Kified X) := kifiedTopologicalSpace.{u, w} X
    let _ : TopologicalSpace (Kified Y) := kifiedTopologicalSpace.{u, w} Y
    Continuous (fun x : Kified X ↦ Kified.mk (f x.of)) :=
  by
    let _ : TopologicalSpace (Kified X) := kifiedTopologicalSpace.{u, w} X
    let _ : TopologicalSpace (Kified Y) := kifiedTopologicalSpace.{u, w} Y
    -- Continuity into an induced topology is checked after composing with the forgetful map.
    have hof :
        @Continuous (Kified X) X (kifiedTopologicalSpace.{u, w} X)
          (TopologicalSpace.compactlyGenerated.{u, w} X) Kified.of := by
      simpa [kifiedTopologicalSpace] using
        (continuous_induced_dom :
          @Continuous (Kified X) X
            (TopologicalSpace.induced Kified.of (TopologicalSpace.compactlyGenerated.{u, w} X))
            (TopologicalSpace.compactlyGenerated.{u, w} X) Kified.of)
    have hcomp :
        @Continuous (Kified X) Y (kifiedTopologicalSpace.{u, w} X)
          (TopologicalSpace.compactlyGenerated.{u, w} Y) (fun x : Kified X ↦ f x.of) := by
      have hfg :
          @Continuous X Y (TopologicalSpace.compactlyGenerated.{u, w} X)
            (TopologicalSpace.compactlyGenerated.{u, w} Y) f :=
        continuous_compactlyGenerated_of_continuous (f := f) hf
      exact
        @Continuous.comp (Kified X) X Y (kifiedTopologicalSpace.{u, w} X)
          (TopologicalSpace.compactlyGenerated.{u, w} X)
          (TopologicalSpace.compactlyGenerated.{u, w} Y)
          Kified.of f hfg hof
    -- Forgetting the target k-topology leaves the usual composite `f ∘ Kified.of`.
    refine continuous_induced_rng.2 ?_
    simpa [Function.comp] using hcomp

/-- The underlying `TopCat` object of the k-ification of a weak Hausdorff space. -/
private abbrev weakHausdorffKificationToTopObj (X : weakHausdorffSpaceCat.{w}) : TopCat.{w} :=
  let _ : TopologicalSpace (Kified X.obj) := kifiedTopologicalSpace.{w, w} X.obj
  TopCat.of (Kified X.obj)

/-- The underlying `TopCat` morphism of the k-ification functor. -/
private abbrev weakHausdorffKificationToTopMap
    {X Y : weakHausdorffSpaceCat.{w}} (f : X ⟶ Y) :
    weakHausdorffKificationToTopObj X ⟶ weakHausdorffKificationToTopObj Y :=
  let _ : TopologicalSpace (Kified X.obj) := kifiedTopologicalSpace.{w, w} X.obj
  let _ : TopologicalSpace (Kified Y.obj) := kifiedTopologicalSpace.{w, w} Y.obj
  let g := f.hom.hom
  TopCat.ofHom ⟨fun x : Kified X.obj ↦ Kified.mk (g x.of),
    continuous_kified_of_continuous g.continuous⟩

/-- The object of `U` obtained by k-ifying a weak Hausdorff space. -/
abbrev weakHausdorffKificationObj (X : weakHausdorffSpaceCat.{w}) :
    compactlyGeneratedWeakHausdorffSpaceCat :=
  let _ : WeaklyHausdorffSpace X.obj := X.property
  let _ : TopologicalSpace (Kified X.obj) := kifiedTopologicalSpace.{w, w} X.obj
  ⟨weakHausdorffKificationToTopObj X, kified_compactlyGeneratedWeakHausdorffSpace⟩

/-- The map part of `weakHausdorffKification` preserves identities. -/
private theorem weakHausdorffKification_map_id (X : weakHausdorffSpaceCat.{w}) :
    ObjectProperty.homMk (weakHausdorffKificationToTopMap (𝟙 X)) =
      𝟙 (weakHausdorffKificationObj X) :=
  by
    -- Reduce the full-subcategory identity law to the underlying continuous maps.
    apply ObjectProperty.hom_ext
    ext x
    cases x
    rfl

/-- The map part of `weakHausdorffKification` preserves composition. -/
private theorem weakHausdorffKification_map_comp
    {X Y Z : weakHausdorffSpaceCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ObjectProperty.homMk (weakHausdorffKificationToTopMap (f ≫ g)) =
      (ObjectProperty.homMk (weakHausdorffKificationToTopMap f) :
          weakHausdorffKificationObj X ⟶ weakHausdorffKificationObj Y) ≫
        (ObjectProperty.homMk (weakHausdorffKificationToTopMap g) :
          weakHausdorffKificationObj Y ⟶ weakHausdorffKificationObj Z) :=
  by
    -- Reduce the composition law to pointwise equality of the underlying maps on `Kified`.
    apply ObjectProperty.hom_ext
    ext x
    cases x
    rfl

/-- The functor `k : wU ⥤ U` from Definition 5.2.8 sends a weak Hausdorff space to its
k-ification. -/
def weakHausdorffKification :
    weakHausdorffSpaceCat.{w} ⥤ compactlyGeneratedWeakHausdorffSpaceCat :=
  { obj := weakHausdorffKificationObj
    map := fun f ↦ ObjectProperty.homMk (weakHausdorffKificationToTopMap f)
    map_id := weakHausdorffKification_map_id
    map_comp := weakHausdorffKification_map_comp }

/-- The source-facing category `U` forgets canonically to mathlib's bundled category of
compactly generated spaces. -/
abbrev compactlyGeneratedWeakHausdorffToCompactlyGenerated :
    compactlyGeneratedWeakHausdorffSpaceCat ⥤ CompactlyGenerated.{w, w} where
  obj X :=
    let _ : CompactlyGeneratedWeakHausdorffSpace X.obj := X.property
    CompactlyGenerated.of X.obj
  map {X Y} f :=
    let _ : CompactlyGeneratedWeakHausdorffSpace X.obj := X.property
    let _ : CompactlyGeneratedWeakHausdorffSpace Y.obj := Y.property
    CompactlyGenerated.ofHom f.hom.hom

/-- The canonical bridge `U ⥤ CompactlyGenerated` is fully faithful. -/
abbrev fullyFaithfulCompactlyGeneratedWeakHausdorffToCompactlyGenerated :
    compactlyGeneratedWeakHausdorffToCompactlyGenerated.FullyFaithful where
  preimage f := ObjectProperty.homMk (TopCat.ofHom f.hom.hom)
  map_preimage f := by
    ext x
    change (TopCat.Hom.hom f.hom) x = (TopCat.Hom.hom f.hom) x
    rfl
  preimage_map f := by
    ext x
    change (TopCat.Hom.hom f.hom) x = (TopCat.Hom.hom f.hom) x
    rfl

/-- Every compactly generated weak Hausdorff space is weak Hausdorff. -/
private theorem compactlyGeneratedWeakHausdorffProperty_le_weakHausdorffProperty :
    compactlyGeneratedWeakHausdorffProperty ≤ weakHausdorffProperty :=
  fun _ hX ↦ hX.toWeaklyHausdorffSpace

/-- The forgetful functor `j : U ⥤ wU` from Definition 5.2.8 is the canonical inclusion of the
full subcategory of compactly generated weak Hausdorff spaces into weak Hausdorff spaces. -/
abbrev compactlyGeneratedWeakHausdorffToWeakHausdorff :
    compactlyGeneratedWeakHausdorffSpaceCat ⥤ weakHausdorffSpaceCat.{w} :=
  ObjectProperty.ιOfLE compactlyGeneratedWeakHausdorffProperty_le_weakHausdorffProperty

/-- The forgetful functor `j : U ⥤ wU` acts on morphisms by forgetting only the compactly
generated structure. -/
theorem compactlyGeneratedWeakHausdorffToWeakHausdorff_map
    {X Y : compactlyGeneratedWeakHausdorffSpaceCat} (f : X ⟶ Y) :
    compactlyGeneratedWeakHausdorffToWeakHausdorff.map f =
      (ObjectProperty.homMk f.hom :
        compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶
          compactlyGeneratedWeakHausdorffToWeakHausdorff.obj Y) :=
  by
    -- The inclusion functor acts on morphisms by rewrapping the same underlying `TopCat` map.
    rfl

/-- The forgetful functor `j : U ⥤ wU` is fully faithful, so it exhibits `U` as a full
subcategory of `wU`. -/
abbrev fullyFaithfulCompactlyGeneratedWeakHausdorffToWeakHausdorff :
    compactlyGeneratedWeakHausdorffToWeakHausdorff.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE compactlyGeneratedWeakHausdorffProperty_le_weakHausdorffProperty
