import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order

universe u v w

open scoped Topology

-- Semantic search hit: `TopologicalSpace.compactlyGenerated`; local Chapter 5 owners
-- `ordinaryProductTopology`, `compactlyGeneratedProductTopology`, and
-- `instCompactlyGeneratedWeakHausdorffSpaceCompactlyGenerated`. This proposition is a bridge/view
-- statement comparing the source-facing compactly generated product topology with the ordinary
-- product topology formed after replacing each factor by its k-ification.

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private abbrev compactlyGeneratedFactorsOrdinaryProductTopologyAux
    (X : Type u) (Y : Type v) (tX : TopologicalSpace X) (tY : TopologicalSpace Y) :
    TopologicalSpace (X × Y) :=
  let _ : TopologicalSpace X := tX
  let _ : TopologicalSpace Y := tY
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
  X ×_c Y

/-- The ordinary product topology obtained after replacing the factor topologies on `X` and `Y`
by their k-ifications `TopologicalSpace.compactlyGenerated X` and
`TopologicalSpace.compactlyGenerated Y`. -/
abbrev compactlyGeneratedFactorsOrdinaryProductTopology (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  compactlyGeneratedFactorsOrdinaryProductTopologyAux X Y inferInstance inferInstance

/-- The textbook compactly generated product `kX × kY`: first kify each factor, take their
ordinary product, and then kify that product as required by the chapter's unadorned product
notation. -/
abbrev compactlyGeneratedFactorsProductTopology (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (X × Y) :=
  @TopologicalSpace.compactlyGenerated.{max u v, max u v} (X × Y)
    (compactlyGeneratedFactorsOrdinaryProductTopology X Y)

private abbrev generatorIndex (Z : Type w) [TopologicalSpace Z] :=
  (S : CompHaus.{w}) × C(S, Z)

private abbrev generatorSource (Z : Type w) [TopologicalSpace Z] :=
  Σ j : generatorIndex Z, j.1

private abbrev generatorEval (Z : Type w) [TopologicalSpace Z] :
    generatorSource Z → Z := fun z ↦
  z.1.2 z.2

private abbrev generatorPairIndex (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :=
  generatorIndex X × generatorIndex Y

private abbrev generatorPairSource (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :=
  Σ ij : generatorPairIndex X Y, ij.1.1 × ij.2.1

private abbrev generatorPairEval (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :
    generatorPairSource X Y → X × Y := fun z ↦
  (z.1.1.2 z.2.1, z.1.2.2 z.2.2)

/-- Helper for Proposition 5.1.18: the product of the two compact-probe sigma sources evaluates
to `X × Y` coordinatewise. -/
private abbrev generatorProdEval (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :
    generatorSource X × generatorSource Y → X × Y := fun z ↦
  (generatorEval X z.1, generatorEval Y z.2)

/-- Helper for Proposition 5.1.18: the universal compact-probe evaluation is surjective, because
the one-point compact Hausdorff probe can realize any target point as a constant map. -/
lemma generatorEval_surjective (Z : Type w) [TopologicalSpace Z] :
    Function.Surjective (generatorEval Z) := by
  intro z
  let i : generatorIndex Z := ⟨CompHaus.of PUnit, ContinuousMap.const _ z⟩
  -- The constant probe from `PUnit` already hits the requested target point.
  exact ⟨⟨i, PUnit.unit⟩, rfl⟩

/-- Helper for Proposition 5.1.18: the kification topology on `Z` is by definition the quotient
topology induced by the universal compact-probe evaluation. -/
lemma generatorEval_isQuotientMap (Z : Type w) [TopologicalSpace Z] :
    @Topology.IsQuotientMap (generatorSource Z) Z inferInstance
      (TopologicalSpace.compactlyGenerated.{w, w} Z) (generatorEval Z) := by
  exact
    @Topology.IsQuotientMap.mk (generatorSource Z) Z inferInstance
      (TopologicalSpace.compactlyGenerated.{w, w} Z) (generatorEval Z)
      (generatorEval_surjective (Z := Z))
      (by
        -- Unfolding `TopologicalSpace.compactlyGenerated` exposes the defining coinduced
        -- topology with the codomain topology fixed explicitly.
        rw [TopologicalSpace.compactlyGenerated])

/-- Helper for Proposition 5.1.18: a map from a compact Hausdorff space to `X` that is
continuous for the original topology is automatically continuous for the same-universe
k-ification `TopologicalSpace.compactlyGenerated X`. -/
lemma continuousToCompactlyGeneratedOfContinuous
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] {f : K → X}
    (hf : Continuous f) :
    Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} X] f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, X)), j.fst) → X := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, X) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, X),
        Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    -- Rewrite the sigma-family of generators to the owner map in the definition of `kX`.
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  -- The chosen compact-source map is one of the generators defining the k-ification.
  simpa [F, i] using hgenerator i

/-- Helper for Proposition 5.1.18: the product generator evaluation is literally the product map
of the two factor generator evaluations. -/
lemma generatorProdEval_eq_prodMap_generatorEval :
    generatorProdEval X Y = Prod.map (generatorEval X) (generatorEval Y) := by
  -- Both sides evaluate the two generator-source coordinates independently.
  funext z
  rfl

/-- Helper for Proposition 5.1.18: the kification topology on any space is compactly generated
in the textbook `UCompactlyGeneratedSpace` sense. -/
lemma uCompactlyGeneratedSpaceCompactlyGenerated (Z : Type w) [TopologicalSpace Z] :
    @UCompactlyGeneratedSpace.{w} Z (TopologicalSpace.compactlyGenerated.{w, w} Z) := by
  refine
    @uCompactlyGeneratedSpace_of_isClosed Z
      (TopologicalSpace.compactlyGenerated.{w, w} Z) ?_
  intro A hA
  refine isClosed_compactlyGenerated_of_compHausClosed (X := Z) ?_
  intro S f
  have hfk :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{w, w} Z]
        (f : S → Z) :=
    continuousToCompactlyGeneratedOfContinuous (X := Z) f.continuous
  let fk : @ContinuousMap S Z inferInstance (TopologicalSpace.compactlyGenerated.{w, w} Z) :=
    @ContinuousMap.mk S Z inferInstance (TopologicalSpace.compactlyGenerated.{w, w} Z)
      (f : S → Z) hfk
  have hClosedPreimage : IsClosed (((fk : S → Z) ⁻¹' A)) := hA S fk
  -- Repackaging the probe with the stronger codomain continuity leaves the preimage unchanged.
  simpa [fk] using hClosedPreimage

/-- Helper for Proposition 5.1.18: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by its compactly generated topology, even when the source
universe is larger than the target universe. -/
lemma continuousCompHausToCompactlyGenerated
    {K : Type max u v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K›
      (TopologicalSpace.compactlyGenerated.{max u v, w} Z) f := by
  let F : (Σ (j : (S : CompHaus.{max u v}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{max u v}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators defining the k-ification.
  have hgenerator :
      ∀ j : (S : CompHaus.{max u v}) × C(S, Z),
        @Continuous j.fst Z inferInstance (TopologicalSpace.compactlyGenerated.{max u v, w} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    -- Rewriting to the sigma-family owner exposes the canonical continuity statement.
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  -- Specializing the sigma-family statement recovers continuity of the original map.
  simpa [F, i] using hgenerator i

/-- Helper for Proposition 5.1.18: a continuous map from a compact Hausdorff source into a weakly
Hausdorff space factors through its compact range, so it is continuous into the same-universe
k-ification `TopologicalSpace.compactlyGenerated X`. -/
lemma continuousToCompactlyGeneratedOfContinuousWeaklyHausdorff
    [WeaklyHausdorffSpace.{u, max u v} X] {K : Type max u v} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] {f : K → X} (hf : Continuous f) :
    Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} X] f := by
  let fRange : K → Set.range f := fun k ↦ ⟨f k, ⟨k, rfl⟩⟩
  have hfRange : Continuous fRange := hf.subtype_mk fun k ↦ ⟨k, rfl⟩
  let _ : CompactSpace (Set.range f) :=
    isCompact_iff_compactSpace.mp (isCompact_range hf)
  let _ : T2Space (Set.range f) :=
    range_t2Space_of_compactHausdorffMap (K := K) (X := X) (g := f) hf
  have hval :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
        (Subtype.val : Set.range f → X) :=
    continuousToCompactlyGeneratedOfContinuous (X := X) continuous_subtype_val
  -- Rewriting through the compact range subtype puts the map into the same-universe form.
  simpa [fRange, Function.comp] using
    (@Continuous.comp K (Set.range f) X ‹TopologicalSpace K› inferInstance
      (TopologicalSpace.compactlyGenerated.{u, u} X)
      fRange Subtype.val hval hfRange)

/-- Helper for Proposition 5.1.18: a map from a compact Hausdorff space to `X × Y` that is
continuous for the ordinary product topology is also continuous for the product topology obtained
after kifying both factors. -/
lemma continuousToCompactlyGeneratedFactorsOrdinaryProductTopologyOfContinuous
    [WeaklyHausdorffSpace.{u, max u v} X] [WeaklyHausdorffSpace.{v, max u v} Y]
    {K : Type max u v} [TopologicalSpace K] [CompactSpace K] [T2Space K] {g : K → X × Y}
    (hg : Continuous[‹TopologicalSpace K›, X ×_c Y] g) :
    Continuous[‹TopologicalSpace K›, compactlyGeneratedFactorsOrdinaryProductTopology X Y] g := by
  have hLeft :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} X]
        (fun k ↦ (g k).1) :=
    continuousToCompactlyGeneratedOfContinuousWeaklyHausdorff (X := X) hg.fst
  have hRight :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (fun k ↦ (g k).2) :=
    continuousToCompactlyGeneratedOfContinuousWeaklyHausdorff (X := Y) hg.snd
  -- Local instance justification (transport): the target is the ordinary product after replacing
  -- each factor topology by its k-ification, so we temporarily expose exactly those factor
  -- structures to use the standard product continuity constructor.
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
  change Continuous g
  -- Once the factor topologies are normalized, product continuity is coordinatewise.
  simpa using hLeft.prodMk hRight

/-- Helper for Proposition 5.1.18: a weak Hausdorff structure that controls compact probes from
`Type (max u v)` sources restricts to the same-universe weak Hausdorff structure on `X`. -/
lemma weaklyHausdorffSpaceRestrictMaxUniverse
    (X : Type u) [TopologicalSpace X] [hX : WeaklyHausdorffSpace.{u, max u v} X] :
    WeaklyHausdorffSpace.{u, u} X where
  isClosed_range := by
    intro K _ _ _ g hg
    let gLift : ULift.{v} K → X := fun k ↦ g k.down
    have hgLift : Continuous gLift := hg.comp continuous_uliftDown
    have hClosedLift : IsClosed (Set.range gLift) := hX.isClosed_range gLift hgLift
    have hRange : Set.range gLift = Set.range g := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k.down, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨ULift.up k, rfl⟩
    -- The lifted probe has exactly the same image in `X`.
    simpa [gLift, hRange] using hClosedLift

/-- Helper for Proposition 5.1.18: the ordinary product of weak Hausdorff spaces is weak
Hausdorff. -/
lemma weaklyHausdorffSpaceProd [hX : WeaklyHausdorffSpace.{u, max u v} X]
    [hY : WeaklyHausdorffSpace.{v, max u v} Y] :
    WeaklyHausdorffSpace.{max u v, max u v} (X × Y) := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  let gLeft : K → X := fun k ↦ (g k).1
  let gRight : K → Y := fun k ↦ (g k).2
  have hgLeft : Continuous gLeft := hg.fst
  have hgRight : Continuous gRight := hg.snd
  let rectangle : Set (X × Y) := Set.range gLeft ×ˢ Set.range gRight
  let _ : T2Space (Set.range gLeft) :=
    range_t2Space_of_compactHausdorffMap (X := X) hgLeft
  let _ : T2Space (Set.range gRight) :=
    range_t2Space_of_compactHausdorffMap (X := Y) hgRight
  have hLeftClosed : IsClosed (Set.range gLeft) := Continuous.isClosed_range hgLeft
  have hRightClosed : IsClosed (Set.range gRight) := Continuous.isClosed_range hgRight
  have hRectangleClosed : IsClosed rectangle := hLeftClosed.prod hRightClosed
  let rectangleMap : K → rectangle := fun k ↦ ⟨g k, ⟨⟨k, rfl⟩, ⟨k, rfl⟩⟩⟩
  let rectangleHomeomorph : Set.range gLeft × Set.range gRight ≃ₜ rectangle :=
    (Homeomorph.Set.prod (Set.range gLeft) (Set.range gRight)).symm
  let _ : T2Space rectangle := rectangleHomeomorph.t2Space
  have hRectangleMap : Continuous rectangleMap := by
    -- The compact-source map lands in the coordinate rectangle by construction.
    exact hg.subtype_mk fun k ↦ ⟨⟨k, rfl⟩, ⟨k, rfl⟩⟩
  have hClosedRangeRectangle : IsClosed (Set.range rectangleMap) :=
    Continuous.isClosed_range hRectangleMap
  have hClosedImage :
      IsClosed (((↑) : rectangle → X × Y) '' Set.range rectangleMap) :=
    hRectangleClosed.isClosedMap_subtype_val _ hClosedRangeRectangle
  have hRangeEq : ((↑) : rectangle → X × Y) '' Set.range rectangleMap = Set.range g := by
    -- Forgetting the rectangle subtype recovers exactly the original image in the ambient product.
    ext p
    constructor
    · rintro ⟨q, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨rectangleMap k, ⟨k, rfl⟩, rfl⟩
  simpa [hRangeEq] using hClosedImage

/-- Helper for Proposition 5.1.18: a compact Hausdorff space is `UCompactlyGeneratedSpace` in its
own universe because the identity map is one of the compact probes. -/
lemma compactHausdorff_uCompactlyGenerated
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K] :
    @UCompactlyGeneratedSpace.{w} K ‹TopologicalSpace K› := by
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z _ f hf
  -- The identity probe on `K` already belongs to the defining compact family.
  simpa [Function.comp] using hf (CompHaus.of K) ⟨id, continuous_id⟩

/-- Helper for Proposition 5.1.18: the sigma-type source indexing pairs of compact probes into
`X` and `Y` is `UCompactlyGeneratedSpace`. -/
lemma generatorPairSource_uCompactlyGenerated
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    @UCompactlyGeneratedSpace.{max u v} (generatorPairSource X Y)
      inferInstance := by
  let _ :
      ∀ ij : generatorPairIndex X Y,
        @UCompactlyGeneratedSpace.{max u v} (ij.1.1 × ij.2.1) inferInstance :=
    fun ij ↦ compactHausdorff_uCompactlyGenerated (K := ij.1.1 × ij.2.1)
  -- Each fiber is a compact Hausdorff product, so the sigma source is compactly generated.
  infer_instance

/-- Helper for Proposition 5.1.18: the first coordinate of the paired compact-probe evaluation
map is continuous into the kification of `X`. -/
lemma generatorPairEvalFst_continuousToCompactlyGenerated
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
      (fun z : generatorPairSource X Y ↦ (generatorPairEval X Y z).1) := by
  let leftSource : generatorPairSource X Y → generatorSource X := fun z ↦ ⟨z.1.1, z.2.1⟩
  have hleftSource : Continuous leftSource := by
    -- On each sigma fiber, the left selector is `Sigma.mk _ ∘ Prod.fst`.
    change Continuous
      (fun z : Σ ij : generatorPairIndex X Y, ij.1.1 × ij.2.1 ↦
        (⟨z.1.1, z.2.1⟩ : generatorSource X))
    refine continuous_sigma_iff.mpr ?_
    intro ij
    simpa [leftSource] using
      (continuous_sigmaMk.comp continuous_fst :
        Continuous (fun p : ij.1.1 × ij.2.1 ↦ (Sigma.mk ij.1 p.1 : generatorSource X)))
  have hEval :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
        (fun z : generatorSource X ↦ z.1.2 z.2) := by
    -- This is exactly the coinducing evaluation map used in the definition of `kX`.
    simpa using
      (continuous_coinduced_rng :
        Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
          (fun z : generatorSource X ↦ z.1.2 z.2))
  -- Composing the selector with the generator evaluation recovers the first coordinate.
  simpa [leftSource, generatorPairEval, Function.comp] using
    (@Continuous.comp (generatorPairSource X Y) (generatorSource X) X inferInstance inferInstance
      (TopologicalSpace.compactlyGenerated.{u, u} X)
      leftSource (fun z : generatorSource X ↦ z.1.2 z.2) hEval hleftSource)

/-- Helper for Proposition 5.1.18: the second coordinate of the paired compact-probe evaluation
map is continuous into the kification of `Y`. -/
lemma generatorPairEvalSnd_continuousToCompactlyGenerated
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
      (fun z : generatorPairSource X Y ↦ (generatorPairEval X Y z).2) := by
  let rightSource : generatorPairSource X Y → generatorSource Y := fun z ↦ ⟨z.1.2, z.2.2⟩
  have hrightSource : Continuous rightSource := by
    -- On each sigma fiber, the right selector is `Sigma.mk _ ∘ Prod.snd`.
    change Continuous
      (fun z : Σ ij : generatorPairIndex X Y, ij.1.1 × ij.2.1 ↦
        (⟨z.1.2, z.2.2⟩ : generatorSource Y))
    refine continuous_sigma_iff.mpr ?_
    intro ij
    simpa [rightSource] using
      (continuous_sigmaMk.comp continuous_snd :
        Continuous (fun p : ij.1.1 × ij.2.1 ↦ (Sigma.mk ij.2 p.2 : generatorSource Y)))
  have hEval :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (fun z : generatorSource Y ↦ z.1.2 z.2) := by
    -- This is exactly the coinducing evaluation map used in the definition of `kY`.
    simpa using
      (continuous_coinduced_rng :
        Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
          (fun z : generatorSource Y ↦ z.1.2 z.2))
  -- Composing the selector with the generator evaluation recovers the second coordinate.
  simpa [rightSource, generatorPairEval, Function.comp] using
    (@Continuous.comp (generatorPairSource X Y) (generatorSource Y) Y inferInstance inferInstance
      (TopologicalSpace.compactlyGenerated.{v, v} Y)
      rightSource (fun z : generatorSource Y ↦ z.1.2 z.2) hEval hrightSource)

/-- Helper for Proposition 5.1.18: the paired compact-probe evaluation map is continuous into the
ordinary product of the kified factors. -/
lemma generatorPairEval_continuousToCompactlyGeneratedFactorsOrdinaryProductTopology
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    Continuous[ inferInstance, compactlyGeneratedFactorsOrdinaryProductTopology X Y]
      (generatorPairEval X Y) := by
  have hLeft :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
        (fun z : generatorPairSource X Y ↦ (generatorPairEval X Y z).1) :=
    generatorPairEvalFst_continuousToCompactlyGenerated (X := X) (Y := Y)
  have hRight :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (fun z : generatorPairSource X Y ↦ (generatorPairEval X Y z).2) :=
    generatorPairEvalSnd_continuousToCompactlyGenerated (X := X) (Y := Y)
  -- Exposing the factor kifications turns the target into the ordinary product topology.
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
  -- Product continuity is exactly continuity of the two coordinate maps.
  simpa [compactlyGeneratedFactorsOrdinaryProductTopology,
    compactlyGeneratedFactorsOrdinaryProductTopologyAux, generatorPairEval] using
    hLeft.prodMk hRight

/-- Helper for Proposition 5.1.18: the coinduced topology of the paired compact-probe evaluation
is always no finer than the ordinary product of the factor kifications. -/
lemma coinduced_generatorPairEval_le_compactlyGeneratedFactorsOrdinaryProductTopology
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    TopologicalSpace.coinduced (generatorPairEval X Y) inferInstance ≤
      compactlyGeneratedFactorsOrdinaryProductTopology X Y := by
  -- This is the direct topology inequality encoded by continuity of the paired evaluation map.
  exact
    continuous_iff_coinduced_le.mp
      (generatorPairEval_continuousToCompactlyGeneratedFactorsOrdinaryProductTopology
        (X := X) (Y := Y))

/-- Helper for Proposition 5.1.18: the coinduced topology presented by the paired compact-probe
evaluation is compactly generated because its source already is. -/
lemma uCompactlyGeneratedSpaceCoinducedGeneratorPairEval
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    @UCompactlyGeneratedSpace.{max u v} (X × Y)
      (TopologicalSpace.coinduced (generatorPairEval X Y) inferInstance) := by
  let _ :
      @UCompactlyGeneratedSpace.{max u v} (generatorPairSource X Y) inferInstance :=
    generatorPairSource_uCompactlyGenerated (X := X) (Y := Y)
  let _ : TopologicalSpace (X × Y) :=
    TopologicalSpace.coinduced (generatorPairEval X Y) inferInstance
  -- The coinduced image of a compactly generated source is compactly generated.
  exact
    uCompactlyGeneratedSpace_of_coinduced
      (f := generatorPairEval X Y) continuous_coinduced_rng rfl

/-- Helper for Proposition 5.1.18: a compact Hausdorff source map that is continuous into the
ordinary product of the two kified factors is already continuous into the original product
topology on `X × Y`. -/
lemma continuousToOrdinaryProductOfContinuousCompactlyGeneratedFactors
    {K : Type max u v} [TopologicalSpace K] [CompactSpace K] [T2Space K] {g : K → X × Y}
    (hg :
      Continuous[‹TopologicalSpace K›, compactlyGeneratedFactorsOrdinaryProductTopology X Y] g) :
    Continuous[‹TopologicalSpace K›, X ×_c Y] g := by
  have hLeftCG :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} X]
        (fun k ↦ (g k).1) := by
    -- Expose the kified factor topologies so the product-continuity hypotheses match the RHS.
    let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
    let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
    simpa using hg.fst
  have hRightCG :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (fun k ↦ (g k).2) := by
    -- The second coordinate is handled by the same normalization of the RHS factor topologies.
    let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
    let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
    simpa using hg.snd
  have hLeft : Continuous[‹TopologicalSpace K›, ‹TopologicalSpace X›] (fun k ↦ (g k).1) := by
    -- Compose with the identity `kX → X` to recover continuity into the original first factor.
    exact
      @Continuous.comp K X X ‹TopologicalSpace K›
        (TopologicalSpace.compactlyGenerated.{u, u} X) ‹TopologicalSpace X›
        (fun k ↦ (g k).1) id
        (continuous_id_compactlyGenerated (X := X)) hLeftCG
  have hRight : Continuous[‹TopologicalSpace K›, ‹TopologicalSpace Y›] (fun k ↦ (g k).2) := by
    -- The same identity bridge recovers continuity into the original second factor.
    exact
      @Continuous.comp K Y Y ‹TopologicalSpace K›
        (TopologicalSpace.compactlyGenerated.{v, v} Y) ‹TopologicalSpace Y›
        (fun k ↦ (g k).2) id
        (continuous_id_compactlyGenerated (X := Y)) hRightCG
  -- Once both coordinates land continuously in the original factors, the ordinary product follows.
  simpa using hLeft.prodMk hRight

/-- Helper for Proposition 5.1.18: the paired compact-probe evaluation is surjective, using the
constant probes from the one-point compact Hausdorff space. -/
lemma generatorPairEval_surjective :
    Function.Surjective (generatorPairEval X Y) := by
  intro p
  let leftIndex : generatorIndex X := ⟨CompHaus.of PUnit, ContinuousMap.const _ p.1⟩
  let rightIndex : generatorIndex Y := ⟨CompHaus.of PUnit, ContinuousMap.const _ p.2⟩
  -- The constant compact probes already hit the requested point of `X × Y`.
  refine ⟨⟨(leftIndex, rightIndex), (PUnit.unit, PUnit.unit)⟩, ?_⟩
  rfl

/-- Helper for Proposition 5.1.18: every compact Hausdorff probe into the ordinary product of the
kified factors lifts through the paired generator evaluation by factoring each coordinate through
its compact range. -/
lemma compactProbeFactorsThroughGeneratorPairEval
    [WeaklyHausdorffSpace.{u, max u v} X] [WeaklyHausdorffSpace.{v, max u v} Y]
    {K : Type max u v} [TopologicalSpace K] [CompactSpace K] [T2Space K] {g : K → X × Y}
    (hg :
      Continuous[‹TopologicalSpace K›, compactlyGeneratedFactorsOrdinaryProductTopology X Y] g) :
    ∃ lift : K → generatorPairSource X Y,
      Continuous lift ∧ generatorPairEval X Y ∘ lift = g := by
  let gLeft : K → X := fun k ↦ (g k).1
  let gRight : K → Y := fun k ↦ (g k).2
  have hLeftCG :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} X] gLeft := by
    -- Expose the factor kifications so that the product-continuity hypotheses match the codomain.
    let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
    let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
    simpa [gLeft] using hg.fst
  have hRightCG :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{v, v} Y] gRight := by
    -- The second coordinate is handled by the same normalization of the RHS factor topologies.
    let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
    let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
    simpa [gRight] using hg.snd
  have hLeft : Continuous gLeft := by
    -- Forgetting from `kX` to the original topology recovers an ordinary compact-source probe.
    exact
      @Continuous.comp K X X ‹TopologicalSpace K›
        (TopologicalSpace.compactlyGenerated.{u, u} X) ‹TopologicalSpace X›
        gLeft id
        (continuous_id_compactlyGenerated (X := X)) hLeftCG
  have hRight : Continuous gRight := by
    -- The same identity bridge forgets the kification on the second factor.
    exact
      @Continuous.comp K Y Y ‹TopologicalSpace K›
        (TopologicalSpace.compactlyGenerated.{v, v} Y) ‹TopologicalSpace Y›
        gRight id
        (continuous_id_compactlyGenerated (X := Y)) hRightCG
  let leftRange : K → Set.range gLeft := fun k ↦ ⟨gLeft k, ⟨k, rfl⟩⟩
  let rightRange : K → Set.range gRight := fun k ↦ ⟨gRight k, ⟨k, rfl⟩⟩
  have hLeftRange : Continuous leftRange := hLeft.subtype_mk fun k ↦ ⟨k, rfl⟩
  have hRightRange : Continuous rightRange := hRight.subtype_mk fun k ↦ ⟨k, rfl⟩
  let _ : CompactSpace (Set.range gLeft) :=
    isCompact_iff_compactSpace.mp (isCompact_range hLeft)
  let _ : CompactSpace (Set.range gRight) :=
    isCompact_iff_compactSpace.mp (isCompact_range hRight)
  let _ : T2Space (Set.range gLeft) :=
    range_t2Space_of_compactHausdorffMap (K := K) (X := X) (g := gLeft) hLeft
  let _ : T2Space (Set.range gRight) :=
    range_t2Space_of_compactHausdorffMap (K := K) (X := Y) (g := gRight) hRight
  let leftIndex : generatorIndex X :=
    ⟨CompHaus.of (Set.range gLeft), ⟨Subtype.val, continuous_subtype_val⟩⟩
  let rightIndex : generatorIndex Y :=
    ⟨CompHaus.of (Set.range gRight), ⟨Subtype.val, continuous_subtype_val⟩⟩
  let lift : K → generatorPairSource X Y := fun k ↦
    ⟨(leftIndex, rightIndex), (leftRange k, rightRange k)⟩
  have hLiftPair : Continuous fun k ↦ (leftRange k, rightRange k) := hLeftRange.prodMk hRightRange
  have hLift : Continuous lift := by
    -- The lift lands in one fixed sigma fiber indexed by the two compact coordinate ranges.
    simpa [lift] using
      (continuous_sigmaMk.comp hLiftPair :
        Continuous (fun k ↦
          (Sigma.mk (leftIndex, rightIndex) (leftRange k, rightRange k) :
            generatorPairSource X Y)))
  refine ⟨lift, hLift, ?_⟩
  -- Evaluating the chosen compact-range coordinates recovers the original probe pointwise.
  funext k
  rfl

/-- Helper for Proposition 5.1.18: a product of compact-probe sigma sources reorganizes into the
single sigma source indexed by pairs of probes. -/
private noncomputable def generatorNestedToFlatHomeomorph :
    (Σ i : generatorIndex X, Σ j : generatorIndex Y, i.1 × j.1) ≃ₜ
      Σ ij : (Sigma fun _ : generatorIndex X => generatorIndex Y), ij.1.1 × ij.2.1 where
  toEquiv :=
    { toFun := fun z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      invFun := fun z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      left_inv := by
        intro z
        cases z
        rfl
      right_inv := by
        intro z
        cases z
        rfl }
  continuous_toFun := by
    -- Each nested sigma fiber lands in one fixed flattened sigma component.
    refine continuous_sigma fun i ↦ ?_
    refine continuous_sigma fun j ↦ ?_
    change Continuous
      (@Sigma.mk
        (Sigma fun _ : generatorIndex X => generatorIndex Y)
        (fun ij : Sigma fun _ : generatorIndex X => generatorIndex Y ↦ ij.1.1 × ij.2.1)
        ⟨i, j⟩)
    exact continuous_sigmaMk
  continuous_invFun := by
    -- Flattened sigma points return to their outer and inner probe indices componentwise.
    refine continuous_sigma fun ij ↦ ?_
    change Continuous fun p : ij.1.1 × ij.2.1 ↦
      (Sigma.mk ij.1
        (Sigma.mk ij.2 p : Σ j : generatorIndex Y, ij.1.1 × j.1) :
          Σ i : generatorIndex X, Σ j : generatorIndex Y, i.1 × j.1)
    exact continuous_sigmaMk.comp continuous_sigmaMk

/-- Helper for Proposition 5.1.18: swapping a fixed factor across the inner sigma source is a
homeomorphism fiberwise in the outer compact probe index. -/
private noncomputable def generatorSigmaSwapHomeomorph
    (i : generatorIndex X) :
    (Σ j : generatorIndex Y, j.1 × i.1) ≃ₜ Σ j : generatorIndex Y, i.1 × j.1 where
  toEquiv :=
    { toFun := fun z ↦ ⟨z.1, Prod.swap z.2⟩
      invFun := fun z ↦ ⟨z.1, Prod.swap z.2⟩
      left_inv := by
        intro z
        cases z
        simp
      right_inv := by
        intro z
        cases z
        simp }
  continuous_toFun := by
    -- On each sigma component this is just the standard product-coordinate swap.
    refine continuous_sigma fun j ↦ ?_
    change Continuous fun p : j.1 × i.1 ↦
      (Sigma.mk j (Prod.swap p) : Σ j : generatorIndex Y, i.1 × j.1)
    exact continuous_sigmaMk.comp continuous_swap
  continuous_invFun := by
    -- The inverse is the same coordinate swap, now read in the opposite direction.
    refine continuous_sigma fun j ↦ ?_
    change Continuous fun p : i.1 × j.1 ↦
      (Sigma.mk j (Prod.swap p) : Σ j : generatorIndex Y, j.1 × i.1)
    exact continuous_sigmaMk.comp continuous_swap

/-- Helper for Proposition 5.1.18: each outer compact probe index sees the second sigma source as
an ordinary product with a fixed compact source. -/
private noncomputable def generatorFiberHomeomorph
    (i : generatorIndex X) :
    i.1 × generatorSource Y ≃ₜ Σ j : generatorIndex Y, i.1 × j.1 :=
  (Homeomorph.prodComm i.1 (generatorSource Y)).trans
    ((Homeomorph.sigmaProdDistrib (X := fun j : generatorIndex Y ↦ j.1) (Y := i.1)).trans
      (generatorSigmaSwapHomeomorph (X := X) (Y := Y) i))

/-- Helper for Proposition 5.1.18: distributing the second sigma source across each outer probe
index is a homeomorphism. -/
private noncomputable def generatorOuterFiberHomeomorph :
    (Σ i : generatorIndex X, i.1 × generatorSource Y) ≃ₜ
      Σ i : generatorIndex X, Σ j : generatorIndex Y, i.1 × j.1 where
  toEquiv :=
    { toFun := fun z ↦ ⟨z.1, generatorFiberHomeomorph (X := X) (Y := Y) z.1 z.2⟩
      invFun := fun z ↦ ⟨z.1, (generatorFiberHomeomorph (X := X) (Y := Y) z.1).symm z.2⟩
      left_inv := by
        intro z
        cases z
        simp [generatorFiberHomeomorph]
      right_inv := by
        intro z
        cases z
        simp [generatorFiberHomeomorph] }
  continuous_toFun := by
    -- On each outer sigma component this is the fixed-index fiber homeomorphism.
    refine continuous_sigma fun i ↦ ?_
    change Continuous fun p : i.1 × generatorSource Y ↦
      (Sigma.mk i ((generatorFiberHomeomorph (X := X) (Y := Y) i) p) :
        Σ i : generatorIndex X, Σ j : generatorIndex Y, i.1 × j.1)
    exact continuous_sigmaMk.comp (generatorFiberHomeomorph (X := X) (Y := Y) i).continuous_toFun
  continuous_invFun := by
    -- The inverse applies the same fixed-index homeomorphism backwards on each component.
    refine continuous_sigma fun i ↦ ?_
    change Continuous fun p : Σ j : generatorIndex Y, i.1 × j.1 ↦
      (Sigma.mk i ((generatorFiberHomeomorph (X := X) (Y := Y) i).symm p) :
        Σ i : generatorIndex X, i.1 × generatorSource Y)
    exact continuous_sigmaMk.comp (generatorFiberHomeomorph (X := X) (Y := Y) i).continuous_invFun

/-- Helper for Proposition 5.1.18: the flattened sigma indexed by `Σ i, generatorIndex Y`
repackages to the paired sigma indexed by `generatorIndex X × generatorIndex Y`. -/
private noncomputable def generatorFlatToPairHomeomorph :
    (Σ ij : (Sigma fun _ : generatorIndex X => generatorIndex Y), ij.1.1 × ij.2.1) ≃ₜ
      generatorPairSource X Y where
  toEquiv :=
    { toFun := fun z ↦ ⟨(z.1.1, z.1.2), z.2⟩
      invFun := fun z ↦ ⟨⟨z.1.1, z.1.2⟩, z.2⟩
      left_inv := by
        intro z
        cases z
        rfl
      right_inv := by
        intro z
        cases z
        rfl }
  continuous_toFun := by
    -- Each flattened sigma component lands in the corresponding paired probe component.
    refine continuous_sigma fun ij ↦ ?_
    change Continuous
      (@Sigma.mk
        (generatorPairIndex X Y)
        (fun ij : generatorPairIndex X Y ↦ ij.1.1 × ij.2.1)
        (ij.1, ij.2))
    exact continuous_sigmaMk
  continuous_invFun := by
    -- The inverse simply rebrackets the pair of probe indices back into one sigma index.
    refine continuous_sigma fun ij ↦ ?_
    change Continuous
      (@Sigma.mk
        (Sigma fun _ : generatorIndex X => generatorIndex Y)
        (fun ij : Sigma fun _ : generatorIndex X => generatorIndex Y ↦ ij.1.1 × ij.2.1)
        ⟨ij.1, ij.2⟩)
    exact continuous_sigmaMk

/-- Helper for Proposition 5.1.18: the product of the two generator sigma sources is homeomorphic
to the single sigma source indexed by pairs of compact probes. -/
private noncomputable def generatorProdSourceHomeomorphPairSource :
    generatorSource X × generatorSource Y ≃ₜ generatorPairSource X Y := by
  -- Route correction: normalize the source to a plain product of the two generator sigmas before
  -- transporting compact generation back to the paired sigma source.
  exact
    (Homeomorph.sigmaProdDistrib (X := fun i : generatorIndex X ↦ i.1)
      (Y := generatorSource Y)).trans
      ((generatorOuterFiberHomeomorph (X := X) (Y := Y)).trans
        ((generatorNestedToFlatHomeomorph (X := X) (Y := Y)).trans
          (generatorFlatToPairHomeomorph (X := X) (Y := Y))))

/-- Helper for Proposition 5.1.18: the source homeomorphism intertwines the paired and product
generator evaluations. -/
lemma generatorPairEval_eq_generatorProdEval_comp_prodSourceHomeomorphPairSource_symm :
    generatorPairEval X Y =
      generatorProdEval X Y ∘
        (generatorProdSourceHomeomorphPairSource (X := X) (Y := Y)).symm := by
  funext z
  simp [generatorProdSourceHomeomorphPairSource, generatorOuterFiberHomeomorph,
    generatorNestedToFlatHomeomorph, generatorFlatToPairHomeomorph, generatorFiberHomeomorph,
    generatorSigmaSwapHomeomorph, generatorProdEval, generatorPairEval]

/-- Helper for Proposition 5.1.18: the paired and product generator evaluations induce the same
coinduced topology on `X × Y`. -/
lemma coinduced_generatorPairEval_eq_coinduced_generatorProdEval :
    TopologicalSpace.coinduced (generatorPairEval X Y) inferInstance =
      TopologicalSpace.coinduced (generatorProdEval X Y) inferInstance := by
  let e := generatorProdSourceHomeomorphPairSource (X := X) (Y := Y)
  have hcoinduced :
      (inferInstance : TopologicalSpace (generatorSource X × generatorSource Y)) =
        TopologicalSpace.coinduced e.symm
          (inferInstance : TopologicalSpace (generatorPairSource X Y)) := by
    -- Bind the quotient-map transport with an explicit codomain topology to avoid dependent `rw`.
    simpa using e.symm.isQuotientMap.eq_coinduced
  calc
    TopologicalSpace.coinduced (generatorPairEval X Y) inferInstance =
        TopologicalSpace.coinduced (generatorProdEval X Y ∘ e.symm) inferInstance := by
      rw [generatorPairEval_eq_generatorProdEval_comp_prodSourceHomeomorphPairSource_symm
        (X := X) (Y := Y)]
    _ =
        TopologicalSpace.coinduced (generatorProdEval X Y)
          (TopologicalSpace.coinduced e.symm inferInstance) := by
      rw [← coinduced_compose]
    _ = TopologicalSpace.coinduced (generatorProdEval X Y) inferInstance := by
      simp [hcoinduced]

/-- Helper for Proposition 5.1.18: the product of the two generator sigma sources is
`UCompactlyGeneratedSpace` because it is homeomorphic to the paired generator sigma source. -/
lemma generatorProdSource_uCompactlyGenerated
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    @UCompactlyGeneratedSpace.{max u v} (generatorSource X × generatorSource Y) inferInstance := by
  let _ :
      @UCompactlyGeneratedSpace.{max u v} (generatorPairSource X Y) inferInstance :=
    generatorPairSource_uCompactlyGenerated (X := X) (Y := Y)
  let e := generatorProdSourceHomeomorphPairSource (X := X) (Y := Y)
  -- Transport compact generation back across the product/pair source homeomorphism.
  exact uCompactlyGeneratedSpace_of_coinduced e.symm.continuous e.symm.isQuotientMap.eq_coinduced

/-- Helper for Proposition 5.1.18: the product evaluation map from the two generator sigma
sources is continuous into the ordinary product of the kified factors. -/
lemma generatorProdEval_continuousToCompactlyGeneratedFactorsOrdinaryProductTopology
    [WeaklyHausdorffSpace.{u, u} X] [WeaklyHausdorffSpace.{v, v} Y] :
    Continuous[ inferInstance, compactlyGeneratedFactorsOrdinaryProductTopology X Y]
      (generatorProdEval X Y) := by
  have hEvalX :
      Continuous[ (inferInstance : TopologicalSpace (generatorSource X)),
        TopologicalSpace.compactlyGenerated.{u, u} X] (generatorEval X) := by
    -- The first factor topology is definitionally the coinduced topology of `generatorEval X`.
    rw [TopologicalSpace.compactlyGenerated]
    simpa [generatorEval] using
      (continuous_coinduced_rng :
        Continuous[ (inferInstance : TopologicalSpace (generatorSource X)),
          TopologicalSpace.coinduced (generatorEval X)
            (inferInstance : TopologicalSpace (generatorSource X))] (generatorEval X))
  have hEvalY :
      Continuous[ (inferInstance : TopologicalSpace (generatorSource Y)),
        TopologicalSpace.compactlyGenerated.{v, v} Y] (generatorEval Y) := by
    -- The second factor is the same coinduced presentation for `Y`.
    rw [TopologicalSpace.compactlyGenerated]
    simpa [generatorEval] using
      (continuous_coinduced_rng :
        Continuous[ (inferInstance : TopologicalSpace (generatorSource Y)),
          TopologicalSpace.coinduced (generatorEval Y)
            (inferInstance : TopologicalSpace (generatorSource Y))] (generatorEval Y))
  have hLeft :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} X]
        (fun z : generatorSource X × generatorSource Y ↦ generatorEval X z.1) := by
    -- The first product coordinate is the canonical kification evaluation after `Prod.fst`.
    simpa [generatorProdEval, Function.comp] using
      (@Continuous.comp (generatorSource X × generatorSource Y) (generatorSource X) X
        inferInstance inferInstance (TopologicalSpace.compactlyGenerated.{u, u} X)
        Prod.fst (generatorEval X) hEvalX continuous_fst)
  have hRight :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (fun z : generatorSource X × generatorSource Y ↦ generatorEval Y z.2) := by
    -- The second product coordinate is handled symmetrically after `Prod.snd`.
    simpa [generatorProdEval, Function.comp] using
      (@Continuous.comp (generatorSource X × generatorSource Y) (generatorSource Y) Y
        inferInstance inferInstance (TopologicalSpace.compactlyGenerated.{v, v} Y)
        Prod.snd (generatorEval Y) hEvalY continuous_snd)
  -- Exposing the factor kifications turns the target into the ordinary product topology.
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
  -- Product continuity is coordinatewise once the target has the ordinary product form.
  simpa [compactlyGeneratedFactorsOrdinaryProductTopology,
    compactlyGeneratedFactorsOrdinaryProductTopologyAux, generatorProdEval] using
    hLeft.prodMk hRight

/-- Proposition 5.1.18. If `X` and `Y` are weak Hausdorff, then the chapter's compactly generated
product `X × Y = k(X ×_c Y)` agrees with `kX × kY`.  The product on the right is again the
chapter's compactly generated product, so it includes the outer kification after forming the
ordinary product of `kX` and `kY`. -/
theorem compactlyGeneratedProductTopology_eq_compactlyGeneratedFactorsProductTopology
    [hX : WeaklyHausdorffSpace.{u, max u v} X] [hY : WeaklyHausdorffSpace.{v, max u v} Y] :
    compactlyGeneratedProductTopology X Y =
      compactlyGeneratedFactorsProductTopology X Y := by
  apply le_antisymm
  · rw [compactlyGeneratedProductTopology_def, ← continuous_id_iff_le]
    refine
      @continuous_from_compactlyGenerated.{max u v, max u v, max u v}
        (X × Y) (X × Y)
        (X ×_c Y) (compactlyGeneratedFactorsProductTopology X Y)
        id ?_
    intro S g
    have hgFactors :
        Continuous[ inferInstance, compactlyGeneratedFactorsOrdinaryProductTopology X Y] g :=
      continuousToCompactlyGeneratedFactorsOrdinaryProductTopologyOfContinuous
        (X := X) (Y := Y) g.continuous
    let _ : TopologicalSpace (X × Y) :=
      compactlyGeneratedFactorsOrdinaryProductTopology X Y
    simpa [Function.comp] using
      (continuousToCompactlyGeneratedOfContinuous (X := X × Y) hgFactors)
  · rw [← continuous_id_iff_le]
    refine
      @continuous_from_compactlyGenerated.{max u v, max u v, max u v}
        (X × Y) (X × Y)
        (compactlyGeneratedFactorsOrdinaryProductTopology X Y)
        (compactlyGeneratedProductTopology X Y)
        id ?_
    intro S g
    let _ : TopologicalSpace (X × Y) :=
      compactlyGeneratedFactorsOrdinaryProductTopology X Y
    have hgFactors : Continuous g := g.continuous
    have hgOrdinary : Continuous[ inferInstance, X ×_c Y] g :=
      continuousToOrdinaryProductOfContinuousCompactlyGeneratedFactors
        (X := X) (Y := Y) hgFactors
    let _ : TopologicalSpace (X × Y) := X ×_c Y
    simpa [Function.comp] using
      (continuousToCompactlyGeneratedOfContinuous (X := X × Y) hgOrdinary)

end
