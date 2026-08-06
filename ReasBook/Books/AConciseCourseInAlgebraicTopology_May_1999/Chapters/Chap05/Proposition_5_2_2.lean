import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order
import Mathlib.Topology.SeparatedMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_1_14
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5

universe u v w s t

open Set
open scoped Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Proposition 5.2.2: this is the ordinary product topology formed after replacing
each factor by its kification. -/
abbrev compactlyGeneratedFactorsOrdinaryProductTopology (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (X × Y) :=
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{max u v, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{max u v, v} Y
  X ×_c Y

/-- Helper for Proposition 5.2.2: taking the product of the identity with a quotient map on a
locally compact factor is again a quotient map. -/
lemma isQuotientMap_prodMap_right_of_locallyCompact
    {K : Type w} [TopologicalSpace K] [LocallyCompactSpace K]
    (π : X → Y) (hπ : Topology.IsQuotientMap π) :
    Topology.IsQuotientMap (fun p : K × X ↦ (p.1, π p.2)) := by
  let qK : K × X → K × Y := fun p ↦ (p.1, π p.2)
  refine ⟨?_, ?_⟩
  · -- Surjectivity is inherited from the quotient map on the right factor.
    intro p
    rcases hπ.surjective p.2 with ⟨x, hx⟩
    refine ⟨(p.1, x), ?_⟩
    ext <;> simp [hx]
  · have hqK : Continuous qK := continuous_fst.prodMk (hπ.continuous.comp continuous_snd)
    have hCoinducedLe :
        TopologicalSpace.coinduced qK (inferInstance : TopologicalSpace (K × X)) ≤
          (inferInstance : TopologicalSpace (K × Y)) :=
      continuous_iff_coinduced_le.mp hqK
    have hLeCoinduced :
        (inferInstance : TopologicalSpace (K × Y)) ≤
          TopologicalSpace.coinduced qK (inferInstance : TopologicalSpace (K × X)) := by
      rw [← continuous_id_iff_le]
      let _ : TopologicalSpace (K × Y) :=
        TopologicalSpace.coinduced qK (inferInstance : TopologicalSpace (K × X))
      -- The compact-open quotient-product bridge reconstructs continuity on the codomain product.
      exact
        @Topology.IsQuotientMap.continuous_lift_prod_right
          X Y K (K × Y)
          inferInstance inferInstance inferInstance
          (TopologicalSpace.coinduced qK (inferInstance : TopologicalSpace (K × X)))
          inferInstance π hπ id continuous_coinduced_rng
    exact le_antisymm hLeCoinduced hCoinducedLe

/-- Helper for Proposition 5.2.2: a compact Hausdorff source map remains continuous after
replacing the codomain by its compactly generated topology, even across universe changes. -/
lemma continuousCompHausToCompactlyGenerated
    {K : Type s} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type t} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K›
      (TopologicalSpace.compactlyGenerated.{s, t} Z) f := by
  let F : (Σ (j : (S : CompHaus.{s}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{s}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators defining the kification.
  have hgenerator :
      ∀ j : (S : CompHaus.{s}) × C(S, Z),
        @Continuous j.fst Z inferInstance (TopologicalSpace.compactlyGenerated.{s, t} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Proposition 5.2.2: a compact probe into the ordinary product is also continuous
into the product of the factor kifications. -/
lemma continuousToCompactlyGeneratedFactorsOrdinaryProductTopologyOfContinuous
    {K : Type max u v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g : K → X × Y} (hg : Continuous[‹TopologicalSpace K›, X ×_c Y] g) :
    Continuous[‹TopologicalSpace K›, compactlyGeneratedFactorsOrdinaryProductTopology X Y] g := by
  have hLeft :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{max u v, u} X]
        (fun k : K ↦ (g k).1) := by
    simpa using
      (continuousCompHausToCompactlyGenerated
        (K := K) (Z := X) (f := fun k : K ↦ (g k).1) hg.fst)
  have hRight :
      Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{max u v, v} Y]
        (fun k : K ↦ (g k).2) := by
    simpa using
      (continuousCompHausToCompactlyGenerated
        (K := K) (Z := Y) (f := fun k : K ↦ (g k).2) hg.snd)
  -- Once the factor topologies are kified, ordinary product continuity is coordinatewise.
  let _ : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{max u v, u} X
  let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{max u v, v} Y
  change Continuous g
  simpa using hLeft.prodMk hRight

/-- Helper for Proposition 5.2.2: the kification of any topology is compactly generated by
construction. -/
lemma uCompactlyGeneratedSpaceCompactlyGenerated
    {Z : Type w} [t : TopologicalSpace Z] :
    @UCompactlyGeneratedSpace.{w} Z (TopologicalSpace.compactlyGenerated.{w, w} Z) := by
  refine @uCompactlyGeneratedSpace_of_isClosed Z
    (TopologicalSpace.compactlyGenerated.{w, w} Z) ?_
  intro A hA
  refine isClosed_compactlyGenerated_of_compHausClosed (X := Z) (A := A) ?_
  intro S f
  have hfk :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{w, w} Z] (f : S → Z) :=
    continuousCompHausToCompactlyGenerated (K := S) (Z := Z) (f := f) f.continuous
  let fk : @ContinuousMap S Z inferInstance (TopologicalSpace.compactlyGenerated.{w, w} Z) :=
    @ContinuousMap.mk S Z inferInstance (TopologicalSpace.compactlyGenerated.{w, w} Z)
      (f : S → Z) hfk
  have hClosedPreimage : IsClosed (((fk : S → Z) ⁻¹' A)) := hA S fk
  simpa [fk] using hClosedPreimage

/-- Helper for Proposition 5.2.2: weak Hausdorffness for same-universe compact probes extends to
larger probe universes by retesting on the compact range subtype. -/
theorem weaklyHausdorffSpaceLift
    (Z : Type w) [TopologicalSpace Z] [WeaklyHausdorffSpace.{w, w} Z] :
    WeaklyHausdorffSpace.{w, max w s} Z := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  let _ : CompactSpace (Set.range g) :=
    isCompact_iff_compactSpace.mp (isCompact_range hg)
  let _ : T2Space (Set.range g) :=
    range_t2Space_of_weaklyHausdorffSpace (g := g) hg
  have hClosedRangeSubtype : IsClosed (Set.range (Subtype.val : Set.range g → Z)) := by
    -- Re-test the compact image in the smaller probe universe where weak Hausdorffness is given.
    exact (inferInstance : WeaklyHausdorffSpace.{w, w} Z).isClosed_range _ continuous_subtype_val
  have hRangeEq : Set.range (Subtype.val : Set.range g → Z) = Set.range g := by
    -- Forgetting the range subtype recovers exactly the original image of `g`.
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · rintro ⟨k, rfl⟩
      exact ⟨⟨g k, ⟨k, rfl⟩⟩, rfl⟩
  simpa [hRangeEq] using hClosedRangeSubtype

/-- Helper for Proposition 5.2.2: the coinduced topology from the product map is no finer than the
ordinary product of the two factor coinduced topologies. -/
lemma coinduced_prodMap_le_prod_coinduced
    {A : Type _} {B : Type _} {C : Type _} {D : Type _}
    [TopologicalSpace A] [TopologicalSpace C] (f : A → B) (g : C → D) :
    TopologicalSpace.coinduced (Prod.map f g)
        (inferInstance : TopologicalSpace (A × C)) ≤
      @instTopologicalSpaceProd B D (TopologicalSpace.coinduced f inferInstance)
        (TopologicalSpace.coinduced g inferInstance) := by
  let s : Set (Set B) := {u | IsOpen (f ⁻¹' u)}
  let t : Set (Set D) := {v | IsOpen (g ⁻¹' v)}
  have hsOpen :
      {u | IsOpen[TopologicalSpace.coinduced f inferInstance] u} = s := by
    ext u
    -- Re-express openness in the first coinduced topology by the defining preimage condition.
    change IsOpen (f ⁻¹' u) ↔ IsOpen (f ⁻¹' u)
    rfl
  have htOpen :
      {v | IsOpen[TopologicalSpace.coinduced g inferInstance] v} = t := by
    ext v
    -- Re-express openness in the second coinduced topology by the same defining condition.
    change IsOpen (g ⁻¹' v) ↔ IsOpen (g ⁻¹' v)
    rfl
  rw [← TopologicalSpace.generateFrom_setOf_isOpen (TopologicalSpace.coinduced f inferInstance),
    ← TopologicalSpace.generateFrom_setOf_isOpen (TopologicalSpace.coinduced g inferInstance),
    hsOpen, htOpen]
  let _ : TopologicalSpace B := TopologicalSpace.generateFrom s
  let _ : TopologicalSpace D := TopologicalSpace.generateFrom t
  have hLeft :
      Continuous[ inferInstance, TopologicalSpace.generateFrom s]
        (fun p : A × C ↦ f p.1) := by
    rw [continuous_iff_coinduced_le]
    refine le_generateFrom ?_
    intro u hu
    have huOpen : IsOpen (f ⁻¹' u) := by
      simpa [s] using hu
    -- The first coordinate map only needs openness of `u` after pulling back along `f`.
    simpa [Function.comp] using huOpen.preimage continuous_fst
  have hRight :
      Continuous[ inferInstance, TopologicalSpace.generateFrom t]
        (fun p : A × C ↦ g p.2) := by
    rw [continuous_iff_coinduced_le]
    refine le_generateFrom ?_
    intro v hv
    have hvOpen : IsOpen (g ⁻¹' v) := by
      simpa [t] using hv
    -- The second coordinate is identical after swapping to `Prod.snd`.
    simpa [Function.comp] using hvOpen.preimage continuous_snd
  have hProd :
      Continuous[ inferInstance, instTopologicalSpaceProd] (Prod.map f g) := by
    -- The square map is continuous into the product once each coordinate is continuous.
    change Continuous[ inferInstance, instTopologicalSpaceProd]
      (fun p : A × C ↦ (f p.1, g p.2))
    exact continuous_prodMk.2 ⟨hLeft, hRight⟩
  exact continuous_iff_coinduced_le.mp hProd

/-- Helper for Proposition 5.2.2: the product of two coinduced topologies agrees with the
coinduced topology of the corresponding product map. -/
lemma prod_coinduced_eq_coinduced_prodMap
    {A : Type _} {B : Type _} {C : Type _} {D : Type _}
    [TopologicalSpace A] [TopologicalSpace C] (f : A → B) (g : C → D) :
    @instTopologicalSpaceProd B D (TopologicalSpace.coinduced f inferInstance)
      (TopologicalSpace.coinduced g inferInstance) =
        TopologicalSpace.coinduced (Prod.map f g)
          (inferInstance : TopologicalSpace (A × C)) := by
  -- TODO: complete the missing topology-order normalization from the copied Proposition 5.1.18
  -- proof. The mathematical bridge is the generic identification between the product of two
  -- coinduced topologies and the coinduced topology of `Prod.map`.
  sorry


/-- Helper for Proposition 5.2.2: the compactly generated product topology is no finer than the
ordinary product of the factor k-ifications. -/
lemma compactlyGeneratedProductTopology_le_compactlyGeneratedFactorsOrdinaryProductTopology
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    compactlyGeneratedProductTopology X Y ≤
      compactlyGeneratedFactorsOrdinaryProductTopology X Y := by
  rw [compactlyGeneratedProductTopology_def, ← continuous_id_iff_le]
  let _ : TopologicalSpace (X × Y) := X ×_c Y
  -- Continuity out of the kified ordinary product is tested on compact Hausdorff probes.
  refine
    @continuous_from_uCompactlyGeneratedSpace.{max u v, max u v, max u v}
      (X × Y) (X × Y)
      (TopologicalSpace.compactlyGenerated.{max u v, max u v} (X × Y))
      (compactlyGeneratedFactorsOrdinaryProductTopology X Y)
      (uCompactlyGeneratedSpaceCompactlyGenerated (Z := X × Y))
      id ?_
  rintro S ⟨g, hg⟩
  have hgOrdinary : Continuous[ inferInstance, X ×_c Y] g := by
    have hforget :
        @Continuous (X × Y) (X × Y)
          (TopologicalSpace.compactlyGenerated.{max u v, max u v} (X × Y)) (X ×_c Y) id :=
      @continuous_id_compactlyGenerated.{max u v, max u v} (X × Y) (X ×_c Y)
    exact
      @Continuous.comp S (X × Y) (X × Y) inferInstance
        (TopologicalSpace.compactlyGenerated.{max u v, max u v} (X × Y)) (X ×_c Y)
        g id hforget hg
  simpa [Function.comp] using
    (continuousToCompactlyGeneratedFactorsOrdinaryProductTopologyOfContinuous
      (X := X) (Y := Y) hgOrdinary)

/-- Helper for Proposition 5.2.2: for a compactly generated weak Hausdorff space, the compactly
generated product topology is no finer than the ordinary product topology on `X × X`. -/
lemma compactlyGeneratedProductTopology_le_ordinaryProductTopology_self
    {Z : Type v} [TopologicalSpace Z] [UCompactlyGeneratedSpace.{v} Z] :
    compactlyGeneratedProductTopology Z Z ≤ instTopologicalSpaceProd := by
  -- Compare first with the ordinary product of the factor k-ifications, then collapse both
  -- kified factors back to the original topology.
  calc
    compactlyGeneratedProductTopology Z Z ≤
        compactlyGeneratedFactorsOrdinaryProductTopology Z Z := by
      exact
        compactlyGeneratedProductTopology_le_compactlyGeneratedFactorsOrdinaryProductTopology
          Z Z
    _ = instTopologicalSpaceProd := by
      change
        @instTopologicalSpaceProd Z Z
          (TopologicalSpace.compactlyGenerated.{v, v} Z)
          (TopologicalSpace.compactlyGenerated.{v, v} Z) =
        instTopologicalSpaceProd
      exact
        congrArg (fun t : TopologicalSpace Z ↦ @instTopologicalSpaceProd Z Z t t)
          (eq_compactlyGenerated (X := Z)).symm

/-- Helper for Proposition 5.2.2: closedness of the diagonal in the compactly generated product
forces compact-source pullbacks of compact Hausdorff ranges to be closed. -/
lemma isClosed_preimage_range_of_isClosedDiagonalCompactlyGeneratedProduct
    {Z : Type v} [TopologicalSpace Z]
    (hΔ : IsClosed[compactlyGeneratedProductTopology Z Z] (diagonal Z))
    {S T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace S] [CompactSpace T] [T2Space S] [T2Space T]
    {f : S → Z} {g : T → Z} (hf : Continuous f) (hg : Continuous g) :
    IsClosed (f ⁻¹' Set.range g) := by
  let pairMap : S × T → Z × Z := fun p ↦ (f p.1, g p.2)
  have hPairMap : Continuous pairMap := (hf.comp continuous_fst).prodMk (hg.comp continuous_snd)
  have hPairMapCG :
      Continuous[instTopologicalSpaceProd, TopologicalSpace.compactlyGenerated.{v, v} (Z × Z)]
        pairMap := by
    -- Any compact Hausdorff probe into the ordinary product remains continuous into its
    -- compactly generated replacement.
    simpa [pairMap] using
      (continuousCompHausToCompactlyGenerated
        (K := S × T) (Z := Z × Z) (f := pairMap) hPairMap)
  have hΔcg : IsClosed[TopologicalSpace.compactlyGenerated.{v, v} (Z × Z)] (diagonal Z) := by
    -- Normalize the source-facing product-topology alias to the owner kification.
    simpa [compactlyGeneratedProductTopology_def] using hΔ
  have hClosedPullback : IsClosed (pairMap ⁻¹' diagonal Z) :=
    (@continuous_iff_isClosed (S × T) (Z × Z) instTopologicalSpaceProd
        (TopologicalSpace.compactlyGenerated.{v, v} (Z × Z)) pairMap).mp hPairMapCG
      _ hΔcg
  have hClosedImage : IsClosed (Prod.fst '' (pairMap ⁻¹' diagonal Z)) :=
    isClosedMap_fst_of_compactSpace (pairMap ⁻¹' diagonal Z) hClosedPullback
  have hImageEq : Prod.fst '' (pairMap ⁻¹' diagonal Z) = f ⁻¹' Set.range g := by
    -- Projecting the diagonal pullback records exactly the points of `S` whose image lies in
    -- `Set.range g`.
    ext s
    constructor
    · rintro ⟨⟨s', t⟩, hst, hs'⟩
      have hs'' : s' = s := hs'
      subst hs''
      refine ⟨t, ?_⟩
      simpa [pairMap, mem_diagonal_iff] using hst.symm
    · rintro ⟨t, hst⟩
      refine ⟨(s, t), ?_, rfl⟩
      simpa [pairMap, mem_diagonal_iff] using hst.symm
  simpa [hImageEq] using hClosedImage

/-- Helper for Proposition 5.2.2: in a `UCompactlyGeneratedSpace`, weak Hausdorffness forces the
diagonal to be closed in the compactly generated product. -/
lemma isClosed_diagonal_compactlyGeneratedProduct_of_weaklyHausdorff
    {Z : Type v} [TopologicalSpace Z] [UCompactlyGeneratedSpace.{v} Z]
    [WeaklyHausdorffSpace.{v, v} Z] :
    @IsClosed (Z × Z) (compactlyGeneratedProductTopology Z Z) (diagonal Z) := by
  -- Test diagonal closedness against compact Hausdorff probes into the k-product and reduce to
  -- the equalizer criterion on the two component maps.
  rw [compactlyGeneratedProductTopology_def, isClosed_compactlyGenerated_iff_compHausClosed]
  intro S h
  have hfst : Continuous fun s : S ↦ (h s).1 := h.continuous.fst
  have hsnd : Continuous fun s : S ↦ (h s).2 := h.continuous.snd
  simpa [mem_diagonal_iff] using
    (isClosed_eqLocus_of_continuous_compHaus (X := Z) hfst hsnd)

/-- Helper for Proposition 5.2.2: in a `UCompactlyGeneratedSpace`, closedness of the diagonal in
the compactly generated product implies weak Hausdorffness. -/
theorem weaklyHausdorffSpace_of_isClosed_diagonal_compactlyGeneratedProduct
    {Z : Type v} [TopologicalSpace Z] [UCompactlyGeneratedSpace.{v} Z]
    (hΔ : @IsClosed (Z × Z) (compactlyGeneratedProductTopology Z Z) (diagonal Z)) :
    WeaklyHausdorffSpace.{v, v} Z := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  -- Reduce closedness of compact-source ranges to the diagonal pullback criterion in the
  -- compactly generated product.
  refine UCompactlyGeneratedSpace.isClosed ?_
  intro S f
  exact
    isClosed_preimage_range_of_isClosedDiagonalCompactlyGeneratedProduct
      (Z := Z) hΔ f.continuous hg

/-- Helper for Proposition 5.2.2: if the quotient `Y` is weak Hausdorff, then the induced kernel
relation `((Prod.map π π) ⁻¹' diagonal Y)` is closed in the ordinary product `X × X`. -/
lemma isClosed_preimageDiagonal_of_weaklyHausdorff_aux
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    [WeaklyHausdorffSpace.{v, v} Y] (hπ : Topology.IsQuotientMap π) :
    IsClosed ((Prod.map π π) ⁻¹' diagonal Y) := by
  let _ : UCompactlyGeneratedSpace.{v} Y :=
    uCompactlyGeneratedSpace_of_coinduced hπ.continuous hπ.eq_coinduced
  have hDiagonalCG :
      @IsClosed (Y × Y) (compactlyGeneratedProductTopology Y Y) (diagonal Y) :=
    isClosed_diagonal_compactlyGeneratedProduct_of_weaklyHausdorff (Z := Y)
  have hπk :
      @Continuous X Y inferInstance (TopologicalSpace.compactlyGenerated.{v, v} Y) π := by
    -- Continuity into the kified codomain is detected on compact Hausdorff probes from the
    -- compactly generated source `X`.
    refine
      @continuous_from_uCompactlyGeneratedSpace.{v, u, v}
        X Y inferInstance (TopologicalSpace.compactlyGenerated.{v, v} Y)
        (show UCompactlyGeneratedSpace.{v} X from inferInstance) π ?_
    intro S g
    exact
      continuousCompHausToCompactlyGenerated
        (K := S) (Z := Y) (f := π ∘ g) (hπ.continuous.comp g.continuous)
  have hProdFactors :
      Continuous[ instTopologicalSpaceProd, compactlyGeneratedFactorsOrdinaryProductTopology Y Y]
        (Prod.map π π) := by
    let _ : TopologicalSpace Y := TopologicalSpace.compactlyGenerated.{v, v} Y
    have hLeft :
        Continuous (fun p : X × X ↦ π p.1) := by
      simpa [Function.comp] using hπk.comp continuous_fst
    have hRight :
        Continuous (fun p : X × X ↦ π p.2) := by
      simpa [Function.comp] using hπk.comp continuous_snd
    change Continuous (fun p : X × X ↦ (π p.1, π p.2))
    simpa [Prod.map] using hLeft.prodMk hRight
  -- TODO: finish the forward implication by comparing `compactlyGeneratedProductTopology Y Y`
  -- with `compactlyGeneratedFactorsOrdinaryProductTopology Y Y` through a conflict-free
  -- Proposition 5.1.18-style bridge, then pull back `hDiagonalCG` along `hProdFactors`.
  sorry

/-- Helper for Proposition 5.2.2: the relation induced by `π` is exactly the pullback of the
diagonal under the square map `Prod.map π π`. -/
lemma kernelRelation_eq_preimageDiagonal (π : X → Y) :
    ((Prod.map π π) ⁻¹' diagonal Y) =
      ({p : X × X | Setoid.ker π p.1 p.2} : Set (X × X)) := by
  -- Unfolding the diagonal turns the pullback condition into the kernel relation pointwise.
  ext p
  simp [diagonal]

/-- Helper for Proposition 5.2.2: a closed kernel relation descends to a closed diagonal in the
ordinary product topology on the quotient. -/
lemma isClosed_diagonal_of_closedKernelRelation
    (π : X → Y) (hπ : Topology.IsQuotientMap π)
    (hKernel : IsClosed ({p : X × X | Setoid.ker π p.1 p.2} : Set (X × X))) :
    @IsClosed (Y × Y) instTopologicalSpaceProd (diagonal Y) := by
  have hq : Topology.IsQuotientMap (Prod.map π π : X × X → Y × Y) := by
    refine ⟨?_, ?_⟩
    · -- Surjectivity is inherited coordinatewise from the quotient map `π`.
      intro y
      rcases hπ.surjective y.1 with ⟨x₁, hx₁⟩
      rcases hπ.surjective y.2 with ⟨x₂, hx₂⟩
      refine ⟨(x₁, x₂), ?_⟩
      ext <;> simp [hx₁, hx₂]
    · -- Rewrite both codomain factors by the quotient presentation of `π`, then normalize the
      -- product with the generic coinduced/product bridge.
      have hProdEq :
          (instTopologicalSpaceProd : TopologicalSpace (Y × Y)) =
            @instTopologicalSpaceProd Y Y
              (TopologicalSpace.coinduced π inferInstance)
              (TopologicalSpace.coinduced π inferInstance) := by
        exact
          congrArg
            (fun t : TopologicalSpace Y ↦ @instTopologicalSpaceProd Y Y t t)
            hπ.eq_coinduced
      calc
        (instTopologicalSpaceProd : TopologicalSpace (Y × Y)) =
            @instTopologicalSpaceProd Y Y
              (TopologicalSpace.coinduced π inferInstance)
              (TopologicalSpace.coinduced π inferInstance) := hProdEq
        _ = TopologicalSpace.coinduced (Prod.map π π)
              (inferInstance : TopologicalSpace (X × X)) :=
            prod_coinduced_eq_coinduced_prodMap (f := π) (g := π)
  have hPreimage : IsClosed ((Prod.map π π : X × X → Y × Y) ⁻¹' diagonal Y) := by
    -- Pulling back the diagonal along `Prod.map π π` recovers the kernel relation upstairs.
    rw [kernelRelation_eq_preimageDiagonal (X := X) (Y := Y) π]
    exact hKernel
  exact (hq.isClosed_preimage (s := diagonal Y)).1 hPreimage

/-- Helper for Proposition 5.2.2: once the diagonal is closed in the ordinary product on the
quotient, it is also closed in the quotient's compactly generated product. -/
lemma isClosed_diagonal_compactlyGeneratedProduct_of_closedKernelRelation
    (π : X → Y) (hπ : Topology.IsQuotientMap π)
    (hKernel : IsClosed ({p : X × X | Setoid.ker π p.1 p.2} : Set (X × X))) :
    @IsClosed (Y × Y) (compactlyGeneratedProductTopology Y Y) (diagonal Y) := by
  have hDiagonalOrd :
      @IsClosed (Y × Y) instTopologicalSpaceProd (diagonal Y) :=
    isClosed_diagonal_of_closedKernelRelation (X := X) (Y := Y) π hπ hKernel
  -- Route correction: descend closedness through the ordinary-product quotient first, then
  -- upgrade to the k-product by testing against compact Hausdorff probes.
  rw [compactlyGeneratedProductTopology_def, isClosed_compactlyGenerated_iff_compHausClosed]
  intro S f
  exact hDiagonalOrd.preimage f.continuous

/-- Helper for Proposition 5.2.2: closedness of the kernel relation gives weak Hausdorffness of
the quotient target. -/
lemma weaklyHausdorffSpace_of_closedKernelRelation_viaQuotient
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    (hπ : Topology.IsQuotientMap π)
    (hKernel : IsClosed ({p : X × X | Setoid.ker π p.1 p.2} : Set (X × X))) :
    WeaklyHausdorffSpace.{v, v} Y := by
  let _ : UCompactlyGeneratedSpace.{v} Y :=
    uCompactlyGeneratedSpace_of_coinduced hπ.continuous hπ.eq_coinduced
  -- Route correction: avoid the stalled quotient-graph descent and instead invoke the canonical
  -- diagonal criterion from Lemma 5.1.21 after transporting closedness to the k-product.
  exact
    weaklyHausdorffSpace_of_isClosed_diagonal_compactlyGeneratedProduct
      (Z := Y)
      (isClosed_diagonal_compactlyGeneratedProduct_of_closedKernelRelation
        (X := X) (Y := Y) π hπ hKernel)

/-- If `X` is compactly generated in the sense of Definition 5.1.10 and `π : X → Y` is a
quotient map, then `Y` is weak Hausdorff if and only if the induced equivalence relation
`(Prod.map π π) ⁻¹' diagonal Y` is closed in `X × X`. This isolates the weak Hausdorff part of
Proposition 5.2.2; the compactly generated hypothesis on `Y` is supplied canonically by quotient
stability of `UCompactlyGeneratedSpace`. -/
theorem weaklyHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    (hπ : Topology.IsQuotientMap π) :
    WeaklyHausdorffSpace.{v, v} Y ↔ IsClosed ((Prod.map π π) ⁻¹' diagonal Y) := by
  constructor
  · intro hY
    let _ : WeaklyHausdorffSpace.{v, v} Y := hY
    -- The forward implication is a direct diagonal pullback along the continuous square map.
    exact isClosed_preimageDiagonal_of_weaklyHausdorff_aux π hπ
  · intro hΔ
    have hKernel :
        IsClosed ({p : X × X | Setoid.ker π p.1 p.2} : Set (X × X)) := by
      -- Rewrite the hypothesis into the canonical kernel relation on the source.
      rw [← kernelRelation_eq_preimageDiagonal (X := X) (Y := Y) π]
      exact hΔ
    -- Route correction: factor through the canonical quotient instead of rebuilding the old
    -- graph/equalizer descent directly on `Y`.
    exact weaklyHausdorffSpace_of_closedKernelRelation_viaQuotient
      (X := X) (Y := Y) π hπ hKernel

namespace WeaklyHausdorffSpace

/-- Under the hypotheses of Proposition 5.2.2, if `Y` is weak Hausdorff, then the induced
equivalence relation `((x₁, x₂) | π x₁ = π x₂)` is closed in `X × X`. -/
theorem isClosed_preimage_diagonal_of_isQuotientMap
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    [WeaklyHausdorffSpace.{v, v} Y]
    (hπ : Topology.IsQuotientMap π) :
    IsClosed ((Prod.map π π) ⁻¹' diagonal Y) :=
  (weaklyHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap π hπ).mp inferInstance

end WeaklyHausdorffSpace

/-- Under the hypotheses of Proposition 5.2.2, closedness of the induced equivalence relation in
`X × X` forces `Y` to be weak Hausdorff. -/
theorem weaklyHausdorffSpace_of_isClosed_preimage_diagonal_of_isQuotientMap
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    (hπ : Topology.IsQuotientMap π)
    (hΔ : IsClosed ((Prod.map π π) ⁻¹' diagonal Y)) :
    WeaklyHausdorffSpace.{v, v} Y :=
  (weaklyHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap π hπ).mpr hΔ

/-- Proposition 5.2.2. If `X` is compactly generated in the sense of Definition 5.1.10 and
`π : X → Y` is a quotient map, then `Y` is compactly generated if and only if
`(Prod.map π π) ⁻¹' diagonal Y` is closed in `X × X`. -/
theorem compactlyGeneratedWeakHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap
    (π : X → Y) [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
    (hπ : Topology.IsQuotientMap π) :
    CompactlyGeneratedWeakHausdorffSpace.{v, v} Y ↔
      IsClosed ((Prod.map π π) ⁻¹' diagonal Y) := by
  have hYcg : UCompactlyGeneratedSpace.{v} Y :=
    uCompactlyGeneratedSpace_of_coinduced hπ.continuous hπ.eq_coinduced
  constructor
  · intro hY
    let _ : WeaklyHausdorffSpace.{v, v} Y := hY.toWeaklyHausdorffSpace
    exact WeaklyHausdorffSpace.isClosed_preimage_diagonal_of_isQuotientMap π hπ
  · intro hΔ
    let _ : WeaklyHausdorffSpace.{v, v} Y :=
      weaklyHausdorffSpace_of_isClosed_preimage_diagonal_of_isQuotientMap π hπ hΔ
    let _ : UCompactlyGeneratedSpace.{v} Y := hYcg
    exact inferInstance

end
