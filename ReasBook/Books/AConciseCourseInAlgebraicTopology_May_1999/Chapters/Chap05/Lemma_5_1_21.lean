import Mathlib.Topology.Maps.Proper.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_1_14
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5

universe u

open Set
open scoped Topology

-- Semantic search hits: `t2_iff_isClosed_diagonal` and `TopologicalSpace.compactlyGenerated`;
-- local Chapter 5 precedent uses `WeaklyHausdorffSpace` and `compactlyGeneratedProductTopology`
-- for the source-facing weak Hausdorff and k-product APIs.

section

/-- Helper for Lemma 5.1.21: a map from a compact Hausdorff space into `Y` that is continuous for
the original topology `t` is automatically continuous into
`TopologicalSpace.compactlyGenerated Y`. -/
lemma continuousToCompactlyGeneratedOfContinuousCompHaus
    {Y : Type u} (t : TopologicalSpace Y) {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] {f : K → Y} (hf : Continuous[‹TopologicalSpace K›, t] f) :
    Continuous[‹TopologicalSpace K›, TopologicalSpace.compactlyGenerated.{u, u} Y] f := by
  -- Realize `f` as one of the generating maps in the sigma-family defining the k-ification.
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{u, u} Y]
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    -- Rewrite to the owner definition so the sigma-family continuity is the canonical generator.
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  -- Specialize the sigma-family statement to the chosen compact Hausdorff source.
  simpa [F, i] using hgenerator i

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Lemma 5.1.21: if `f g : K → X` are continuous from a compact Hausdorff space into a
weakly Hausdorff space, then their equalizer is closed. -/
private lemma lemma_5_1_21_isClosed_eqLocus_of_continuous_compHaus
    [WeaklyHausdorffSpace.{u, u} X]
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed {x : K | f x = g x} := by
  let rangePair : K → Set.range f × Set.range g := fun x ↦
    (⟨f x, ⟨x, rfl⟩⟩, ⟨g x, ⟨x, rfl⟩⟩)
  have hRangePairLeft : Continuous fun x : K => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f) :=
    hf.subtype_mk fun x ↦ ⟨x, rfl⟩
  have hRangePairRight : Continuous fun x : K => (⟨g x, ⟨x, rfl⟩⟩ : Set.range g) :=
    hg.subtype_mk fun x ↦ ⟨x, rfl⟩
  have hRangePair : Continuous rangePair :=
    hRangePairLeft.prodMk hRangePairRight
  let commonRange : Set X := Set.range f ∩ Set.range g
  have hRangeGClosed : IsClosed (Set.range g) :=
    Continuous.isClosed_range hg
  have hCommonRangeCompact : IsCompact commonRange := by
    -- The common range is a closed subset of the compact range of `f`.
    simpa [commonRange] using (isCompact_range hf).inter_right hRangeGClosed
  let _ : CompactSpace commonRange := isCompact_iff_compactSpace.mp hCommonRangeCompact
  let _ : WeaklyHausdorffSpace.{u, u} commonRange := Subtype.weaklyHausdorffSpace
  let _ : T2Space commonRange := CompactSpace.toT2Space_of_weaklyHausdorffSpace commonRange
  let diagonalMap : commonRange → Set.range f × Set.range g := fun x ↦
    (⟨x.1, x.2.1⟩, ⟨x.1, x.2.2⟩)
  have hDiagonalLeft :
      Continuous fun x : commonRange => (⟨x.1, x.2.1⟩ : Set.range f) :=
    continuous_subtype_val.subtype_mk fun x ↦ x.2.1
  have hDiagonalRight :
      Continuous fun x : commonRange => (⟨x.1, x.2.2⟩ : Set.range g) :=
    continuous_subtype_val.subtype_mk fun x ↦ x.2.2
  have hDiagonalMap : Continuous diagonalMap :=
    hDiagonalLeft.prodMk hDiagonalRight
  -- Local instance justification (typeclass): the two range subspaces carry explicit compact
  -- Hausdorff source data, and binding their `T2Space` instances avoids a timeout when Lean tries
  -- to synthesize the product instance through the parameterized range construction.
  let _ : T2Space (Set.range f) := range_t2Space_of_weaklyHausdorffSpace f hf
  -- Local instance justification (typeclass): this is the second factor needed for the product
  -- codomain of `diagonalMap`.
  let _ : T2Space (Set.range g) := range_t2Space_of_weaklyHausdorffSpace g hg
  have hDiagonalRangeCompact : IsCompact (Set.range diagonalMap) :=
    isCompact_range hDiagonalMap
  have hClosedDiagonalRange : IsClosed (Set.range diagonalMap) :=
    hDiagonalRangeCompact.isClosed
  have hEqualizerEq :
      rangePair ⁻¹' Set.range diagonalMap = {x : K | f x = g x} := by
    -- Pulling back the diagonal image records exactly the points where the two maps agree.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy⟩
      have hleft : y.1 = f x :=
        congrArg Subtype.val (congrArg Prod.fst hy)
      have hright : y.1 = g x :=
        congrArg Subtype.val (congrArg Prod.snd hy)
      exact hleft.symm.trans hright
    · intro hx
      refine ⟨⟨f x, ⟨⟨x, rfl⟩, ⟨x, hx.symm⟩⟩⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hx
  have hClosedEqualizerPullback : IsClosed (rangePair ⁻¹' Set.range diagonalMap) :=
    hClosedDiagonalRange.preimage hRangePair
  rwa [hEqualizerEq] at hClosedEqualizerPullback

/-- Helper for Lemma 5.1.21: if the diagonal is closed in the compactly generated product, then
compact-source pullbacks of compact Hausdorff ranges are closed. -/
lemma isClosed_preimage_range_of_isClosedDiagonalCompactlyGeneratedProduct
    (hΔ : IsClosed[compactlyGeneratedProductTopology X X] (diagonal X))
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace S] [CompactSpace T] [T2Space S] [T2Space T]
    {f : S → X} {g : T → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed (f ⁻¹' Set.range g) := by
  let pairMap : S × T → X × X := fun p ↦ (f p.1, g p.2)
  have hPairMapLeft : Continuous fun p : S × T => f p.1 :=
    hf.comp continuous_fst
  have hPairMapRight : Continuous fun p : S × T => g p.2 :=
    hg.comp continuous_snd
  have hPairMap : Continuous pairMap :=
    hPairMapLeft.prodMk hPairMapRight
  have hPairMapOriginal : Continuous[instTopologicalSpaceProd, instTopologicalSpaceProd] pairMap :=
    hPairMap
  have hPairMapCG :
      Continuous[instTopologicalSpaceProd, TopologicalSpace.compactlyGenerated.{u, u} (X × X)]
        pairMap :=
    continuousToCompactlyGeneratedOfContinuousCompHaus
      (Y := X × X) (K := S × T) (t := instTopologicalSpaceProd) (f := pairMap) hPairMapOriginal
  have hΔcg : IsClosed[TopologicalSpace.compactlyGenerated.{u, u} (X × X)] (diagonal X) := by
    -- Normalize the source-facing product topology alias to the canonical k-product owner.
    simpa [compactlyGeneratedProductTopology_def] using hΔ
  have hClosedPullback : IsClosed (pairMap ⁻¹' diagonal X) :=
    (@continuous_iff_isClosed (S × T) (X × X) instTopologicalSpaceProd
        (TopologicalSpace.compactlyGenerated.{u, u} (X × X)) pairMap).mp hPairMapCG
      _ hΔcg
  have hClosedImage : IsClosed (Prod.fst '' (pairMap ⁻¹' diagonal X)) :=
    isClosedMap_fst_of_compactSpace (pairMap ⁻¹' diagonal X) hClosedPullback
  have hImageEq : Prod.fst '' (pairMap ⁻¹' diagonal X) = f ⁻¹' Set.range g := by
    -- Projecting the diagonal pullback records exactly the points of `S` mapping into `range g`.
    ext s
    constructor
    · rintro ⟨⟨s', k⟩, hk, hs⟩
      have hs' : s' = s := hs
      subst hs'
      refine ⟨k, ?_⟩
      simpa [pairMap, mem_diagonal_iff] using hk.symm
    · rintro ⟨k, hk⟩
      refine ⟨(s, k), ?_, rfl⟩
      simpa [pairMap, mem_diagonal_iff] using hk.symm
  simpa [hImageEq] using hClosedImage

end

section

variable {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]

/-- Lemma 5.1.21. If `X` is a k-space, formalized here by `UCompactlyGeneratedSpace.{u} X`, then
`X` is weak Hausdorff if and only if the diagonal `diagonal X` is closed in the compactly
generated product `X × X`. -/
theorem weaklyHausdorffSpace_iff_isClosed_diagonal_compactlyGeneratedProduct :
    WeaklyHausdorffSpace.{u, u} X ↔
      IsClosed[compactlyGeneratedProductTopology X X] (diagonal X) := by
  constructor
  · intro hX
    let _ : WeaklyHausdorffSpace.{u, u} X := hX
    -- Test closedness in the k-product against compact Hausdorff sources.
    rw [compactlyGeneratedProductTopology_def, isClosed_compactlyGenerated_iff_compHausClosed]
    intro S h
    have hfst : Continuous fun s : S => (h s).1 :=
      h.continuous.fst
    have hsnd : Continuous fun s : S => (h s).2 :=
      h.continuous.snd
    -- The diagonal pullback is the equalizer of the two component maps.
    simpa [mem_diagonal_iff] using
      (lemma_5_1_21_isClosed_eqLocus_of_continuous_compHaus (X := X) hfst hsnd)
  · intro hΔ
    refine WeaklyHausdorffSpace.mk ?_
    intro K _ _ _ g hg
    -- Reduce closedness of `range g` to the k-space closedness test against compact Hausdorff maps.
    refine UCompactlyGeneratedSpace.isClosed ?_
    intro S f
    exact
      isClosed_preimage_range_of_isClosedDiagonalCompactlyGeneratedProduct
        (X := X) hΔ f.continuous hg

namespace WeaklyHausdorffSpace

/-- In a k-space, weak Hausdorffness forces the diagonal to be closed in the compactly generated
product. -/
theorem isClosed_diagonal_compactlyGeneratedProduct [WeaklyHausdorffSpace.{u, u} X] :
    IsClosed[compactlyGeneratedProductTopology X X] (diagonal X) :=
  weaklyHausdorffSpace_iff_isClosed_diagonal_compactlyGeneratedProduct.mp inferInstance

end WeaklyHausdorffSpace

/-- In a k-space, diagonal closedness in the compactly generated product implies weak
Hausdorffness. -/
theorem weaklyHausdorffSpace_of_isClosed_diagonal_compactlyGeneratedProduct
    (hΔ : IsClosed[compactlyGeneratedProductTopology X X] (diagonal X)) :
    WeaklyHausdorffSpace.{u, u} X :=
  weaklyHausdorffSpace_iff_isClosed_diagonal_compactlyGeneratedProduct.mpr hΔ

end
