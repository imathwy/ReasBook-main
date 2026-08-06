import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_8
import Mathlib.Topology.Maps.Basic

universe u

open Set CategoryTheory

-- Semantic search hits: `uCompactlyGeneratedSpace_of_isClosed`,
-- `compactlyGeneratedSpace_of_isClosed`; local precedent: the colimit owner
-- `inclusionSequenceColimit` and its closed-set criterion
-- `isClosed_inclusionSequenceColimit_iff` from `Construction 5.2.5`.

section

variable {α : Type u} [TopologicalSpace α]

/-- Under the closed-image hypothesis of Proposition 5.2.6, each successor structure map
`X i ↪ X (i + 1)` is a closed embedding. -/
theorem inclusionSequenceStageMap_isClosedEmbedding
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) (i : ℕ) :
    Topology.IsClosedEmbedding (inclusionSequenceStageMap X hX i) := by
  simpa [inclusionSequenceStageMap_apply] using
    Topology.IsClosedEmbedding.inclusion (hX (Nat.le_succ i)) (hclosed i)

/-- Helper for Proposition 5.2.6: every forward map in the sequential diagram is a closed
embedding once each successor inclusion has closed image. -/
theorem inclusionSequenceDiagramMap_isClosedEmbedding
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) {i j : ℕ} (hij : i ≤ j) :
    Topology.IsClosedEmbedding ((inclusionSequenceDiagram X hX).map (homOfLE hij)) := by
  -- Compose the successor closed embeddings along the chain `i ≤ j`.
  induction j, hij using Nat.le_induction with
  | base =>
      simpa using
        (Topology.IsClosedEmbedding.id : Topology.IsClosedEmbedding (id : X i → X i))
  | succ j hij ih =>
      -- Extend the closed embedding by the next closed successor inclusion.
      have hstep : Topology.IsClosedEmbedding (inclusionSequenceStageMap X hX j) :=
        inclusionSequenceStageMap_isClosedEmbedding X hX hclosed j
      rw [← CategoryTheory.homOfLE_comp hij (Nat.le_succ j), Functor.map_comp,
        inclusionSequenceDiagram_map_succ]
      simpa [Function.comp] using hstep.comp ih

/-- Helper for Proposition 5.2.6: the colimit cocone is compatible with any forward stage map
`X i ⟶ X j`. -/
theorem inclusionSequenceColimitHom_naturality_of_le
    (X : ℕ → Set α) (hX : Monotone X) {i j : ℕ} (hij : i ≤ j) :
    (inclusionSequenceDiagram X hX).map (homOfLE hij) ≫ inclusionSequenceColimitHom X j =
      inclusionSequenceColimitHom X i := by
  -- Read the compatibility from the naturality of the colimit cocone.
  simpa [inclusionSequenceColimitCocone_ι_app] using
    (inclusionSequenceColimitCocone X hX).ι.naturality (homOfLE hij)

/-- Helper for Proposition 5.2.6: each stage inclusion into the union colimit is injective on the
underlying points. -/
theorem inclusionSequenceColimitInclusion_injective
    (X : ℕ → Set α) (i : ℕ) :
    Function.Injective (inclusionSequenceColimitInclusion X i) := by
  -- Equality in the colimit subtype remembers the ambient point in `α`.
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : inclusionSequenceColimit X ↦ z.1) hxy)

/-- Helper for Proposition 5.2.6: the pullback of the image of a closed stage subset along any
other stage inclusion is closed. -/
theorem isClosed_preimage_image_inclusionSequenceColimitInclusion
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) {i : ℕ} {s : Set (X i)}
    (hs : IsClosed s) (j : ℕ) :
    IsClosed ((inclusionSequenceColimitInclusion X j) ⁻¹'
      (inclusionSequenceColimitInclusion X i '' s)) := by
  -- Normalize the pullback by comparing the two stages in the total order on `ℕ`.
  rcases Nat.le_total i j with hij | hji
  · let f : X i → X j := (inclusionSequenceDiagram X hX).map (homOfLE hij)
    have hf : Topology.IsClosedEmbedding f :=
      inclusionSequenceDiagramMap_isClosedEmbedding X hX hclosed hij
    have hcompat :
        ∀ x : X i, inclusionSequenceColimitInclusion X j (f x) =
          inclusionSequenceColimitInclusion X i x := by
      intro x
      -- Evaluate cocone naturality at the chosen point of `X i`.
      exact congrArg (fun m ↦ m x) (inclusionSequenceColimitHom_naturality_of_le X hX hij)
    have hset :
        (inclusionSequenceColimitInclusion X j) ⁻¹'
            (inclusionSequenceColimitInclusion X i '' s) =
          f '' s := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hyx⟩
        refine ⟨y, hy, ?_⟩
        apply inclusionSequenceColimitInclusion_injective X j
        exact (hcompat y).trans hyx
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, (hcompat y).symm⟩
    -- In the forward direction the pullback is the image of `s` under a closed embedding.
    rw [hset]
    exact hf.isClosedMap s hs
  · let f : X j → X i := (inclusionSequenceDiagram X hX).map (homOfLE hji)
    have hf : Topology.IsClosedEmbedding f :=
      inclusionSequenceDiagramMap_isClosedEmbedding X hX hclosed hji
    have hcompat :
        ∀ x : X j, inclusionSequenceColimitInclusion X i (f x) =
          inclusionSequenceColimitInclusion X j x := by
      intro x
      -- Evaluate cocone naturality at the chosen point of `X j`.
      exact congrArg (fun m ↦ m x) (inclusionSequenceColimitHom_naturality_of_le X hX hji)
    have hset :
        (inclusionSequenceColimitInclusion X j) ⁻¹'
            (inclusionSequenceColimitInclusion X i '' s) =
          f ⁻¹' s := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hyx⟩
        have hfx : f x = y := by
          apply inclusionSequenceColimitInclusion_injective X i
          exact (hcompat x).trans hyx.symm
        simpa [hfx] using hy
      · intro hx
        exact ⟨f x, hx, hcompat x⟩
    -- In the backward direction the pullback is an ordinary preimage of the closed set `s`.
    rw [hset]
    exact hs.preimage hf.continuous

/-- Helper for Proposition 5.2.6: every stage inclusion into the sequential colimit is a closed
embedding. -/
theorem inclusionSequenceColimitInclusion_isClosedEmbedding
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) (i : ℕ) :
    Topology.IsClosedEmbedding (inclusionSequenceColimitInclusion X i) := by
  -- Use the closed-set criterion for the colimit to show the stage inclusion is a closed map.
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (inclusionSequenceColimitHom X i).hom.continuous
      (inclusionSequenceColimitInclusion_injective X i) ?_
  intro s hs
  rw [isClosed_inclusionSequenceColimit_iff hX]
  intro j
  exact isClosed_preimage_image_inclusionSequenceColimitInclusion X hX hclosed hs j

/-- Helper for Proposition 5.2.6: the range of a continuous map from a compact Hausdorff source
into the sequential colimit is closed. -/
theorem isClosed_range_compactMap_to_inclusionSequenceColimit
    (X : ℕ → Set α) (hX : Monotone X) (hwh : ∀ i, WeaklyHausdorffSpace.{u, u} (X i))
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) {K : Type u}
    [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → inclusionSequenceColimit X)
    (hg : Continuous g) :
    IsClosed (Set.range g) := by
  -- Check the weak Hausdorff range condition stagewise using the closed-set criterion.
  rw [isClosed_inclusionSequenceColimit_iff hX]
  intro i
  let hi : Topology.IsClosedEmbedding (inclusionSequenceColimitInclusion X i) :=
    inclusionSequenceColimitInclusion_isClosedEmbedding X hX hclosed i
  have hcompactRange : IsCompact (Set.range g) := isCompact_range hg
  have hcompactPreimage :
      IsCompact ((inclusionSequenceColimitInclusion X i) ⁻¹' Set.range g) :=
    hi.isCompact_preimage hcompactRange
  let _ : WeaklyHausdorffSpace.{u, u} (X i) := hwh i
  -- Compact subsets of a weak Hausdorff stage are closed.
  exact IsCompact.isClosed_of_weaklyHausdorff hcompactPreimage

/-- The sequential colimit from Construction 5.2.5 is a `k`-space under the hypotheses of
Proposition 5.2.6. This is the reusable `UCompactlyGeneratedSpace` layer of the result. -/
instance inclusionSequenceColimit_uCompactlyGeneratedSpace (X : ℕ → Set α) (hX : Monotone X)
    (hcg : ∀ i, UCompactlyGeneratedSpace.{u} (X i)) :
    UCompactlyGeneratedSpace.{u} (inclusionSequenceColimit X) := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
  rw [isClosed_inclusionSequenceColimit_iff hX]
  intro i
  let _ : UCompactlyGeneratedSpace.{u} (X i) := hcg i
  refine UCompactlyGeneratedSpace.isClosed fun K f ↦ ?_
  simpa [Set.preimage_preimage, Function.comp, inclusionSequenceColimitInclusion] using
    hs K
      ⟨inclusionSequenceColimitInclusion X i ∘ f,
        (inclusionSequenceColimitHom X i).hom.continuous.comp f.continuous⟩

/-- Proposition 5.2.6. The final topology union `inclusionSequenceColimit X` is weak Hausdorff
when the stages are compactly generated weak Hausdorff and each successor inclusion has closed
image. This isolates the weak Hausdorff bridge needed to recover the textbook compactly generated
owner. -/
instance inclusionSequenceColimit_weaklyHausdorffSpace_of_isClosed
    (X : ℕ → Set α) (hX : Monotone X) (hwh : ∀ i, WeaklyHausdorffSpace.{u, u} (X i))
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) :
    WeaklyHausdorffSpace.{u, u} (inclusionSequenceColimit X) := by
  refine ⟨?_⟩
  intro K _ _ _ g hg
  -- Apply the stagewise closed-range lemma to the compact Hausdorff test map `g`.
  exact isClosed_range_compactMap_to_inclusionSequenceColimit X hX hwh hclosed g hg

/-- Proposition 5.2.6. Formalized using the explicit sequential-union colimit
`inclusionSequenceColimit X` from Construction 5.2.5: if each stage `X i` is compactly generated
in the textbook sense and each successor inclusion `X i ↪ X (i + 1)` has closed image, then the
colimit `colim X_i`, realized as `inclusionSequenceColimit X`, is compactly generated. -/
instance inclusionSequenceColimit_compactlyGeneratedWeakHausdorffSpace_of_isClosed
    (X : ℕ → Set α) (hX : Monotone X)
    (hcg : ∀ i, CompactlyGeneratedWeakHausdorffSpace.{u, u} (X i))
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (inclusionSequenceColimit X) := by
  let _ : UCompactlyGeneratedSpace.{u} (inclusionSequenceColimit X) :=
    inclusionSequenceColimit_uCompactlyGeneratedSpace X hX
      (fun i ↦ (hcg i).toUCompactlyGeneratedSpace)
  let _ : WeaklyHausdorffSpace.{u, u} (inclusionSequenceColimit X) :=
    inclusionSequenceColimit_weaklyHausdorffSpace_of_isClosed X hX
      (fun i ↦ (hcg i).toWeaklyHausdorffSpace) hclosed
  infer_instance

end
