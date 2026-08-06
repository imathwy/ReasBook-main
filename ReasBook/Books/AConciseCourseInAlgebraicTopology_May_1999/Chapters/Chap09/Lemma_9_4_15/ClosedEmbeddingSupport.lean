import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_2_5
import Mathlib.Topology.Maps.Basic

universe u

open Set CategoryTheory

namespace Lemma9415Support

section

variable {α : Type u} [TopologicalSpace α]

/-- Helper for Lemma 9.4.15: each successor structure map in the inclusion sequence is a closed
embedding once the predecessor is closed in the successor stage. -/
theorem inclusionSequenceStageMap_isClosedEmbedding
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) (i : ℕ) :
    Topology.IsClosedEmbedding (inclusionSequenceStageMap X hX i) := by
  -- The stage map is the subtype inclusion, so the given closed-image hypothesis is exactly the
  -- closed-embedding criterion for `Set.inclusion`.
  simpa [inclusionSequenceStageMap_apply] using
    Topology.IsClosedEmbedding.inclusion (hX (Nat.le_succ i)) (hclosed i)

/-- Helper for Lemma 9.4.15: every forward map in the inclusion diagram is a closed embedding
when each successor map is. -/
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
      -- Extend the closed embedding by one more successor inclusion.
      have hstep : Topology.IsClosedEmbedding (inclusionSequenceStageMap X hX j) :=
        inclusionSequenceStageMap_isClosedEmbedding X hX hclosed j
      rw [← CategoryTheory.homOfLE_comp hij (Nat.le_succ j), Functor.map_comp,
        inclusionSequenceDiagram_map_succ]
      simpa [Function.comp] using hstep.comp ih

/-- Helper for Lemma 9.4.15: the colimit cocone is compatible with any forward stage map. -/
theorem inclusionSequenceColimitHom_naturality_of_le
    (X : ℕ → Set α) (hX : Monotone X) {i j : ℕ} (hij : i ≤ j) :
    (inclusionSequenceDiagram X hX).map (homOfLE hij) ≫ inclusionSequenceColimitHom X j =
      inclusionSequenceColimitHom X i := by
  -- This is the cocone naturality specialized to the forward map `i ⟶ j`.
  simpa [inclusionSequenceColimitCocone_ι_app] using
    (inclusionSequenceColimitCocone X hX).ι.naturality (homOfLE hij)

/-- Helper for Lemma 9.4.15: each stage inclusion into the colimit remembers the ambient point,
so it is injective. -/
theorem inclusionSequenceColimitInclusion_injective
    (X : ℕ → Set α) (i : ℕ) :
    Function.Injective (inclusionSequenceColimitInclusion X i) := by
  -- Equality in the colimit subtype is equality of the underlying points in `α`.
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : inclusionSequenceColimit X ↦ z.1) hxy)

/-- Helper for Lemma 9.4.15: the pullback of the image of a closed subset of one stage along any
other stage inclusion is closed. -/
theorem isClosed_preimage_image_inclusionSequenceColimitInclusion
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) {i : ℕ} {s : Set (X i)}
    (hs : IsClosed s) (j : ℕ) :
    IsClosed ((inclusionSequenceColimitInclusion X j) ⁻¹'
      (inclusionSequenceColimitInclusion X i '' s)) := by
  -- Compare the two stages using the total order on `ℕ`, then normalize the pullback.
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

/-- Helper for Lemma 9.4.15: each stage inclusion into the sequential colimit is a closed
embedding. -/
theorem inclusionSequenceColimitInclusion_isClosedEmbedding
    (X : ℕ → Set α) (hX : Monotone X)
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i}) (i : ℕ) :
    Topology.IsClosedEmbedding (inclusionSequenceColimitInclusion X i) := by
  -- Use the closed-set criterion for the final-topology colimit together with the pullback lemma.
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (inclusionSequenceColimitHom X i).hom.continuous
      (inclusionSequenceColimitInclusion_injective X i) ?_
  intro s hs
  rw [isClosed_inclusionSequenceColimit_iff hX]
  intro j
  exact isClosed_preimage_image_inclusionSequenceColimitInclusion X hX hclosed hs j

end

end Lemma9415Support
