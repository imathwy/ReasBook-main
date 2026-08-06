import Mathlib.Topology.Separation.CompletelyRegular

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology
open scoped unitInterval

-- Semantic search hits: `t35Space_iff_isEmbedding_stoneCechUnit`, `Function.compactSpace`;
-- local precedent in Chapter 5 uses `T35Space` for the textbook notion "Tychonoff" and
-- `ι → Set.Icc (0 : ℝ) 1` for cubes.

/-- Helper for Problem 5.3.4: the evaluation map into the cube of `I`-valued continuous
functions induces the original topology of a completely regular space. -/
lemma isInducing_continuousMapCubeEval (Y : Type u) [TopologicalSpace Y]
    [CompletelyRegularSpace Y] :
    IsInducing (fun y : Y ↦ fun f : C(Y, I) ↦ f y) := by
  -- The forward inequality is the continuity of every coordinate projection `y ↦ f y`.
  rw [isInducing_iff_nhds]
  intro y
  apply le_antisymm
  · rw [← Filter.map_le_iff_le_comap]
    exact (continuous_pi fun f : C(Y, I) ↦ f.continuous).continuousAt
  · -- Complete regularity gives one coordinate separating `y` from the closed complement of `U`.
    simp_rw [le_nhds_iff, ((nhds_basis_opens _).comap _).mem_iff, and_assoc]
    intro U hyU hU
    obtain ⟨f, hf, hfy, hfU⟩ := CompletelyRegularSpace.completely_regular_isOpen y U hU hyU
    let g : C(Y, I) := ⟨f, hf⟩
    refine ⟨{φ : C(Y, I) → I | φ g ≠ 1}, ?_, ?_, ?_⟩
    · simp [g, hfy]
    · simpa [Set.preimage, g] using isOpen_compl_singleton.preimage (continuous_apply g)
    · intro z hz
      by_contra hzU
      have hz' : f z ≠ 1 := by
        simpa [g] using hz
      exact hz' (hfU hzU)

/-- The evaluation map embeds `StoneCech X` into the cube indexed by its continuous `I`-valued
functions. -/
theorem isEmbedding_stoneCechEvalCube (X : Type u) [TopologicalSpace X] :
    IsEmbedding (fun x : StoneCech X ↦ fun f : C(StoneCech X, I) ↦ f x) := by
  -- `StoneCech X` is Hausdorff, hence T₀, so the inducing map from the helper upgrades to
  -- an embedding.
  exact (isInducing_continuousMapCubeEval (Y := StoneCech X)).isEmbedding

/-- Helper for Problem 5.3.4: a Tychonoff space embeds into the cube of `I`-valued continuous
functions on its Stone-Cech compactification. -/
lemma exists_embedding_in_cube_of_t35Space (X : Type u) [TopologicalSpace X] [T35Space X] :
    ∃ ι : Type u, ∃ f : X → (ι → I), IsEmbedding f := by
  -- Compose the canonical embedding into `StoneCech X` with the evaluation embedding of the
  -- compactification into its function cube.
  refine ⟨C(StoneCech X, I), fun x g ↦ g (stoneCechUnit x), ?_⟩
  simpa [Function.comp] using
    (isEmbedding_stoneCechEvalCube X).comp (isEmbedding_stoneCechUnit (X := X))

/-- Problem 5.3.4: a space is Tychonoff if and only if it admits an embedding into a cube
`ι → Set.Icc (0 : ℝ) 1`. -/
theorem t35Space_iff_exists_embedding_in_cube (X : Type u) [TopologicalSpace X] :
    T35Space X ↔ ∃ ι : Type u, ∃ f : X → (ι → Set.Icc (0 : ℝ) 1), IsEmbedding f := by
  constructor
  · intro hX
    -- For the forward implication, install the Tychonoff structure and use the Stone-Cech
    -- factorization helper.
    letI : T35Space X := hX
    simpa using exists_embedding_in_cube_of_t35Space X
  · rintro ⟨ι, f, hf⟩
    -- The cube is Tychonoff, and `T35Space` pulls back along an embedding.
    exact hf.t35Space
