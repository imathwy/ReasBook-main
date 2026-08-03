module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Hausdorff
import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
import Topology_Munkres_2000.Book.Exercise_50_6
import Topology_Munkres_2000.Book.Exercise_50_10

public section

universe u

/-- Helper for Exercise 50.11: a closed embedding into finite-dimensional Euclidean space
gives a finite covering-dimension bound. -/
private lemma finiteCoveringDimension_of_isClosedEmbedding_euclidean
    {X : Type u} [TopologicalSpace X] {N : ℕ}
    {f : X → EuclideanSpace ℝ (Fin N)} (hf : Topology.IsClosedEmbedding f) :
    FiniteCoveringDimension X := by
  -- Bound the closed range by its ambient Euclidean dimension.
  have hrange : HasCoveringDimensionLE (Set.range f) N :=
    closedSubset_euclideanSpace_hasCoveringDimensionLE (Set.range f) hf.isClosed_range
  -- Identify the source with that range and transport the bound back to it.
  exact ⟨N, HasCoveringDimensionLE.homeomorph hf.isEmbedding.toHomeomorph.symm hrange⟩

/-- Helper for Exercise 50.11: a global covering-dimension bound supplies the compact-subspace
bounds required by the Euclidean closed-embedding theorem. -/
private lemma exists_isClosedEmbedding_euclidean_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] {m : ℕ} (hm : HasCoveringDimensionLE X m) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsClosedEmbedding f := by
  -- Compact subsets are closed, so the global bound restricts to every compact subtype.
  exact exists_isClosedEmbedding_euclidean_of_compactDimension_le fun K hK ↦
    hm.closedSubtype hK.isClosed

/-- Exercise 50.11. A space admits a closed embedding into some finite-dimensional real
Euclidean space if and only if it is locally compact, Hausdorff, second countable, and
has finite covering dimension. -/
theorem exists_isClosedEmbedding_euclidean_iff {X : Type u} [TopologicalSpace X] :
    (∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsClosedEmbedding f) ↔
      LocallyCompactSpace X ∧ T2Space X ∧ SecondCountableTopology X ∧
        FiniteCoveringDimension X := by
  constructor
  · rintro ⟨N, f, hf⟩
    -- Pull the ambient separation, countability, and local compactness structures to `X`.
    exact ⟨hf.locallyCompactSpace, hf.isEmbedding.t2Space,
      hf.isEmbedding.secondCountableTopology,
      finiteCoveringDimension_of_isClosedEmbedding_euclidean hf⟩
  · rintro ⟨hlocal, hT2, hsecond, m, hm⟩
    -- Install the structural hypotheses so the fixed-bound embedding theorem applies.
    letI : LocallyCompactSpace X := hlocal
    letI : T2Space X := hT2
    letI : SecondCountableTopology X := hsecond
    obtain ⟨f, hf⟩ := exists_isClosedEmbedding_euclidean_of_hasCoveringDimensionLE hm
    -- Package the explicit Euclidean dimension supplied by that theorem.
    exact ⟨2 * m + 1, f, hf⟩

/-- A locally compact Hausdorff second-countable space of finite covering dimension admits a
closed embedding into some finite-dimensional real Euclidean space. -/
theorem exists_isClosedEmbedding_euclidean_of_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] (h_dim : FiniteCoveringDimension X) :
    ∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsClosedEmbedding f :=
  exists_isClosedEmbedding_euclidean_iff.mpr
    ⟨inferInstance, inferInstance, inferInstance, h_dim⟩
