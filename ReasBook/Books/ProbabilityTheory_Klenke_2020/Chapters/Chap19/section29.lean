import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_19_29 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe v w

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/- `source-facing`: this file owns the textbook recurrence statement for simple random walks on
subgraphs of the square lattice.
`core/canonical`: recurrence is expressed through `IsRecurrentMarkovChain`, the discrete kernel
owner `discreteMatrixKernel`, the graph-walk owner `IsSimpleRandomWalk`, the conductance owner
`conductanceTransitionMatrix`, and the existing lattice-graph owner `latticeGraph 2`.
`bridge/view`: the full square-lattice walk is used only through the canonical conductance
normalization of the unit edge weights `simpleGraphWeights (latticeGraph 2)` in order to feed the
Chapter 17 recurrence theorem into the Chapter 19 subgraph monotonicity theorem. -/

-- Proof sketch: each square-lattice vertex has exactly four nearest neighbors, so the row sum is
-- `1`, and the conductance-normalized unit-edge walk is precisely the simple random walk on
-- `latticeGraph 2`.
private theorem squareLatticeKernel_isSimpleRandomWalk :
    IsSimpleRandomWalk
      (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
      (latticeGraph 2) := sorry

-- Proof sketch: adjacency in `latticeGraph 2` depends only on the increment `y - x`, so the
-- normalized unit-edge walk does as well.
private theorem squareLatticeKernel_translationInvariant :
    IsTranslationInvariantStepMatrix
      (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) := sorry

-- Proof sketch: from the origin, the four nearest-neighbor moves in the coordinate directions
-- each occur with probability `1 / 4`, matching `symmetricSimpleRandomWalkStepPMF 2`.
private theorem squareLatticeKernel_row_zero (y : LatticePoint 2) :
    conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)) 0 y =
      symmetricSimpleRandomWalkStepPMF 2 y := sorry

private theorem exists_recurrent_squareLattice_realization :
    ∃ (Ω : Type), ∃ _ : MeasurableSpace Ω,
        ∃ P : LatticePoint 2 → ProbabilityMeasure Ω,
          ∃ X : ℕ → Ω → LatticePoint 2,
            IsMarkovProcessRealization
              (fun n ↦
                discreteMatrixKernel
                  (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) P X ∧
            IsRecurrentMarkovChain P X := by
  letI :
      IsMarkovKernel
        (discreteMatrixKernel
          (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))) :=
    discreteMatrixKernel_isMarkovKernel
      (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
      (IsRandomWalkWithWeights.isStochasticMatrix squareLatticeKernel_isSimpleRandomWalk)
  letI :
      IsMarkovSemigroup
        (fun n : ℕ ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) :=
    isMarkovSemigroup_kernelPowers
      (discreteMatrixKernel
        (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))))
  rcases exists_markovProcessRealization_of_markovSemigroup
      (fun n ↦
        discreteMatrixKernel
          (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) with
    ⟨Ω, mΩ, X, P, hreal⟩
  letI :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) P X :=
    hreal
  refine ⟨Ω, mΩ, P, X, hreal, ?_⟩
  exact
    (symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
      2 P X (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
      squareLatticeKernel_translationInvariant
      squareLatticeKernel_row_zero).2 (by simp)

private theorem recurrent_of_squareLattice_subgraph
    {Ω : Type v} {Ω' : Type w} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (H : (latticeGraph 2).Subgraph)
    (p₀ : LatticePoint 2 → LatticePoint 2 → ℝ≥0∞)
    (p : H.verts → H.verts → ℝ≥0∞)
    (P₀ : LatticePoint 2 → ProbabilityMeasure Ω') (X₀ : ℕ → Ω' → LatticePoint 2)
    (P : H.verts → ProbabilityMeasure Ω) (X : ℕ → Ω → H.verts)
    [IsSimpleRandomWalk p₀ (latticeGraph 2)]
    [IsSimpleRandomWalk p H.coe]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p₀ ^ n) P₀ X₀]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hrec₀ : IsRecurrentMarkovChain P₀ X₀) :
    IsRecurrentMarkovChain P X := by
  have hsub : H.coe ≤ SimpleGraph.induce H.verts (latticeGraph 2) := by
    intro x y hxy
    exact H.coe_adj_sub x y hxy
  exact
    @simpleRandomWalk_recurrent_of_subgraph
      (LatticePoint 2) inferInstance inferInstance Ω' inferInstance Ω inferInstance
      (latticeGraph 2) H.verts inferInstance H.coe p₀ p P₀ X₀ P X
      inferInstance inferInstance inferInstance inferInstance hsub hrec₀

section

variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: realize the full square-lattice walk once using the canonical conductance
-- normalization of `simpleGraphWeights (latticeGraph 2)`, apply the Chapter 17 recurrence theorem
-- in dimension `2`, and then pass to the subgraph `H` with Theorem 19.30.
/-- Example 19.29: every simple random walk on a subgraph `H` of the square lattice
`latticeGraph 2` is recurrent. This strengthens the textbook connected-subgraph statement,
since the recurrence transfer through Theorem 19.30 does not use connectedness. The textbook
proof uses Rayleigh's monotonicity principle to compare the effective resistance from `0` to `∞`
in `H` with the effective resistance in the full square lattice, which is infinite. -/
theorem simpleRandomWalk_on_subgraph_of_square_lattice_isRecurrent
    (H : (latticeGraph 2).Subgraph)
    (p : H.verts → H.verts → ℝ≥0∞)
    (P : H.verts → ProbabilityMeasure Ω) (X : ℕ → Ω → H.verts)
    [IsSimpleRandomWalk p H.coe]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X] :
    IsRecurrentMarkovChain P X := by
  letI :
      IsSimpleRandomWalk
        (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
        (latticeGraph 2) :=
    squareLatticeKernel_isSimpleRandomWalk
  rcases exists_recurrent_squareLattice_realization with ⟨Ω', mΩ', P', X', hreal', hrec'⟩
  letI : MeasurableSpace Ω' := mΩ'
  letI :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) P' X' :=
    hreal'
  exact
    recurrent_of_squareLattice_subgraph
      H (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) p P' X' P X hrec'

end

end ProbabilityTheory
