import LecturesConvexOptimization_Nesterov_2018.Chap07.Algorithm_7_6
import LecturesConvexOptimization_Nesterov_2018.Chap07.Proposition_7_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped BigOperators Topology

variable {m n : ℕ}

/- Proposition New 2 lies in Chapter 7's sampled-prefix radius / subsequential compactness
domain.

Sampled owner-style declarations:
- `CentralSymmetryRoundingAlgorithm.selectedRadius` and the coercion to its inverse-matrix
  sequence in `Chap07/Algorithm_7_6`, the Chapter 7 owner of Algorithm 7.6's sampled radii and
  matrices;
- `bestRadiusUpTo` and `bestRadiusUpTo_le` in `Chap03/Theorem_3_2_10`, the existing chapter owner
  for the sampled prefix minimum `min_{0 ≤ k ≤ N} r_k`;
- `sqrt_div_bestRadiusUpTo_ge_one_sub_sqrt_log_bound` and
  `tendsto_bestRadiusUpTo_of_sqrt_le` in `Chap07/Proposition_7_10`, the existing owner-level
  rate and convergence theorems for that sampled minimum;
- `IsCompact.tendsto_subseq` and `MapClusterPt.tendsto_subseq` in mathlib, the canonical
  compactness and cluster-point bridges to convergent subsequences.

Best owner abstraction:
- source-facing: Proposition New 2's rate, convergence, and compactness conclusions for the
  selected radii and inverse matrices attached to Algorithm 7.6;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `bestRadiusUpTo`, and `MapClusterPt`;
- bridge/view: the direct subsequence and cluster-point data extracted from compactness.

Primitive data:
- the Algorithm 7.6 owner `algorithm`;
- the squared-deviation bound, the lower trace bound, compactness of `Set.range algorithm`, and
  the selected-radius sequence attached to that owner.

Derived API:
- the selected-radius sequence `algorithm.selectedRadius`;
- the sampled minimum `bestRadiusUpTo algorithm.selectedRadius N`;
- its lower bound from the trace hypothesis;
- the direct subsequence and cluster-point data produced from compactness.

Source/core/bridge triage:
- source-facing: the three proposition statements below;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `bestRadiusUpTo`, and `MapClusterPt`;
- bridge/view: the explicit convergent subsequence and the selected-radius limit along it.

The previous version erased the Algorithm 7.6 owner and duplicated the chapter owner
`bestRadiusUpTo` under `partialMinRadius`. This refinement rewrites the file directly on
`CentralSymmetryRoundingAlgorithm.selectedRadius` and `bestRadiusUpTo`, keeping explicit
subsequence data only as the source-facing bridge.
-/

/-- Proposition New  2: if the selected radii `r_k = algorithm.selectedRadius k` attached to
Algorithm 7.6 satisfy the summation bound
`∑_{k=0}^N (1 - √n / r_k)^2 ≤ 2 n log R`
and the trace lower bound `√n ≤ r_k`, then the sampled minimum
`r_N^* = bestRadiusUpTo algorithm.selectedRadius N`
satisfies
`√n / r_N^* ≥ 1 - √(((2 n) / (N + 1)) log R)`. -/
-- Proof sketch: apply the owner-level estimate
-- `sqrt_div_bestRadiusUpTo_ge_one_sub_sqrt_log_bound` from Proposition 7.10 to the selected-radius
-- sequence `algorithm.selectedRadius`, using the trace lower bound to supply the needed
-- positivity of that sequence.
theorem sqrt_div_bestRadiusUpTo_selectedRadius_ge_one_sub_sqrt_log_bound
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R)
    (N : ℕ) :
    Real.sqrt (n : ℝ) / bestRadiusUpTo algorithm.selectedRadius N ≥
      1 - Real.sqrt (((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R) := sorry

/-- Under the same summation and trace lower bounds, the sampled minima
`r_N^* = bestRadiusUpTo algorithm.selectedRadius N` converge to `√n`. -/
-- Proof sketch: apply `tendsto_bestRadiusUpTo_of_sqrt_le` from Proposition 7.10 to the selected
-- radius sequence `algorithm.selectedRadius`; the hypothesis `htrace_bound` yields the lower bound
-- `√n ≤ bestRadiusUpTo algorithm.selectedRadius N`.
theorem tendsto_bestRadiusUpTo_selectedRadius
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R) :
    Tendsto
      (fun N : ℕ ↦ bestRadiusUpTo algorithm.selectedRadius N)
      atTop
      (𝓝 (Real.sqrt (n : ℝ))) := sorry

/-- If the inverse matrices attached to Algorithm 7.6 form a compact set, then some subsequence
of inverse matrices converges, and along that same subsequence the selected radii converge to
`√n`. -/
-- Proof sketch: use `tendsto_bestRadiusUpTo_selectedRadius` to obtain
-- `bestRadiusUpTo algorithm.selectedRadius N → √n`, choose indices whose selected radii are
-- asymptotically close to those sampled minima, extract a convergent subsequence of the matrix
-- sequence from compactness of `Set.range algorithm`, and pass to the same subsequence on the
-- selected radii.
theorem exists_subseq_tendsto_selectedRadius_sqrt_of_compact_range
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R)
    (hcompact : IsCompact (Set.range algorithm)) :
    ∃ Gstar : Matrix (Fin n) (Fin n) ℝ,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto (algorithm ∘ φ) atTop (𝓝 Gstar) ∧
            Tendsto (algorithm.selectedRadius ∘ φ) atTop (𝓝 (Real.sqrt (n : ℝ))) := sorry

end
