import Mathlib
import Nesterov.Chap05.Definition_5_3_4_1
import Nesterov.Chap05.Definition_5_4_4_4
import Nesterov.Chap05.Definition_5_4_4_5
import Nesterov.Chap05.Definition_5_4_4_6
import Nesterov.Chap05.Theorem_5_3_3
import Nesterov.Chap05.Theorem_5_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {m n : ℕ}

/- This item lies in the semidefinite short-step path-following domain.

Sampled owner-style declarations:
* `SemidefiniteOptimizationProblem` and `SemidefiniteOptimizationProblem.feasibleSet` in
  `Definition_5_4_4_4`, the chapter owner for SDP data, feasible matrices, and the trace
  objective `trace (C X)`;
* `SemidefiniteOptimizationProblem.strictFeasibleSet` and `logDetBarrierAmbient` in
  `Definition_5_4_4_5`, the source-facing strict-feasibility owner and the ambient bridge for
  the textbook barrier formula `X ↦ -log det X`;
* `realSymmetricMatrixConstraintMap` and
  `realSymmetricMatrixAssociatedAffineSubspace` in `Definition_5_4_4_6`, the canonical owner
  bridge from the SDP Frobenius equalities to the intrinsic affine constraint space;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` in
  `Theorem_5_4_4_3`, the chapter owner theorem for the `n`-self-concordant barrier on
  `𝕊ⁿ₊₊`;
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith.comp_affineMap` in `Theorem_5_3_3`, the canonical affine
  pullback owner theorem for restricting a barrier to an affine slice.

Best owner abstraction:
* source-facing: the SDP owner `SemidefiniteOptimizationProblem n m` together with its explicit
  strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the canonical affine bridge from the constraint kernel
  `(realSymmetricMatrixConstraintMap problem.constraintMatrices).ker` to the affine slice
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`,
  together with the affine pullback of `logDetBarrierAmbient n`.

Primitive data:
* `problem : SemidefiniteOptimizationProblem n m`.

Derived API:
* the strict feasible owner `problem.strictFeasibleSet`;
* the affine constraint space
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`;
* the public affine bridge from
  `(realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs).direction`
  back to the affine slice;
* the common short-step existence package theorem and its source-facing projections.

Source/core/bridge triage:
* source-facing: the SDP owner `problem` and its strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the affine translation from `𝓛.direction` to the affine slice `𝓛`, together
  with its induced strict domain and pulled-back `logDetBarrierAmbient n`.

This refinement removes the mathematically incorrect ambient-domain barrier hypothesis on
`problem.strictFeasibleSet`, which is generally not open in `𝕊^n`. The theorem now runs the
short-step scheme on the direction space of the canonical affine slice
`realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`, and the
required affine translation by a strict feasible base point is exposed as a public bridge on the
SDP owner. -/

local notation "SymmMat" => 𝕊^n

namespace SemidefiniteOptimizationProblem

instance affineSliceLogDetBarrier.instIsSelfConcordantBarrierOnWith
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    IsSelfConcordantBarrierOnWith
      (problem.affineSliceStrictDomain xRef)
      n
      (problem.affineSliceLogDetBarrier xRef) := by
  have hbarrier :
      IsSelfConcordantBarrierOnWith
        (𝕊^n₊₊ : Set SymmMat)
        n
        (logDetBarrierAmbient n) := by
    simpa using negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone n
  simpa [affineSliceStrictDomain, affineSliceLogDetBarrier] using
    hbarrier.comp_affineMap (problem.affineSliceMap xRef)

theorem affineSliceMap_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceMap xRef Δ ∈ problem.affineSlice := by
  have hxRef_strict : (xRef : SymmMat) ∈ problem.strictFeasibleSet := xRef.2
  change
    (xRef : SymmMat) ∈ (𝕊^n₊₊ : Set SymmMat) ∩ (problem.affineSlice : Set SymmMat) at hxRef_strict
  rw [Set.mem_inter_iff] at hxRef_strict
  have hxRef : (xRef : SymmMat) ∈ problem.affineSlice := by
    exact hxRef_strict.2
  simpa using AffineSubspace.vadd_mem_of_mem_direction Δ.2 hxRef

theorem affineSliceMap_mem_strictFeasibleSet_of_mem_affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    {Δ : problem.affineSlice.direction}
    (hΔ : Δ ∈ problem.affineSliceStrictDomain xRef) :
    problem.affineSliceMap xRef Δ ∈ problem.strictFeasibleSet := by
  rw [strictFeasibleSet, Set.mem_inter_iff]
  refine ⟨?_, problem.affineSliceMap_mem_affineSlice xRef Δ⟩
  simpa [affineSliceStrictDomain] using hΔ

theorem affineSliceMap_mem_feasibleSet_of_mem_affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    {Δ : problem.affineSlice.direction}
    (hΔ : Δ ∈ problem.affineSliceStrictDomain xRef) :
    problem.affineSliceMap xRef Δ ∈ problem.feasibleSet := by
  have hstrict :
      problem.affineSliceMap xRef Δ ∈ problem.strictFeasibleSet :=
    problem.affineSliceMap_mem_strictFeasibleSet_of_mem_affineSliceStrictDomain xRef hΔ
  rcases (problem.mem_strictFeasibleSet_iff _).1 hstrict with ⟨hpd, hEq⟩
  rw [problem.mem_feasibleSet_iff]
  refine ⟨?_, hEq⟩
  rw [mem_positiveSemidefiniteCone_iff]
  exact (strictPositiveSemidefiniteCone_posDef ⟨_, hpd⟩).posSemidef

end SemidefiniteOptimizationProblem

section

variable (problem : SemidefiniteOptimizationProblem n m)
local notation "𝓕°" => problem.strictFeasibleSet

variable {ε : ℝ}

/-- Theorem 5.4.4.4 (1): if `problem.strictFeasibleSet` is nonempty, `xOpt` is optimal for the
SDP owner `problem` on `problem.feasibleSet`, and `ε > 0`, then there exist common short-step
path-following data for the SDP affine-slice barrier: a strict feasible base point `X̄`,
parameters `β`, `γ`, an iteration-bound constant `C₀`, a strict starting point in the direction
space, and a barrier path-following scheme whose stopping iterate is strictly feasible (hence
feasible), `ε`-accurate relative to `xOpt`, and whose stopping index satisfies the stated
`O(√n log (n / ε))` bound. -/
theorem exists_semidefinitePathFollowingScheme
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : NNRealˣ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                β < 1 / 2 ∧
                  0 < γ ∧
                  problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈
                    problem.strictFeasibleSet ∧
                  problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.feasibleSet ∧
                  problem (problem.affineSliceMap xRef (scheme scheme.stopIndex)) ≤
                    problem (xOpt : SymmMat) + ε ∧
                  scheme.stopIndex ≤
                    ⌈((C₀ : NNReal) : ℝ) * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊ := sorry

-- Proof sketch: extract the positive constant controlling the iteration bound from the core
-- short-step existence theorem.
/-- Theorem 5.4.4.4 (2): under the same hypotheses, there exists a positive constant `C₀`
appearing in the short-step complexity estimate for the semidefinite path-following scheme. -/
theorem exists_semidefinitePathFollowingScheme_iteration_constant_pos
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : ℝ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ _scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                0 < C₀ := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, -, -, -, -⟩
  refine ⟨xRef, β, γ, ((C₀ : NNReal) : ℝ), z0, scheme, ?_⟩
  have hC₀ : (0 : NNReal) < (C₀ : NNReal) := by
    exact pos_iff_ne_zero.mpr (Units.ne_zero C₀)
  exact_mod_cast hC₀

-- Proof sketch: extract the stopping-index estimate from the core short-step existence theorem.
/-- Theorem 5.4.4.4 (3): under the same hypotheses, there exists a semidefinite path-following
scheme whose stopping index is bounded by `O(√n log (n / ε))`. This bound depends on the barrier
parameter `n`, not on the ambient dimension `dim (𝕊ⁿ) = n (n + 1) / 2`. -/
theorem exists_semidefinitePathFollowingScheme_stopIndex_le_iteration_bound
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : ℝ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                scheme.stopIndex ≤
                  ⌈C₀ * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊ := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, -, -, -, hscheme⟩
  exact ⟨xRef, β, γ, ((C₀ : NNReal) : ℝ), z0, scheme, by simpa using hscheme⟩

-- Proof sketch: extract the strict-feasibility, feasibility, and owner-level `ε`-accuracy
-- clauses from the common short-step existence theorem.
/-- Theorem 5.4.4.4 (4): under the same hypotheses, there exists a semidefinite path-following
scheme whose stopping iterate is strictly feasible (hence feasible) and whose SDP objective value
is within `ε` of the optimal reference value `problem (xOpt : SymmMat)`. -/
theorem exists_semidefinitePathFollowingScheme_stop_trace_le_add_epsilon
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ z0 : problem.affineSliceStrictDomain xRef,
            ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
              problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.strictFeasibleSet ∧
                problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.feasibleSet ∧
                problem (problem.affineSliceMap xRef (scheme scheme.stopIndex)) ≤
                  problem (xOpt : SymmMat) + ε := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, hstrictStop, hfeasStop, hgap, -⟩
  exact ⟨xRef, β, γ, z0, scheme, hstrictStop, hfeasStop, hgap⟩

end

end
