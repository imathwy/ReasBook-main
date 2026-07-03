import Mathlib
import Nesterov.Chap05.Definition_5_0_20
import Nesterov.Chap05.Definition_5_3_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The explicit logarithmic iteration bound obtained from the geometric lower estimate on the
path parameters in the proof of Theorem `5.3.11`. -/
abbrev barrierPathFollowingTerminationBound
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) : ℝ :=
  1 +
    ((β + Real.sqrt (ν : ℝ)) / γ) *
      Real.log
        (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) * referenceObjectiveNorm) /
          (γ * (1 - 2 * β)))

-- Proof sketch: unfold `barrierPathFollowingTerminationBound`.
/-- Expanding `barrierPathFollowingTerminationBound ν β γ ε h` gives the logarithmic complexity
expression obtained by solving the geometric lower bound for `tₖ` against the stopping threshold
`(5.3.29)`. -/
theorem barrierPathFollowingTerminationBound_def
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) :
    barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm =
      1 +
        ((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) *
                referenceObjectiveNorm) /
              (γ * (1 - 2 * β))) := sorry

-- Proof sketch: use the geometric lower bound `hgrowth` for the path parameters `tₖ` together
-- with the first-hit conditions `hcontinue` and `hstop` to show that the threshold `(5.3.29)` is
-- reached by the stated natural-ceiling index. For the accuracy claim, apply the objective-gap
-- estimate from Theorem `5.3.10` at the stopping iterate `x_N`, using the residual-centering
-- hypothesis `happrox_stop` and the threshold inequality `hstop`.
/-- Theorem 5.3.11: if a path-following sequence `(tₖ, xₖ)` for a `ν`-self-concordant barrier has
the geometric lower bound coming from the analytic center `x_F^*`, and if `N` is the first index
at which the stopping threshold `(5.3.29)` is reached while `x_N` is still `β`-centered, then
`N` is bounded by a logarithmic complexity estimate of order `O(√ν log (‖c‖*_{x_F^*} / ε))`;
moreover, the stopping iterate satisfies `⟪c, x_N⟫ - c^* ≤ ε`. -/
theorem pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) {β γ ε : ℝ}
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    (t : ℕ → ℝ) (x : ℕ → E)
    (mem_dom : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (hβ_half : β < 1 / 2)
    (hγ : 0 < γ)
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex →
        t k < barrierPathFollowingStoppingThreshold ν β ε)
    (hstop :
      barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xStar : E)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
                  hxStarH
                  ((InnerProductSpace.toDual ℝ E) c)) *
            (1 + γ / (β + Real.sqrt (ν : ℝ))) ^ (k - 1) ≤
          t k)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_dom stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    stopIndex ≤
        ⌈barrierPathFollowingTerminationBound ν β γ ε
          (HessianDualLocalNorm.ofDetNeZero F (xStar : E)
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
            ((InnerProductSpace.toDual ℝ E) c))⌉₊ ∧
      inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤ ε := sorry

end
