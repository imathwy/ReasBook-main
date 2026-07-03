import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_26_19 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

private abbrev signInitialLaw : Measure (Fin 1 → ℝ) :=
  Measure.dirac (oneDimensionalState (0 : ℝ))

variable
    (L : GeneralizedWeakSDESolution
      signInitialLaw
      (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
      (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))))

-- Proof sketch: negation preserves continuity of sample paths, adaptation, and the Dirac initial
-- law at `0`; for the sign SDE, oddness of the diffusion coefficient and vanishing drift show that
-- the negated state process again satisfies the same generalized-diffusion relation.
/-- The pathwise negation of the state process of a sign-SDE weak solution is again adapted to the
same filtration. -/
theorem WeakSDESolution.negateSignState_adapted :
    Adapted L.ℱ (fun t ω ↦ -(L ω t)) := sorry

-- Proof sketch: the initial law of `L` is `δ₀`, and negation fixes the origin, so the negated
-- initial state still has law `δ₀`.
/-- The negated state process of a sign-SDE weak solution has the same Dirac initial law at `0`. -/
theorem WeakSDESolution.negateSignState_initialLaw :
    HasLaw (fun ω ↦ (-L ω) 0) signInitialLaw L.μ := sorry

-- Proof sketch: starting from the generalized-diffusion decomposition for `L`, negate the state
-- process and use that the sign diffusion coefficient is odd while the drift coefficient vanishes
-- to obtain the same sign-SDE relation for `-X`.
/-- The pathwise-negated state process of a sign-SDE weak solution again satisfies the same SDE. -/
theorem WeakSDESolution.negateSignState_solvesSDE :
    SolvesGeneralizedSDE
      (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
      (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ)))
      L.ℱ L.μ (fun ω ↦ -L ω) L.W := sorry

/-- The weak solution obtained by negating the state path of a weak solution of the sign SDE. -/
def WeakSDESolution.negateSignState :
    GeneralizedWeakSDESolution
      signInitialLaw
      (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
      (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))) :=
  { Ω := L.Ω
    instMeasurableSpace := L.instMeasurableSpace
    μ := L.μ
    instIsProbabilityMeasure := L.instIsProbabilityMeasure
    ℱ := L.ℱ
    instUsualConditions := L.instUsualConditions
    X := fun ω ↦ -L ω
    W := L.W
    brownian := L.brownian
    coordinate_martingale := L.coordinate_martingale
    adapted := L.negateSignState_adapted
    initialLaw := L.negateSignState_initialLaw
    solves_sde := L.negateSignState_solvesSDE }

-- Proof sketch: unfold `WeakSDESolution.negateSignState`; its state-path field is defined by
-- pointwise negation of the original continuous path.
/-- Evaluating the negated sign-SDE weak solution returns the negated original path. -/
theorem WeakSDESolution.negateSignState_apply (ω : L.Ω) :
    (WeakSDESolution.negateSignState L) ω = -L ω := sorry

-- Proof sketch: apply Example 26.15 to obtain a weak solution of the sign SDE. The companion
-- construction `WeakSDESolution.negateSignState` is another weak solution on the same filtered
-- probability space with the same Brownian driver, and the original solution is not almost surely
-- equal to its negation; this violates `WeakSDESolution.IsPathwiseUnique`.
/-- Example 26.19: negating a weak solution of the one-dimensional sign SDE gives another weak
solution on the same filtered probability space, so pathwise uniqueness fails for this equation. -/
theorem sign_sde_pathwiseUniqueness_fails :
    ∃ L :
        GeneralizedWeakSDESolution
          signInitialLaw
          (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
          (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))),
      ¬ L.IsPathwiseUnique := sorry

end ProbabilityTheory
