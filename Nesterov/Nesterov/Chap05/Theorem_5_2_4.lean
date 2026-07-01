import Mathlib
import Nesterov.Chap05.Definition_5_1_1
import Nesterov.Chap05.Proposition_5_2_1
import Nesterov.Chap05.Theorem_5_1_8
import Nesterov.Chap05.Theorem_5_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SelfConcordantAuxiliaryFunction IntermediateNewtonQuadraticConvergenceRegion

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scaled suboptimality `Δ_f(x) = M_f^2 (f(x) - f^*)` used in the path-following bounds. -/
def selfConcordantScaledSuboptimality
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) : ℝ :=
  (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar)

-- Proof sketch: unfold `selfConcordantScaledSuboptimality`.
/-- Expanding `selfConcordantScaledSuboptimality f M_f x f*` gives `M_f^2 (f(x) - f*)`. -/
theorem selfConcordantScaledSuboptimality_def
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) :
    selfConcordantScaledSuboptimality f Mf x fStar =
      (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) := sorry

/-- The diameter of the initial sublevel set `{x ∈ dom | f x ≤ f(y₀)}` measured in the local norm
at the base point `y₀`. -/
def pathFollowingLevelSetDiameter
    {dom : Set E} (f : E → ℝ) (y0 : dom) : ℝ :=
  sSup
    ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
      {p : E × E |
        p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)})

-- Proof sketch: unfold `pathFollowingLevelSetDiameter`.
/-- Expanding `pathFollowingLevelSetDiameter f y₀` gives the supremum of the local-norm distances
between pairs of points in the initial sublevel set. -/
theorem pathFollowingLevelSetDiameter_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) :
    pathFollowingLevelSetDiameter f y0 =
      sSup
        ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
          {p : E × E |
            p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)}) := sorry

/-- A chosen inverse value of the self-concordant auxiliary function `ω(t) = t - log(1 + t)`. -/
noncomputable def selfConcordantOmegaInverse (s : ℝ) : Set.Ioi (-1 : ℝ) :=
  Function.invFun ω s

-- Proof sketch: unfold `selfConcordantOmegaInverse`.
/-- Expanding `selfConcordantOmegaInverse s` gives the chosen inverse value of
`selfConcordantOmega` at `s`. -/
theorem selfConcordantOmegaInverse_def (s : ℝ) :
    selfConcordantOmegaInverse s = Function.invFun ω s := sorry

/-- The path-following threshold argument
`((1 - β(τ)) (1 - 2 β(τ))) / 2` always lies in `(-1, ∞)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_mem_Ioi (τ : ℝ) :
    -1 <
      ((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2 := by
  have hsquare : 0 ≤ (4 * pathFollowingCenteringBeta τ - 3) ^ (2 : ℕ) := sq_nonneg _
  nlinarith

/-- The threshold on `t_k` ensuring that the `k`-th path-following iterate has entered the
quadratic-convergence region of the intermediate Newton method. -/
def pathFollowingQuadraticRegionTimeThreshold
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  ω
      (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
        pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
    ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
      selfConcordantOmegaInverse
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar)))

-- Proof sketch: unfold `pathFollowingQuadraticRegionTimeThreshold`.
/-- Expanding `pathFollowingQuadraticRegionTimeThreshold` gives the scalar threshold on `t_k`
obtained by rearranging the entry condition from the proof of `(5.2.22)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionTimeThreshold f Mf y0 xStar τ =
      ω
          (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
            pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
        ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
          selfConcordantOmegaInverse
            (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) := sorry

/-- The explicit lower bound on the iteration index in `(5.2.22)` forcing the path-following
iterates into the quadratic-convergence region. -/
def pathFollowingQuadraticRegionEntryBound
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  Real.sqrt
    (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
        (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
      Real.log
        (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
            selfConcordantOmegaInverse
              (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
          ω
            (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
              pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ))))

-- Proof sketch: unfold `pathFollowingQuadraticRegionEntryBound`.
/-- Expanding `pathFollowingQuadraticRegionEntryBound` recovers the square-root bound from
display `(5.2.22)`, written with `pathFollowingGammaRadius τ` and `pathFollowingKappa τ`. -/
theorem pathFollowingQuadraticRegionEntryBound_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionEntryBound f Mf y0 xStar τ =
      Real.sqrt
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
            (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
          Real.log
            (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
                selfConcordantOmegaInverse
                  (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
              ω
                (⟨((1 - pathFollowingCenteringBeta τ) *
                    (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
                  pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)))) := sorry

-- Proof sketch: if no iterate up to `N` has yet entered the quadratic-convergence region, the
-- hypothesis `hdecay` gives the exponential estimate for `t_N`. The lower bound `hN` makes this
-- estimate at most `pathFollowingQuadraticRegionTimeThreshold f Mf y₀ x* τ`, so `hentry`
-- forces `y_N` into the region, a contradiction. Therefore some earlier iterate enters the
-- region, and the forward-invariance hypothesis `hstable` propagates that membership to `y_N`.
/-- Theorem 5.2.4: for a path-following process generated by `(5.2.16)`, every index above the
bound `(5.2.22)` yields an iterate in the quadratic-convergence region of the intermediate Newton
method. The textbook statement writes `𝒬_f`; here the conclusion is formalized by the region
`𝒟[f | dom, M_f]` proved in the accompanying argument. -/
theorem selfConcordantPathFollowing_mem_intermediateNewtonQuadraticConvergenceRegion_of_large_index
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (htau : τ ≤ 0.23) (y0 : dom) (xStar : E)
    (hmin : IsMinOn f dom xStar)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (hstable :
      ∀ k : ℕ,
        process.y k ∈ 𝒟[f | dom, Mf] →
          process.y (k + 1) ∈ 𝒟[f | dom, Mf])
    (hdecay :
      ∀ m : ℕ,
        (∀ k : ℕ, k ≤ m →
          process.y k ∉ 𝒟[f | dom, Mf]) →
        (process.t m : ℝ) ≤
          Real.exp
            (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (m : ℝ) ^ (2 : ℕ) /
                selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))))
    (hentry :
      ∀ m : ℕ,
        (process.t m : ℝ) ≤ pathFollowingQuadraticRegionTimeThreshold f (Mf : NNReal) y0 xStar τ →
          process.y m ∈ 𝒟[f | dom, Mf])
    {N : ℕ}
    (hN : pathFollowingQuadraticRegionEntryBound f (Mf : NNReal) y0 xStar τ ≤ (N : ℝ)) :
    process.y N ∈ 𝒟[f | dom, Mf] := sorry

end
