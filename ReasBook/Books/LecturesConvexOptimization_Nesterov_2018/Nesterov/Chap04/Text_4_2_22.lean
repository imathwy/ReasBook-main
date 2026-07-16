import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Algorithm_4_2_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_17
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Text_4_2_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped DegreeConditioning FunctionClasses

universe u

variable {E : Type u}

section AcceleratedCubicNewtonQuadraticConvergenceRegion

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Text 4.2.22 lies in the accelerated cubic-Newton / local quadratic-convergence domain on real
Hilbert spaces.

Sampled owner declarations:
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for Algorithm `(4.2.46)`;
* `HasQuadraticConvergenceFrom` in `Text_4_2_24`, the existing Chapter 4 owner for quadratic tail
  convergence from a given index;
* `strongConvexAcceleratedCubicNewtonQuadraticRegion` and
  `InStrongConvexAcceleratedCubicNewtonQuadraticRegion` in `Text_4_2_13`, the nearby Chapter 4
  owner pattern for a source-facing local region together with its iterate-entry predicate;
* `newtonQuadraticConvergenceRegion` and
  `hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion` in `Text_4_2_24`, where
  region membership is bridged to quadratic convergence of the same orbit.

Best owner abstraction:
* source-facing: the local quadratic-convergence region around `xStar`, i.e. the geometric
  threshold neighborhood in which the iterate of Algorithm `(4.2.46)` has entered the local
  regime from Text 4.2.22;
* core/canonical: the tail predicate `HasQuadraticConvergenceFrom` on a fixed accelerated
  cubic-Newton orbit;
* bridge/view: the theorem sending entry of the given orbit into the local region at index `k` to
  `HasQuadraticConvergenceFrom method xStar k`.

Primitive data:
* the objective `f`, the minimizer `xStar`, and the Chapter 4 tail-convergence owner
  `HasQuadraticConvergenceFrom`;
* the source-facing local-region threshold `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`, written in
  multiplication form so the degenerate case `L₃(f) = 0` does not force a division-based API;
* the accelerated orbit `method`, the entry index `k`, and the multiplicative constant `C` for
  the entry-time theorem.

Derived API:
* the local quadratic-convergence region;
* the iterate-entry predicate for the accelerated cubic-Newton orbit into that region;
* the bridge theorem from region entry to `HasQuadraticConvergenceFrom` for the same orbit;
* the explicit nonnegative entry-time bound, obtained by clamping the source logarithmic
  expression below by `0`, together with the corresponding region-entry estimate.

The previous version replaced the source-facing local region by a restart-style wrapper saying
that every accelerated cubic-Newton method restarted from `x` converges quadratically. That
changed the public semantics: Text 4.2.22 is about the same orbit of Algorithm `(4.2.46)` once
it enters the local neighborhood. This refinement therefore keeps the public region as the
displayed threshold set and makes `HasQuadraticConvergenceFrom method xStar k` the semantic owner
attached to entry of the given orbit at index `k`.
-/

/-- The local quadratic-convergence region from Text 4.2.22, written in multiplication form so
that the degenerate case `L₃(f) = 0` does not force a division-based surface. -/
def acceleratedCubicNewtonQuadraticConvergenceRegion
    (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    [HasUniformConvexityParameterOfDegree 3 f]
    (xStar : E) : Set E :=
  {x | L[3](f) * ‖x - xStar‖ ≤ σ[3](f)}

-- Proof sketch: unfold `acceleratedCubicNewtonQuadraticConvergenceRegion`.
/-- Membership in `acceleratedCubicNewtonQuadraticConvergenceRegion f xStar` is exactly the
displayed threshold inequality `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`. -/
theorem mem_acceleratedCubicNewtonQuadraticConvergenceRegion_iff
    {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    [HasUniformConvexityParameterOfDegree 3 f]
    {xStar x : E} :
    x ∈ acceleratedCubicNewtonQuadraticConvergenceRegion f xStar ↔
      L[3](f) * ‖x - xStar‖ ≤ σ[3](f) :=
  Iff.rfl

end AcceleratedCubicNewtonQuadraticConvergenceRegion

section AcceleratedCubicNewtonQuadraticConvergenceEntryPredicate

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}
  [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
  [HasUniformConvexityParameterOfDegree 3 f]
  {x0 : E}

/-- `InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k` means that the `k`th
iterate of the accelerated cubic-Newton orbit lies in the local quadratic-convergence region from
Text 4.2.22. -/
def InAcceleratedCubicNewtonQuadraticConvergenceRegion
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (k : ℕ) : Prop :=
  method k ∈ acceleratedCubicNewtonQuadraticConvergenceRegion f xStar

-- Proof sketch: unfold `InAcceleratedCubicNewtonQuadraticConvergenceRegion`.
/-- Expanding `InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k` says exactly
that the `k`th iterate satisfies the local threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`. -/
theorem inAcceleratedCubicNewtonQuadraticConvergenceRegion_iff
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (k : ℕ) :
    InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k ↔
      L[3](f) * ‖method k - xStar‖ ≤ σ[3](f) :=
  Iff.rfl

/-- Entry of the `k`th accelerated cubic-Newton iterate into the local region from Text 4.2.22
forces quadratic convergence of the same orbit from index `k`. -/
theorem hasQuadraticConvergenceFrom_of_inAcceleratedCubicNewtonQuadraticConvergenceRegion
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    {xStar : E} {k : ℕ}
    (hk : InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k) :
    HasQuadraticConvergenceFrom method xStar k := by
  sorry

-- Proof sketch: unfold the local-region inequality at `method k`.
/-- If the `k`th accelerated cubic-Newton iterate satisfies the threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`, then it lies in the local quadratic-convergence region from
Text 4.2.22. -/
theorem inAcceleratedCubicNewtonQuadraticConvergenceRegion_of_threshold
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    {xStar : E} {k : ℕ}
    (hk : L[3](f) * ‖method k - xStar‖ ≤ σ[3](f)) :
    InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k := by
  exact hk

end AcceleratedCubicNewtonQuadraticConvergenceEntryPredicate

section AcceleratedCubicNewtonQuadraticConvergenceEntry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}
  [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
  [HasUniformConvexityParameterOfDegree 2 f]
  [HasUniformConvexityParameterOfDegree 3 f]
  {x0 : E}

-- Proof sketch: first use the global complexity estimate for the accelerated cubic-Newton method
-- on functions in `𝓕₂₃` to find an iterate satisfying the threshold inequality
-- `L₃(f) ‖x_k - xStar‖ ≤ σ₃(f)`. Then apply
-- `inAcceleratedCubicNewtonQuadraticConvergenceRegion_of_threshold` and then
-- `hasQuadraticConvergenceFrom_of_inAcceleratedCubicNewtonQuadraticConvergenceRegion` to upgrade
-- that threshold bound to quadratic convergence of the same orbit from index `k`. On the public
-- theorem surface, the only conditioning owner is `[f ∈ 𝓕₂₃]`; the degree-two and degree-three
-- uniform-convexity parameters together with the degree-three Lipschitz constant are inherited
-- from that source-facing class. The absolute constant is quantified before the problem data in
-- the repo-standard `∃ C > 0, ∀ ...` shape, and the real-valued source logarithmic expression is
-- factored through the explicit nonnegative owner
-- `acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound`, obtained by clamping it below by
-- `0`.
/-- The entry-time bound from Text 4.2.22, written as an explicit nonnegative real number because
it bounds a natural iterate index. This is the source logarithmic expression clamped below by
`0`. -/
def acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (C : ℝ) : ℝ :=
  max 0
    (C *
      (Real.rpow (L[3](f) / σ[3](f)) (1 / 3 : ℝ) *
        Real.log ((L[3](f) / σ[2](f)) * ‖method 0 - xStar‖)))

/-- The entry-time bound from Text 4.2.22 is nonnegative by construction. -/
theorem acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound_nonneg
    (method : AcceleratedCubicNewtonMethod f L[3](f) x0)
    (xStar : E) (C : ℝ) :
    0 ≤ acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C :=
  le_max_left 0
    (C *
      (Real.rpow (L[3](f) / σ[3](f)) (1 / 3 : ℝ) *
        Real.log ((L[3](f) / σ[2](f)) * ‖method 0 - xStar‖)))

/-- Text 4.2.22: there exists a positive absolute constant `C` such that for every
`f ∈ 𝓕₂₃`, every minimizer `xStar` of `f`, and every accelerated cubic-Newton method `(4.2.46)`
initialized at `x₀` with the canonical Hessian-Lipschitz constant `L₃(f)`, some iterate enters
the local quadratic-convergence region `L₃(f) ‖x - xStar‖ ≤ σ₃(f)`, and from that same index the
orbit itself converges quadratically to `xStar`. The entry time is bounded by the nonnegative owner
`acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C`, i.e. by the source
logarithmic expression
`C * ((L₃(f) / σ₃(f))^(1/3) * log ((L₃(f) / σ₂(f)) * ‖x₀ - xStar‖))`
clamped below by `0`. -/
theorem acceleratedCubicNewton_enters_quadratic_convergence_region :
    ∃ C > 0,
      ∀ {f : E → ℝ} [f ∈ 𝓕₂₃] {x0 : E}
        (xStar : E)
        (_ : IsMinOn f Set.univ xStar)
        (method : AcceleratedCubicNewtonMethod f L[3](f) x0),
          ∃ k : ℕ,
            (k : ℝ) ≤ acceleratedCubicNewtonQuadraticConvergenceRegionEntryBound method xStar C ∧
              InAcceleratedCubicNewtonQuadraticConvergenceRegion method xStar k ∧
              HasQuadraticConvergenceFrom method xStar k := by
  sorry

end AcceleratedCubicNewtonQuadraticConvergenceEntry
