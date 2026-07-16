import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_2_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Algorithm_1_7_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient DegreeConditioning FunctionClasses

noncomputable section

universe u

/- Text 4.2.24 lies in the Chapter 4 Newton / quadratic-entry domain.

Sampled owner declarations:
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the Chapter 1 owner for
  the quadratic scalar error recursion;
* `quadraticGradientRegion` in `Text_4_2_12`, the nearby Newton threshold-region owner;
* `strongConvexAcceleratedCubicNewtonQuadraticRegion` in `Text_4_2_13`, the chapter pattern
  "region set + entry predicate + first-entry index";
* `acceleratedCubicNewtonQuadraticConvergenceRegion` and
  `InAcceleratedCubicNewtonQuadraticConvergenceRegion` in `Text_4_2_22`, the closest sibling
  declarations in the same local quadratic-entry domain;
* `HasIteratedFDerivLipschitzConstantOfDegree.contDiff` in `Definition_4_2_11`, the owner-level
  bridge from degree-three derivative Lipschitz control to the redundant `ContDiff ℝ 2 f`
  regularity that should stay derived rather than primitive here;
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the chapter owner for minimizer
  uniqueness once the `𝓕₂Lip` degree-two uniform-convexity data has been converted into
  strong convexity;
* `NewtonSystem.Method` in `Algorithm_1_7_1`, the orbit owner for Newton iterates.

Best owner abstraction:
* source-facing: the intrinsic Newton quadratic-convergence neighborhood around `xStar`, the raw
  threshold region used by the entry estimate, the direct tail property
  `HasQuadraticConvergenceFrom`, and the explicit entry-time estimate;
* core/canonical: the Newton orbit `NewtonSystem.Method (∇ f) x0`;
* bridge/view: the Chapter 1 scalar error owner `HasEventuallySuperlinearErrorBound`, and the
  bridge from a sufficiently small threshold inequality to quadratic convergence of the same
  Newton orbit.

Primitive data:
* an orbit `x` for the tail predicate, and the initial point `x0` for the explicit entry-time
  bound;
* the limit point `xStar`;
* the source-facing threshold parameter `σ₃`;
* the degree-two and degree-three conditioning constants `σ[2](f)`, `L[2](f)`, and `L[3](f)`.

Derived API:
* `HasQuadraticConvergenceFrom`, built from trajectory convergence plus the Chapter 1 scalar error
  owner;
* the fixed local neighborhood `newtonQuadraticConvergenceRegion`, written in multiplication form
  as `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`;
* the raw threshold neighborhood `newtonThresholdRegion`, written in multiplication form to avoid
  the division-based surface `σ₃ / L₃(f)`;
* the bridge theorem sending entry into a sufficiently small threshold neighborhood to entry into
  `newtonQuadraticConvergenceRegion`, and hence to quadratic convergence of the same orbit from
  that iterate onward;
* the explicit nonnegative entry-time bound and the corresponding entry estimate;
* the induced tail-convergence theorem extracted from the entry estimate once the threshold is
  known to lie inside the fixed quadratic neighborhood.

The previous version duplicated the Chapter 1 quadratic-recurrence owner inside
`HasQuadraticConvergenceFrom`, and treated the raw threshold inequality
`L₃(f) ‖x - xStar‖ ≤ σ₃` as if it were itself the quadratic-convergence region for every `σ₃`.
This refinement keeps the canonical tail predicate `HasQuadraticConvergenceFrom` directly for
actual Newton orbits, splits the intrinsic quadratic neighborhood from the auxiliary threshold
region used by the entry estimate, and only upgrades threshold entry to quadratic convergence when
the threshold is small enough to lie inside the fixed neighborhood. The quadratic tail property is
expressed through the canonical scalar error owner `HasEventuallySuperlinearErrorBound`, the `C²`
regularity remains derived from the degree-three Lipschitz owner, minimizer uniqueness stays at
the strong-convexity owner layer instead of a local duplicate wrapper, and the entry-time bound is
exposed at the initial-data layer as an explicit nonnegative scalar owner obtained by clamping the
source logarithmic expression below by `0`. -/

section QuadraticConvergence

variable {E : Type u} [SeminormedAddCommGroup E]

variable {x : ℕ → E} {xStar : E}

/-- A Newton orbit has quadratic convergence to `xStar` from index `k` if it converges to
`xStar` and its error sequence satisfies the Chapter 1 quadratic scalar recurrence from that index
onward. -/
def HasQuadraticConvergenceFrom (x : ℕ → E) (xStar : E) (k : ℕ) : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      Filter.Tendsto x Filter.atTop (nhds xStar) ∧
        HasEventuallySuperlinearErrorBound (fun j ↦ ‖x j - xStar‖) 0 c k

end QuadraticConvergence

section NewtonMethodTail

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace NewtonSystem.Method

/-- If the tail of a Newton method converges quadratically from its initial index, then the
original Newton method converges quadratically from the corresponding shifted index. -/
theorem hasQuadraticConvergenceFrom_of_tail
    {F : E → E} {x0 xStar : E} (method : NewtonSystem.Method F x0) {k : ℕ}
    (h : HasQuadraticConvergenceFrom (method.tail k) xStar 0) :
    HasQuadraticConvergenceFrom method xStar k := by
  rcases h with ⟨c, hc, htendsto, hbound⟩
  refine ⟨c, hc, ?_, Nat.zero_le k, ?_⟩
  · simpa using (Filter.tendsto_add_atTop_iff_nat k).1 htendsto
  · intro j hj
    rcases Nat.exists_eq_add_of_le hj with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.sub_zero] using
      hbound.bound (Nat.zero_le n)

end NewtonSystem.Method

end NewtonMethodTail

section NewtonQuadraticConvergenceRegion

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

/-- The intrinsic Newton quadratic-convergence neighborhood around `xStar`. It is written in
multiplication form as `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`, so no division-based surface is
forced. This is the fixed local neighborhood whose membership is bridged to
`HasQuadraticConvergenceFrom` below. -/
def newtonQuadraticConvergenceRegion
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (xStar : E) : Set E :=
  {x | 4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ)}

-- Proof sketch: unfold `newtonQuadraticConvergenceRegion`.
/-- Membership in `newtonQuadraticConvergenceRegion f xStar` is exactly the displayed
local inequality `4 L₂(f) L₃(f) ‖x - xStar‖ ≤ σ₂(f)^2`. -/
theorem mem_newtonQuadraticConvergenceRegion_iff
    {f : E → ℝ} [f ∈ 𝓕₂Lip] {xStar x : E} :
    x ∈ newtonQuadraticConvergenceRegion f xStar ↔
      4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ) :=
  Iff.rfl

end NewtonQuadraticConvergenceRegion

section NewtonThresholdRegion

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]

/-- The raw threshold neighborhood `L₃(f) ‖x - xStar‖ ≤ σ₃` appearing in Text 4.2.24, written in
multiplication form so that the degenerate case `L₃(f) = 0` does not force a division-based
surface. This is the source-facing threshold region used in the entry estimate. -/
def newtonThresholdRegion
    (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    (xStar : E) (σ₃ : ℝ) : Set E :=
  {x | L[3](f) * ‖x - xStar‖ ≤ σ₃}

-- Proof sketch: unfold `newtonThresholdRegion`.
/-- Membership in `newtonThresholdRegion f xStar σ₃` is exactly the displayed threshold inequality
`L₃(f) ‖x - xStar‖ ≤ σ₃`. -/
theorem mem_newtonThresholdRegion_iff
    {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f]
    {xStar x : E} {σ₃ : ℝ} :
    x ∈ newtonThresholdRegion f xStar σ₃ ↔
      L[3](f) * ‖x - xStar‖ ≤ σ₃ :=
  Iff.rfl

end NewtonThresholdRegion

section NewtonQuadraticConvergenceRegionBridge

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
variable {xStar : E} {σ₃ : ℝ}

-- Proof sketch: prove the local Newton-region theorem at index `0` for a Newton orbit started in
-- `newtonQuadraticConvergenceRegion f xStar` from the chapter `𝓕₂Lip` data and the minimizer
-- hypothesis on `xStar`, then apply it to the tail `method.tail k` and transfer the estimate back
-- to the original orbit via `NewtonSystem.Method.hasQuadraticConvergenceFrom_of_tail`.
/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, and the `k`th Newton iterate lies in the intrinsic
quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`, then the same Newton
orbit converges quadratically to `xStar` from index `k` onward. -/
theorem hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion
    (_ : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hk : method k ∈ newtonQuadraticConvergenceRegion f xStar) :
    HasQuadraticConvergenceFrom method xStar k := by
  sorry

-- Proof sketch: unfold the threshold-region and intrinsic-region inequalities, multiply the
-- threshold inequality by `4 L₂(f)`, and use the smallness hypothesis
-- `4 L₂(f) σ₃ ≤ σ₂(f)^2`.
section

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If the threshold parameter `σ₃` is small enough that
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, then membership in `newtonThresholdRegion f xStar σ₃` forces membership in
the intrinsic Newton quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`. -/
theorem mem_newtonQuadraticConvergenceRegion_of_mem_newtonThresholdRegion
    {x : E}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hx : x ∈ newtonThresholdRegion f xStar σ₃) :
    x ∈ newtonQuadraticConvergenceRegion f xStar := by
  have hmul :
      (4 * L[2](f)) * (L[3](f) * ‖x - xStar‖) ≤ (4 * L[2](f)) * σ₃ := by
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  change 4 * L[2](f) * L[3](f) * ‖x - xStar‖ ≤ σ[2](f) ^ (2 : ℕ)
  simpa [mul_assoc] using hmul.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hσ₃)

end

/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, the threshold parameter `σ₃` satisfies
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, and the `k`th Newton iterate lies in the threshold region
`newtonThresholdRegion f xStar σ₃`, then the same Newton orbit converges quadratically to `xStar`
from index `k` onward. -/
theorem hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion
    (hxStar : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hk : method k ∈ newtonThresholdRegion f xStar σ₃) :
    HasQuadraticConvergenceFrom method xStar k := by
  exact hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion hxStar method
    (mem_newtonQuadraticConvergenceRegion_of_mem_newtonThresholdRegion hσ₃ hk)

/-- If `f ∈ 𝓕₂Lip`, `xStar` minimizes `f`, the threshold parameter `σ₃` satisfies
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, and the `k`th Newton iterate satisfies the threshold inequality
`L₃(f) ‖x_k - xStar‖ ≤ σ₃`, then the actual Newton orbit converges quadratically to `xStar` from
that iterate onward. -/
theorem hasQuadraticConvergenceFrom_of_threshold
    (hxStar : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ))
    (hk : L[3](f) * ‖method k - xStar‖ ≤ σ₃) :
    HasQuadraticConvergenceFrom method xStar k := by
  exact hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion hxStar method hσ₃
    (show method k ∈ newtonThresholdRegion f xStar σ₃ from hk)

end NewtonQuadraticConvergenceRegionBridge

section NewtonQuadraticConvergenceEntryBound

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

/-- The entry-time bound from Text 4.2.24, written as an explicit nonnegative real number because
it bounds a natural iterate index. It depends only on the initial point `x0`, the target point
`xStar`, the threshold `σ₃`, and the conditioning data of `f`. This is the source logarithmic
expression clamped below by `0`. -/
def newtonQuadraticConvergenceEntryBound
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (σ₃ C : ℝ) : ℝ :=
  max 0
    (C *
      (Real.sqrt (L[2](f) / σ[2](f)) *
        Real.log (L[2](f) * L[3](f) ^ (2 : ℕ) / σ₃ ^ (2 : ℕ)) *
        ‖x0 - xStar‖ ^ (2 : ℕ)))

/-- The entry-time bound from Text 4.2.24 is nonnegative by construction. -/
theorem newtonQuadraticConvergenceEntryBound_nonneg
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (σ₃ C : ℝ) :
    0 ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C :=
  le_max_left 0
    (C *
      (Real.sqrt (L[2](f) / σ[2](f)) *
        Real.log (L[2](f) * L[3](f) ^ (2 : ℕ) / σ₃ ^ (2 : ℕ)) *
        ‖x0 - xStar‖ ^ (2 : ℕ))
    )

end NewtonQuadraticConvergenceEntryBound

section NewtonQuadraticConvergenceEntry

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]
variable {x0 : E}

-- Proof sketch: combine the `𝓕₂^{Lip}` regularity data `σ₂(f)`, `L₂(f)`, and `L₃(f)` with the
-- global Newton complexity estimate to obtain an iterate satisfying the threshold inequality
-- `L₃(f) ‖x_k - xStar‖ ≤ σ₃`, then convert that estimate to actual membership of `method k` in
-- `newtonThresholdRegion f xStar σ₃`. Because the displayed real expression upper-bounds a
-- natural-number iterate index, the statement factors it through the explicit nonnegative owner
-- `newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C`, defined at the initial-data layer by
-- clamping the source logarithmic expression below by `0`.
/-- Text 4.2.24, entry-threshold form: let `f ∈ 𝓕₂^{Lip}`, let `xStar` be a minimizer of `f`
(hence automatically the unique minimizer, since the degree-two uniform-convexity owner behind
`f ∈ 𝓕₂Lip` yields positive strong convexity and then `StrongConvexOn.eq_of_isMinOn`), and let
`x` be the Newton orbit
`x_{k+1} = x_k - [∇² f(x_k)]⁻¹ ∇ f(x_k)`. Then for every threshold `σ₃ > 0`, some iterate enters
the threshold region `L₃(f) ‖x - xStar‖ ≤ σ₃`. The entry time is at most
`newtonQuadraticConvergenceEntryBound f x₀ xStar σ₃ C = max 0
  (C * (sqrt (L₂(f) / σ₂(f)) * log (L₂(f) * L₃(f)^2 / σ₃^2) * ‖x₀ - xStar‖^2))`
steps for some positive absolute constant `C`. -/
theorem newton_enters_threshold_region_of_f2Lip
    : ∃ C > 0,
        ∀ {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
          (xStar : E)
          (_ : IsMinOn f Set.univ xStar)
          (method : NewtonSystem.Method (∇ f) x0)
          {σ₃ : ℝ} (_ : 0 < σ₃),
            ∃ k : ℕ,
              (k : ℝ) ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C ∧
                method k ∈ newtonThresholdRegion f xStar σ₃ := by
  sorry

-- Proof sketch: combine `newton_enters_threshold_region_of_f2Lip` with the bridge
-- `hasQuadraticConvergenceFrom_of_mem_newtonThresholdRegion`. The extra smallness hypothesis
-- `4 L₂(f) σ₃ ≤ σ₂(f)^2` ensures that the raw threshold region lies inside the intrinsic local
-- quadratic-convergence neighborhood.
/-- Text 4.2.24, quadratic-regime form: if the entry threshold `σ₃` is small enough that
`4 L₂(f) σ₃ ≤ σ₂(f)^2`, then the same entry estimate forces an iterate of the Newton orbit into
the intrinsic quadratic-convergence region `newtonQuadraticConvergenceRegion f xStar`, and from
that iterate onward Newton's method converges quadratically to `xStar`. -/
theorem newton_enters_quadratic_convergence_region_of_f2Lip
    : ∃ C > 0,
        ∀ {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
          (xStar : E)
          (hxStar : IsMinOn f Set.univ xStar)
          (method : NewtonSystem.Method (∇ f) x0)
          {σ₃ : ℝ} (_ : 0 < σ₃)
          (hσ₃ : 4 * L[2](f) * σ₃ ≤ σ[2](f) ^ (2 : ℕ)),
            ∃ k : ℕ,
              (k : ℝ) ≤ newtonQuadraticConvergenceEntryBound f x0 xStar σ₃ C ∧
                method k ∈ newtonQuadraticConvergenceRegion f xStar ∧
                HasQuadraticConvergenceFrom method xStar k := by
  sorry

end NewtonQuadraticConvergenceEntry
