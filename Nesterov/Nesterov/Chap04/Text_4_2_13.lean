import Mathlib
import Nesterov.Chap04.Algorithm_4_2_4
import Nesterov.Chap04.Theorem_4_2_3

open scoped BigOperators Gradient
open StrongConvexAcceleratedCubicNewton

noncomputable section

universe u

variable {E : Type u}

/- Text 4.2.13 lies in the strongly-convex accelerated cubic-Newton / quadratic-entry domain on
real Hilbert spaces.

Sampled owner declarations:
* `StrongConvexAcceleratedCubicNewton.stageRadius`, `stageLength`, `stageSteps`, and `method` in
  `Algorithm_4_2_4`, the chapter owners for the multistage restart schedule and outer orbit;
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, the nearby source-facing region owner
  for a quadratic regime, written in multiplication form to avoid division-by-zero artifacts;
* `quadraticGradientRegion` in `Text_4_2_12`, the nearby source-facing threshold-region owner for
  Newton dynamics, again written in multiplication form;
* `StrongConvexOn` together with `f ∈ C22[L3]`, the canonical whole-space strong-convexity and
  Hessian-Lipschitz owners used by the surrounding chapter API.

Best owner abstraction:
* source-facing: the quadratic-entry region for the multistage accelerated cubic-Newton orbit and
  the first stage index at which the orbit enters that region;
* core/canonical: `StrongConvexAcceleratedCubicNewton.method` and the region set itself;
* bridge/view: the pointwise membership and least-entry-set expansion.

Primitive data:
* the objective `f`;
* the minimizer `xStar`;
* the strong-convexity modulus `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the multistage outer orbit data coming from `StrongConvexAcceleratedCubicNewton.method`.

Derived API:
* the quadratic-entry region inequality, kept in multiplication form
  `8 L₃² (f x - f xStar) ≤ σ₂³`;
* the predicate that stage `k` has entered that region;
* the canonical least-entry witness `IsLeast {k | ...}` and the logarithmic stage bound.

The previous version organized the file around one-off scalar threshold / stage-bound definitions.
This refinement follows the region-style owner pattern already used nearby in Chapter 4: the public
surface is the quadratic-entry region and the corresponding least stage index at which the
multistage orbit enters it, while the displayed scalar inequalities appear only as defining
formulas inside that owner API. -/

/-- The quadratic-entry region for Text 4.2.13, written in multiplication form so that the
degenerate case `L₃ = 0` still gives the intended whole-space threshold region. -/
def strongConvexAcceleratedCubicNewtonQuadraticRegion
    (f : E → ℝ) (xStar : E) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ)}

-- Proof sketch: unfold `strongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Membership in `strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ₂ L₃` is exactly
the quadratic-entry inequality `8 L₃² (f x - f xStar) ≤ σ₂³`. -/
theorem mem_strongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    {f : E → ℝ} {xStar x : E} {σ2 : ℝ} {L3 : NNReal} :
    x ∈ strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3 ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ) :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L3 : NNReal}

/-- `InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ₂ R y₀ k` means that
the `k`th outer-stage iterate of Algorithm 4.2.4 has entered the quadratic region from
Text 4.2.13. -/
def InStrongConvexAcceleratedCubicNewtonQuadraticRegion
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) : Prop :=
  method innerMethod σ2 R y0 k ∈
    strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3

-- Proof sketch: unfold `InStrongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Expanding `InStrongConvexAcceleratedCubicNewtonQuadraticRegion` says exactly that the `k`th
outer iterate satisfies `8 L₃² (f(y_k) - f(x^*)) ≤ σ₂³`. -/
theorem inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) :
    InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ2 R y0 k ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
          (f (method innerMethod σ2 R y0 k) - f xStar) ≤
        σ2 ^ (3 : ℕ) :=
  Iff.rfl

-- Proof sketch: prove by induction that `‖method innerMethod σ₂ R y₀ k - xStar‖ ≤ R / 2^k`
-- using strong convexity together with
-- `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` applied to the restarted inner owner
-- `innerMethod (method innerMethod σ₂ R y₀ k)` at the scheduled stage length
-- `stageSteps σ₂ L₃ R k`. The owner lower bound `stageLength σ₂ L₃ R k ≤ stageSteps σ₂ L₃ R k`
-- yields the factor `1 / 2`. Then deduce the gap contraction
-- `f (method innerMethod σ₂ R y₀ (k + 1)) - f xStar ≤
--    (1 / 4) * (f (method innerMethod σ₂ R y₀ k) - f xStar)`,
-- iterate this recurrence from the initial cubic upper bound, and solve the threshold inequality
-- `8 L₃² (f (method innerMethod σ₂ R y₀ N) - f xStar) ≤ σ₂³` for `N`. Since the least-entry
-- formulation allows the initial stage `N = 0`, the final real-valued stage bound is
-- clamped below by `0`.
/-- Text 4.2.13 (1): if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, and the canonical
multistage accelerated cubic-Newton method from Algorithm 4.2.4 started at `y₀` satisfies
`‖y₀ - x^*‖ ≤ R`, then the first stage index `N` whose outer iterate enters the quadratic region
`{x | 8 L₃² (f x - f xStar) ≤ σ₂³}` satisfies
`N ≤ max 0 ((1 / log 4) * log (((8 / 3) * (L₃ R)^3) / σ₂^3))`. The `max 0` is the stage-zero-safe
reformulation of the textbook logarithmic estimate for the natural-number stage indexing used by
`StrongConvexAcceleratedCubicNewton.method`. Under `f ∈ C22[L₃]`, this is the canonical-owner
reformulation of the textbook Hessian-lower-bound hypothesis. -/
theorem strongConvexAcceleratedCubicNewton_firstQuadraticRegionIndex_le_stageBound
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ} {xStar y0 : E}
    (hσ2 : 0 < σ2)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    {R : ℝ} (hR : 0 ≤ R)
    (hy0 : ‖y0 - xStar‖ ≤ R)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ |
          InStrongConvexAcceleratedCubicNewtonQuadraticRegion
            xStar innerMethod σ2 R y0 k}
        N) :
    (N : ℝ) ≤
      max 0
        (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
          Real.log 4) := sorry

private theorem strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one :
    |((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ)| < 1 := by
  rw [abs_of_pos]
  · have hpow : 1 < Real.rpow (2 : ℝ) (1 / 3 : ℝ) := by
      apply Real.one_lt_rpow
      · norm_num
      · norm_num
    exact inv_lt_one_of_one_lt₀ hpow
  · exact inv_pos.2 (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)

-- Proof sketch: iterate `stageLength_succ` to express the source schedule
-- `m_k = stageLength σ₂ L₃ R k` as the geometric progression `m_k = m₀ · 2^{-k / 3}`.
/-- For `σ₂ > 0` and `R ≥ 0`, the source stage lengths of Algorithm 4.2.4 form the geometric
progression `m_k = m₀ · 2^{-k / 3}`. -/
theorem strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) (k : ℕ) :
    stageLength σ2 L3 R k =
      stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      rw [stageLength_succ k hσ2 hR, hk]
      ring_nf

-- Proof sketch: combine the geometric closed form for `stageLength` with the canonical real
-- geometric-series identity `∑' k, ρ^k = (1 - ρ)⁻¹` for `ρ = 2^{-1 / 3}`.
/-- Text 4.2.13 (2): for the source stage schedule `m_k = stageLength σ₂ L₃ R k` of
Algorithm 4.2.4 with `σ₂ > 0` and `R ≥ 0`, the total stage-length budget is summable and equals
`m₀ / (1 - 2^{-1 / 3})`. This is the exact real source-schedule estimate; the discrete Newton
counts used by the algorithm remain `stageSteps σ₂ L₃ R k = ⌈m_k⌉₊`. -/
theorem strongConvexAcceleratedCubicNewton_totalStageLength_eq_geometricFactor_mul_firstStageLength
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) :
    Summable (stageLength σ2 L3 R) ∧
      ∑' k, stageLength σ2 L3 R k =
        stageLength σ2 L3 R 0 * (1 - (Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹)⁻¹ := by
  have hgeom :
      Summable (fun k : ℕ ↦ ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one
      strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one
  have hsum :
      Summable
        (fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    hgeom.mul_left _
  have hstage :
      stageLength σ2 L3 R =
        fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k := by
    funext k
    exact strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
      hσ2 hR k
  refine ⟨?_, ?_⟩
  · have h := hsum
    rwa [← hstage] at h
  · have htsum :
        ∑' k, stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k =
          stageLength σ2 L3 R 0 * (1 - ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ))⁻¹ := by
        rw [tsum_mul_left,
          tsum_geometric_of_abs_lt_one
            strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one]
    have h := htsum
    rwa [← hstage] at h

end

end
