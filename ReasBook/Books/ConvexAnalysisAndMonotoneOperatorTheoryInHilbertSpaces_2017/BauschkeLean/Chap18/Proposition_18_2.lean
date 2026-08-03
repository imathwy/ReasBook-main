import Mathlib
import BauschkeLean.Chap08.Theorem_8_38
import BauschkeLean.Chap09.Proposition_9_27
import BauschkeLean.Chap18.Proposition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

namespace ERealFunction

section SymmetricSecondDifferences

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.2 packages the source set `S_ε`.
- `core/canonical`: Proposition 18.1 already owns the pointwise predicate
  `HasSymmetricSecondDifferenceBound f x ε`.
- `bridge/view`: this file turns that pointwise owner into the set-valued surface `S_ε`.
-/

/-- The source-defined set `S_ε`: continuity points `x ∈ cont f` for which some positive symmetric
second-difference quotient has unit-sphere supremum strictly below `ε`. -/
noncomputable def symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (ε : Set.Ioi (0 : ℝ)) : Set H :=
  {x | x ∈ cont f ∧ HasSymmetricSecondDifferenceBound f x ε}

-- Proof sketch: unfold the defining set-builder for `S_ε`.
/-- Membership in `S_ε` means source continuity `x ∈ cont f` together with the Chapter 18
symmetric second-difference bound at tolerance `ε`. -/
@[simp] theorem mem_symmetricSecondDifferenceSublevelSet_iff
    (f : H → Set.Ioi (⊥ : EReal)) (ε : Set.Ioi (0 : ℝ)) (x : H) :
    x ∈ symmetricSecondDifferenceSublevelSet f ε ↔
      x ∈ cont f ∧ HasSymmetricSecondDifferenceBound f x ε :=
  Iff.rfl

end SymmetricSecondDifferences

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 18 2: a shorter step on the ray from `x` to `x + β • y` is the convex
combination used by Proposition 9.27. -/
private lemma ray_point_eq_convex_combination_endpoint
    (x y : H) {α β : ℝ} (hβ : 0 < β) :
    x + α • y = (α / β) • (x + β • y) + (1 - α / β) • x := by
  -- Rewrite the shorter ray point in the convex-combination form needed for effective-domain
  -- shrinking arguments.
  have hscalar : (α / β) * β = α := by
    field_simp [hβ.ne']
  calc
    x + α • y = x + (((α / β) * β) • y) := by rw [hscalar]
    _ = (1 : ℝ) • x + (α / β) • (β • y) := by simp [smul_smul]
    _ = ((α / β) + (1 - α / β)) • x + (α / β) • (β • y) := by simp
    _ = (α / β) • x + (1 - α / β) • x + (α / β) • (β • y) := by
          rw [add_smul]
    _ = (α / β) • x + ((α / β) • (β • y)) + (1 - α / β) • x := by abel_nf
    _ = (α / β) • (x + β • y) + (1 - α / β) • x := by
          simp [smul_add, add_assoc]

/-- Helper for Proposition 18 2: a smaller point on a finite convex ray stays in the effective
domain. -/
private lemma ray_point_mem_effectiveDomain_of_le
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hβy : x + β • y ∈ effectiveDomain f) :
    x + α • y ∈ effectiveDomain f := by
  by_cases hEq : α = β
  · -- In the equality case the larger-step hypothesis is already the desired conclusion.
    simpa [hEq] using hβy
  · have hlt : α < β := lt_of_le_of_ne hαβ hEq
    have hβ : 0 < β := lt_of_lt_of_le hα hαβ
    have hlam0 : 0 ≤ α / β := by
      exact (div_nonneg hα.le hβ.le)
    have hlam1 : 0 ≤ 1 - α / β := by
      rw [sub_nonneg]
      exact (div_le_one hβ).2 hαβ
    have hlam_sum : α / β + (1 - α / β) = 1 := by ring
    -- Rewrite the shorter point as the source convex combination and apply convexity of the
    -- effective domain.
    rw [ray_point_eq_convex_combination_endpoint x y hβ]
    exact hconv.convex_effectiveDomain hβy hx hlam0 hlam1 hlam_sum

omit [NormedSpace ℝ H] in
/-- Helper for Proposition 18 2: every point of a Lipschitz ball belongs to the Chapter 18
continuity set `cont f`. -/
private lemma mem_cont_of_mem_ball_of_lipschitzOnWith_ball
    (f : H → Set.Ioi (⊥ : EReal)) {x z : H} {ρ : ℝ} {β : NNReal}
    (hball : Metric.ball x ρ ⊆ effectiveDomain f)
    (hlip : LipschitzOnWith β (fun y ↦ (f y : EReal).toReal) (Metric.ball x ρ))
    (hz : z ∈ Metric.ball x ρ) :
    z ∈ cont f := by
  refine ⟨ρ - dist z x, ?_, ?_, ?_⟩
  · -- The margin to the boundary of the ball is positive because `z` lies strictly inside it.
    rw [Metric.mem_ball] at hz
    linarith
  · -- A smaller ball around `z` stays inside the original effective-domain ball by the triangle
    -- inequality.
    intro y hy
    apply hball
    rw [Metric.mem_ball] at hy hz ⊢
    have htriangle : dist y x ≤ dist y z + dist z x := dist_triangle y z x
    linarith
  · -- The Lipschitz estimate on the ambient open ball upgrades to ambient continuity at `z`.
    exact hlip.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)

/-- Helper for Proposition 18 2: if one sampled endpoint were `⊤`, then the corresponding
symmetric second-difference quotient would also be `⊤`; hence a strict real upper bound forces
both sample points into the effective domain. -/
private lemma sample_points_mem_effectiveDomain_of_symmetric_second_difference_lt
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    (η : Set.Ioi (0 : ℝ)) {r : ℝ}
    (hquot :
      (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
          2 * (f x : EReal)) / (η : ℝ)) <
        ((r : ℝ) : EReal)) :
    x + (η : ℝ) • y ∈ effectiveDomain f ∧
      x - (η : ℝ) • y ∈ effectiveDomain f := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := by
    rfl
  have htwo_top : (2 * (f x : EReal)) ≠ ⊤ := by
    rw [htwo, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hη_pos : (0 : EReal) < ((η : ℝ) : EReal) := by
    exact_mod_cast η.2
  have hη_ne_top : ((η : ℝ) : EReal) ≠ ⊤ := ne_of_lt (EReal.coe_lt_top _)
  have hplus_bot : (f (x + (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (η : ℝ) • y) : EReal) from
      (f (x + (η : ℝ) • y)).2)
  have hminus_bot : (f (x - (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x - (η : ℝ) • y) : EReal) from
      (f (x - (η : ℝ) • y)).2)
  have hplus_top : (f (x + (η : ℝ) • y) : EReal) ≠ ⊤ := by
    intro htop
    have hquot_top :
        (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) = ⊤ := by
      rw [htop, EReal.top_add_of_ne_bot hminus_bot, EReal.top_sub htwo_top,
        EReal.top_div_of_pos_ne_top hη_pos hη_ne_top]
    have : ¬ (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) < ((r : ℝ) : EReal) := by
      simp [hquot_top]
    exact this hquot
  have hminus_top : (f (x - (η : ℝ) • y) : EReal) ≠ ⊤ := by
    intro htop
    have hquot_top :
        (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) = ⊤ := by
      rw [htop, EReal.add_top_of_ne_bot hplus_bot, EReal.top_sub htwo_top,
        EReal.top_div_of_pos_ne_top hη_pos hη_ne_top]
    have : ¬ (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) < ((r : ℝ) : EReal) := by
      simp [hquot_top]
    exact this hquot
  constructor
  · -- The first sample is finite because the strict bound excludes the `⊤` branch.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top hplus_top
  · -- The second sample is finite for the same reason.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top hminus_top

/-- Helper for Proposition 18 2: once the center and both sampled endpoints are finite, the
symmetric second-difference quotient is the cast of the corresponding real quotient. -/
private lemma symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    (η : Set.Ioi (0 : ℝ))
    (hplus : x + (η : ℝ) • y ∈ effectiveDomain f)
    (hminus : x - (η : ℝ) • y ∈ effectiveDomain f) :
    (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) =
      (((((f (x + (η : ℝ) • y) : EReal).toReal +
          (f (x - (η : ℝ) • y) : EReal).toReal -
          2 * (f x : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hplus_top : (f (x + (η : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hplus)
  have hplus_bot : (f (x + (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (η : ℝ) • y) : EReal) from
      (f (x + (η : ℝ) • y)).2)
  have hminus_top :
      (f (x - (η : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hminus)
  have hminus_bot :
      (f (x - (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x - (η : ℝ) • y) : EReal) from
      (f (x - (η : ℝ) • y)).2)
  have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := by
    rfl
  -- Rewrite each finite `EReal` value as a real cast and collapse the quotient to real algebra.
  rw [← EReal.coe_toReal hplus_top hplus_bot, ← EReal.coe_toReal hminus_top hminus_bot,
    htwo, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_div]
  simp

/-- Helper for Proposition 18 2: if the center and sampled endpoint are finite, the directional
difference quotient is the cast of the corresponding real quotient. -/
private lemma directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hx : x ∈ effectiveDomain f) (η : Set.Ioi (0 : ℝ))
    (hη : x + (η : ℝ) • y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y η =
      ((((f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) /
          (η : ℝ) : ℝ) : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hη_top : (f (x + (η : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hη)
  have hη_bot : (f (x + (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (η : ℝ) • y) : EReal) from
      (f (x + (η : ℝ) • y)).2)
  -- Route correction: as in Proposition 9.27, finite endpoint values let the `EReal` quotient
  -- collapse to the corresponding real difference quotient.
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hη_top hη_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 18 2: summing the directional difference quotients in directions `y`
and `-y` recovers the symmetric second-difference quotient at the same step. -/
private lemma directionalDifferenceQuotient_add_neg_eq_symmetric_second_difference
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    (η : Set.Ioi (0 : ℝ))
    (hplus : x + (η : ℝ) • y ∈ effectiveDomain f)
    (hminus : x - (η : ℝ) • y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y η +
        directionalDifferenceQuotient f x (-y) η =
      (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
          2 * (f x : EReal)) / (η : ℝ)) := by
  have hminus' : x + (η : ℝ) • (-y) ∈ effectiveDomain f := by
    simpa [sub_eq_add_neg, smul_neg] using hminus
  have hq_pos :=
    directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx η hplus
  have hq_neg :
      directionalDifferenceQuotient f x (-y) η =
        ((((f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) /
            (η : ℝ) : ℝ) : EReal) := by
    simpa [sub_eq_add_neg, smul_neg] using
      (directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
        f hx (y := -y) η hminus')
  let a : ℝ :=
    ((f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (η : ℝ)
  let b : ℝ :=
    ((f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (η : ℝ)
  let c : ℝ :=
    ((f (x + (η : ℝ) • y) : EReal).toReal +
        (f (x - (η : ℝ) • y) : EReal).toReal -
        2 * (f x : EReal).toReal) / (η : ℝ)
  have habc : a + b = c := by
    dsimp [a, b, c]
    field_simp [(show (η : ℝ) ≠ 0 from η.2.ne')]
    ring
  -- Convert both directional quotients to real casts and combine them into the symmetric form.
  calc
    directionalDifferenceQuotient f x y η + directionalDifferenceQuotient f x (-y) η =
        ((a : ℝ) : EReal) + ((b : ℝ) : EReal) := by
          simp [a, b, hq_pos, hq_neg]
    _ =
        (((a + b : ℝ) : EReal)) := by
          rw [← EReal.coe_add]
    _ =
        ((c : ℝ) : EReal) := by
          rw [habc]
    _ =
        (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) := by
          dsimp [c]
          symm
          exact symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain f hx η hplus hminus

/-- Helper for Proposition 18 2: shrinking the step along a fixed ray can only decrease the
symmetric second-difference quotient. -/
private lemma symmetric_second_difference_le_of_le_step
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f)
    {η η₀ : Set.Ioi (0 : ℝ)} (hηη₀ : (η : ℝ) ≤ (η₀ : ℝ))
    (hplus₀ : x + (η₀ : ℝ) • y ∈ effectiveDomain f)
    (hminus₀ : x - (η₀ : ℝ) • y ∈ effectiveDomain f) :
    (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) ≤
      (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
          2 * (f x : EReal)) / (η₀ : ℝ)) := by
  have hplus :
      x + (η : ℝ) • y ∈ effectiveDomain f :=
    ray_point_mem_effectiveDomain_of_le f hconv hx η.2 hηη₀ hplus₀
  have hminus :
      x - (η : ℝ) • y ∈ effectiveDomain f := by
    have hneg :
        x + (η : ℝ) • (-y) ∈ effectiveDomain f :=
      ray_point_mem_effectiveDomain_of_le f hconv hx η.2 hηη₀ (by
        simpa [sub_eq_add_neg, smul_neg] using hminus₀)
    simpa [sub_eq_add_neg, smul_neg] using hneg
  have hmono_pos := directionalDifferenceQuotient_monotone f hconv hx y hηη₀
  have hmono_neg := directionalDifferenceQuotient_monotone f hconv hx (-y) hηη₀
  -- Proposition 9.27 controls each directional quotient separately; summing the two monotone
  -- inequalities gives the desired symmetric second-difference comparison.
  calc
    (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) =
      directionalDifferenceQuotient f x y η +
        directionalDifferenceQuotient f x (-y) η := by
          symm
          exact directionalDifferenceQuotient_add_neg_eq_symmetric_second_difference
            f hx η hplus hminus
    _ ≤ directionalDifferenceQuotient f x y η₀ +
          directionalDifferenceQuotient f x (-y) η₀ := by
          exact add_le_add hmono_pos hmono_neg
    _ = (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η₀ : ℝ)) := by
          exact directionalDifferenceQuotient_add_neg_eq_symmetric_second_difference
            f hx η₀ hplus₀ hminus₀

/-- Helper for Proposition 18 2: if `z` lies close enough to `x`, then the four sample points
used in the fixed-step symmetric second-difference comparison all stay inside the common
Lipschitz ball around `x`. -/
private lemma sample_points_mem_ball_of_dist_add_lt
    {x z y : H} {ρ : ℝ} (η : Set.Ioi (0 : ℝ))
    (hy : ‖y‖ = 1) (hclose : dist z x + (η : ℝ) < ρ) :
    x + (η : ℝ) • y ∈ Metric.ball x ρ ∧
      x - (η : ℝ) • y ∈ Metric.ball x ρ ∧
      z + (η : ℝ) • y ∈ Metric.ball x ρ ∧
      z - (η : ℝ) • y ∈ Metric.ball x ρ := by
  have hdist_nonneg : 0 ≤ dist z x := dist_nonneg
  have hη_lt : (η : ℝ) < ρ := by
    nlinarith [hdist_nonneg, (show (0 : ℝ) < (η : ℝ) from η.2), hclose]
  have hx_plus : x + (η : ℝ) • y ∈ Metric.ball x ρ := by
    -- The unit-sphere normalization identifies the translated distance with the step size.
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, norm_smul, hy,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ (η : ℝ) from η.2.le)] using hη_lt
  have hx_minus : x - (η : ℝ) • y ∈ Metric.ball x ρ := by
    -- The same estimate applies to the opposite endpoint because negation preserves the norm.
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, norm_smul, norm_neg, hy,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ (η : ℝ) from η.2.le)] using hη_lt
  have hz_plus : z + (η : ℝ) • y ∈ Metric.ball x ρ := by
    -- The triangle inequality compares the translated center `z + η • y` with the reference
    -- center `x` through `z`.
    rw [Metric.mem_ball]
    have htriangle : dist (z + (η : ℝ) • y) x ≤ dist (z + (η : ℝ) • y) z + dist z x :=
      dist_triangle (z + (η : ℝ) • y) z x
    have hdist_step : dist (z + (η : ℝ) • y) z = (η : ℝ) := by
      rw [dist_eq_norm]
      simp [sub_eq_add_neg, add_assoc, norm_smul, hy,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ (η : ℝ) from η.2.le)]
    linarith
  have hz_minus : z - (η : ℝ) • y ∈ Metric.ball x ρ := by
    -- The opposite translated endpoint is handled by the same triangle-inequality estimate.
    rw [Metric.mem_ball]
    have htriangle : dist (z - (η : ℝ) • y) x ≤ dist (z - (η : ℝ) • y) z + dist z x :=
      dist_triangle (z - (η : ℝ) • y) z x
    have hdist_step : dist (z - (η : ℝ) • y) z = (η : ℝ) := by
      rw [dist_eq_norm]
      simp [sub_eq_add_neg, norm_smul, norm_neg, hy,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ (η : ℝ) from η.2.le)]
    linarith
  exact ⟨hx_plus, hx_minus, hz_plus, hz_minus⟩

/-- Helper for Proposition 18 2: on a common Lipschitz ball, the fixed-step symmetric
second-difference quotient at a nearby center is controlled by the quotient at the original center
plus a Lipschitz error proportional to the center displacement. -/
private lemma symmetric_second_difference_toReal_le_of_lipschitz_perturbation
    (f : H → Set.Ioi (⊥ : EReal))
    {x z y : H} {ρ : ℝ} {β : NNReal}
    (hlip : LipschitzOnWith β (fun w ↦ (f w : EReal).toReal) (Metric.ball x ρ))
    (η : Set.Ioi (0 : ℝ))
    (hy : ‖y‖ = 1) (hclose : dist z x + (η : ℝ) < ρ) :
    (((f (z + (η : ℝ) • y) : EReal).toReal +
          (f (z - (η : ℝ) • y) : EReal).toReal -
          2 * (f z : EReal).toReal) / (η : ℝ)) ≤
      (((f (x + (η : ℝ) • y) : EReal).toReal +
            (f (x - (η : ℝ) • y) : EReal).toReal -
            2 * (f x : EReal).toReal) / (η : ℝ)) +
        (4 * (β : ℝ) * dist z x) / (η : ℝ) := by
  rcases sample_points_mem_ball_of_dist_add_lt (η := η) hy hclose with
    ⟨hx_plus, hx_minus, hz_plus, hz_minus⟩
  have hdist_nonneg : 0 ≤ dist z x := dist_nonneg
  have hz_ball : z ∈ Metric.ball x ρ := by
    -- The center itself lies in the Lipschitz ball because the step size is positive.
    rw [Metric.mem_ball]
    nlinarith [hdist_nonneg, (show (0 : ℝ) < (η : ℝ) from η.2), hclose]
  have hρ_pos : 0 < ρ := by
    have : 0 < dist z x + (η : ℝ) := by
      nlinarith [hdist_nonneg, (show (0 : ℝ) < (η : ℝ) from η.2)]
    linarith
  have hx_ball : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ_pos
  have hdist_plus : dist (z + (η : ℝ) • y) (x + (η : ℝ) • y) = dist z x := by
    -- Translating both endpoints by the same vector preserves the distance.
    rw [show z + (η : ℝ) • y = z - (-(η : ℝ) • y) by
      simp [sub_eq_add_neg]]
    rw [show x + (η : ℝ) • y = x - (-(η : ℝ) • y) by
      simp [sub_eq_add_neg]]
    exact dist_sub_right z x (-(η : ℝ) • y)
  have hdist_minus : dist (z - (η : ℝ) • y) (x - (η : ℝ) • y) = dist z x := by
    -- The same translation invariance applies to the negative endpoint.
    exact dist_sub_right z x ((η : ℝ) • y)
  have hplus_abs :
      |(f (z + (η : ℝ) • y) : EReal).toReal -
          (f (x + (η : ℝ) • y) : EReal).toReal| ≤
        (β : ℝ) * dist z x := by
    -- Apply the Lipschitz estimate to the positive translated pair.
    simpa [Real.dist_eq, hdist_plus] using
      hlip.dist_le_mul (z + (η : ℝ) • y) hz_plus (x + (η : ℝ) • y) hx_plus
  have hminus_abs :
      |(f (z - (η : ℝ) • y) : EReal).toReal -
          (f (x - (η : ℝ) • y) : EReal).toReal| ≤
        (β : ℝ) * dist z x := by
    -- Apply the Lipschitz estimate to the negative translated pair.
    simpa [Real.dist_eq, hdist_minus] using
      hlip.dist_le_mul (z - (η : ℝ) • y) hz_minus (x - (η : ℝ) • y) hx_minus
  have hcenter_abs :
      |(f z : EReal).toReal - (f x : EReal).toReal| ≤ (β : ℝ) * dist z x := by
    -- Apply the Lipschitz estimate to the centers themselves.
    simpa [Real.dist_eq] using hlip.dist_le_mul z hz_ball x hx_ball
  have hplus_le :
      (f (z + (η : ℝ) • y) : EReal).toReal ≤
        (f (x + (η : ℝ) • y) : EReal).toReal + (β : ℝ) * dist z x := by
    have hsub :
        (f (z + (η : ℝ) • y) : EReal).toReal -
            (f (x + (η : ℝ) • y) : EReal).toReal ≤
          (β : ℝ) * dist z x :=
      le_trans (le_abs_self _) hplus_abs
    linarith
  have hminus_le :
      (f (z - (η : ℝ) • y) : EReal).toReal ≤
        (f (x - (η : ℝ) • y) : EReal).toReal + (β : ℝ) * dist z x := by
    have hsub :
        (f (z - (η : ℝ) • y) : EReal).toReal -
            (f (x - (η : ℝ) • y) : EReal).toReal ≤
          (β : ℝ) * dist z x :=
      le_trans (le_abs_self _) hminus_abs
    linarith
  have hcenter_le :
      (f x : EReal).toReal - (f z : EReal).toReal ≤ (β : ℝ) * dist z x := by
    have hcenter_abs' :
        |(f x : EReal).toReal - (f z : EReal).toReal| ≤ (β : ℝ) * dist z x := by
      simpa [abs_sub_comm] using hcenter_abs
    exact le_trans (le_abs_self _) hcenter_abs'
  have hnum :
      (f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal ≤
        (f (x + (η : ℝ) • y) : EReal).toReal +
            (f (x - (η : ℝ) • y) : EReal).toReal -
            2 * (f x : EReal).toReal +
          4 * (β : ℝ) * dist z x := by
    -- Summing the three one-step estimates yields the source numerator perturbation bound.
    linarith
  -- Divide the numerator estimate by the positive step size to recover the quotient estimate.
  calc
    (((f (z + (η : ℝ) • y) : EReal).toReal +
          (f (z - (η : ℝ) • y) : EReal).toReal -
          2 * (f z : EReal).toReal) / (η : ℝ)) ≤
        ((f (x + (η : ℝ) • y) : EReal).toReal +
              (f (x - (η : ℝ) • y) : EReal).toReal -
              2 * (f x : EReal).toReal +
            4 * (β : ℝ) * dist z x) / (η : ℝ) := by
          exact (div_le_div_iff_of_pos_right (show (0 : ℝ) < (η : ℝ) from η.2)).2 hnum
    _ =
        (((f (x + (η : ℝ) • y) : EReal).toReal +
              (f (x - (η : ℝ) • y) : EReal).toReal -
              2 * (f x : EReal).toReal) / (η : ℝ)) +
          (4 * (β : ℝ) * dist z x) / (η : ℝ) := by
            field_simp [(show (η : ℝ) ≠ 0 from η.2.ne')]

/-- Helper for Proposition 18 2: a uniform spherewise quotient bound strictly below `ε` packages
directly into the owner predicate `HasSymmetricSecondDifferenceBound`. -/
private lemma hasSymmetricSecondDifferenceBound_of_forall_mem_sphere_quotient_lt_real
    (f : H → Set.Ioi (⊥ : EReal)) {z : H}
    (ε : Set.Ioi (0 : ℝ)) (η : Set.Ioi (0 : ℝ)) {M : ℝ} (hMε : M < (ε : ℝ))
    (hpointwise :
      ∀ y ∈ Metric.sphere (0 : H) 1,
        (((f (z + (η : ℝ) • y) : EReal) + (f (z - (η : ℝ) • y) : EReal) -
              2 * (f z : EReal)) / (η : ℝ)) <
          ((M : ℝ) : EReal)) :
    HasSymmetricSecondDifferenceBound f z ε := by
  let ε' : Set.Ioi (0 : ℝ) :=
    ⟨((max M 0) + (ε : ℝ)) / 2, by
      have hmax_nonneg : 0 ≤ max M 0 := le_max_right M 0
      exact div_pos (add_pos_of_nonneg_of_pos hmax_nonneg ε.2) zero_lt_two⟩
  have hε'lt : (ε' : ℝ) < (ε : ℝ) := by
    -- The midpoint between `max M 0` and `ε` stays strictly below `ε`.
    have hmax_lt : max M 0 < (ε : ℝ) := by
      exact max_lt_iff.mpr ⟨hMε, ε.2⟩
    dsimp [ε']
    linarith
  have hMleε' : (M : ℝ) ≤ (ε' : ℝ) := by
    -- The midpoint also lies above `M`, so it gives the uniform margin needed for the supremum.
    have hMlemax : (M : ℝ) ≤ max M 0 := le_max_left _ _
    have hmax_lt : max M 0 < (ε : ℝ) := by
      exact max_lt_iff.mpr ⟨hMε, ε.2⟩
    dsimp [ε']
    nlinarith
  refine (hasSymmetricSecondDifferenceBound_iff f z ε).mpr ?_
  refine ⟨η, ?_⟩
  have hsSup_le :
      sSup (symmetricSecondDifferenceQuotientSet f z η) ≤ (((ε' : ℝ) : EReal)) := by
    -- Bound each sampled quotient by the midpoint margin and pass to the supremum.
    refine sSup_le_iff.mpr ?_
    intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    exact (hpointwise y hy).le.trans (by exact_mod_cast hMleε')
  exact lt_of_le_of_lt hsSup_le (by exact_mod_cast hε'lt)

-- Proof sketch: for `x ∈ S_ε`, fix a witness `η > 0` with symmetric second-difference supremum
-- `σ < ε`. The source continuity datum `x ∈ cont f` already provides a ball contained in
-- `effectiveDomain f` and ambient continuity of the finite-valued representative there, so the
-- convex continuity theorem gives a Lipschitz bound on a smaller ball. Then Proposition 9.27
-- controls the same symmetric second-difference quotient at nearby points by `σ` plus a Lipschitz
-- error term, so a smaller ball around `x` remains in `S_ε`.
/-- Proposition 18 2: for a convex `]-∞,+∞]`-valued function, the set `S_ε` of continuity points
`x ∈ cont f` admitting some positive symmetric second-difference radius whose unit-sphere
supremum is strictly below `ε` is open. -/
theorem isOpen_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (ε : Set.Ioi (0 : ℝ)) :
    IsOpen (symmetricSecondDifferenceSublevelSet f ε) := by
  rw [Metric.isOpen_iff]
  intro x hx
  rcases (mem_symmetricSecondDifferenceSublevelSet_iff f ε x).mp hx with ⟨hxcont, hxbound⟩
  have hxdom : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hxcont
  rcases hxcont with ⟨ρ₀, hρ₀, hball₀, hcont₀⟩
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv hxdom
  have hlipBall :
      ∃ β : NNReal, ∃ ρ > 0,
        Metric.ball x ρ ⊆ effectiveDomain f ∧
          LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ) := by
    -- The source continuity witness is clause (2) in Theorem 8.38, so we can read off clause (1).
    have hcontBall :
        ∃ ρ > 0,
          Metric.ball x ρ ⊆ effectiveDomain f ∧
            ContinuousAt (fun z ↦ (f z : EReal).toReal) x := by
      exact ⟨ρ₀, hρ₀, hball₀, hcont₀⟩
    exact (List.TFAE.out htfae 1 0).mp hcontBall
  rcases hlipBall with ⟨β, ρ, hρ, hball, hlip⟩
  -- Route correction: the local regularity part is now settled. The remaining step is the
  -- source-faithful quantitative argument: shrink the original witness radius into the Lipschitz
  -- ball, use Proposition 9.27 to keep the symmetric second-difference bound at `x`, and then
  -- propagate that bound to nearby centers by a Lipschitz perturbation estimate.
  have hlocal_cont :
      ∀ z ∈ Metric.ball x ρ, z ∈ cont f := by
    intro z hz
    exact mem_cont_of_mem_ball_of_lipschitzOnWith_ball f hball hlip hz
  rcases (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ε).mp hxbound with
    ⟨η₀, ε₀, hε₀lt, hpointwise₀⟩
  have hquarter_pos : 0 < ρ / 4 := by
    positivity
  let η : Set.Ioi (0 : ℝ) := ⟨min (η₀ : ℝ) (ρ / 4), lt_min η₀.2 hquarter_pos⟩
  have hη_le_η₀ : (η : ℝ) ≤ (η₀ : ℝ) := by
    exact min_le_left _ _
  have hη_le_quarter : (η : ℝ) ≤ ρ / 4 := by
    exact min_le_right _ _
  have hη_lt_ρ : (η : ℝ) < ρ := by
    linarith
  let gap : ℝ := (ε : ℝ) - (ε₀ : ℝ)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  let δ : ℝ := min (ρ / 4) (((η : ℝ) * gap) / (8 * ((β : ℝ) + 1)))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · positivity
    · exact div_pos (mul_pos (show (0 : ℝ) < (η : ℝ) from η.2) hgap_pos) (by positivity)
  have hδ_le_quarter : δ ≤ ρ / 4 := by
    exact min_le_left _ _
  have hδ_upper :
      δ ≤ (((η : ℝ) * gap) / (8 * ((β : ℝ) + 1))) := by
    exact min_le_right _ _
  have hδ_lt_ρ : δ < ρ := by
    linarith
  have hβ_nonneg : 0 ≤ (β : ℝ) := by
    exact_mod_cast β.2
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_upper' :
      δ * (8 * ((β : ℝ) + 1)) ≤ (η : ℝ) * gap := by
    have hden_pos : 0 < 8 * ((β : ℝ) + 1) := by positivity
    exact (le_div_iff₀ hden_pos).1 hδ_upper
  have herror_le_halfgap :
      (4 * (β : ℝ) * δ) / (η : ℝ) ≤ gap / 2 := by
    have hnum :
        2 * (4 * (β : ℝ) * δ) ≤ (η : ℝ) * gap := by
      have hcoeff :
          2 * (4 * (β : ℝ) * δ) ≤ δ * (8 * ((β : ℝ) + 1)) := by
        nlinarith
      exact le_trans hcoeff hδ_upper'
    have hcross :
        4 * (β : ℝ) * δ ≤ (gap / 2) * (η : ℝ) := by
      nlinarith
    exact (div_le_iff₀ (show (0 : ℝ) < (η : ℝ) from η.2)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
  let M : ℝ := (ε₀ : ℝ) + (4 * (β : ℝ) * δ) / (η : ℝ)
  have hMε : M < (ε : ℝ) := by
    have hhalf_gap_lt_gap : gap / 2 < gap := by
      nlinarith
    dsimp [M, gap]
    linarith
  -- Package the quantitative witness into an explicit ball contained in the source sublevel set.
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hz
  have hzρ : z ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball] at hz ⊢
    linarith
  have hzcont : z ∈ cont f := hlocal_cont z hzρ
  have hzdom : z ∈ effectiveDomain f := hball hzρ
  refine (mem_symmetricSecondDifferenceSublevelSet_iff f ε z).2 ⟨hzcont, ?_⟩
  refine hasSymmetricSecondDifferenceBound_of_forall_mem_sphere_quotient_lt_real
    (f := f) (z := z) ε η hMε ?_
  intro y hy
  have hyNorm : ‖y‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using hy
  have hquot₀ :
      (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η₀ : ℝ)) <
        ((ε₀ : ℝ) : EReal) := by
    have hη₀_pos : (0 : EReal) < ((η₀ : ℝ) : EReal) := by
      exact_mod_cast η₀.2
    have hη₀_ne_top : ((η₀ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    exact (EReal.div_lt_iff hη₀_pos hη₀_ne_top).2 (by
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hpointwise₀ y hy)
  have hsample₀ :=
    sample_points_mem_effectiveDomain_of_symmetric_second_difference_lt f hxdom η₀ hquot₀
  rcases hsample₀ with ⟨hplus₀, hminus₀⟩
  have hplus :
      x + (η : ℝ) • y ∈ effectiveDomain f :=
    ray_point_mem_effectiveDomain_of_le f hconv hxdom η.2 hη_le_η₀ hplus₀
  have hminus :
      x - (η : ℝ) • y ∈ effectiveDomain f := by
    have hneg :
        x + (η : ℝ) • (-y) ∈ effectiveDomain f :=
      ray_point_mem_effectiveDomain_of_le f hconv hxdom η.2 hη_le_η₀ (by
        simpa [sub_eq_add_neg, smul_neg] using hminus₀)
    simpa [sub_eq_add_neg, smul_neg] using hneg
  have hmono :
      (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) ≤
        (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η₀ : ℝ)) := by
    exact symmetric_second_difference_le_of_le_step
      f hconv hxdom hη_le_η₀ hplus₀ hminus₀
  have hquotη :
      (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) <
        ((ε₀ : ℝ) : EReal) :=
    lt_of_le_of_lt hmono hquot₀
  have hquotη_real :
      (((f (x + (η : ℝ) • y) : EReal).toReal +
            (f (x - (η : ℝ) • y) : EReal).toReal -
            2 * (f x : EReal).toReal) / (η : ℝ)) <
        (ε₀ : ℝ) := by
    have hcast :
        (((((f (x + (η : ℝ) • y) : EReal).toReal +
              (f (x - (η : ℝ) • y) : EReal).toReal -
              2 * (f x : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) <
          ((ε₀ : ℝ) : EReal) := by
      simpa [symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
        f hxdom η hplus hminus] using hquotη
    exact_mod_cast hcast
  have hz_close : dist z x + (η : ℝ) < ρ := by
    rw [Metric.mem_ball] at hz
    linarith
  have hpert :=
    symmetric_second_difference_toReal_le_of_lipschitz_perturbation
      f hlip η hyNorm hz_close
  have hdist_le : dist z x ≤ δ := hz.le
  have herr_num :
      4 * (β : ℝ) * dist z x ≤ 4 * (β : ℝ) * δ := by
    exact mul_le_mul_of_nonneg_left hdist_le (by positivity)
  have herr_le :
      (4 * (β : ℝ) * dist z x) / (η : ℝ) ≤
        (4 * (β : ℝ) * δ) / (η : ℝ) := by
    exact (div_le_div_iff_of_pos_right (show (0 : ℝ) < (η : ℝ) from η.2)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using herr_num)
  have hquotz_real :
      (((f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal) / (η : ℝ)) < M := by
    have hsum_lt :
        (((f (x + (η : ℝ) • y) : EReal).toReal +
              (f (x - (η : ℝ) • y) : EReal).toReal -
              2 * (f x : EReal).toReal) / (η : ℝ)) +
            (4 * (β : ℝ) * dist z x) / (η : ℝ) < M := by
      dsimp [M]
      exact add_lt_add_of_lt_of_le hquotη_real herr_le
    exact lt_of_le_of_lt hpert hsum_lt
  rcases sample_points_mem_ball_of_dist_add_lt (η := η) hyNorm hz_close with
    ⟨-, -, hzplus_ball, hzminus_ball⟩
  have hzplus_dom : z + (η : ℝ) • y ∈ effectiveDomain f := hball hzplus_ball
  have hzminus_dom : z - (η : ℝ) • y ∈ effectiveDomain f := hball hzminus_ball
  have hquotz_cast :
      (((((f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) <
        ((M : ℝ) : EReal) := by
    exact_mod_cast hquotz_real
  simpa [symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
    f hzdom η hzplus_dom hzminus_dom] using hquotz_cast

end EkelandLebourgTheorem

end ERealFunction
