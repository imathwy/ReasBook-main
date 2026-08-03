import Mathlib
import BauschkeLean.Chap09.Proposition_9_27
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

open scoped InnerProductSpace

section ContinuitySet

variable {H : Type u} [NormedAddCommGroup H]

/- Source/core/bridge triage:
- `source-facing`: the textbook continuity set `cont f` records the ambient continuity points of
  the finite-valued representative together with the local effective-domain witness needed to avoid
  collapsing exterior `⊤` values through `EReal.toReal`.
- `core/canonical`: the primitive data are a positive ball contained in `effectiveDomain f` and
  ambient continuity of `fun y ↦ (f y : EReal).toReal`.
- `bridge/view`: Chapter 16's `ContinuousAtOnEffectiveDomain f x` is the restriction-level view
  obtained from a point of `cont f`.
-/

/-- The textbook continuity set `cont f`: points admitting a neighborhood contained in
`effectiveDomain f` on which the finite-valued representative of `f` is ambiently continuous. -/
def cont (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {x | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
    ContinuousAt (fun y ↦ (f y : EReal).toReal) x}

/-- Membership in `cont f` is exactly the source-facing local effective-domain continuity datum. -/
@[simp] theorem mem_cont_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ cont f ↔
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun y ↦ (f y : EReal).toReal) x :=
  Iff.rfl

/-- A point of `cont f` lies in the effective domain of `f`. -/
theorem mem_effectiveDomain_of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    x ∈ effectiveDomain f := by
  rcases hx with ⟨ρ, hρ, hball, _⟩
  exact hball (Metric.mem_ball_self hρ)

/-- A point of `cont f` is an interior point of the effective domain. -/
theorem mem_interior_effectiveDomain_of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    x ∈ interior (effectiveDomain f) := by
  rcases hx with ⟨ρ, hρ, hball, _⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hρ) hball

/-- The Chapter 16 continuity-on-the-effective-domain owner is the restricted view of a point of
`cont f`. -/
theorem ContinuousAtOnEffectiveDomain.of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    ContinuousAtOnEffectiveDomain f x := by
  rcases hx with ⟨ρ, hρ, hball, hcont⟩
  exact ⟨hball (Metric.mem_ball_self hρ), hcont.continuousWithinAt⟩

end ContinuitySet

section SymmetricSecondDifferences

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 18 1: a shorter ray point is the convex combination of the base point
and the longer ray point dictated by the ratio `α / β`. -/
private lemma ray_point_eq_convex_combination_endpoint
    (x y : H) {α β : ℝ} (hβ : 0 < β) :
    x + α • y = (α / β) • (x + β • y) + (1 - α / β) • x := by
  -- Rewrite the shorter ray point into the convex-combination form needed for shrinking
  -- effective-domain information along a convex ray.
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

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.1 characterizes Fréchet differentiability by small symmetric
  second differences on the unit sphere.
- `core/canonical`: the primitive Chapter 18 owner is the unit-sphere symmetric second-difference
  quotient set and its `ε`-sublevel predicate at a point.
- `bridge/view`: Proposition 18.2 packages that pointwise predicate into the open set `S_ε`.
-/

/-- The unit-sphere symmetric second-difference quotients of `f` at `x` with step size `η`. -/
noncomputable def symmetricSecondDifferenceQuotientSet
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (η : Set.Ioi (0 : ℝ)) : Set EReal :=
  (fun y : H ↦
      ((f (x + (η : ℝ) • y) : EReal) +
          (f (x - (η : ℝ) • y) : EReal) -
          2 * (f x : EReal)) /
        (η : ℝ)) '' Metric.sphere (0 : H) 1

/-- A point `x` satisfies the symmetric second-difference bound `ε` when some positive step size
controls the unit-sphere symmetric second-difference quotients strictly below `ε`. -/
noncomputable def HasSymmetricSecondDifferenceBound
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) : Prop :=
  ∃ η : Set.Ioi (0 : ℝ),
    sSup (symmetricSecondDifferenceQuotientSet f x η) < ((ε : ℝ) : EReal)

/-- Unfolding `HasSymmetricSecondDifferenceBound` yields the symmetric second-difference quotient
sublevel condition. -/
theorem hasSymmetricSecondDifferenceBound_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) :
    HasSymmetricSecondDifferenceBound f x ε ↔
      ∃ η : Set.Ioi (0 : ℝ),
        sSup (symmetricSecondDifferenceQuotientSet f x η) < ((ε : ℝ) : EReal) :=
  Iff.rfl

/-- The symmetric second-difference bound is equivalent to the source-facing pointwise unit-sphere
estimate. -/
theorem hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) :
    HasSymmetricSecondDifferenceBound f x ε ↔
      ∃ η : Set.Ioi (0 : ℝ), ∃ ε' : Set.Ioi (0 : ℝ), (ε' : ℝ) < (ε : ℝ) ∧
        ∀ y ∈ Metric.sphere (0 : H) 1,
          (f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
              2 * (f x : EReal) <
            ((((η : ℝ) * (ε' : ℝ) : ℝ) : EReal)) := by
  -- Route correction: the converse with the same tolerance `ε` is false in general, because a
  -- pointwise strict upper bound need only imply `sSup ≤ ε`. Introducing a smaller auxiliary
  -- tolerance records the uniform margin needed to recover the `sSup < ε` owner formulation.
  constructor
  · intro hbound
    rcases hbound with ⟨η, hη⟩
    let S := symmetricSecondDifferenceQuotientSet f x η
    -- Choose a positive finite EReal bound strictly between `max (sSup S) 0` and `ε`.
    have hmax_lt : max (sSup S) (0 : EReal) < ((ε : ℝ) : EReal) := by
      refine max_lt_iff.mpr ?_
      constructor
      · simpa [S] using hη
      · exact_mod_cast ε.2
    obtain ⟨δ, hδ_lower, hδ_upper⟩ := exists_between hmax_lt
    have hδ_pos : 0 < δ := lt_of_le_of_lt (le_max_right (sSup S) (0 : EReal)) hδ_lower
    have hδ_lt_top : δ < ⊤ := lt_of_lt_of_le hδ_upper le_top
    have hδ_ne_top : δ ≠ ⊤ := ne_of_lt hδ_lt_top
    have hδ_ne_bot : δ ≠ ⊥ := by
      have hbot_lt_zero : (⊥ : EReal) < 0 := by simp
      exact ne_of_gt (lt_trans hbot_lt_zero hδ_pos)
    let ε' : Set.Ioi (0 : ℝ) := ⟨δ.toReal, EReal.toReal_pos hδ_pos hδ_ne_top⟩
    have hε'_eq : (((ε' : ℝ) : EReal)) = δ := by
      dsimp [ε']
      simpa using (EReal.coe_toReal hδ_ne_top hδ_ne_bot)
    refine ⟨η, ε', ?_, ?_⟩
    · -- Convert the intermediate EReal bound back to a strictly smaller positive real tolerance.
      have hε'_lt : (((ε' : ℝ) : EReal)) < ((ε : ℝ) : EReal) := by
        simpa [hε'_eq] using hδ_upper
      exact EReal.coe_lt_coe_iff.mp hε'_lt
    · intro y hy
      -- Every sampled quotient lies below the chosen intermediary `δ`, hence below `η * ε'`.
      have hsample_le :
          (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
                2 * (f x : EReal)) /
              (η : ℝ)) ≤ sSup S := by
        apply le_sSup
        exact ⟨y, hy, rfl⟩
      have hsSup_lt : sSup S < ((ε' : ℝ) : EReal) := by
        have : sSup S < δ := lt_of_le_of_lt (le_max_left (sSup S) (0 : EReal)) hδ_lower
        simpa [hε'_eq] using this
      have hquot_lt :
          (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
                2 * (f x : EReal)) /
              (η : ℝ)) < ((ε' : ℝ) : EReal) :=
        lt_of_le_of_lt hsample_le hsSup_lt
      have hη_pos : (0 : EReal) < ((η : ℝ) : EReal) := by
        exact_mod_cast η.2
      have hη_ne_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hmul_lt :=
        (EReal.div_lt_iff hη_pos hη_ne_top).1 hquot_lt
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hmul_lt
  · rintro ⟨η, ε', hε'lt, hpointwise⟩
    refine ⟨η, ?_⟩
    let S := symmetricSecondDifferenceQuotientSet f x η
    -- The pointwise bound gives `sSup S ≤ ε'`, and the auxiliary margin `ε' < ε` then yields the
    -- strict owner bound `sSup S < ε`.
    have hsSup_le : sSup S ≤ ((ε' : ℝ) : EReal) := by
      refine sSup_le_iff.mpr ?_
      intro q hq
      rcases hq with ⟨y, hy, rfl⟩
      have hη_pos : (0 : EReal) < ((η : ℝ) : EReal) := by
        exact_mod_cast η.2
      have hη_ne_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hquot_lt :
          (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
                2 * (f x : EReal)) /
              (η : ℝ)) < ((ε' : ℝ) : EReal) :=
        (EReal.div_lt_iff hη_pos hη_ne_top).2 <|
          by simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hpointwise y hy
      exact hquot_lt.le
    exact lt_of_le_of_lt hsSup_le (by exact_mod_cast hε'lt)

/-- Helper for Proposition 18 1: a shorter point on a finite convex ray remains in the effective
domain. -/
private lemma ray_point_mem_effectiveDomain_of_le
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hβy : x + β • y ∈ effectiveDomain f) :
    x + α • y ∈ effectiveDomain f := by
  by_cases hEq : α = β
  · -- The endpoint case is immediate from the larger-step hypothesis.
    simpa [hEq] using hβy
  · have hlt : α < β := lt_of_le_of_ne hαβ hEq
    have hβ : 0 < β := lt_of_lt_of_le hα hαβ
    have hlam0 : 0 ≤ α / β := div_nonneg hα.le hβ.le
    have hlam1 : 0 ≤ 1 - α / β := by
      rw [sub_nonneg]
      exact (div_le_one hβ).2 hαβ
    have hlam_sum : α / β + (1 - α / β) = 1 := by ring
    -- Rewrite the shorter point into the convex-combination shape handled by convexity of the
    -- effective domain.
    rw [ray_point_eq_convex_combination_endpoint x y hβ]
    exact hconv.convex_effectiveDomain hβy hx hlam0 hlam1 hlam_sum

/-- Helper for Proposition 18 1: a strict real upper bound on the symmetric second-difference
quotient forces both sampled points to be finite. -/
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
  have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := rfl
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
    rw [hquot_top] at hquot
    exact (not_lt_of_ge le_top) hquot
  have hminus_top : (f (x - (η : ℝ) • y) : EReal) ≠ ⊤ := by
    intro htop
    have hquot_top :
        (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) = ⊤ := by
      rw [htop, EReal.add_top_of_ne_bot hplus_bot, EReal.top_sub htwo_top,
        EReal.top_div_of_pos_ne_top hη_pos hη_ne_top]
    rw [hquot_top] at hquot
    exact (not_lt_of_ge le_top) hquot
  constructor
  · -- The strict bound excludes the `⊤` branch at the positive sample.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top hplus_top
  · -- The same argument applies to the negative sample.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_ne le_top hminus_top

/-- Helper for Proposition 18 1: once the center and both samples are finite, the symmetric
second-difference quotient is the cast of the corresponding real quotient. -/
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
  have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := rfl
  -- Rewrite the finite `EReal` values as real casts and collapse the quotient to ordinary real
  -- algebra.
  rw [← EReal.coe_toReal hplus_top hplus_bot, ← EReal.coe_toReal hminus_top hminus_bot,
    htwo, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_div]
  simp

/-- Helper for Proposition 18 1: the directional difference quotient is the cast of the
corresponding real quotient at a finite sample. -/
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
  -- Finite endpoint values reduce the `EReal` quotient to the corresponding real difference
  -- quotient.
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hη_top hη_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 18 1: summing the directional difference quotients in directions `y`
and `-y` recovers the symmetric second-difference quotient. -/
private lemma symmetric_second_difference_quotient_eq_add_directional_quotients
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
  have hq_neg :=
    directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx (y := -y) η hminus'
  -- Convert both directional quotients to real casts and combine them into the symmetric form.
  calc
    directionalDifferenceQuotient f x y η + directionalDifferenceQuotient f x (-y) η =
        ((((f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (η : ℝ) +
            ((f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (η : ℝ) :
          ℝ) : EReal) := by
          rw [hq_pos, hq_neg, ← EReal.coe_add]
          simp [sub_eq_add_neg, smul_neg]
    _ =
        (((((f (x + (η : ℝ) • y) : EReal).toReal +
            (f (x - (η : ℝ) • y) : EReal).toReal -
            2 * (f x : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) := by
          have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt η.2
          congr 1
          field_simp [hη_ne]
          ring
    _ =
        (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η : ℝ)) := by
          symm
          exact symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain f hx η hplus hminus

/-- Helper for Proposition 18 1: shrinking the step along a fixed ray can only decrease the
symmetric second-difference quotient. -/
private lemma symmetric_second_difference_quotient_monotone
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
  -- Proposition 9.27 controls each directional quotient separately, and summing those controls
  -- the symmetric quotient.
  calc
    (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) =
      directionalDifferenceQuotient f x y η +
        directionalDifferenceQuotient f x (-y) η := by
          symm
          exact symmetric_second_difference_quotient_eq_add_directional_quotients
            f hx η hplus hminus
    _ ≤ directionalDifferenceQuotient f x y η₀ +
          directionalDifferenceQuotient f x (-y) η₀ := by
          exact add_le_add hmono_pos hmono_neg
    _ = (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
            2 * (f x : EReal)) / (η₀ : ℝ)) := by
          exact symmetric_second_difference_quotient_eq_add_directional_quotients
            f hx η₀ hplus₀ hminus₀

end SymmetricSecondDifferences

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 18 1: a subgradient at `x` yields the lower affine support inequality
in ordinary real form at every finite point `y`. -/
private lemma inner_le_sub_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  have hxy :
      (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff f x u).1 hu y
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hreal : ⟪y - x, u⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
    -- Move the `EReal` inequality to the finite real branch because both endpoint values are
    -- finite on the effective domain.
    have hcast :
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      calc
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) =
            (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
              rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
              simp
        _ ≤ (f y : EReal) := hxy
        _ = (((f y : EReal).toReal : ℝ) : EReal) := by
              exact (EReal.coe_toReal hy_top hy_bot).symm
    exact_mod_cast hcast
  linarith

omit [CompleteSpace H] in
/-- Helper for Proposition 18 1: one fixed subgradient controls the real first-order remainder by
the matching real symmetric second difference. -/
private lemma subgradient_remainder_le_symmetric_second_difference
    (f : H → Set.Ioi (⊥ : EReal)) {x u y : H}
    (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    (η : Set.Ioi (0 : ℝ))
    (hplus : x + (η : ℝ) • y ∈ effectiveDomain f)
    (hminus : x - (η : ℝ) • y ∈ effectiveDomain f) :
    0 ≤ (f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
        ⟪u, (η : ℝ) • y⟫_ℝ ∧
      (f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
          ⟪u, (η : ℝ) • y⟫_ℝ ≤
        (f (x + (η : ℝ) • y) : EReal).toReal +
            (f (x - (η : ℝ) • y) : EReal).toReal -
          2 * (f x : EReal).toReal := by
  have hplus_support :
      ⟪u, (η : ℝ) • y⟫_ℝ ≤
        (f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal := by
    -- Evaluate the real-form subgradient inequality at the forward sample.
    have hforward :
        ⟪x + (η : ℝ) • y - x, u⟫_ℝ ≤
          (f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal :=
      inner_le_sub_of_mem_subdifferential (x := x) (y := x + (η : ℝ) • y) hx hplus hu
    have hdisp : x + (η : ℝ) • y - x = (η : ℝ) • y := by
      abel_nf
    calc
      ⟪u, (η : ℝ) • y⟫_ℝ = ⟪x + (η : ℝ) • y - x, u⟫_ℝ := by
        rw [hdisp, real_inner_comm]
      _ ≤ (f (x + (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal := hforward
  have hminus_support :
      -⟪u, (η : ℝ) • y⟫_ℝ ≤
        (f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal := by
    -- Evaluate the same inequality at the backward sample so the linear term changes sign.
    have hbackward :
        ⟪x - (η : ℝ) • y - x, u⟫_ℝ ≤
          (f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal :=
      inner_le_sub_of_mem_subdifferential (x := x) (y := x - (η : ℝ) • y) hx hminus hu
    have hdisp : x - (η : ℝ) • y - x = -((η : ℝ) • y) := by
      abel_nf
    calc
      -⟪u, (η : ℝ) • y⟫_ℝ = ⟪x - (η : ℝ) • y - x, u⟫_ℝ := by
        rw [hdisp, inner_neg_left, real_inner_comm]
      _ ≤ (f (x - (η : ℝ) • y) : EReal).toReal - (f x : EReal).toReal := hbackward
  constructor
  · -- The forward sample already dominates the linear model, so the remainder is nonnegative.
    linarith
  · -- Adding the backward support inequality bounds the remainder by the symmetric difference.
    linarith

omit [CompleteSpace H] in
/-- Helper for Proposition 18 1: a witness-step symmetric second-difference bound controls the
normalized first-order remainder at every smaller nearby point. -/
private lemma normalized_remainder_lt_of_pointwise_symmetric_bound
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    (η₀ ε' : Set.Ioi (0 : ℝ))
    (hpointwise :
      ∀ y ∈ Metric.sphere (0 : H) 1,
        (f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
            2 * (f x : EReal) <
          ((((η₀ : ℝ) * (ε' : ℝ) : ℝ) : EReal))) :
    ∀ {z : H}, z ∈ Metric.ball x (η₀ : ℝ) →
      ‖z - x‖⁻¹ *
          ‖(f z : EReal).toReal - (f x : EReal).toReal - ⟪u, z - x⟫_ℝ‖ <
        (ε' : ℝ) := by
  intro z hz
  by_cases hzx : z = x
  · -- At the base point the normalized remainder vanishes exactly.
    subst hzx
    simpa using (show (0 : ℝ) < (ε' : ℝ) from ε'.2)
  · let t : Set.Ioi (0 : ℝ) := ⟨‖z - x‖, norm_pos_iff.mpr (sub_ne_zero.mpr hzx)⟩
    let y : H := (t : ℝ)⁻¹ • (z - x)
    have hy_norm : ‖y‖ = 1 := by
      -- Normalize the displacement to the unit sphere used in the source statement.
      have hzsub_ne : z - x ≠ 0 := sub_ne_zero.mpr hzx
      simpa [y] using norm_smul_inv_norm hzsub_ne
    have hy_sphere : y ∈ Metric.sphere (0 : H) 1 := by
      simpa [mem_sphere_zero_iff_norm] using hy_norm
    have hz_eq : z = x + (t : ℝ) • y := by
      -- Recover `z` as the ray point at step `t` in the normalized direction `y`.
      have hzsub_ne : ‖z - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzx)
      have hstep : (t : ℝ) • y = z - x := by
        dsimp [y, t]
        rw [smul_smul]
        simp [hzsub_ne]
      calc
        z = x + (z - x) := by abel_nf
        _ = x + (t : ℝ) • y := by rw [hstep.symm]
    have hz_norm : ‖z - x‖ = (t : ℝ) := by
      rfl
    have ht_le_η₀ : (t : ℝ) ≤ (η₀ : ℝ) := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact le_of_lt (by simpa [t] using hz)
    have hquot₀ :
        (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
              2 * (f x : EReal)) / (η₀ : ℝ)) <
          ((ε' : ℝ) : EReal) := by
      have hη₀_pos : (0 : EReal) < ((η₀ : ℝ) : EReal) := by
        exact_mod_cast η₀.2
      have hη₀_ne_top : ((η₀ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      exact (EReal.div_lt_iff hη₀_pos hη₀_ne_top).2 (by
        simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hpointwise y hy_sphere)
    have hsample₀ :=
      sample_points_mem_effectiveDomain_of_symmetric_second_difference_lt f hx η₀ hquot₀
    rcases hsample₀ with ⟨hplus₀, hminus₀⟩
    have hplus :
        x + (t : ℝ) • y ∈ effectiveDomain f :=
      ray_point_mem_effectiveDomain_of_le f hconv hx t.2 ht_le_η₀ hplus₀
    have hminus :
        x - (t : ℝ) • y ∈ effectiveDomain f := by
      have hneg :
          x + (t : ℝ) • (-y) ∈ effectiveDomain f :=
        ray_point_mem_effectiveDomain_of_le f hconv hx t.2 ht_le_η₀ (by
          simpa [sub_eq_add_neg, smul_neg] using hminus₀)
      simpa [sub_eq_add_neg, smul_neg] using hneg
    have hmono :
        (((f (x + (t : ℝ) • y) : EReal) + (f (x - (t : ℝ) • y) : EReal) -
              2 * (f x : EReal)) / (t : ℝ)) ≤
          (((f (x + (η₀ : ℝ) • y) : EReal) + (f (x - (η₀ : ℝ) • y) : EReal) -
              2 * (f x : EReal)) / (η₀ : ℝ)) := by
      exact symmetric_second_difference_quotient_monotone
        f hconv hx ht_le_η₀ hplus₀ hminus₀
    have hquot_t :
        (((f (x + (t : ℝ) • y) : EReal) + (f (x - (t : ℝ) • y) : EReal) -
              2 * (f x : EReal)) / (t : ℝ)) <
          ((ε' : ℝ) : EReal) :=
      lt_of_le_of_lt hmono hquot₀
    have hquot_t_real :
        (((f (x + (t : ℝ) • y) : EReal).toReal +
              (f (x - (t : ℝ) • y) : EReal).toReal -
              2 * (f x : EReal).toReal) / (t : ℝ)) <
          (ε' : ℝ) := by
      have hcast :
          (((((f (x + (t : ℝ) • y) : EReal).toReal +
                (f (x - (t : ℝ) • y) : EReal).toReal -
                2 * (f x : EReal).toReal) / (t : ℝ)) : ℝ) : EReal) <
            ((ε' : ℝ) : EReal) := by
        simpa [symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
          f hx t hplus hminus] using hquot_t
      exact_mod_cast hcast
    rcases
        subgradient_remainder_le_symmetric_second_difference
          f hx hu t hplus hminus with
      ⟨hrem_nonneg, hrem_le⟩
    have hrem_div_le :
        ((f (x + (t : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
            ⟪u, (t : ℝ) • y⟫_ℝ) / (t : ℝ) ≤
          ((f (x + (t : ℝ) • y) : EReal).toReal +
              (f (x - (t : ℝ) • y) : EReal).toReal -
            2 * (f x : EReal).toReal) / (t : ℝ) := by
      exact div_le_div_of_nonneg_right hrem_le t.2.le
    have hrem_lt :
        (t : ℝ)⁻¹ *
            ‖(f (x + (t : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
                ⟪u, (t : ℝ) • y⟫_ℝ‖ <
          (ε' : ℝ) := by
      have hdiv_lt :
          ((f (x + (t : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
              ⟪u, (t : ℝ) • y⟫_ℝ) / (t : ℝ) <
            (ε' : ℝ) := by
        exact lt_of_le_of_lt hrem_div_le hquot_t_real
      have habs :
          ‖(f (x + (t : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
              ⟪u, (t : ℝ) • y⟫_ℝ‖ =
            (f (x + (t : ℝ) • y) : EReal).toReal - (f x : EReal).toReal -
              ⟪u, (t : ℝ) • y⟫_ℝ := by
        rw [Real.norm_of_nonneg hrem_nonneg]
      simpa [div_eq_mul_inv, habs, mul_comm, mul_left_comm, mul_assoc] using hdiv_lt
    simpa [hz_eq, hy_norm, norm_smul, Real.norm_of_nonneg t.2.le] using hrem_lt

/-- Helper for Proposition 18 1: once one subgradient is fixed at `x`, the source symmetric
second-difference bounds force it to be the Fréchet gradient. -/
private lemma hasGradientAt_of_mem_subdifferential_of_forall_pos_hasSymmetricSecondDifferenceBound
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    (hbound : ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε) :
    HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := by
  rw [hasGradientAt_iff_tendsto, Metric.tendsto_nhds_nhds]
  intro ε hε
  rcases (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ⟨ε, hε⟩).mp
      (hbound ⟨ε, hε⟩) with
    ⟨η₀, ε', hε'lt, hpointwise⟩
  refine ⟨(η₀ : ℝ), η₀.2, ?_⟩
  intro z hz
  -- Apply the radial normalization lemma inside the witness ball and then weaken `ε' < ε`.
  have hz_ball : z ∈ Metric.ball x (η₀ : ℝ) := by
    simpa [Metric.mem_ball] using hz
  have hsmall :=
    normalized_remainder_lt_of_pointwise_symmetric_bound
      f hconv hx hu η₀ ε' hpointwise hz_ball
  have hnonneg :
      0 ≤ ‖z - x‖⁻¹ * ‖(f z : EReal).toReal - (f x : EReal).toReal - ⟪u, z - x⟫_ℝ‖ := by
    positivity
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using lt_trans hsmall hε'lt

-- Proof sketch: for the forward implication, `x ∈ cont f` supplies a ball on which the
-- finite-valued representative is an ambient convex real function, so Fréchet differentiability at
-- `x` gives a first-order expansion whose error is `o (‖h‖)`; evaluating it at `h = ± η y` and
-- adding cancels the linear part and yields the source-facing symmetric second-difference estimate
-- for every unit vector `y`. For the reverse implication, Proposition 16.17 applies at the
-- Chapter 16 bridge point `ContinuousAtOnEffectiveDomain.of_mem_cont hxcont` to provide a
-- subgradient at `x`; combine the subgradient inequality with the symmetric estimate and the
-- secant-slope monotonicity theorem in the radial direction to obtain the uniform little-o
-- remainder required for Fréchet differentiability.
/-- Proposition 18 1: for a convex `]-∞,+∞]`-valued function on a real Hilbert space, ambient
continuity at `x` in the source sense `x ∈ cont f` is equivalent to Fréchet differentiability of
the finite-valued representative at `x` together with the source symmetric second-difference
estimate at every positive tolerance. -/
theorem differentiableAt_toReal_iff_forall_pos_exists_pos_symmetricSecondDifference_lt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔
      ∀ ε : Set.Ioi (0 : ℝ), ∃ η : Set.Ioi (0 : ℝ), ∀ y : H, ‖y‖ = 1 →
        (f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal) <
          (((η : ℝ) * (ε : ℝ) : ℝ) : EReal) := by
  -- Route correction: after fixing the helper theorem above, the textbook statement is obtained
  -- from the owner-level `HasSymmetricSecondDifferenceBound` characterization by a standard
  -- epsilon-halving conversion in each direction.
  have howner :
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔
        ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε := by
    constructor
    · intro hdiff ε
      let g : H → ℝ := fun y ↦ (f y : EReal).toReal
      let u : H := gradient g x
      have hgrad : HasGradientAt g u x := by
        simpa [g, u] using hdiff.hasGradientAt
      have hxdom : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hxcont
      rcases hxcont with ⟨ρ, hρ, hball, hcontx⟩
      let εhalf : Set.Ioi (0 : ℝ) := ⟨(ε : ℝ) / 2, show 0 < (ε : ℝ) / 2 from half_pos ε.2⟩
      have hhalf_lt : (εhalf : ℝ) < (ε : ℝ) := by
        dsimp [εhalf]
        exact half_lt_self ε.2
      have hquarter_pos : 0 < ((εhalf : ℝ) / 2) := by
        exact half_pos εhalf.2
      rw [hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere]
      rw [hasGradientAt_iff_tendsto, Metric.tendsto_nhds_nhds] at hgrad
      obtain ⟨δ, hδ, hδbound⟩ := hgrad ((εhalf : ℝ) / 2) hquarter_pos
      let ηReal : ℝ := min (ρ / 2) (δ / 2)
      have hηReal_pos : 0 < ηReal := by
        dsimp [ηReal]
        exact lt_min (half_pos hρ) (half_pos hδ)
      let η : Set.Ioi (0 : ℝ) := ⟨ηReal, hηReal_pos⟩
      have hη_lt_ρ : (η : ℝ) < ρ := by
        dsimp [η, ηReal]
        have : min (ρ / 2) (δ / 2) ≤ ρ / 2 := min_le_left _ _
        linarith
      have hη_lt_δ : (η : ℝ) < δ := by
        dsimp [η, ηReal]
        have : min (ρ / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
        linarith
      refine ⟨η, εhalf, hhalf_lt, ?_⟩
      intro y hy
      have hyNorm : ‖y‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using hy
      let zplus : H := x + (η : ℝ) • y
      let zminus : H := x - (η : ℝ) • y
      have hzplus_dist : dist zplus x = (η : ℝ) := by
        dsimp [zplus]
        rw [dist_eq_norm, sub_eq_add_neg]
        have : x + (η : ℝ) • y + -x = (η : ℝ) • y := by abel_nf
        rw [this, norm_smul, hyNorm, Real.norm_of_nonneg η.2.le, mul_one]
      have hzminus_dist : dist zminus x = (η : ℝ) := by
        dsimp [zminus]
        rw [dist_eq_norm, sub_eq_add_neg]
        have : x - (η : ℝ) • y + -x = -((η : ℝ) • y) := by abel_nf
        rw [this, norm_neg, norm_smul, hyNorm, Real.norm_of_nonneg η.2.le, mul_one]
      have hzplus_ball : zplus ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball, hzplus_dist]
        exact hη_lt_ρ
      have hzminus_ball : zminus ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball, hzminus_dist]
        exact hη_lt_ρ
      have hplus_dom : zplus ∈ effectiveDomain f := hball hzplus_ball
      have hminus_dom : zminus ∈ effectiveDomain f := hball hzminus_ball
      have hzplus_small :
          ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ / (η : ℝ) < (εhalf : ℝ) / 2 := by
        have hbound := (hδbound (x := zplus)) (by simpa [hzplus_dist] using hη_lt_δ)
        have hnonneg :
            0 ≤ ‖zplus - x‖⁻¹ * ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ := by
          positivity
        simpa [Real.dist_eq, abs_of_nonneg hnonneg, div_eq_mul_inv, hzplus_dist, zplus, norm_smul,
          hyNorm, Real.norm_of_nonneg η.2.le, mul_comm, mul_one] using hbound
      have hzminus_small :
          ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ / (η : ℝ) < (εhalf : ℝ) / 2 := by
        have hbound := (hδbound (x := zminus)) (by simpa [hzminus_dist] using hη_lt_δ)
        have hnonneg :
            0 ≤ ‖zminus - x‖⁻¹ * ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ := by
          positivity
        simpa [Real.dist_eq, abs_of_nonneg hnonneg, div_eq_mul_inv, hzminus_dist, zminus,
          norm_smul, hyNorm, Real.norm_of_nonneg η.2.le, mul_comm, mul_one] using hbound
      have hzplus_abs :
          ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ < (η : ℝ) * ((εhalf : ℝ) / 2) := by
        have hlt :
            ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ < ((εhalf : ℝ) / 2) * (η : ℝ) :=
          (div_lt_iff₀ (show 0 < (η : ℝ) from η.2)).mp hzplus_small
        simpa [mul_comm] using hlt
      have hzminus_abs :
          ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ < (η : ℝ) * ((εhalf : ℝ) / 2) := by
        have hlt :
            ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ < ((εhalf : ℝ) / 2) * (η : ℝ) :=
          (div_lt_iff₀ (show 0 < (η : ℝ) from η.2)).mp hzminus_small
        simpa [mul_comm] using hlt
      have hsum_abs :
          ‖(g zplus - g x - ⟪u, zplus - x⟫_ℝ) +
              (g zminus - g x - ⟪u, zminus - x⟫_ℝ)‖ < (η : ℝ) * (εhalf : ℝ) := by
        have htriangle :
            ‖(g zplus - g x - ⟪u, zplus - x⟫_ℝ) +
                (g zminus - g x - ⟪u, zminus - x⟫_ℝ)‖ ≤
              ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ +
                ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ := norm_add_le _ _
        have hsum_lt :
            ‖g zplus - g x - ⟪u, zplus - x⟫_ℝ‖ +
                ‖g zminus - g x - ⟪u, zminus - x⟫_ℝ‖ <
              (η : ℝ) * ((εhalf : ℝ) / 2) + (η : ℝ) * ((εhalf : ℝ) / 2) := by
          exact add_lt_add hzplus_abs hzminus_abs
        have hsum_eq :
            (η : ℝ) * ((εhalf : ℝ) / 2) + (η : ℝ) * ((εhalf : ℝ) / 2) =
              (η : ℝ) * (εhalf : ℝ) := by
          ring
        refine lt_of_le_of_lt htriangle ?_
        simpa [hsum_eq] using hsum_lt
      have hcancel :
          (g zplus - g x - ⟪u, zplus - x⟫_ℝ) + (g zminus - g x - ⟪u, zminus - x⟫_ℝ) =
            g zplus + g zminus - 2 * g x := by
        dsimp [zplus, zminus]
        have hneg_inner : ⟪u, x - (η : ℝ) • y - x⟫_ℝ = -⟪u, (η : ℝ) • y⟫_ℝ := by
          have : x - (η : ℝ) • y - x = -((η : ℝ) • y) := by abel_nf
          rw [this, inner_neg_right]
        have hpos_inner : ⟪u, x + (η : ℝ) • y - x⟫_ℝ = ⟪u, (η : ℝ) • y⟫_ℝ := by
          have : x + (η : ℝ) • y - x = (η : ℝ) • y := by abel_nf
          rw [this]
        rw [hpos_inner, hneg_inner]
        ring
      have hraw_real_lt :
          (f zplus : EReal).toReal + (f zminus : EReal).toReal - 2 * (f x : EReal).toReal <
            (η : ℝ) * (εhalf : ℝ) := by
        have hle :
            (g zplus + g zminus - 2 * g x) ≤
              ‖(g zplus - g x - ⟪u, zplus - x⟫_ℝ) +
                  (g zminus - g x - ⟪u, zminus - x⟫_ℝ)‖ := by
          have := le_abs_self ((g zplus - g x - ⟪u, zplus - x⟫_ℝ) +
            (g zminus - g x - ⟪u, zminus - x⟫_ℝ))
          simpa [Real.norm_eq_abs, hcancel] using this
        exact lt_of_le_of_lt hle hsum_abs
      have hquot_real :
          (((f zplus : EReal).toReal + (f zminus : EReal).toReal -
                2 * (f x : EReal).toReal) / (η : ℝ)) < (εhalf : ℝ) := by
        exact (div_lt_iff₀ η.2).2 (by simpa [mul_comm] using hraw_real_lt)
      have hquot_ereal :
          (((f zplus : EReal) + (f zminus : EReal) - 2 * (f x : EReal)) / (η : ℝ)) <
            ((εhalf : ℝ) : EReal) := by
        calc
          (((f zplus : EReal) + (f zminus : EReal) - 2 * (f x : EReal)) / (η : ℝ)) =
              (((((f zplus : EReal).toReal + (f zminus : EReal).toReal -
                    2 * (f x : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) := by
                simpa [zplus, zminus] using
                  symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
                    f hxdom η hplus_dom hminus_dom
          _ < ((εhalf : ℝ) : EReal) := by
                exact_mod_cast hquot_real
      have hη_pos : (0 : EReal) < ((η : ℝ) : EReal) := by
        exact_mod_cast η.2
      have hη_ne_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc, zplus, zminus] using
        (EReal.div_lt_iff hη_pos hη_ne_top).1 hquot_ereal
    · intro hbound
      have hxdom : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hxcont
      rcases
          subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
            f hconv hxcont with
        ⟨⟨u, hu⟩, -⟩
      have hgrad :
          HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := by
        -- The source-faithful reverse route fixes one subgradient and upgrades it to the Fréchet
        -- gradient using the witness-step symmetric second-difference bounds at every tolerance.
        exact
          hasGradientAt_of_mem_subdifferential_of_forall_pos_hasSymmetricSecondDifferenceBound
            f hconv hxdom hu hbound
      exact hgrad.differentiableAt
  constructor
  · intro hdiff ε
    have hbound :
        HasSymmetricSecondDifferenceBound f x ε := (howner.mp hdiff) ε
    rcases (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ε).mp hbound with
      ⟨η, ε', hε'lt, hpointwise⟩
    refine ⟨η, ?_⟩
    intro y hy
    have hySphere : y ∈ Metric.sphere (0 : H) 1 := by
      simpa [mem_sphere_zero_iff_norm] using hy
    have hmul_le :
        ((((η : ℝ) * (ε' : ℝ) : ℝ) : EReal)) ≤ ((((η : ℝ) * (ε : ℝ) : ℝ) : EReal)) := by
      exact_mod_cast mul_le_mul_of_nonneg_left hε'lt.le (le_of_lt η.2)
    exact lt_of_lt_of_le (hpointwise y hySphere) hmul_le
  · intro hpointwise
    have hbound :
        ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε := by
      intro ε
      let εhalf : Set.Ioi (0 : ℝ) := ⟨(ε : ℝ) / 2, show 0 < (ε : ℝ) / 2 from half_pos ε.2⟩
      have hhalf : ∃ η : Set.Ioi (0 : ℝ), ∀ y : H, ‖y‖ = 1 →
          (f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
              2 * (f x : EReal) <
            (((η : ℝ) * (εhalf : ℝ) : ℝ) : EReal) := hpointwise εhalf
      rcases hhalf with ⟨η, hη⟩
      have hhalf_lt : (εhalf : ℝ) < (ε : ℝ) := by
        dsimp [εhalf]
        exact half_lt_self ε.2
      refine (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ε).mpr ?_
      refine ⟨η, εhalf, hhalf_lt, ?_⟩
      intro y hy
      have hyNorm : ‖y‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using hy
      exact hη y hyNorm
    exact howner.mpr hbound

end EkelandLebourgTheorem

end ERealFunction
