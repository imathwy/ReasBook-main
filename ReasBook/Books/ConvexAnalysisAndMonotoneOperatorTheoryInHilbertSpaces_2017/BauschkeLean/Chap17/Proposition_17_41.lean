import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open SetValuedOperator
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 17 41: Corollary 8.39 identifies the continuity set of a
`Γ₀(H)` function with the interior of its effective domain. -/
private lemma continuous_points_eq_interior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
      ContinuousAt (fun y ↦ (f y : EReal).toReal) x} = interior (effectiveDomain f) := by
  simpa using
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      f hf.2 (Or.inr (Or.inl hf.1))

/-- Helper for Proposition 17 41: interior effective-domain points of a `Γ₀(H)` function are
continuity points of its finite-valued restriction. -/
lemma continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ContinuousAtOnEffectiveDomain f x := by
  -- Corollary 8.39 identifies the interior effective domain with the continuity set.
  rw [← continuous_points_eq_interior_effectiveDomain_of_mem_gammaZero hf] at hx
  rcases hx with ⟨ρ, hρ, hball, hcont⟩
  exact ⟨hball (Metric.mem_ball_self hρ), hcont.continuousWithinAt⟩

/-- Helper for Proposition 17 41: from an interior effective-domain point, every fixed ray stays
inside the effective domain for sufficiently small positive times. -/
lemma eventually_mem_effectiveDomain_along_ray_of_mem_interior
    {f : H → Set.Ioi (⊥ : EReal)} {x d : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f := by
  -- Openness of the interior gives a ball around `x`, and continuity of the ray map enters that
  -- ball for all sufficiently small `α`.
  have hinterior : interior (effectiveDomain f) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  rcases Metric.mem_nhds_iff.mp hinterior with ⟨r, hr, hrball⟩
  have hcont : ContinuousAt (fun α : ℝ ↦ x + α • d) 0 := by
    simpa using (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hball_nhds : Metric.ball x r ∈ 𝓝 x := Metric.ball_mem_nhds x hr
  have hball_nhds0 : Metric.ball x r ∈ 𝓝 ((fun α : ℝ ↦ x + α • d) 0) := by
    simpa using hball_nhds
  have hevent_ball : ∀ᶠ α : ℝ in 𝓝 0, x + α • d ∈ Metric.ball x r := by
    exact hcont hball_nhds0
  have hevent_ball_within :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ Metric.ball x r :=
    nhdsWithin_le_nhds hevent_ball
  filter_upwards [hevent_ball_within] with α hα
  exact interior_subset (hrball hα)

/-- Helper for Proposition 17 41: every interior effective-domain point of a `Γ₀(H)` function is a
point where the subdifferential is nonempty. -/
lemma interior_effectiveDomain_subset_subdifferentialDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    interior (effectiveDomain f) ⊆ SetValuedOperator.dom (∂ f) := by
  intro x hx
  -- Interior-domain membership first yields the source continuity predicate from Proposition
  -- 16.27.
  have hxcont : ContinuousPoint f x :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  rcases
      subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
        f hf.2 hxcont with
    ⟨hxsub, -⟩
  rw [SetValuedOperator.mem_dom_iff]
  exact hxsub

/-- Helper for Proposition 17 41: a point of the subdifferential domain carries an actual
subgradient. -/
lemma exists_mem_subdifferential_of_mem_dom
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ SetValuedOperator.dom (∂ f)) :
    ∃ u : H, u ∈ (∂ f) x := by
  -- This is exactly the definition of membership in the domain of a set-valued operator.
  simpa [SetValuedOperator.mem_dom_iff] using hx

/-- Helper for Proposition 17 41: a subgradient at `x` gives the lower affine support inequality in
ordinary real form at every finite point `y`. -/
lemma inner_le_sub_of_mem_subdifferential
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
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
            = (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
                rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                simp
        _ ≤ (f y : EReal) := hxy
        _ = (((f y : EReal).toReal : ℝ) : EReal) := by
              exact (EReal.coe_toReal hy_top hy_bot).symm
    exact_mod_cast hcast
  linarith

/-- Helper for Proposition 17 41: a subgradient at `y` gives the matching upper affine support
inequality in ordinary real form when evaluated at `x`. -/
lemma sub_le_inner_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {x y v : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hv : v ∈ (∂ f) y) :
    (f y : EReal).toReal - (f x : EReal).toReal ≤ ⟪y - x, v⟫_ℝ := by
  have hswap :
      ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal :=
    inner_le_sub_of_mem_subdifferential (x := y) (y := x) hy hx hv
  have hneg : ⟪x - y, v⟫_ℝ = -⟪y - x, v⟫_ℝ := by
    have hxy : x - y = -(y - x) := by
      abel
    calc
      ⟪x - y, v⟫_ℝ = ⟪-(y - x), v⟫_ℝ := by rw [hxy]
      _ = -⟪y - x, v⟫_ℝ := by rw [inner_neg_left]
  have hswap' :
      -⟪y - x, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
    simpa [hneg] using hswap
  linarith

/-- Helper for Proposition 17 41: every actual subgradient lies over a finite point of `f`. -/
lemma effectiveDomain_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hu : u ∈ (∂ f) x) :
    x ∈ effectiveDomain f := by
  -- A concrete subgradient witnesses subdifferentiability, so Proposition 16.4 applies directly.
  exact SubdifferentiableAt.mem_effectiveDomain hf.2.nonempty ⟨u, hu⟩

/-- Helper for Proposition 17 41: a subgradient at `y` controls the gap between the Fréchet
remainders at `y` and at the shifted point `y + t • (v - u)`. -/
lemma remainder_gap_lower_bound_of_mem_subdifferential_step
    {f : H → Set.Ioi (⊥ : EReal)} {x y u v : H} {t : ℝ}
    (hy : y ∈ effectiveDomain f) (hz : y + t • (v - u) ∈ effectiveDomain f)
    (hv : v ∈ (∂ f) y) :
    t * ‖v - u‖ ^ 2 ≤
      ((f (y + t • (v - u)) : EReal).toReal - (f x : EReal).toReal -
          ⟪u, (y + t • (v - u)) - x⟫_ℝ) -
        ((f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ) := by
  -- Apply the real-form subgradient inequality at `y`, then isolate the quadratic term
  -- contributed by the special step `t • (v - u)`.
  have hsub :
      ⟪(y + t • (v - u)) - y, v⟫_ℝ ≤
        (f (y + t • (v - u)) : EReal).toReal - (f y : EReal).toReal :=
    inner_le_sub_of_mem_subdifferential (x := y) (y := y + t • (v - u)) hy hz hv
  have hquad :
      t * ‖v - u‖ ^ 2 =
        ⟪(y + t • (v - u)) - y, v⟫_ℝ - ⟪u, (y + t • (v - u)) - y⟫_ℝ := by
    have hstep : (y + t • (v - u)) - y = t • (v - u) := by
      abel_nf
    have hinner :
        ⟪v - u, v - u⟫_ℝ = ⟪v - u, v⟫_ℝ - ⟪u, v - u⟫_ℝ := by
      calc
        ⟪v - u, v - u⟫_ℝ = ⟪v - u, v⟫_ℝ - ⟪v - u, u⟫_ℝ := by
          rw [inner_sub_right]
        _ = ⟪v - u, v⟫_ℝ - ⟪u, v - u⟫_ℝ := by
          have hcomm : ⟪v - u, u⟫_ℝ = ⟪u, v - u⟫_ℝ := by
            rw [real_inner_comm]
          rw [hcomm]
    calc
      t * ‖v - u‖ ^ 2 = t * ⟪v - u, v - u⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      _ = t * (⟪v - u, v⟫_ℝ - ⟪u, v - u⟫_ℝ) := by rw [hinner]
      _ = t * ⟪v - u, v⟫_ℝ - t * ⟪u, v - u⟫_ℝ := by ring
      _ = ⟪t • (v - u), v⟫_ℝ - ⟪u, t • (v - u)⟫_ℝ := by
        rw [inner_smul_left, inner_smul_right]
        simp
      _ = ⟪(y + t • (v - u)) - y, v⟫_ℝ - ⟪u, (y + t • (v - u)) - y⟫_ℝ := by
        rw [hstep]
  have hcore :
      t * ‖v - u‖ ^ 2 ≤
        (f (y + t • (v - u)) : EReal).toReal - (f y : EReal).toReal -
          ⟪u, (y + t • (v - u)) - y⟫_ℝ := by
    linarith [hsub, hquad]
  have hrewrite :
      ((f (y + t • (v - u)) : EReal).toReal - (f x : EReal).toReal -
          ⟪u, (y + t • (v - u)) - x⟫_ℝ) -
        ((f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ) =
      (f (y + t • (v - u)) : EReal).toReal - (f y : EReal).toReal -
        ⟪u, (y + t • (v - u)) - y⟫_ℝ := by
    have hsplit : (y + t • (v - u)) - x = ((y + t • (v - u)) - y) + (y - x) := by
      abel_nf
    rw [hsplit, inner_add_right]
    ring
  rw [hrewrite]
  exact hcore

/-- Helper for Proposition 17 41: `HasGradientAt` gives the quantitative ballwise remainder bound
needed in the source Fréchet argument. -/
lemma frechet_remainder_bound_on_ball
    {f : H → Set.Ioi (⊥ : EReal)} {x u : H}
    (hgrad : HasGradientAt (fun y ↦ (f y : EReal).toReal) u x) :
    ∀ κ > 0, ∃ η > 0, ∀ y ∈ Metric.ball x η,
      ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ ≤ κ * ‖y - x‖ := by
  intro κ hκ
  -- Unpack the Fréchet gradient into the normalized remainder estimate from mathlib.
  rw [hasGradientAt_iff_tendsto, Metric.tendsto_nhds_nhds] at hgrad
  rcases hgrad κ hκ with ⟨η, hηpos, hηbound⟩
  refine ⟨η, hηpos, ?_⟩
  intro y hy
  by_cases hxy : y = x
  · -- At the base point the remainder vanishes, so the bound is trivial.
    subst hxy
    simp
  · -- Away from `x`, divide by `‖y - x‖` and then clear the positive denominator.
    have hy_norm_pos : 0 < ‖y - x‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hprod_nonneg :
        0 ≤ ‖y - x‖⁻¹ *
            ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ := by
      positivity
    have hquot_lt :
        ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ / ‖y - x‖ < κ := by
      have hy_dist : dist y x < η := by
        simpa [Metric.mem_ball] using hy
      have hdist_lt := hηbound hy_dist
      simpa [Real.dist_eq, abs_of_nonneg hprod_nonneg, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hdist_lt
    exact (div_le_iff₀ hy_norm_pos).mp (le_of_lt hquot_lt)

/-- Helper for Proposition 17 41: Proposition 16.17 local boundedness can be converted into a
uniform scalar norm bound on every nearby subgradient. -/
lemma subgradient_norm_bound_on_small_ball_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∃ ρ > 0, ∃ M > 0, ∀ y ∈ Metric.ball x ρ, ∀ v ∈ (∂ f) y, ‖v‖ ≤ M := by
  -- Read the bounded union of nearby fibers through a single closed ball around the origin.
  have hxcont : ContinuousPoint f x :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  rcases
      subdifferential_ball_union_bounded_of_continuousPoint
        f hf.2 hxcont with
    ⟨ρ, hρpos, hbounded⟩
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : H)
  refine ⟨ρ, hρpos, max R 0 + 1, by positivity, ?_⟩
  intro y hy v hv
  have hvUnion : v ∈ ⋃ y' ∈ Metric.ball x ρ, (∂ f) y' := by
    exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hv⟩⟩
  have hvBall : v ∈ Metric.closedBall (0 : H) R := hR hvUnion
  rw [Metric.mem_closedBall, dist_eq_norm] at hvBall
  have hvNorm : ‖v‖ ≤ R := by simpa using hvBall
  linarith [hvNorm, le_max_left R 0]

/-- Helper for Proposition 17 41: the source step point
`y + (δ / B) • (v - u)` stays in the target ball when `y` is close to `x` and
`‖v - u‖ ≤ B`. -/
lemma step_point_dist_le_two_mul_delta_of_norm_sub_le
    {x y u v : H} {δ B : ℝ}
    (hy : y ∈ Metric.ball x δ) (hB : 0 < B) (hvu : ‖v - u‖ ≤ B) :
    dist (y + (δ / B) • (v - u)) x ≤ 2 * δ := by
  -- The step has norm at most `δ`, so the triangle inequality gives an exact `2 * δ` bound.
  have hy_dist : dist y x < δ := by
    simpa [Metric.mem_ball] using hy
  have hy_norm_le : ‖y - x‖ ≤ δ := by
    simpa [dist_eq_norm] using hy_dist.le
  have hδ_nonneg : 0 ≤ δ := le_trans (norm_nonneg (y - x)) hy_norm_le
  have hstep_eq : (δ / B) * B = δ := by
    field_simp [hB.ne']
  have hstep_norm_le : ‖(δ / B) • (v - u)‖ ≤ δ := by
    calc
      ‖(δ / B) • (v - u)‖ = |δ / B| * ‖v - u‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (δ / B) * ‖v - u‖ := by
            rw [abs_of_nonneg (div_nonneg hδ_nonneg hB.le)]
      _ ≤ (δ / B) * B := mul_le_mul_of_nonneg_left hvu (div_nonneg hδ_nonneg hB.le)
      _ = δ := hstep_eq
  have hsub :
      y + (δ / B) • (v - u) - x = (y - x) + (δ / B) • (v - u) := by
    abel_nf
  calc
    dist (y + (δ / B) • (v - u)) x = ‖y + (δ / B) • (v - u) - x‖ := by rw [dist_eq_norm]
    _ = ‖(y - x) + (δ / B) • (v - u)‖ := by rw [hsub]
    _ ≤ ‖y - x‖ + ‖(δ / B) • (v - u)‖ := norm_add_le _ _
    _ ≤ δ + δ := add_le_add hy_norm_le hstep_norm_le
    _ = 2 * δ := by ring

/-- Helper for Proposition 17 41: the source step point
`y + (δ / B) • (v - u)` lies in the ball `Metric.ball x η` whenever the doubled radius
`2 * δ` is still below `η`. -/
lemma step_point_mem_ball_of_norm_sub_le
    {x y u v : H} {δ B η : ℝ}
    (hy : y ∈ Metric.ball x δ) (hB : 0 < B) (hvu : ‖v - u‖ ≤ B)
    (hsmall : 2 * δ < η) :
    y + (δ / B) • (v - u) ∈ Metric.ball x η := by
  -- The step has norm at most `δ`, so the triangle inequality keeps the new point in range.
  rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
  have hδ_nonneg : 0 ≤ δ := le_trans (norm_nonneg (y - x)) hy.le
  have hstep_eq : (δ / B) * B = δ := by
    field_simp [hB.ne']
  have hstep_norm_le : ‖(δ / B) • (v - u)‖ ≤ δ := by
    calc
      ‖(δ / B) • (v - u)‖ = |δ / B| * ‖v - u‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (δ / B) * ‖v - u‖ := by
            rw [abs_of_nonneg (div_nonneg hδ_nonneg hB.le)]
      _ ≤ (δ / B) * B := mul_le_mul_of_nonneg_left hvu (div_nonneg hδ_nonneg hB.le)
      _ = δ := hstep_eq
  have hsub :
      y + (δ / B) • (v - u) - x = (y - x) + (δ / B) • (v - u) := by
    abel_nf
  calc
    ‖y + (δ / B) • (v - u) - x‖ = ‖(y - x) + (δ / B) • (v - u)‖ := by rw [hsub]
    _ ≤ ‖y - x‖ + ‖(δ / B) • (v - u)‖ := norm_add_le _ _
    _ ≤ δ + δ := add_le_add hy.le hstep_norm_le
    _ = 2 * δ := by ring
    _ < η := hsmall

/-- Helper for Proposition 17 41: the step-gap lower bound and the Fréchet remainder bounds force
the subgradient gap norm to be small. -/
lemma lt_of_step_gap_and_remainder_bounds
    {a δ B κ ε Ry Rz : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hB : 0 < B) (hε : 0 < ε)
    (hgap : (δ / B) * a ^ 2 ≤ Rz - Ry)
    (hRy : |Ry| ≤ κ * δ) (hRz : |Rz| ≤ 2 * κ * δ)
    (hkappa : 4 * κ * B < ε ^ 2) :
    a < ε := by
  -- The absolute-value bounds force `κ` to be nonnegative because `δ > 0`.
  have hkappa_nonneg : 0 ≤ κ := by
    have hκδ_nonneg : 0 ≤ κ * δ := le_trans (abs_nonneg Ry) hRy
    nlinarith
  -- The remainder gap is at most the sum of the two absolute-value bounds.
  have hgap_upper : Rz - Ry ≤ 3 * κ * δ := by
    have hRz_upper : Rz ≤ |Rz| := le_abs_self Rz
    have hRy_upper : -Ry ≤ |Ry| := by simpa using neg_le_abs Ry
    nlinarith
  -- Clearing the denominator shows `a^2` is strictly below `ε^2`.
  have ha_sq_lt : a ^ 2 < ε ^ 2 := by
    have hmul :
        δ * a ^ 2 ≤ B * (Rz - Ry) := by
      have hmul_raw := mul_le_mul_of_nonneg_right hgap hB.le
      simpa [div_eq_mul_inv, hB.ne', mul_assoc, mul_left_comm, mul_comm] using hmul_raw
    have hupper_scaled : B * (Rz - Ry) ≤ 3 * κ * B * δ := by
      nlinarith
    have ha_sq_le : a ^ 2 ≤ 3 * κ * B := by
      nlinarith
    have hthree_le_four : 3 * κ * B ≤ 4 * κ * B := by
      nlinarith
    exact lt_of_le_of_lt (le_trans ha_sq_le hthree_le_four) hkappa
  -- With `a ≥ 0` and `ε > 0`, the square inequality gives the desired strict inequality.
  nlinarith

/-- Helper for Proposition 17 41: Fréchet differentiability at `x` should force nearby
subdifferentials to lie in arbitrarily small norm balls around the unique subgradient `u`. -/
lemma subdifferential_subset_closedBall_of_hasGradientAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hgrad : HasGradientAt (fun y ↦ (f y : EReal).toReal) u x) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, (∂ f) y ⊆ Metric.closedBall u ε := by
  intro ε hε
  -- Route correction: keep the textbook step-point argument and isolate the geometry and real
  -- arithmetic into the two helper lemmas above.
  have hinterior : interior (effectiveDomain f) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  rcases Metric.mem_nhds_iff.mp hinterior with ⟨rdom, hrdom_pos, hrdom_ball⟩
  have hrdom_subset : Metric.ball x rdom ⊆ effectiveDomain f := fun y hy ↦
    interior_subset (hrdom_ball hy)
  rcases subgradient_norm_bound_on_small_ball_of_mem_interior_effectiveDomain hf hx with
    ⟨ρ, hρ_pos, M, hM_pos, hMbound⟩
  let B : ℝ := max 1 (M + ‖u‖)
  have hB : 0 < B := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (M + ‖u‖))
  let κ : ℝ := ε ^ 2 / (8 * B)
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    have h8B_pos : 0 < 8 * B := by positivity
    exact div_pos (sq_pos_of_pos hε) h8B_pos
  have hκ_small : 4 * κ * B < ε ^ 2 := by
    have hcalc : 4 * κ * B = ε ^ 2 / 2 := by
      dsimp [κ]
      field_simp [hB.ne']
      ring
    rw [hcalc]
    nlinarith [sq_pos_of_pos hε]
  rcases frechet_remainder_bound_on_ball hgrad κ hκ_pos with ⟨η, hη_pos, hηbound⟩
  let δ : ℝ := min ρ (min (rdom / 4) (η / 4))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min hρ_pos ?_
    refine lt_min ?_ ?_
    · nlinarith [hrdom_pos]
    · nlinarith [hη_pos]
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy v hv
  -- Keep the source data fixed: bound `v`, build the step point `z`, then compare remainders.
  have hy_dist : dist y x < δ := by
    simpa [Metric.mem_ball] using hy
  have hy_norm_le : ‖y - x‖ ≤ δ := by
    simpa [dist_eq_norm] using hy_dist.le
  have hyρ : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball] at hy ⊢
    exact lt_of_lt_of_le hy (min_le_left ρ (min (rdom / 4) (η / 4)))
  have hyM : ‖v‖ ≤ M := hMbound y hyρ v hv
  have hvuB : ‖v - u‖ ≤ B := by
    calc
      ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ M + ‖u‖ := add_le_add hyM le_rfl
      _ ≤ B := le_max_right 1 (M + ‖u‖)
  have hδ_le_rdom_quarter : δ ≤ rdom / 4 := by
    dsimp [δ]
    exact le_trans (min_le_right ρ (min (rdom / 4) (η / 4))) (min_le_left (rdom / 4) (η / 4))
  have hδ_le_eta_quarter : δ ≤ η / 4 := by
    dsimp [δ]
    exact le_trans (min_le_right ρ (min (rdom / 4) (η / 4))) (min_le_right (rdom / 4) (η / 4))
  have htwoδ_lt_rdom : 2 * δ < rdom := by
    nlinarith [hδ_le_rdom_quarter, hrdom_pos]
  have htwoδ_lt_eta : 2 * δ < η := by
    nlinarith [hδ_le_eta_quarter, hη_pos]
  let z : H := y + (δ / B) • (v - u)
  have hz_ball_dom : z ∈ Metric.ball x rdom := by
    simpa [z] using
      step_point_mem_ball_of_norm_sub_le (x := x) (y := y) (u := u) (v := v)
        hy hB hvuB htwoδ_lt_rdom
  have hz_ball_eta : z ∈ Metric.ball x η := by
    simpa [z] using
      step_point_mem_ball_of_norm_sub_le (x := x) (y := y) (u := u) (v := v)
        hy hB hvuB htwoδ_lt_eta
  have hz_dist_le : dist z x ≤ 2 * δ := by
    simpa [z] using
      step_point_dist_le_two_mul_delta_of_norm_sub_le (x := x) (y := y) (u := u) (v := v)
        hy hB hvuB
  have hy_eff : y ∈ effectiveDomain f := effectiveDomain_of_mem_subdifferential hf hv
  have hz_eff : z ∈ effectiveDomain f := hrdom_subset hz_ball_dom
  let Ry : ℝ := (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ
  let Rz : ℝ := (f z : EReal).toReal - (f x : EReal).toReal - ⟪u, z - x⟫_ℝ
  have hy_ball_eta : y ∈ Metric.ball x η := by
    rw [Metric.mem_ball] at hy ⊢
    exact lt_trans
      (lt_of_lt_of_le hy hδ_le_eta_quarter)
      (by nlinarith [hη_pos])
  have hRy_abs : |Ry| ≤ κ * δ := by
    have hnorm : ‖Ry‖ ≤ κ * δ := by
      have hbase :=
        hηbound y hy_ball_eta
      simpa [Ry] using
        calc
          ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ ≤ κ * ‖y - x‖ := hbase
          _ ≤ κ * δ := mul_le_mul_of_nonneg_left hy_norm_le hκ_pos.le
    simpa [Real.norm_eq_abs] using hnorm
  have hRz_abs : |Rz| ≤ 2 * κ * δ := by
    have hnorm : ‖Rz‖ ≤ 2 * κ * δ := by
      have hbase :=
        hηbound z hz_ball_eta
      simpa [Rz] using
        calc
          ‖(f z : EReal).toReal - (f x : EReal).toReal - ⟪u, z - x⟫_ℝ‖ ≤ κ * ‖z - x‖ := hbase
          _ = κ * dist z x := by rw [dist_eq_norm]
          _ ≤ κ * (2 * δ) := mul_le_mul_of_nonneg_left hz_dist_le hκ_pos.le
          _ = 2 * κ * δ := by ring
    simpa [Real.norm_eq_abs] using hnorm
  have hgap :
      (δ / B) * ‖v - u‖ ^ 2 ≤ Rz - Ry := by
    simpa [z, Ry, Rz] using
      remainder_gap_lower_bound_of_mem_subdifferential_step
        (x := x) (y := y) (u := u) (v := v) (t := δ / B) hy_eff hz_eff hv
  have hvu_lt : ‖v - u‖ < ε := by
    exact
      lt_of_step_gap_and_remainder_bounds
        (a := ‖v - u‖) (δ := δ) (B := B) (κ := κ) (ε := ε) (Ry := Ry) (Rz := Rz)
        (norm_nonneg _) hδ_pos hB hε hgap hRy_abs hRz_abs hκ_small
  -- Membership in the closed ball is exactly the norm bound on `v - u`.
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hvu_lt.le

/-- Helper for Proposition 17 41: once every nearby fiber lies in arbitrarily small balls around
`u`, the fiber at `x` itself must be the singleton `{u}`. -/
lemma subdifferential_eq_singleton_of_hasGradientAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hgrad : HasGradientAt (fun y ↦ (f y : EReal).toReal) u x) :
    (∂ f) x = ({u} : Set H) := by
  -- Recover the singleton fiber by specializing the nearby closed-ball estimate at `y = x`.
  have hsubset : (∂ f) x ⊆ ({u} : Set H) := by
    intro v hv
    by_cases hvu : v = u
    · rw [Set.mem_singleton_iff]
      exact hvu
    · have hdist_pos : 0 < dist v u := dist_pos.mpr hvu
      rcases
          subdifferential_subset_closedBall_of_hasGradientAt hf hx hgrad
            (dist v u / 2) (by positivity) with
        ⟨δ, hδpos, hδball⟩
      have hvball : v ∈ Metric.closedBall u (dist v u / 2) := by
        have hxball : x ∈ Metric.ball x δ := Metric.mem_ball_self hδpos
        exact hδball x hxball hv
      have hvle : dist v u ≤ dist v u / 2 := by
        simpa [Metric.mem_closedBall] using hvball
      exfalso
      linarith
  apply Set.Subset.antisymm hsubset
  have hxdom : x ∈ SetValuedOperator.dom (∂ f) :=
    interior_effectiveDomain_subset_subdifferentialDomain_of_mem_gammaZero hf hx
  rcases exists_mem_subdifferential_of_mem_dom hxdom with ⟨w, hw⟩
  have hw_eq_u : w = u := by
    have hw_single : w ∈ ({u} : Set H) := hsubset hw
    simpa using hw_single
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  simpa [hv, hw_eq_u] using hw

/-- Helper for Proposition 17 41: comparing the two affine support inequalities squeezes the
Fréchet remainder between `0` and a norm product. -/
lemma remainder_norm_le_norm_mul_of_two_subgradients
    {f : H → Set.Ioi (⊥ : EReal)} {x y u v : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hu : u ∈ (∂ f) x) (hv : v ∈ (∂ f) y) :
    0 ≤ (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ ∧
      ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖
        ≤ ‖y - x‖ * ‖v - u‖ := by
  -- The lower support at `x` gives nonnegativity of the remainder.
  have hlower :
      ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal :=
    inner_le_sub_of_mem_subdifferential hx hy hu
  -- The upper support at `y` bounds the same remainder by the inner product against `v - u`.
  have hupper :
      (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ ≤
        ⟪y - x, v - u⟫_ℝ := by
    have hupper' :
        (f y : EReal).toReal - (f x : EReal).toReal ≤ ⟪y - x, v⟫_ℝ :=
      sub_le_inner_of_mem_subdifferential hx hy hv
    have hupper_sub :
        (f y : EReal).toReal - (f x : EReal).toReal - ⟪y - x, u⟫_ℝ ≤
          ⟪y - x, v⟫_ℝ - ⟪y - x, u⟫_ℝ :=
      sub_le_sub_right hupper' _
    calc
      (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ
          = (f y : EReal).toReal - (f x : EReal).toReal - ⟪y - x, u⟫_ℝ := by
              rw [real_inner_comm]
      _ ≤ ⟪y - x, v⟫_ℝ - ⟪y - x, u⟫_ℝ := hupper_sub
      _ = ⟪y - x, v - u⟫_ℝ := by rw [inner_sub_right]
  have hnonneg :
      0 ≤ (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ := by
    exact sub_nonneg.mpr (by simpa [real_inner_comm] using hlower)
  refine ⟨hnonneg, ?_⟩
  -- Convert the upper bound into a norm bound using Cauchy-Schwarz.
  rw [Real.norm_of_nonneg hnonneg]
  exact hupper.trans (real_inner_le_norm (y - x) (v - u))

/-- Helper for Proposition 17 41: a norm-continuous local selection of `∂ f` at an interior
effective-domain point yields Fréchet differentiability there. -/
lemma differentiableAt_of_exists_selectionContinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsel :
      ∃ G : Selection (∂ f),
        SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
  rcases hsel with ⟨G, hG⟩
  let x0 : (∂ f).dom :=
    ⟨x, interior_effectiveDomain_subset_subdifferentialDomain_of_mem_gammaZero hf hx⟩
  let u : H := (G x0 : H)
  have hcont : ContinuousAt (fun z : (∂ f).dom ↦ (G z : H)) x0 := hG x0.2
  have hxeff : x ∈ effectiveDomain f := interior_subset hx
  have hu : u ∈ (∂ f) x := by
    dsimp [u]
    exact selection_apply_mem G x0
  have hgrad : HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := by
    -- Route correction: use the textbook remainder sandwich
    -- `0 ≤ R_x(y) ≤ ‖y - x‖ * ‖G y - u‖` and continuity of the selection.
    rw [hasGradientAt_iff_tendsto]
    rw [Metric.tendsto_nhds_nhds]
    intro ε hε
    rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx) with ⟨ρ, hρpos, hρball⟩
    rw [Metric.continuousAt_iff] at hcont
    rcases hcont ε hε with ⟨δ, hδpos, hδbound⟩
    refine ⟨min ρ δ, lt_min hρpos hδpos, ?_⟩
    intro y hy
    by_cases hxy : y = x
    · -- The normalized remainder vanishes exactly at the base point.
      subst hxy
      simpa [u] using hε
    · have hyball : dist y x < min ρ δ := by
        simpa [Metric.mem_ball] using hy
      have hyρ : y ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball]
        exact (lt_min_iff.mp hyball).1
      have hyδ : y ∈ Metric.ball x δ := by
        rw [Metric.mem_ball]
        exact (lt_min_iff.mp hyball).2
      have hyint : y ∈ interior (effectiveDomain f) := hρball hyρ
      have hyDom : y ∈ (∂ f).dom :=
        interior_effectiveDomain_subset_subdifferentialDomain_of_mem_gammaZero hf hyint
      let y0 : (∂ f).dom := ⟨y, hyDom⟩
      have hy0_ball : y0 ∈ Metric.ball x0 δ := by
        simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hyδ
      have hGy_lt : ‖(G y0 : H) - u‖ < ε := by
        have hy0_dist : dist y0 x0 < δ := by
          simpa [Metric.mem_ball] using hy0_ball
        simpa [u, x0, y0, dist_eq_norm] using hδbound hy0_dist
      have hyeff : y ∈ effectiveDomain f := interior_subset hyint
      have hv : (G y0 : H) ∈ (∂ f) y := by
        exact selection_apply_mem G y0
      have hrem :=
        remainder_norm_le_norm_mul_of_two_subgradients hxeff hyeff hu hv
      have hy_norm_pos : 0 < ‖y - x‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hquot_le :
          ‖y - x‖⁻¹ *
              ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ ≤
            ‖(G y0 : H) - u‖ := by
        have hdiv_le :
            ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ / ‖y - x‖ ≤
              ‖(G y0 : H) - u‖ := by
          refine (div_le_iff₀ hy_norm_pos).2 ?_
          simpa [mul_comm, mul_left_comm, mul_assoc] using hrem.2
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le
      have hprod_nonneg :
          0 ≤ ‖y - x‖⁻¹ *
              ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ := by
        positivity
      simpa [Real.dist_eq, abs_of_nonneg hprod_nonneg] using
        (lt_of_le_of_lt hquot_le hGy_lt)
  simpa [u] using hgrad.differentiableAt

-- Proof sketch: use the interior-domain hypotheses together with the local boundedness and
-- nonemptiness results for `∂ f` to compare subgradient selections near `x`. Fréchet
-- differentiability forces all such selections to converge to the unique subgradient at `x`,
-- clause (ii) trivially implies clause (iii), and a continuous local selection yields the little-o
-- estimate characterizing Fréchet differentiability.
/-- Proposition 17 41: for `f ∈ Γ₀(H)` and `x ∈ interior (effectiveDomain f)`, the following are
equivalent: (i) `x ↦ (f x : EReal).toReal` is Fréchet differentiable at `x`; (ii) every selection
of `∂ f` is continuous at `x`; (iii) there exists a selection of `∂ f` that is continuous at
`x`. -/
theorem frechetDifferentiableAt_tfae_subdifferentialSelections_continuousAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    List.TFAE
      [DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x,
        ∀ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x,
        ∃ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x] := by
  tfae_have 1 → 2 := by
    intro hdiff G
    -- Once nearby fibers collapse to the Fréchet gradient, every selection converges strongly to
    -- the unique value at `x`.
    let g : H → ℝ := fun y ↦ (f y : EReal).toReal
    let x0 : (∂ f).dom :=
      ⟨x, interior_effectiveDomain_subset_subdifferentialDomain_of_mem_gammaZero hf hx⟩
    let u : H := gradient g x
    have hgrad : HasGradientAt g u x := by
      simpa [g, u] using hdiff.hasGradientAt
    have hsubx : (∂ f) x = ({u} : Set H) :=
      subdifferential_eq_singleton_of_hasGradientAt hf hx (by simpa [g] using hgrad)
    have hGx : (G x0 : H) = u := by
      have hmem : (G x0 : H) ∈ (∂ f) x := by
        exact selection_apply_mem G x0
      have hsingle : (G x0 : H) ∈ ({u} : Set H) := by
        simpa [hsubx] using hmem
      exact Set.mem_singleton_iff.mp hsingle
    have hcont0 : ContinuousAt (fun z : (∂ f).dom ↦ (G z : H)) x0 := by
      rw [Metric.continuousAt_iff]
      intro ε hε
      rcases
          subdifferential_subset_closedBall_of_hasGradientAt hf hx (by simpa [g] using hgrad)
            (ε / 2) (by positivity) with
        ⟨δ, hδpos, hδball⟩
      refine ⟨δ, hδpos, ?_⟩
      intro z hz
      have hzbase : (z : H) ∈ Metric.ball x δ := by
        simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hz
      have hzmem : (G z : H) ∈ Metric.closedBall u (ε / 2) := by
        exact hδball (z : H) hzbase (selection_apply_mem G z)
      have hdist_le : dist (G z : H) u ≤ ε / 2 := by
        simpa [Metric.mem_closedBall] using hzmem
      calc
        dist (G z : H) (G x0 : H) = dist (G z : H) u := by rw [hGx]
        _ ≤ ε / 2 := hdist_le
        _ < ε := by linarith
    intro hxdom
    have hxeq : (⟨x, hxdom⟩ : (∂ f).dom) = x0 := by
      apply Subtype.ext
      rfl
    simpa [x0, hxeq] using hcont0
  tfae_have 2 → 3 := by
    intro hall
    classical
    let hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := fun z ↦ by
      rcases
          (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.2 with
        ⟨u, hu⟩
      exact ⟨⟨u, hu⟩⟩
    let G : Selection (∂ f) := fun z ↦ Classical.choice (hnonempty z)
    exact ⟨G, hall G⟩
  tfae_have 3 → 1 := by
    intro hsel
    exact differentiableAt_of_exists_selectionContinuousAt hf hx hsel
  tfae_finish

end DifferentiabilityOfConvexFunctions

end ERealFunction
