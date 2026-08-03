import BauschkeLean.Chap12.Definition_12_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 12 26: on the effective domain, the proximal objective is the
corresponding finite real-valued expression. -/
private theorem proximalObjective_eq_coe_toReal_add_quadratic
    (f : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∈ effectiveDomain f) :
    proximalObjective f x z =
      (((f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal) := by
  -- Rewrite the finite value of `f z` through `toReal` and regroup the finite sum.
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  rw [proximalObjective, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_add]
  simp

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 12 26: outside the effective domain, the proximal objective is `⊤`
because the function value itself is `⊤`. -/
private theorem proximalObjective_eq_top_of_not_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∉ effectiveDomain f) :
    proximalObjective f x z = ⊤ := by
  -- Rewrite `f z` as `⊤`; adding the finite quadratic term leaves the value equal to `⊤`.
  have hz_top : (f z : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz))
  rw [proximalObjective, hz_top, EReal.top_add_coe]

/-- Helper for Proposition 12 26: subtracting the left endpoint from a line-map point produces
the scaled chord. -/
private theorem lineMap_sub_eq_smul_sub (p y : H) (α : ℝ) :
    AffineMap.lineMap p y α - p = α • (y - p) := by
  -- Expand the affine combination and cancel the base point.
  simpa [vsub_eq_sub] using AffineMap.lineMap_vsub_left p y α

/-- Helper for Proposition 12 26: subtracting a point on the segment from `x` isolates the
residual `x - p` minus the scaled chord. -/
private theorem sub_lineMap_eq_sub_smul_sub (x p y : H) (α : ℝ) :
    x - AffineMap.lineMap p y α = (x - p) - α • (y - p) := by
  -- Rewrite the segment point as `p + α • (y - p)` and collect terms.
  rw [sub_eq_add_neg, AffineMap.lineMap_apply_module', sub_eq_add_neg]
  abel_nf

/-- Helper for Proposition 12 26: a proximal point has finite function value. -/
private theorem mem_effectiveDomain_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p : H}
    (hp : IsProxPoint f x p) :
    p ∈ effectiveDomain f := by
  -- Compare the proximal objective at `p` with a known finite domain point.
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  rcases hconv.nonempty with ⟨q, hq⟩
  have hobj_q_ne_top : proximalObjective f x q ≠ ⊤ := by
    rw [proximalObjective_eq_coe_toReal_add_quadratic f x q hq]
    exact EReal.coe_ne_top _
  by_contra hp_dom
  have hobj_p_top : proximalObjective f x p = ⊤ :=
    proximalObjective_eq_top_of_not_mem_effectiveDomain f x p hp_dom
  have hpq : proximalObjective f x p ≤ proximalObjective f x q := hp q
  rw [hobj_p_top] at hpq
  exact hobj_q_ne_top (top_le_iff.mp hpq)

/-- Helper for Proposition 12 26: along an interior segment from a proximal point toward an
effective-domain point, the source variational inequality holds up to a quadratic error term. -/
private theorem inner_add_le_add_quadratic_error_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p : H}
    (hp : IsProxPoint f x p) {y : H} (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤
      (f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 := by
  -- Unfold proximality to the pointwise minimizing property of the proximal objective.
  have hp_dom : p ∈ effectiveDomain f := mem_effectiveDomain_of_isProxPoint f hconv hp
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  let z : H := AffineMap.lineMap p y α
  have hz_eq : z = α • y + (1 - α) • p := by
    -- Rewrite the line-map point as the usual convex combination.
    simpa [z, add_comm, add_left_comm, add_assoc] using (AffineMap.lineMap_apply_module p y α)
  have hz : z ∈ effectiveDomain f := by
    -- Convexity of the effective domain keeps the interior segment point finite.
    rw [hz_eq]
    exact hconv.convex_effectiveDomain hy hp_dom hα0.le (sub_nonneg.mpr hα1.le) (by linarith)
  have hmin :
      (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    -- Compare the proximal objective at the minimizer `p` and at the segment point `z`.
    have hpz : proximalObjective f x p ≤ proximalObjective f x z := hp z
    rw [proximalObjective_eq_coe_toReal_add_quadratic f x p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic f x z hz] at hpz
    exact_mod_cast hpz
  have hconv_real :
      (f z : EReal).toReal ≤
        α * (f y : EReal).toReal + (1 - α) * (f p : EReal).toReal := by
    -- Apply convexity to the real representative of `f` on the effective domain.
    rw [hz_eq]
    exact hconv.toReal_convexOn_effectiveDomain.2 hy hp_dom hα0.le (sub_nonneg.mpr hα1.le)
      (by linarith)
  have hstep :
      (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (α * (f y : EReal).toReal + (1 - α) * (f p : EReal).toReal) +
          (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    -- Insert the convexity bound for `f z` into the minimizer inequality.
    exact le_trans hmin (add_le_add hconv_real le_rfl)
  have hnorm :
      ‖x - z‖ ^ 2 =
        ‖x - p‖ ^ 2 - 2 * α * ⟪y - p, x - p⟫_ℝ + α ^ 2 * ‖y - p‖ ^ 2 := by
    -- Expand the squared residual to isolate the desired inner-product term.
    simpa [z, sub_lineMap_eq_sub_smul_sub, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hα0.le, pow_two, mul_assoc, mul_left_comm, mul_comm,
      real_inner_comm] using
      (norm_sub_sq_real (x - p) (α • (y - p)))
  have hscaled :
      α * (⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal) ≤
        α * (f y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
    -- Rearranging the quadratic expansion yields the scaled variational inequality.
    nlinarith [hstep, hnorm]
  have hscaled' :
      α * (⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal) ≤
        α * ((f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) := by
    -- Rewrite the right-hand side into the factorized form needed for cancellation.
    have hfactor :
        α * ((f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) =
          α * (f y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
      ring
    rwa [hfactor]
  -- Cancel the common positive factor `α`.
  exact le_of_mul_le_mul_left hscaled' hα0

/-- Helper for Proposition 12 26: proximal points satisfy the finite variational inequality
against every finite comparison point. -/
private theorem inner_add_toReal_le_toReal_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p y : H}
    (hp : IsProxPoint f x p) (hy : y ∈ effectiveDomain f) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let δ : ℝ := min 1 (2 * ε / (‖y - p‖ ^ 2 + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    positivity
  rcases exists_nat_one_div_lt hδ_pos with ⟨n, hn⟩
  let α : ℝ := 1 / (n + 1 : ℝ)
  have hα0 : 0 < α := by
    dsimp [α]
    positivity
  have hα_lt_δ : α < δ := by
    simpa [α] using hn
  have hα1 : α < 1 := lt_of_lt_of_le hα_lt_δ (min_le_left _ _)
  have hαε : (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ ε := by
    have hα_lt :
        α < 2 * ε / (‖y - p‖ ^ 2 + 1) := lt_of_lt_of_le hα_lt_δ (min_le_right _ _)
    have hden_pos : 0 < ‖y - p‖ ^ 2 + 1 := by positivity
    have hmain : α * (‖y - p‖ ^ 2 + 1) < 2 * ε := by
      exact (lt_div_iff₀ hden_pos).mp hα_lt
    have hle :
        α * ‖y - p‖ ^ 2 ≤ α * (‖y - p‖ ^ 2 + 1) := by
      nlinarith [show 0 ≤ α by exact le_of_lt hα0]
    have haux : α * ‖y - p‖ ^ 2 < 2 * ε := lt_of_le_of_lt hle hmain
    nlinarith
  have herr :=
    inner_add_le_add_quadratic_error_of_isProxPoint f hconv hp hy hα0 hα1
  have hbound :
      (f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ (f y : EReal).toReal + ε := by
    nlinarith
  exact le_trans herr hbound

/-- Helper for Proposition 12 26: the textbook variational inequality forces `p` to have a
finite value under `f`. -/
private theorem mem_effectiveDomain_of_variational_inequality
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H)
    (hvar : ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal)) :
    p ∈ effectiveDomain f := by
  -- Compare against a single known finite domain point and rule out the value `⊤` at `p`.
  rcases hconv.nonempty with ⟨q, hq⟩
  by_contra hp_dom
  have hfp_top : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
  have hq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq)
  have hqineq : (⟪q - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f q : EReal) := hvar q
  rw [hfp_top] at hqineq
  have hqeq : (f q : EReal) = ⊤ := by
    simpa using hqineq
  exact hq_top hqeq

/-- Helper for Proposition 12 26: the textbook variational inequality implies that `p`
minimizes the proximal objective pointwise. -/
private theorem proximalObjective_le_of_forall_inner_add_le
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H)
    (hvar : ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal)) :
    ∀ y, proximalObjective f x p ≤ proximalObjective f x y := by
  -- First recover that `f p` is finite, so both sides can be compared through real representatives.
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_variational_inequality f hconv x p hvar
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, expand both proximal objectives and use one quadratic identity.
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hfy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hvar_real :
        ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
      have hcast :
          (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
            (((f y : EReal).toReal : ℝ) : EReal) := by
        have hyvar := hvar y
        rw [← EReal.coe_toReal hfp_top hfp_bot, ← EReal.coe_toReal hfy_top hfy_bot,
          ← EReal.coe_add] at hyvar
        exact hyvar
      exact_mod_cast hcast
    have hquad :
        (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
          (f y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      -- Expand `‖x - y‖²` relative to `p` and use the variational inequality term.
      have hnorm :
          ‖x - y‖ ^ 2 =
            ‖x - p‖ ^ 2 - 2 * ⟪y - p, x - p⟫_ℝ + ‖y - p‖ ^ 2 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, real_inner_comm] using
          (norm_sub_sq_real (x - p) (y - p))
      nlinarith [hvar_real, hnorm]
    have hcast :
        (((f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤
          (((f y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
      exact_mod_cast hquad
    simpa [proximalObjective_eq_coe_toReal_add_quadratic f x p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic f x y hy] using hcast
  · -- Off the effective domain, the proximal objective at `y` is `⊤`.
    have hy_top : proximalObjective f x y = ⊤ :=
      proximalObjective_eq_top_of_not_mem_effectiveDomain f x y hy
    rw [hy_top]
    exact le_top

/-- Helper for Proposition 12 26: on the effective domain, a real-valued variational inequality
casts back to the corresponding `EReal` inequality. -/
private theorem ereal_inner_add_le_of_toReal
    (f : H → Set.Ioi (⊥ : EReal)) {x p y : H}
    (hp : p ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hreal : ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal) :
    (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal) := by
  -- Rewrite the finite values of `f p` and `f y` through `toReal` and cast the real inequality.
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hcast :
      (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hfp_top hfp_bot, EReal.coe_toReal hfy_top hfy_bot, EReal.coe_add] using
    hcast

-- Proof sketch: use the primitive convexity hypothesis on `effectiveDomain f`, unfold
-- `IsProxPoint` through the canonical owner `Argmin` of `proximalObjective f x`, rewrite the
-- resulting minimizer condition as the corresponding pointwise inequality, and expand the
-- quadratic term on both sides.
/-- Proposition 12 26: if `f` is convex on its effective domain (in particular if `f ∈ Γ₀(H)`),
then a point `p` is a proximal point of `f` at `x` exactly when it satisfies the textbook
variational inequality `(12.25)`,
`⟪y - p, x - p⟫ + f(p) ≤ f(y)` for every `y ∈ H`. -/
theorem isProxPoint_iff_forall_inner_add_le
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H) :
    IsProxPoint f x p ↔
      ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal) := by
  constructor
  · intro hp y
    by_cases hy : y ∈ effectiveDomain f
    · -- Remove the quadratic error by choosing a sufficiently small segment parameter.
      have hp_dom : p ∈ effectiveDomain f := mem_effectiveDomain_of_isProxPoint f hconv hp
      have hreal :
          ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal :=
        inner_add_toReal_le_toReal_of_isProxPoint f hconv hp hy
      -- Cast the finite real inequality back to the ambient `EReal` statement.
      exact ereal_inner_add_le_of_toReal f hp_dom hy hreal
    · -- Off the effective domain, the right-hand side is `⊤`.
      have hfy_top : (f y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
      rw [hfy_top]
      exact le_top
  · intro hvar
    -- Rewrite the variational inequality as pointwise minimality of the proximal objective.
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
    exact proximalObjective_le_of_forall_inner_add_le f hconv x p hvar

end ERealFunction
