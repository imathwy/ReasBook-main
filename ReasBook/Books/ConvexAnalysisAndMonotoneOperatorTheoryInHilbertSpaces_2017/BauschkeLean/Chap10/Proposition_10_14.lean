import BauschkeLean.Chap10.Corollary_10_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

section

variable {f : H → Set.Ioi (⊥ : EReal)}

-- In this owner API, `f : H → ]-∞,+∞]` already rules out the value `-∞`, and
-- `hconv.nonempty` supplies the nonempty effective domain. Thus the explicit convexity binder is
-- the source's proper-convex hypothesis in the current canonical surface.

/-- The midpoint Jensen-gap modulus takes the infimum of the midpoint Jensen gaps over all
effective-domain pairs at a prescribed distance. -/
noncomputable def midpointModulusOfConvexity
    (f : H → Set.Ioi (⊥ : EReal)) : NNReal → EReal :=
  fun t ↦ sInf
    {δ : EReal |
      ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f,
        ‖x - y‖₊ = t ∧
          δ = jensenGap f (1 / 2 : ℝ) x y}

/-- The midpoint Jensen-gap modulus is bounded above by every midpoint Jensen gap realized at the
given radius. -/
-- Proof sketch: unfold `midpointModulusOfConvexity` and apply `sInf_le` to the witness set element
-- determined by the chosen points `x` and `y`.
theorem midpointModulusOfConvexity_le_gap
    (f : H → Set.Ioi (⊥ : EReal)) {t : NNReal} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (ht : ‖x - y‖₊ = t) :
    midpointModulusOfConvexity f t ≤ jensenGap f (1 / 2 : ℝ) x y := by
  -- Realize the chosen midpoint gap as one witness in the defining infimum set.
  refine sInf_le ?_
  exact ⟨x, hx, y, hy, ht, rfl⟩

/-- For a convex `]-∞,+∞]`-valued function, the midpoint Jensen-gap modulus is nonnegative. -/
theorem midpointModulusOfConvexity_nonneg
    (hconv : ConvexOn f (effectiveDomain f)) (t : NNReal) :
    0 ≤ midpointModulusOfConvexity f t := by
  -- Show that every midpoint-gap witness in the defining set is nonnegative.
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, _ht, rfl⟩
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hmid_bot : (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (f _).2
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hhalf_mul_ne_top : ((((1 / 2 : ℝ) : EReal)) * (f x : EReal)) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hfx_top⟩
  have hhalfE : (1 - (((1 / 2 : ℝ) : EReal))) = ((((1 - (1 / 2 : ℝ)) : ℝ)) : EReal) := by
    exact_mod_cast rfl
  have hhalf'_nonneg : (0 : EReal) ≤ (1 - (((1 / 2 : ℝ) : EReal))) := by
    rw [hhalfE]
    exact_mod_cast (show 0 ≤ (1 - (1 / 2 : ℝ)) by norm_num)
  have hhalf'_mul_ne_top : ((1 - (((1 / 2 : ℝ) : EReal))) * (f y : EReal)) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl ?_, Or.inl hhalf'_nonneg, Or.inl ?_, Or.inr hfy_top⟩
    · rw [hhalfE]
      exact EReal.coe_ne_bot (1 - (1 / 2 : ℝ))
    · rw [hhalfE]
      exact EReal.coe_ne_top (1 - (1 / 2 : ℝ))
  have hsum_ne_top :
      ((((1 / 2 : ℝ) : EReal)) * (f x : EReal) +
          (1 - (((1 / 2 : ℝ) : EReal))) * (f y : EReal)) ≠ ⊤ :=
    EReal.add_ne_top hhalf_mul_ne_top hhalf'_mul_ne_top
  -- Rewrite the midpoint Jensen inequality into the midpoint-gap form.
  rw [jensenGap, EReal.sub_nonneg (Or.inl hsum_ne_top) (Or.inr hmid_bot)]
  simpa using hconv.ineq hx hy (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)

/-- Helper for Proposition 10.14: the weighted endpoint sum in a Jensen gap is finite on the
effective domain. -/
private theorem weightedJensenSum_neTop
    {X : Type u} {f : X → Set.Ioi (⊥ : EReal)} {x y : X}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
  -- Effective-domain values are finite, so the weighted endpoint terms stay away from `⊤`.
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have h1α0 : 0 < 1 - α := by
    linarith
  have h1α_nonneg : 0 ≤ (1 - α : EReal) := by
    exact_mod_cast h1α0.le
  have hα_mul_ne_top : (α : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hfx_top⟩
  have h1α_mul_ne_top : (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfy_top⟩
  exact EReal.add_ne_top hα_mul_ne_top h1α_mul_ne_top

/-- Helper for Proposition 10.14: effective-domain values can be rewritten through `EReal.toReal`
inside local real-arithmetic normalizations. -/
private theorem coe_toReal_eq {X : Type u} {f : X → Set.Ioi (⊥ : EReal)} {x : X}
    (hx : x ∈ effectiveDomain f) :
    (((f x : EReal).toReal : ℝ) : EReal) = (f x : EReal) := by
  exact EReal.coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx)) (ne_of_gt (f x).2)

/-- Helper for Proposition 10.14: every midpoint Jensen gap of a convex function is nonnegative. -/
private theorem midpointJensenGap_nonneg
    (hconv : ConvexOn f (effectiveDomain f)) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    0 ≤ jensenGap f (1 / 2 : ℝ) x y := by
  -- Rewrite the midpoint Jensen inequality into the midpoint-gap form.
  have hmid_bot : (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (f _).2
  have hsum_ne_top :
      (((1 / 2 : ℝ) : EReal) * (f x : EReal) +
          (1 - (((1 / 2 : ℝ) : EReal))) * (f y : EReal)) ≠ ⊤ := by
    simpa using
      (weightedJensenSum_neTop (f := f) hx hy (hα0 := by norm_num) (hα1 := by norm_num))
  rw [jensenGap, EReal.sub_nonneg (Or.inl hsum_ne_top) (Or.inr hmid_bot)]
  simpa using hconv.ineq hx hy (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)

/-- Helper for Proposition 10.14: swapping the endpoints replaces `α` by `1 - α` without changing
the Jensen gap. -/
private theorem jensenGap_swap
    (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ) (x y : H) :
    jensenGap f α x y = jensenGap f (1 - α) y x := by
  -- Normalize the swapped affine combination and reorder the weighted endpoint sum.
  have hone : 1 - (1 - α) = α := by ring
  have honeE : (1 - ((1 - α : ℝ) : EReal)) = (α : EReal) := by
    exact_mod_cast hone
  have hcoeff : (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
    exact_mod_cast rfl
  have hswap : (1 - α) • y + (1 - (1 - α)) • x = α • x + (1 - α) • y := by
    rw [hone]
    abel_nf
  rw [jensenGap, jensenGap, hswap, honeE, hcoeff]
  rw [add_comm]

/-- Helper for Proposition 10.14: in the strict-half regime, convexity bounds the Jensen gap at
`α` below by `2α` times the midpoint Jensen gap. -/
private theorem two_mul_midpointGap_le_jensenGap_of_lt_half
    (hconv : ConvexOn f (effectiveDomain f)) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ((((2 * α : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) ≤ jensenGap f α x y := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hαhalf⟩
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hm : m ∈ effectiveDomain f := by
    -- The midpoint stays in the convex effective domain.
    dsimp [m]
    exact hconv.convex_effectiveDomain hx hy (by norm_num) (by norm_num) (by ring)
  have hcombo_mem : α • x + (1 - α) • y ∈ effectiveDomain f := by
    -- The strict-half affine combination also stays in the effective domain.
    exact hconv.convex_effectiveDomain hx hy hα0.le (by linarith) (by ring)
  have hcomb :
      (2 * α : ℝ) • m + (1 - 2 * α) • y = α • x + (1 - α) • y := by
    -- Expanding the midpoint produces the original strict-half convex combination.
    dsimp [m]
    rw [smul_add, smul_smul, smul_smul]
    have hhalf : 2 * α * (1 / 2 : ℝ) = α := by ring
    have hhalf' : 2 * α * (1 - (1 / 2 : ℝ)) = α := by ring
    rw [hhalf, hhalf']
    calc
      α • x + α • y + (1 - 2 * α) • y = α • x + (α • y + (1 - 2 * α) • y) := by
        rw [add_assoc]
      _ = α • x + ((α + (1 - 2 * α)) • y) := by
        rw [← add_smul]
      _ = α • x + (1 - α) • y := by
        congr 1
        ring
  have hconv_step :
      (f (α • x + (1 - α) • y) : EReal) ≤
        (((2 * α : ℝ) : EReal)) * (f m : EReal) +
          (1 - (((2 * α : ℝ) : EReal))) * (f y : EReal) := by
    -- Apply convexity to `(m, y)` with coefficient `2 * α`.
    simpa [hcomb] using
      (hconv.ineq hm hy (by nlinarith : 0 < 2 * α) (by nlinarith : (2 * α : ℝ) < 1))
  have hsub_cast : (((1 - 2 * α : ℝ) : EReal)) = 1 - (((2 * α : ℝ) : EReal)) := by
    exact_mod_cast rfl
  have hconv_step_real :
      (f (α • x + (1 - α) • y) : EReal).toReal ≤
        (2 * α) * (f m : EReal).toReal + (1 - 2 * α) * (f y : EReal).toReal := by
    -- Move the convexity estimate to real arithmetic because all participating values are finite.
    have hconv_step' :
        (f (α • x + (1 - α) • y) : EReal) ≤
          (((2 * α : ℝ) : EReal)) * (f m : EReal) +
            (((1 - 2 * α : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hconv_step
    rw [← coe_toReal_eq hcombo_mem, ← coe_toReal_eq hm, ← coe_toReal_eq hy, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add] at hconv_step'
    exact_mod_cast hconv_step'
  have hreal :
      (f (α • x + (1 - α) • y) : EReal).toReal +
          (2 * α) *
              (((1 / 2 : ℝ) * (f x : EReal).toReal +
                    (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal) -
                (f m : EReal).toReal) ≤
        α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
    -- The real inequality is the source proof's coefficient computation.
    nlinarith
  have hreal' :
      (f (α • x + (1 - α) • y) : EReal).toReal +
          α *
              (2 *
                  ((f x : EReal).toReal * (1 / 2 : ℝ) +
                    (f y : EReal).toReal * (1 - (1 / 2 : ℝ)) -
                    (f m : EReal).toReal)) ≤
        α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
    nlinarith
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (f _).2
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ :=
    weightedJensenSum_neTop (f := f) hx hy hα0 (by linarith)
  have hgap :
      ((((2 * α : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) -
          (f (α • x + (1 - α) • y) : EReal) := by
    -- Repackage the real computation as a Jensen-gap inequality in `EReal`.
    rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
    rw [jensenGap, ← coe_toReal_eq hx, ← coe_toReal_eq hy, ← coe_toReal_eq hm,
      ← coe_toReal_eq hcombo_mem]
    norm_num [EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
      add_left_comm, add_comm]
    exact_mod_cast hreal'
  simpa [jensenGap] using hgap

/-- Helper for Proposition 10.14: the strict-half comparison remains valid after weakening the
coefficient from `2α` to `2α(1 - α)`. -/
private theorem midpointGap_mul_le_jensenGap_of_lt_half
    (hconv : ConvexOn f (effectiveDomain f)) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ((((2 * α * (1 - α) : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) ≤
      jensenGap f α x y := by
  -- Compare the smaller coefficient `2α(1 - α)` to the stronger strict-half estimate.
  have hmid_nonneg : 0 ≤ jensenGap f (1 / 2 : ℝ) x y :=
    midpointJensenGap_nonneg (f := f) hconv hx hy
  have hcoeff :
      (((2 * α * (1 - α) : ℝ) : EReal)) ≤ ((((2 * α : ℝ) : EReal))) := by
    exact_mod_cast show 2 * α * (1 - α) ≤ 2 * α by
      nlinarith [Set.mem_Ioo.mp hα]
  calc
    ((((2 * α * (1 - α) : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) ≤
        ((((2 * α : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) := by
          exact mul_le_mul_of_nonneg_right hcoeff hmid_nonneg
    _ ≤ jensenGap f α x y :=
      two_mul_midpointGap_le_jensenGap_of_lt_half (f := f) hconv hx hy hα

/-- Helper for Proposition 10.14: dividing the strict-half comparison by `α(1 - α)` matches the
normalized-gap witnesses defining `exactModulusOfConvexity`. -/
private theorem two_mul_midpointGap_le_normalizedGap_of_lt_half
    (hconv : ConvexOn f (effectiveDomain f)) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    2 * jensenGap f (1 / 2 : ℝ) x y ≤ jensenGap f α x y / (α * (1 - α) : ℝ) := by
  have hden_pos : (0 : EReal) < (((α * (1 - α) : ℝ) : EReal)) := by
    exact_mod_cast show 0 < α * (1 - α) by
      nlinarith [Set.mem_Ioo.mp hα]
  have hmul :
      (2 * jensenGap f (1 / 2 : ℝ) x y) * (((α * (1 - α) : ℝ) : EReal)) ≤
        jensenGap f α x y := by
    have hcoeff :
        (2 : EReal) * (((α * (1 - α) : ℝ) : EReal)) =
          (((2 * α * (1 - α) : ℝ) : EReal)) := by
      have htwo_cast : (2 : EReal) = ((2 : ℝ) : EReal) := by
        simpa using (EReal.coe_natCast (n := 2)).symm
      rw [htwo_cast, ← EReal.coe_mul]
      norm_num [mul_assoc, mul_left_comm, mul_comm]
    have hshape :
        (2 * jensenGap f (1 / 2 : ℝ) x y) * (((α * (1 - α) : ℝ) : EReal)) =
          ((((2 * α * (1 - α) : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) := by
      calc
        (2 * jensenGap f (1 / 2 : ℝ) x y) * (((α * (1 - α) : ℝ) : EReal)) =
            ((2 : EReal) * (((α * (1 - α) : ℝ) : EReal))) * jensenGap f (1 / 2 : ℝ) x y := by
              ac_rfl
        _ = ((((2 * α * (1 - α) : ℝ) : EReal)) * jensenGap f (1 / 2 : ℝ) x y) := by
          rw [hcoeff]
    rw [hshape]
    exact midpointGap_mul_le_jensenGap_of_lt_half (f := f) hconv hx hy hα
  -- Clear the positive denominator exactly once, at the normalized-gap boundary.
  exact (EReal.le_div_iff_mul_le hden_pos (EReal.coe_ne_top (α * (1 - α)))).2 hmul

-- Proof sketch: compare the midpoint Jensen gap with the normalized gaps used in
-- `exactModulusOfConvexity`; convexity at coefficients `α ∈ (0, 1/2]` yields the lower bound
-- `2 ψ ≤ φ`.
/-- Lower bound in Proposition 10.14 (1): twice the midpoint Jensen-gap modulus is bounded above by
the exact modulus of convexity for a convex `]-∞,+∞]`-valued function. -/
theorem two_mul_midpointModulusOfConvexity_le_exactModulusOfConvexity
    (hconv : ConvexOn f (effectiveDomain f))
    (t : NNReal) :
    2 * midpointModulusOfConvexity f t ≤ exactModulusOfConvexity f t := by
  -- Route correction: prove the witness bound branchwise (`<`, `=`, `> 1/2`) and only divide at
  -- the exact-modulus interface.
  rw [exactModulusOfConvexity]
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, hxy, α, hα, rfl⟩
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  by_cases hlt : α < 1 / 2
  · -- In the strict-half branch, use the dedicated normalized-gap comparison.
    have hmid_le_gap :
        midpointModulusOfConvexity f t ≤ jensenGap f (1 / 2 : ℝ) x y :=
      midpointModulusOfConvexity_le_gap f hx hy hxy
    calc
      2 * midpointModulusOfConvexity f t ≤ 2 * jensenGap f (1 / 2 : ℝ) x y := by
        exact mul_le_mul_of_nonneg_left hmid_le_gap (by norm_num)
      _ ≤ jensenGap f α x y / (α * (1 - α) : ℝ) :=
        two_mul_midpointGap_le_normalizedGap_of_lt_half (f := f) hconv hx hy ⟨hα0, hlt⟩
  · have hhalf_le : 1 / 2 ≤ α := le_of_not_gt hlt
    by_cases hEq : α = 1 / 2
    · -- At `α = 1 / 2`, compare directly with the midpoint witness and clear the `1 / 4`
      -- denominator explicitly.
      subst hEq
      have hmid_le_gap :
          midpointModulusOfConvexity f t ≤ jensenGap f (1 / 2 : ℝ) x y :=
        midpointModulusOfConvexity_le_gap f hx hy hxy
      have hmid_nonneg : 0 ≤ jensenGap f (1 / 2 : ℝ) x y :=
        midpointJensenGap_nonneg (f := f) hconv hx hy
      have htwo_le_four :
          2 * midpointModulusOfConvexity f t ≤ 4 * jensenGap f (1 / 2 : ℝ) x y := by
        calc
          2 * midpointModulusOfConvexity f t ≤ 2 * jensenGap f (1 / 2 : ℝ) x y := by
            exact mul_le_mul_of_nonneg_left hmid_le_gap (by norm_num)
          _ ≤ 4 * jensenGap f (1 / 2 : ℝ) x y := by
            have hcoeff : (2 : EReal) ≤ (4 : EReal) := by
              exact_mod_cast (show (2 : ℝ) ≤ 4 by norm_num)
            exact mul_le_mul_of_nonneg_right hcoeff hmid_nonneg
      have hinv : ((((1 / 4 : ℝ) : EReal))⁻¹) = (((4 : ℝ) : EReal)) := by
        calc
          ((((1 / 4 : ℝ) : EReal))⁻¹) = (((1 / 4 : ℝ)⁻¹ : ℝ) : EReal) := by
            rw [← EReal.coe_inv]
          _ = (((4 : ℝ) : EReal)) := by
            norm_num
      have hdiv4 :
          jensenGap f (1 / 2 : ℝ) x y / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) =
            (((4 : ℝ) : EReal) * jensenGap f (1 / 2 : ℝ) x y) := by
        norm_num
        rw [EReal.div_eq_inv_mul, hinv]
      calc
        2 * midpointModulusOfConvexity f t ≤ 4 * jensenGap f (1 / 2 : ℝ) x y := htwo_le_four
        _ = (((4 : ℝ) : EReal) * jensenGap f (1 / 2 : ℝ) x y) := by
          have hfour_cast : (4 : EReal) = (((4 : ℝ) : EReal)) := by
            simpa using (EReal.coe_natCast (n := 4)).symm
          rw [hfour_cast]
        _ = jensenGap f (1 / 2 : ℝ) x y / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) := by
          rw [hdiv4]
    · -- For `α > 1 / 2`, swap the endpoints and reduce to the strict-half branch for `1 - α`.
      have hgt : 1 / 2 < α := lt_of_le_of_ne hhalf_le (Ne.symm hEq)
      have hβ : 1 - α ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
        constructor
        · linarith
        · linarith
      have hyx : ‖y - x‖₊ = t := by
        have hsym : ‖y - x‖₊ = ‖x - y‖₊ := by
          simpa [nndist_eq_nnnorm] using (nndist_comm y x)
        exact hsym.trans hxy
      have hswap :
          jensenGap f (1 - α) y x / (((1 - α) * (1 - (1 - α)) : ℝ)) =
            jensenGap f α x y / (α * (1 - α) : ℝ) := by
        have hone : 1 - (1 - α) = α := by ring
        rw [jensenGap_swap, hone, mul_comm]
      have hmid_le :
          2 * midpointModulusOfConvexity f t ≤
            jensenGap f (1 - α) y x / (((1 - α) * (1 - (1 - α)) : ℝ)) := by
        have hyx_gap :
            midpointModulusOfConvexity f t ≤ jensenGap f (1 / 2 : ℝ) y x :=
          midpointModulusOfConvexity_le_gap f hy hx hyx
        calc
          2 * midpointModulusOfConvexity f t ≤ 2 * jensenGap f (1 / 2 : ℝ) y x := by
            exact mul_le_mul_of_nonneg_left hyx_gap (by norm_num)
          _ ≤ jensenGap f (1 - α) y x / (((1 - α) * (1 - (1 - α)) : ℝ)) :=
            two_mul_midpointGap_le_normalizedGap_of_lt_half (f := f) hconv hy hx hβ
      calc
        2 * midpointModulusOfConvexity f t ≤
            jensenGap f (1 - α) y x / (((1 - α) * (1 - (1 - α)) : ℝ)) := hmid_le
        _ = jensenGap f α x y / (α * (1 - α) : ℝ) := hswap

/-- Helper for Proposition 10.14: quarter-scaling the exact modulus aligns the `α = 1 / 2`
normalized-gap estimate with the midpoint-gap infimum. -/
private theorem quarter_mul_exactModulusOfConvexity_le_midpointModulusOfConvexity
    (f : H → Set.Ioi (⊥ : EReal)) (t : NNReal) :
    (((1 / 4 : ℝ) : EReal) * exactModulusOfConvexity f t) ≤ midpointModulusOfConvexity f t := by
  -- Compare the quarter-scaled exact modulus with each midpoint witness of radius `t`.
  rw [midpointModulusOfConvexity]
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, hxy, rfl⟩
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hgap :
      exactModulusOfConvexity f t ≤
        jensenGap f (1 / 2 : ℝ) x y / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) :=
    exactModulusOfConvexity_le_normalizedGap f hx hy hxy hhalf
  have hgap' := hgap
  norm_num at hgap'
  have hquarter_pos : (0 : EReal) < (((1 / 4 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 < (1 / 4 : ℝ) by norm_num)
  -- Clear the positive denominator to recover an inequality in the midpoint-gap scale.
  have hmul :=
    (EReal.le_div_iff_mul_le hquarter_pos (EReal.coe_ne_top (1 / 4 : ℝ))).1 hgap'
  simpa [mul_comm] using hmul

-- Proof sketch: specialize the defining infimum in `exactModulusOfConvexity` to the coefficient
-- `α = 1 / 2`, so the normalization factor becomes `1 / 4` and gives the estimate `φ ≤ 4 ψ`.
/-- Upper bound in Proposition 10.14 (1): the exact modulus of convexity is bounded above by four
times the midpoint Jensen-gap modulus for a convex `]-∞,+∞]`-valued function. -/
theorem exactModulusOfConvexity_le_four_mul_midpointModulusOfConvexity
    (hconv : ConvexOn f (effectiveDomain f))
    (t : NNReal) :
    exactModulusOfConvexity f t ≤ 4 * midpointModulusOfConvexity f t := by
  -- Route correction: the clean owner-facing proof first proves the quarter-scaled form and then
  -- divides by `1 / 4` once, instead of pushing `4` through the infimum directly.
  change exactModulusOfConvexity f t ≤ (((4 : ℝ) : EReal) * midpointModulusOfConvexity f t)
  have _hconv := hconv
  have hquarter := quarter_mul_exactModulusOfConvexity_le_midpointModulusOfConvexity f t
  have hquarter_pos : (0 : EReal) < (((1 / 4 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 < (1 / 4 : ℝ) by norm_num)
  have hdiv :
      exactModulusOfConvexity f t ≤ midpointModulusOfConvexity f t / (((1 / 4 : ℝ) : EReal)) := by
    exact
      (EReal.le_div_iff_mul_le hquarter_pos (EReal.coe_ne_top (1 / 4 : ℝ))).2
        (by simpa [mul_comm] using hquarter)
  have hinv : ((((1 / 4 : ℝ) : EReal))⁻¹) = (((4 : ℝ) : EReal)) := by
    calc
      ((((1 / 4 : ℝ) : EReal))⁻¹) = (((1 / 4 : ℝ)⁻¹ : ℝ) : EReal) := by
        rw [← EReal.coe_inv]
      _ = (((4 : ℝ) : EReal)) := by
        norm_num
  have hdiv4 : midpointModulusOfConvexity f t / (((1 / 4 : ℝ) : EReal)) =
      (((4 : ℝ) : EReal) * midpointModulusOfConvexity f t) := by
    rw [EReal.div_eq_inv_mul, hinv]
  calc
    exactModulusOfConvexity f t ≤ midpointModulusOfConvexity f t / (((1 / 4 : ℝ) : EReal)) := hdiv
    _ = (((4 : ℝ) : EReal) * midpointModulusOfConvexity f t) := hdiv4

/-- For a convex `]-∞,+∞]`-valued function, the midpoint and exact moduli of convexity vanish at
exactly the same radii. -/
theorem midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
    (hconv : ConvexOn f (effectiveDomain f))
    (t : NNReal) :
    midpointModulusOfConvexity f t = 0 ↔ exactModulusOfConvexity f t = 0 := by
  constructor
  · intro hmid
    have hexact_nonneg : 0 ≤ exactModulusOfConvexity f t :=
      exactModulusOfConvexity_nonneg f hconv t
    have hexact_le_zero : exactModulusOfConvexity f t ≤ 0 := by
      simpa [hmid] using
        exactModulusOfConvexity_le_four_mul_midpointModulusOfConvexity (f := f) hconv t
    exact le_antisymm hexact_le_zero hexact_nonneg
  · intro hexact
    have hmid_nonneg : 0 ≤ midpointModulusOfConvexity f t :=
      midpointModulusOfConvexity_nonneg (f := f) hconv t
    have htwo_nonneg : 0 ≤ 2 * midpointModulusOfConvexity f t := by
      exact mul_nonneg (by norm_num) hmid_nonneg
    have htwo_le_zero : 2 * midpointModulusOfConvexity f t ≤ 0 := by
      simpa [hexact] using
        two_mul_midpointModulusOfConvexity_le_exactModulusOfConvexity (f := f) hconv t
    have htwo_zero : 2 * midpointModulusOfConvexity f t = 0 :=
      le_antisymm htwo_le_zero htwo_nonneg
    have hmid_le_zero : midpointModulusOfConvexity f t ≤ 0 := by
      calc
        midpointModulusOfConvexity f t ≤ 2 * midpointModulusOfConvexity f t := by
          simpa [one_mul, mul_comm] using
            (mul_le_mul_of_nonneg_right (show (1 : EReal) ≤ 2 by norm_num) hmid_nonneg)
        _ = 0 := htwo_zero
    exact le_antisymm hmid_le_zero hmid_nonneg

-- Proof sketch: combine the midpoint-criterion equivalence above with the canonical owner theorem
-- `exactModulusOfConvexity_uniformlyConvex_iff`.
/-- Canonical owner form of Proposition 10.14 (3): for a convex `]-∞,+∞]`-valued function, the
exact modulus of convexity is a modulus of uniform convexity precisely when the midpoint
Jensen-gap modulus vanishes only at `0`. -/
theorem exactModulusOfConvexity_uniformlyConvex_iff_midpointModulusOfConvexity_eq_zero_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    UniformlyConvex f (exactModulusOfConvexity f) ↔
      ∀ t : NNReal, midpointModulusOfConvexity f t = 0 ↔ t = 0 := by
  -- Transport Corollary 10.13 through the coincidence of the midpoint and exact zero sets.
  constructor
  · intro hExact t
    exact
      (midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
        (f := f) hconv t).trans
        ((exactModulusOfConvexity_uniformlyConvex_iff (f := f) hconv).1 hExact t)
  · intro hzero
    exact
      (exactModulusOfConvexity_uniformlyConvex_iff (f := f) hconv).2
        (fun t ↦
          (midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
            (f := f) hconv t).symm.trans
            (hzero t))

-- Proof sketch: transport the vanishing criterion along
-- `midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero`, then apply the
-- canonical Corollary 10.13 owner theorem for `exactModulusOfConvexity`.
/-- Proposition 10.14 (3): a convex `]-∞,+∞]`-valued function is uniformly convex if and only if
its midpoint Jensen-gap modulus vanishes only at `0`. -/
theorem uniformlyConvex_exists_iff_midpointModulusOfConvexity_eq_zero_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    (∃ φ : NNReal → EReal, UniformlyConvex f φ) ↔
      ∀ t : NNReal, midpointModulusOfConvexity f t = 0 ↔ t = 0 := by
  -- Rewrite the exact-modulus vanishing criterion from Corollary 10.13 through the midpoint
  -- zero-set equivalence proved above.
  constructor
  · rintro ⟨φ, hφ⟩ t
    exact
      (midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
        (f := f) hconv t).trans
        ((uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff
          (f := f) hconv).1 ⟨φ, hφ⟩ t)
  · intro hzero
    exact
      (uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff (f := f) hconv).2
        (fun t ↦
          (midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
            (f := f) hconv t).symm.trans
            (hzero t))

end

end ERealFunction
