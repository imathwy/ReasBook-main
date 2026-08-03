import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 17 17: a subgradient at `x` gives a lower bound on every positive
directional increment quotient based at `x`. -/
private theorem inner_le_increment_quotient_of_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal))
    {x u y : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    {α : ℝ} (hα : 0 < α) :
    (⟪y, u⟫_ℝ : EReal) ≤
      (((f (x + α • y) : EReal) - (f x : EReal)) / α) := by
  have huα :
      (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) ≤
        (f (x + α • y) : EReal) := by
    -- Evaluate the affine minorant inequality at the ray point `x + α • y`.
    simpa using (mem_subdifferential_iff f x u).1 hu (x + α • y)
  by_cases hxy : x + α • y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxy)
    have hxy_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from
        (f (x + α • y)).2)
    have huα_real :
        α * ⟪y, u⟫_ℝ + (f x : EReal).toReal ≤
          (f (x + α • y) : EReal).toReal := by
      -- On the finite branch, rewrite the `EReal` inequality as an ordinary real inequality.
      have hcast :
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
            (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
        calc
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
              = (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) := by
                  rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                  simp [real_inner_smul_left, EReal.coe_mul]
          _ ≤ (f (x + α • y) : EReal) := huα
          _ = (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hxy_top hxy_bot).symm
      exact_mod_cast hcast
    have hquot_real :
        ⟪y, u⟫_ℝ ≤
          ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α := by
      -- Divide the real inequality by the positive scalar `α`.
      refine (le_div_iff₀ hα).2 ?_
      linarith
    have hquot_cast :
        (⟪y, u⟫_ℝ : EReal) ≤
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      exact_mod_cast hquot_real
    have hquot_eq :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) =
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      -- Once both endpoint values are finite, the quotient is the cast of the real quotient.
      rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      simp
    rw [hquot_eq]
    exact hquot_cast
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hxy_top : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxy))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
    -- Outside the effective domain, the positive quotient is `⊤`, so the bound is automatic.
    rw [hxy_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    exact le_top

/-- Helper for Proposition 17 17: every subgradient yields a pointwise lower bound for the
directional derivative. -/
private theorem forall_inner_le_directionalDerivative_of_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y := by
  let _ := hconv
  intro y
  rw [directionalDerivative]
  apply le_sInf
  rintro q ⟨α, rfl⟩
  -- Every positive directional difference quotient already dominates the inner product.
  simpa [directionalDifferenceQuotient] using
    inner_le_increment_quotient_of_mem_subdifferential
      (f := f) hx hu (α := (α : ℝ)) α.2

/-- Helper for Proposition 17 17: pointwise domination by the directional derivative recovers the
subgradient inequality at `x`. -/
private theorem mem_subdifferential_of_forall_inner_le_directionalDerivative
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f)
    (hu : ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro z
  have hdir : (⟪z - x, u⟫_ℝ : EReal) ≤ directionalDerivative f x (z - x) := hu (z - x)
  -- Evaluate the directional-derivative bound in the source direction `z - x`.
  calc
    (⟪z - x, u⟫_ℝ : EReal) + (f x : EReal) ≤
        directionalDerivative f x (z - x) + (f x : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdir (f x : EReal)
    _ ≤ (f z : EReal) := directionalDerivative_add_value_le (f := f) hconv hx z

/-- Helper for Proposition 17 17: at an effective-domain point of a convex function, a vector is a
subgradient exactly when its inner-product functional is pointwise dominated by the directional
derivative. -/
theorem mem_subdifferential_iff_inner_le_directionalDerivative
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔ ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y := by
  constructor
  · intro hu
    -- The forward implication is the quotient-bound route followed by the directional limit.
    exact forall_inner_le_directionalDerivative_of_mem_subdifferential
      (f := f) hconv hx hu
  · intro hu
    -- The reverse implication plugs the pointwise bound into Proposition 17.2 (2).
    exact mem_subdifferential_of_forall_inner_le_directionalDerivative
      (f := f) hconv hx hu

/-- Helper for Proposition 17 17: positive rescaling of the direction rescales the directional
derivative by the same factor. -/
private theorem has_directional_derivative_at_smul_pos
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x y ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c • y) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    -- Reparameterize the quotient by the positive scaling `α ↦ α * c`.
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hcoe_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top c
  have hcoe_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hmul :
      Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ξ * c)) := by
    -- Multiplying the reparameterized quotient transports the limit by the same factor.
    exact EReal.Tendsto.mul_const hcomp (Or.inr hcoe_bot) (Or.inr hcoe_top)
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α)
      (fun α ↦ q (α * c) * c) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hc0 : c ≠ 0 := hc.ne'
    have hcoeff : ((((α * c : ℝ) : EReal)⁻¹) * c) = ((α : EReal)⁻¹) := by
      rw [← EReal.coe_inv (α * c), ← EReal.coe_mul, ← EReal.coe_inv α]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        calc
          (α * c)⁻¹ * c = c / (α * c) := by
            rw [div_eq_mul_inv, mul_comm]
          _ = α⁻¹ := by
            simpa [mul_comm] using (div_mul_cancel_left₀ hc0 α)
    -- Rewrite the scaled quotient into the original quotient evaluated at `α * c`.
    calc
      ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) • y) : EReal) - (f x : EReal)) / α) := by
              simp [smul_smul, mul_comm]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) *
            ((((α * c : ℝ) : EReal)⁻¹) * c) := by
              rw [hcoeff]
      _ =
          ((((f (x + (α * c) • y) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
            rw [div_eq_mul_inv]
            exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by
            simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

/-- Helper for Proposition 17 17: positive rescaling of the direction rescales the canonical
directional derivative by the same factor. -/
private theorem directionalDerivative_smul_of_pos
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) {c : ℝ} (hc : 0 < c) :
    directionalDerivative f x (c • y) = directionalDerivative f x y * c := by
  have hdir : HasDirectionalDerivativeAt f x y (directionalDerivative f x y) :=
    hasDirectionalDerivativeAt_directionalDerivative (f := f) hconv hx y
  have hscaled : HasDirectionalDerivativeAt f x (c • y) (directionalDerivative f x y * c) := by
    -- Transport the canonical derivative limit through the positive reparameterization.
    exact has_directional_derivative_at_smul_pos hdir hc
  exact directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := f) hconv hscaled

/-- Helper for Proposition 17 17: the Fenchel conjugate of the directional derivative vanishes
exactly on the subdifferential at the base point. -/
lemma conjugate_directionalDerivative_eq_zero_iff_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) :
    (directionalDerivative f x)∗ u = 0 ↔ u ∈ (∂ f) x := by
  let g : H → EReal := directionalDerivative f x
  have hzero : g 0 = 0 := directionalDerivative_zero hconv hx
  constructor
  · intro hconj
    have hinner : ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ g y := by
      intro y
      have hy : (((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) ≤ g∗ u := by
        -- Test the conjugate supremum at the single direction `y`.
        rw [conjugate_apply]
        exact le_iSup (fun z : H ↦ ((⟪z, u⟫_ℝ : ℝ) : EReal) - g z) y
      have hy' : (((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) ≤ 0 := by
        rwa [hconj] at hy
      exact (EReal.sub_nonpos).1 hy'
    -- Proposition 17.14 turns the pointwise domination back into subgradient membership.
    exact
      (mem_subdifferential_iff_inner_le_directionalDerivative
        (f := f) hconv (x := x) (u := u) hx).2 hinner
  · intro hu
    have hinner :
        ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ g y :=
      (mem_subdifferential_iff_inner_le_directionalDerivative
        (f := f) hconv (x := x) (u := u) hx).1 hu
    have hle : g∗ u ≤ 0 := by
      -- Every supremand is nonpositive once `u` is a subgradient.
      rw [conjugate_apply]
      refine iSup_le ?_
      intro y
      exact (EReal.sub_nonpos).2 (hinner y)
    have hge : 0 ≤ g∗ u := by
      -- The zero direction contributes the value `0` to the conjugate supremum.
      rw [conjugate_apply]
      simpa [hzero] using
        (le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) (0 : H))
    exact le_antisymm hle hge

/-- Helper for Proposition 17 17: if the conjugate of the directional derivative is not `⊤` at
`u`, then the pairing with `u` is dominated by the directional derivative in every direction. -/
lemma inner_le_directionalDerivative_of_conjugate_ne_top
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f)
    (hu : (directionalDerivative f x)∗ u ≠ ⊤) :
    ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y := by
  let g : H → EReal := directionalDerivative f x
  have hzero : g 0 = 0 := directionalDerivative_zero hconv hx
  have hconj_nonneg : (0 : EReal) ≤ g∗ u := by
    -- The zero direction forces the conjugate value to be at least `0`.
    rw [conjugate_apply]
    simpa [hzero] using
      (le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) (0 : H))
  intro y
  by_contra hy
  have hylt : g y < ((⟪y, u⟫_ℝ : ℝ) : EReal) := lt_of_not_ge hy
  have hgy_top : g y ≠ ⊤ := ne_of_lt (lt_trans hylt (EReal.coe_lt_top _))
  have hgy_bot : g y ≠ ⊥ := by
    intro hgy_bot
    have hterm : (((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) ≤ g∗ u := by
      -- Evaluating the supremum at the violating direction already bounds the conjugate below.
      rw [conjugate_apply]
      exact le_iSup (fun z : H ↦ ((⟪z, u⟫_ℝ : ℝ) : EReal) - g z) y
    have htop : g∗ u = ⊤ := by
      apply le_antisymm le_top
      simpa [hgy_bot] using hterm
    exact hu htop
  have hy_real : (g y).toReal < ⟪y, u⟫_ℝ := by
    have hylt' : (((g y).toReal : ℝ) : EReal) < ((⟪y, u⟫_ℝ : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hgy_top hgy_bot] using hylt
    exact_mod_cast hylt'
  let gap : ℝ := ⟪y, u⟫_ℝ - (g y).toReal
  have hgap : 0 < gap := by
    -- The violating direction leaves a positive real gap between the pairing and `g y`.
    dsimp [gap]
    linarith
  have htop : g∗ u = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro M
    obtain ⟨n, hn⟩ := exists_nat_gt (max (M / gap) 0)
    have hn_pos : 0 < (n : ℝ) := by
      exact lt_of_le_of_lt (le_max_right (M / gap) 0) hn
    have hfrac : M / gap < (n : ℝ) := by
      exact lt_of_le_of_lt (le_max_left (M / gap) 0) hn
    have hMgap : M < (n : ℝ) * gap := by
      exact (div_lt_iff₀ hgap).mp hfrac
    have hscaled :
        (((⟪(n : ℝ) • y, u⟫_ℝ : ℝ) : EReal) - g ((n : ℝ) • y)) =
          (((n : ℝ) * gap : ℝ) : EReal) := by
      -- Positive homogeneity turns the violating gap into an arbitrarily large conjugate test term.
      dsimp [g]
      rw [directionalDerivative_smul_of_pos f hconv hx hn_pos]
      have hgy_coe : directionalDerivative f x y = (((g y).toReal : ℝ) : EReal) := by
        simpa [g] using (EReal.coe_toReal hgy_top hgy_bot).symm
      rw [real_inner_smul_left, hgy_coe, ← EReal.coe_mul, ← EReal.coe_sub]
      have hreal :
          (n : ℝ) * ⟪y, u⟫_ℝ - (g y).toReal * (n : ℝ) =
            (n : ℝ) * (⟪y, u⟫_ℝ - (g y).toReal) := by
        ring
      exact_mod_cast hreal
    have hterm :
        (((⟪(n : ℝ) • y, u⟫_ℝ : ℝ) : EReal) - g ((n : ℝ) • y)) ≤ g∗ u := by
      -- Evaluate the conjugate supremum at the scaled violating direction.
      rw [conjugate_apply]
      exact le_iSup (fun z : H ↦ ((⟪z, u⟫_ℝ : ℝ) : EReal) - g z) ((n : ℝ) • y)
    have hterm_gt :
        ((M : ℝ) : EReal) <
          (((⟪(n : ℝ) • y, u⟫_ℝ : ℝ) : EReal) - g ((n : ℝ) • y)) := by
      rw [hscaled]
      exact_mod_cast hMgap
    exact lt_of_lt_of_le hterm_gt hterm
  exact hu htop

/-- Helper for Proposition 17 17: outside the subdifferential, the conjugate of the directional
derivative is forced onto the indicator's `⊤` branch. -/
lemma conjugate_directionalDerivative_eq_top_of_not_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∉ (∂ f) x) :
    (directionalDerivative f x)∗ u = ⊤ := by
  by_contra hnotop
  have hdominate :
      ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y :=
    -- A finite conjugate value would reproduce the same domination criterion as a subgradient.
    inner_le_directionalDerivative_of_conjugate_ne_top
      (f := f) hconv (x := x) (u := u) hx hnotop
  exact hu <|
    (mem_subdifferential_iff_inner_le_directionalDerivative
      (f := f) hconv (x := x) (u := u) hx).2 hdominate

-- Proof sketch: use Proposition 17.14 to rewrite `u ∈ ∂ f(x)` as the pointwise domination
-- `⟪·,u⟫ ≤ f'(x;·)`. Then analyze the conjugate `sup_y (⟪y,u⟫ - f'(x;y))`: on the
-- subdifferential every supremand is `≤ 0` and the zero direction gives equality, while off the
-- subdifferential any violating direction scales to force the supremum to `⊤`.
/-- Proposition 17 17: for a convex `]-∞,+∞]`-valued function and an effective-domain point `x`,
the Fenchel conjugate of the directional derivative `y ↦ f'(x; y)` is the indicator of the
subdifferential `∂ f(x)`. -/
theorem conjugate_directionalDerivative_eq_setIndicator_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    (directionalDerivative f x)∗ = (ι[(∂ f) x]).asEReal := by
  ext u
  by_cases hu : u ∈ (∂ f) x
  · have hzero :
        (directionalDerivative f x)∗ u = 0 :=
      (conjugate_directionalDerivative_eq_zero_iff_mem_subdifferential
        (f := f) hconv (x := x) (u := u) hx).2 hu
    -- On the subdifferential, the conjugate takes the zero branch of the indicator.
    simpa [indicator_apply, hu] using hzero
  · have htop :
        (directionalDerivative f x)∗ u = ⊤ :=
      conjugate_directionalDerivative_eq_top_of_not_mem_subdifferential
        (f := f) hconv (x := x) (u := u) hx hu
    -- Off the subdifferential, the conjugate must take the `⊤` branch.
    simpa [indicator_apply, hu] using htop

end DirectionalDerivativesAndSubgradients

end ERealFunction
