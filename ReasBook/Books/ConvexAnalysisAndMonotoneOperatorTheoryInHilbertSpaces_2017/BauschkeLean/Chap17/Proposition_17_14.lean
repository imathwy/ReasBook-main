import Mathlib
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

include hconv

omit hconv in
/-- Helper for Proposition 17 14: a subgradient at `x` gives a lower bound on every positive
directional increment quotient based at `x`. -/
private theorem inner_le_increment_quotient_of_mem_subdifferential
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

omit hconv in
/-- Helper for Proposition 17 14: every subgradient yields a pointwise lower bound for the
directional derivative. -/
private theorem forall_inner_le_directionalDerivative_of_mem_subdifferential
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) := by
  intro y
  rw [directionalDerivative]
  apply le_sInf
  rintro q ⟨α, rfl⟩
  -- Every positive directional difference quotient dominates the inner product.
  simpa [directionalDifferenceQuotient] using
    inner_le_increment_quotient_of_mem_subdifferential
      (f := f) (x := x) (u := u) (y := y) hx hu (α := (α : ℝ)) α.2

/-- Helper for Proposition 17 14: pointwise domination by the directional derivative recovers the
subgradient inequality at `x`. -/
private theorem mem_subdifferential_of_forall_inner_le_directionalDerivative
    {x u : H} (hx : x ∈ effectiveDomain f)
    (hu : ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro z
  have hdir : (⟪z - x, u⟫_ℝ : EReal) ≤ f′(x; z - x) := hu (z - x)
  -- Evaluate the directional-derivative bound in the source direction `z - x`.
  calc
    (⟪z - x, u⟫_ℝ : EReal) + (f x : EReal) ≤
        f′(x; z - x) + (f x : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hdir (f x : EReal)
    _ ≤ (f z : EReal) := directionalDerivative_add_value_le f hconv hx z

/-- Helper for Proposition 17 14: for a convex function, subdifferentiability at `x` forces
`x` into the effective domain. -/
private theorem mem_effectiveDomain_of_subdifferentiableAt
    {x : H} (hxsub : SubdifferentiableAt f x) :
    x ∈ effectiveDomain f := by
  have hdom : (effectiveDomain f).Nonempty := hconv.nonempty
  -- Convexity supplies a nonempty effective domain, so Proposition 16.4 applies to `hxsub`.
  exact hxsub.mem_effectiveDomain hdom

-- Proof sketch: unfold membership in the subdifferential, apply Proposition 17.2 (2) to the
-- direction `y - x`, and use convexity to pass between the affine-minorant inequality and the
-- directional-derivative lower bound.
/-- Proposition 17 14 (1): at an effective-domain point of a convex function, a vector belongs to
the subdifferential exactly when its inner-product functional is pointwise dominated by the
directional derivative. -/
theorem mem_subdifferential_iff_inner_le_directionalDerivative
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔ ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ (f′(x; y)) := by
  constructor
  · intro hu
    -- The forward implication is the quotient-bound route followed by the directional limit.
    exact forall_inner_le_directionalDerivative_of_mem_subdifferential
      (f := f) hx hu
  · intro hu
    -- The reverse implication plugs the bound into Proposition 17.2 (2).
    exact mem_subdifferential_of_forall_inner_le_directionalDerivative
      (f := f) (hconv := hconv) hx hu

-- Proof sketch: `hconv.nonempty` supplies the nonempty effective-domain hypothesis needed for
-- Proposition 16.4 (1), which yields `x ∈ effectiveDomain f` from `SubdifferentiableAt f x`;
-- then apply Proposition 17.2 (6).
/-- Proposition 17 14 (2): if a convex `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then its directional derivative at `x` is proper. -/
theorem SubdifferentiableAt.directionalDerivative_isProper
    {x : H}
    (hxsub : SubdifferentiableAt f x) :
    IsProper (directionalDerivative f x) := by
  have hx : x ∈ effectiveDomain f :=
    mem_effectiveDomain_of_subdifferentiableAt (f := f) (hconv := hconv) hxsub
  -- Once `x` is in the effective domain, Proposition 17.2 (6) applies directly.
  exact ERealFunction.directionalDerivative_isProper (f := f) hconv hx

-- Proof sketch: derive the nonempty effective-domain input from `hconv.nonempty`, use
-- Proposition 16.4 (1) to obtain `x ∈ effectiveDomain f`, and invoke Proposition 17.2 (4).
/-- Proposition 17 14 (3): if a convex `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then its directional derivative at `x` is sublinear. -/
theorem SubdifferentiableAt.sublinear_directionalDerivative
    {x : H}
    (hxsub : SubdifferentiableAt f x) :
    Sublinear (directionalDerivative f x) := by
  have hx : x ∈ effectiveDomain f :=
    mem_effectiveDomain_of_subdifferentiableAt (f := f) (hconv := hconv) hxsub
  -- The sublinearity clause is Proposition 17.2 (4) at the effective-domain point `x`.
  exact ERealFunction.sublinear_directionalDerivative (f := f) hconv hx

end DirectionalDerivativesAndSubgradients

end ERealFunction
