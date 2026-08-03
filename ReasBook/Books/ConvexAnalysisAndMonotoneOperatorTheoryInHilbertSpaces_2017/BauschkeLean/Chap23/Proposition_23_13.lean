import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall: `lean_leansearch` only surfaced unrelated algebra-spectrum resolvent results,
-- so this item follows the verified local Chapter 22/23 owners
-- `SetValuedOperator.IsStronglyMonotone` and `J[A]`, with explicit resolvent witnesses replacing
-- the textbook single-valued notation `J_A x` and `J_A y`.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 23.13: fixing `γ = 1` in the scaled resolvent criterion identifies
resolvent witnesses with residual memberships `x - p ∈ A p`. -/
private theorem mem_resolvent_iff_residual_mem
    {A : SetValuedOperator H H} {x p : H} :
    p ∈ J[A] x ↔ x - p ∈ A p := by
  constructor
  · intro hp
    -- Reinterpret the resolvent witness through the scale-`1` criterion.
    have hp' : p ∈ J[((1 : ℝ) • A)] x := by
      simpa [one_smul] using hp
    have hscaled : x - p ∈ (1 : ℝ) • A p :=
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p).1 hp'
    simpa [one_smul] using hscaled
  · intro hpA
    -- Collapse the scale-`1` residual membership back to the plain resolvent witness.
    have hscaled : x - p ∈ (1 : ℝ) • A p := by
      simpa [one_smul] using hpA
    have hp' : p ∈ J[((1 : ℝ) • A)] x :=
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p).2 hscaled
    simpa [one_smul] using hp'

/-- Helper for Proposition 23.13: the strong-monotonicity residual pairing becomes the displayed
resolvent pairing after adding `‖p - q‖²`. -/
private theorem residual_pairing_add_eq
    {x y p q : H} :
    ‖p - q‖ ^ 2 + ⟪p - q, (x - p) - (y - q)⟫_ℝ = ⟪x - y, p - q⟫_ℝ := by
  let d : H := p - q
  have hsub : (x - p) - (y - q) = (x - y) - d := by
    dsimp [d]
    abel_nf
  -- Normalize both residual differences to the same core vector `d`.
  calc
    ‖p - q‖ ^ 2 + ⟪p - q, (x - p) - (y - q)⟫_ℝ
        = ‖d‖ ^ 2 + ⟪d, (x - y) - d⟫_ℝ := by
            simp [d, hsub]
    _ = ‖d‖ ^ 2 + (⟪d, x - y⟫_ℝ - ‖d‖ ^ 2) := by
          rw [inner_sub_right, real_inner_self_eq_norm_sq]
    _ = ⟪d, x - y⟫_ℝ := by
          ring
    _ = ⟪x - y, d⟫_ℝ := by
          rw [real_inner_comm]
    _ = ⟪x - y, p - q⟫_ℝ := by
          simp [d]

/-- Helper for Proposition 23.13: evaluating the resolvent inequality at shifted inputs
`u + x` and `v + y` produces the strong-monotonicity pairing plus `‖x - y‖²`. -/
private theorem shifted_input_pairing_eq
    {x y u v : H} :
    ⟪(u + x) - (v + y), x - y⟫_ℝ = ⟪x - y, u - v⟫_ℝ + ‖x - y‖ ^ 2 := by
  let d : H := x - y
  have hsub : (u + x) - (v + y) = (u - v) + d := by
    dsimp [d]
    abel_nf
  -- Expand the shifted input difference into the residual term and the self-pairing.
  calc
    ⟪(u + x) - (v + y), x - y⟫_ℝ = ⟪(u - v) + d, d⟫_ℝ := by
      simp [d, hsub]
    _ = ⟪u - v, d⟫_ℝ + ⟪d, d⟫_ℝ := by
      rw [inner_add_left]
    _ = ⟪x - y, u - v⟫_ℝ + ‖d‖ ^ 2 := by
      rw [real_inner_comm, real_inner_self_eq_norm_sq]
    _ = ⟪x - y, u - v⟫_ℝ + ‖x - y‖ ^ 2 := by
      simp [d]

/-- Proposition 23.13 (1): let `β ∈ ℝ_{++}`. Then `A` is strongly monotone with constant `β` if
and only if any resolvent witnesses `p ∈ J[A] x` and `q ∈ J[A] y` satisfy the explicit
`(β + 1)`-cocoercive inequality `((β : ℝ) + 1) * ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ`. This is the
source statement with the redundant monotonicity hypothesis removed, since the displayed
resolvent inequality already forces the required lower bound, and with witness-based resolvent
values replacing the single-valued notation `J_A x` and `J_A y`. -/
theorem isStronglyMonotone_iff_resolvent_cocoercive_of_mem
    {A : SetValuedOperator H H} (β : PosReal) :
    A.IsStronglyMonotone (β : ℝ) ↔
      ∀ ⦃x y p q : H⦄, p ∈ J[A] x → q ∈ J[A] y →
        ((β : ℝ) + 1) * ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by
  constructor
  · intro hstrong x y p q hp hq
    have hpA : x - p ∈ A p := (mem_resolvent_iff_residual_mem (A := A)).1 hp
    have hqA : y - q ∈ A q := (mem_resolvent_iff_residual_mem (A := A)).1 hq
    have hmono : (β : ℝ) * ‖p - q‖ ^ 2 ≤ ⟪p - q, (x - p) - (y - q)⟫_ℝ :=
      hstrong.ineq hpA hqA
    have hsum :
        ‖p - q‖ ^ 2 + (β : ℝ) * ‖p - q‖ ^ 2 ≤
          ‖p - q‖ ^ 2 + ⟪p - q, (x - p) - (y - q)⟫_ℝ := by
      simpa using add_le_add_left hmono (‖p - q‖ ^ 2)
    -- Add the quadratic correction term and rewrite to the resolvent pairing.
    calc
      ((β : ℝ) + 1) * ‖p - q‖ ^ 2 = ‖p - q‖ ^ 2 + (β : ℝ) * ‖p - q‖ ^ 2 := by
        ring
      _ ≤ ‖p - q‖ ^ 2 + ⟪p - q, (x - p) - (y - q)⟫_ℝ := hsum
      _ = ⟪x - y, p - q⟫_ℝ := residual_pairing_add_eq (x := x) (y := y) (p := p) (q := q)
  · intro hres
    refine ⟨β.2, ?_⟩
    intro x u y v hu hv
    have hxRes : x ∈ J[A] (u + x) := by
      -- Convert the graph witness `u ∈ A x` into the shifted resolvent witness `x ∈ J[A] (u + x)`.
      refine (mem_resolvent_iff_residual_mem (A := A) (x := u + x) (p := x)).2 ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu
    have hyRes : y ∈ J[A] (v + y) := by
      -- Do the same shift conversion for the second graph point.
      refine (mem_resolvent_iff_residual_mem (A := A) (x := v + y) (p := y)).2 ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv
    have hshift :
        ((β : ℝ) + 1) * ‖x - y‖ ^ 2 ≤ ⟪(u + x) - (v + y), x - y⟫_ℝ :=
      hres (x := u + x) (y := v + y) (p := x) (q := y) hxRes hyRes
    have hshift' :
        ((β : ℝ) + 1) * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ + ‖x - y‖ ^ 2 := by
      rw [shifted_input_pairing_eq (x := x) (y := y) (u := u) (v := v)] at hshift
      exact hshift
    have hshift'' :
        (β : ℝ) * ‖x - y‖ ^ 2 + ‖x - y‖ ^ 2 ≤
          ⟪x - y, u - v⟫_ℝ + ‖x - y‖ ^ 2 := by
      simpa [add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hshift'
    -- Cancel the common norm square to recover the strong-monotonicity inequality.
    exact (add_le_add_iff_right (‖x - y‖ ^ 2)).1 hshift''

/-- Proposition 23.13 (2): under the same hypotheses, if `A` is strongly monotone with constant
`β`, then any resolvent witnesses `p ∈ J[A] x` and `q ∈ J[A] y` satisfy the Lipschitz estimate
`‖p - q‖ ≤ (1 / ((β : ℝ) + 1)) * ‖x - y‖`. -/
theorem norm_sub_le_inv_one_add_mul_norm_sub_of_mem_resolvent
    {A : SetValuedOperator H H} (β : PosReal)
    (hstrong : A.IsStronglyMonotone (β : ℝ))
    {x y p q : H} (hp : p ∈ J[A] x) (hq : q ∈ J[A] y) :
    ‖p - q‖ ≤ (1 / ((β : ℝ) + 1)) * ‖x - y‖ := by
  have hβ1_pos : 0 < (β : ℝ) + 1 := by
    linarith [β.2]
  have hineq :
      ((β : ℝ) + 1) * ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ :=
    ((isStronglyMonotone_iff_resolvent_cocoercive_of_mem (A := A) β).1 hstrong) hp hq
  by_cases hpq : p = q
  · -- The zero-distance case is immediate.
    have hnonneg : 0 ≤ (1 / ((β : ℝ) + 1)) * ‖x - y‖ := by
      exact mul_nonneg (one_div_nonneg.mpr (le_of_lt hβ1_pos)) (norm_nonneg _)
    simpa [hpq] using hnonneg
  · have hnorm_pos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
    have hprod :
        ((β : ℝ) + 1) * ‖p - q‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ := by
      calc
        ((β : ℝ) + 1) * ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := hineq
        _ ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
    have hprod' :
        (((β : ℝ) + 1) * ‖p - q‖) * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
      simpa [pow_two, mul_assoc] using hprod
    have hcancel : ((β : ℝ) + 1) * ‖p - q‖ ≤ ‖x - y‖ := by
      -- Cancel the positive factor `‖p - q‖` from the quadratic estimate.
      exact le_of_mul_le_mul_right hprod' hnorm_pos
    have hdiv : ‖p - q‖ ≤ ‖x - y‖ / ((β : ℝ) + 1) := by
      exact (le_div_iff₀ hβ1_pos).2 (by simpa [mul_comm] using hcancel)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Proposition 23.13 (3): for `β ∈ ℝ_{++}`, the Lipschitz constant `1 / (β + 1)` lies in
`]0, 1[`, formalized as `Set.Ioo (0 : ℝ) 1`. -/
theorem inv_one_add_mem_Ioo_zero_one (β : PosReal) :
    (1 / ((β : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hβ1_pos : 0 < (β : ℝ) + 1 := by
    linarith [β.2]
  have hβ1_gt : (1 : ℝ) < (β : ℝ) + 1 := by
    linarith [β.2]
  constructor
  · -- Positivity is immediate from the positive denominator.
    exact one_div_pos.mpr hβ1_pos
  · -- A reciprocal of a number larger than `1` lies strictly below `1`.
    simpa using (div_lt_one hβ1_pos).2 hβ1_gt

end SetValuedOperator
