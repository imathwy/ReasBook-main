import Mathlib
import BauschkeLean.Chap12.Definition_12_20_Core
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 19: a self-conjugate function cannot attain `⊥` at any point. -/
lemma self_conjugate_ne_bot
    {f : H → EReal} (hself : f = f∗) (x : H) :
    f x ≠ ⊥ := by
  intro hbot
  have hdefect :
      (((⟪x, x⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ x := by
    -- Evaluate the defining supremum of `f∗ x` at the primal point `x`.
    rw [conjugate_apply]
    exact le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f y)) x
  have htop_le : (⊤ : EReal) ≤ f∗ x := by
    calc
      (⊤ : EReal) = (((⟪x, x⟫_ℝ : ℝ) : EReal) - f x) := by
        rw [hbot, real_inner_self_eq_norm_sq, EReal.coe_sub_bot]
      _ ≤ f∗ x := hdefect
  have hselfx : f∗ x = ⊥ := by
    calc
      f∗ x = f x := by
        simpa using congrArg (fun g : H → EReal ↦ g x) hself.symm
      _ = ⊥ := hbot
  have htop_eq : f∗ x = ⊤ := top_le_iff.mp htop_le
  rw [hselfx] at htop_eq
  simp at htop_eq

/-- Helper for Proposition 13 19: Fenchel conjugation is pointwise antitone. -/
lemma conjugate_antitone :
    Antitone (conjugate : (H → EReal) → H → EReal) := by
  intro f g hfg u
  -- Compare the defining suprema term-by-term using the reversed affine defects.
  rw [conjugate_apply, conjugate_apply]
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - g x)
        ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) := by
          exact EReal.sub_le_sub le_rfl (hfg x)
    _ ≤ ⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) := by
          exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Helper for Proposition 13 19: every affine defect of the quadratic kernel is bounded above by
the quadratic value at the dual point. -/
lemma affine_defect_half_squared_norm_le
    (x u : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - halfSquaredNorm.asEReal x) ≤
      halfSquaredNorm.asEReal u := by
  -- Rewrite the defect in real coordinates and use `‖x - u‖² ≥ 0`.
  rw [Function.asEReal_apply, halfSquaredNorm_apply, Function.asEReal_apply,
    halfSquaredNorm_apply, ← EReal.coe_sub]
  have hnorm :
      ‖x - u‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, u⟫_ℝ + ‖u‖ ^ 2 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_mul, real_inner_comm] using
      norm_sub_sq_real x u
  have hreal : ⟪x, u⟫_ℝ - (‖x‖ ^ 2) / 2 ≤ (‖u‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg ‖x - u‖, hnorm]
  exact_mod_cast hreal

/-- Helper for Proposition 13 19: the quadratic kernel is below its own Fenchel conjugate by
evaluating the defining supremum at the diagonal point. -/
lemma half_squared_norm_le_conjugate_half_squared_norm :
    ((halfSquaredNorm (H := H)).asEReal : H → EReal) ≤
      ((halfSquaredNorm (H := H)).asEReal : H → EReal)∗ := by
  intro u
  have hdiag :
      (((⟪u, u⟫_ℝ : ℝ) : EReal) - halfSquaredNorm.asEReal u) ≤
        (halfSquaredNorm.asEReal)∗ u := by
    -- The diagonal point `u` is one admissible term in the conjugate supremum.
    rw [conjugate_apply]
    exact le_iSup
      (fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - halfSquaredNorm.asEReal x))
      u
  have hdiag' : ((((‖u‖ ^ 2) / 2 : ℝ) : EReal)) ≤ (halfSquaredNorm.asEReal)∗ u := by
    -- On the diagonal, the affine defect equals the quadratic value itself.
    rw [Function.asEReal_apply, halfSquaredNorm_apply, real_inner_self_eq_norm_sq,
      ← EReal.coe_sub] at hdiag
    have hreal_eq : ‖u‖ ^ 2 - (‖u‖ ^ 2) / 2 = (‖u‖ ^ 2) / 2 := by
      ring
    simpa [hreal_eq] using hdiag
  calc
    halfSquaredNorm.asEReal u = ((((1 / 2 : ℝ) * ‖u‖ ^ 2 : ℝ) : EReal)) := by
      simp [Function.asEReal_apply, div_eq_mul_inv, mul_comm]
    _ = ((((‖u‖ ^ 2) / 2 : ℝ) : EReal)) := by
      congr 1
      ring
    _ ≤ (halfSquaredNorm.asEReal)∗ u := hdiag'

/-- Helper for Proposition 13 19: the quadratic kernel dominates its own Fenchel conjugate because
every affine defect is controlled by the completed-square inequality. -/
lemma conjugate_half_squared_norm_le_half_squared_norm :
    (((halfSquaredNorm (H := H)).asEReal : H → EReal)∗) ≤
      ((halfSquaredNorm (H := H)).asEReal : H → EReal) := by
  intro u
  -- Bound each term in the supremum by the target quadratic value.
  rw [conjugate_apply]
  refine iSup_le fun x ↦ affine_defect_half_squared_norm_le (x := x) (u := u)

/-- Helper for Proposition 13 19: the canonical quadratic is self-conjugate. -/
lemma half_squared_norm_self_conjugate :
    (halfSquaredNorm.asEReal : H → EReal) =
      (halfSquaredNorm.asEReal : H → EReal)∗ := by
  -- The two pointwise bounds meet at equality.
  exact le_antisymm
    half_squared_norm_le_conjugate_half_squared_norm
    conjugate_half_squared_norm_le_half_squared_norm

/-- Helper for Proposition 13 19: self-conjugacy forces the quadratic lower bound
`halfSquaredNorm.asEReal ≤ f`. -/
lemma half_squared_norm_le_of_self_conjugate
    {f : H → EReal} (hself : f = f∗) :
    halfSquaredNorm.asEReal ≤ f := by
  intro x
  by_cases htop : f x = ⊤
  · -- If `f x = ⊤`, the quadratic lower bound is immediate.
    simp [htop, Function.asEReal_apply]
  · have hbot : f x ≠ ⊥ := self_conjugate_ne_bot (H := H) hself x
    have hdefect :
        (((⟪x, x⟫_ℝ : ℝ) : EReal) - f x) ≤ f x := by
      -- Evaluate the conjugate at `x` and rewrite it back with the self-conjugacy identity.
      have hsup :
          (((⟪x, x⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ x := by
        rw [conjugate_apply]
        exact le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f y)) x
      rw [← hself] at hsup
      exact hsup
    have hsum :
        (((⟪x, x⟫_ℝ : ℝ) : EReal) ≤ f x + f x) :=
      (EReal.sub_le_iff_le_add (Or.inl hbot) (Or.inl htop)).1 hdefect
    rw [← EReal.coe_toReal htop hbot, ← EReal.coe_toReal htop hbot, ← EReal.coe_add] at hsum
    have hreal : ⟪x, x⟫_ℝ ≤ (f x).toReal + (f x).toReal := by
      exact_mod_cast hsum
    have hhalf : (‖x‖ ^ 2) / 2 ≤ (f x).toReal := by
      rw [real_inner_self_eq_norm_sq] at hreal
      nlinarith
    have hcast : ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) ≤ f x := by
      -- Return to `EReal` after proving the finite real inequality.
      rw [← EReal.coe_toReal htop hbot]
      exact_mod_cast hhalf
    simpa [Function.asEReal_apply, halfSquaredNorm_apply, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hcast

/-- Helper for Proposition 13 19: antitonicity of Fenchel conjugation turns the quadratic lower
bound into the matching upper bound. -/
lemma self_conjugate_le_half_squared_norm
    {f : H → EReal} (hself : f = f∗) :
    f ≤ halfSquaredNorm.asEReal := by
  -- Conjugate the lower bound and rewrite both fixed-point identities.
  calc
    f = f∗ := hself
    _ ≤ (halfSquaredNorm.asEReal)∗ :=
      conjugate_antitone (half_squared_norm_le_of_self_conjugate (H := H) hself)
    _ = halfSquaredNorm.asEReal := by
      exact half_squared_norm_self_conjugate (H := H).symm

-- Proof sketch: one direction is Example 13.6, which identifies the conjugate of the quadratic
-- `x ↦ ‖x‖² / 2` with itself. For the converse, apply the Fenchel--Young inequality to `f` at
-- `(x, x)` to get the lower bound `‖x‖² / 2 ≤ f x`, then use the order-reversing property of
-- conjugation from Proposition 13.16 together with `f = f∗` to force the reverse inequality.
/-- Proposition 13 19: an extended-real-valued function on a real inner-product space is
self-conjugate exactly when it is the canonical quadratic owner `halfSquaredNorm.asEReal`. -/
theorem self_conjugate_iff_eq_half_squared_norm
    (f : H → EReal) :
    f = f∗ ↔
      f = halfSquaredNorm.asEReal := by
  constructor
  · intro hself
    -- Combine the pointwise lower and upper bounds obtained from the self-conjugacy hypothesis.
    exact le_antisymm
      (self_conjugate_le_half_squared_norm (H := H) hself)
      (half_squared_norm_le_of_self_conjugate (H := H) hself)
  · intro hquad
    -- Rewrite to the canonical quadratic and invoke Example 13.6.
    rw [hquad]
    simpa using (half_squared_norm_self_conjugate (H := H))

end Conjugation

end ERealFunction
