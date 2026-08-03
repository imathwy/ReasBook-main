import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall: `lean_leansearch` only surfaced unrelated single-valued resolvent and
-- convexity API, so this item follows the local Chapter 22/23 owners
-- `SetValuedOperator.IsUniformlyMonotone` and `J[A]`.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace IsUniformlyMonotone

/-- Helper for Proposition 23.12: fixing `γ = 1` in Proposition 23.2 identifies resolvent
witnesses with residual memberships `x - p ∈ A p`. -/
private theorem mem_resolvent_iff_residual_mem
    {A : SetValuedOperator H H} {x p : H} :
    p ∈ J[A] x ↔ x - p ∈ A p := by
  -- Specialize the scaled residual characterization to `γ = 1` in each direction.
  constructor
  · intro hp
    have hp' : p ∈ J[((1 : ℝ) • A)] x := by
      simpa [one_smul] using hp
    have hscaled : x - p ∈ (1 : ℝ) • A p :=
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p).1 hp'
    simpa [one_smul] using hscaled
  · intro hpA
    have hscaled : x - p ∈ (1 : ℝ) • A p := by
      simpa [one_smul] using hpA
    have hp' : p ∈ J[((1 : ℝ) • A)] x :=
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p).2 hscaled
    simpa [one_smul] using hp'

/-- Helper for Proposition 23.12: the residual pairing from the uniform monotonicity inequality
rewrites to the textbook resolvent pairing after adding `‖p - q‖²`. -/
private theorem residual_pairing_add_eq
    {x y p q : H} :
    ‖p - q‖ ^ 2 + ⟪p - q, (x - p) - (y - q)⟫_ℝ = ⟪x - y, p - q⟫_ℝ := by
  let d : H := p - q
  have hsub : (x - p) - (y - q) = (x - y) - d := by
    dsimp [d]
    abel_nf
  -- Normalize the residual difference and collapse the quadratic correction term.
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

/-- Helper for Proposition 23.12: if the residuals `x - p` and `y - q` lie in `A p` and `A q`,
uniform monotonicity yields the resolvent inequality in the source form. -/
private theorem graphResidual_ineq
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ)
    {x y p q : H} (hpA : x - p ∈ A p) (hqA : y - q ∈ A q) :
    ((‖p - q‖ ^ 2 : ℝ) : EReal) + φ ‖p - q‖₊ ≤ (⟪x - y, p - q⟫_ℝ : EReal) := by
  -- Apply uniform monotonicity to the two graph-residual points.
  have hmono :
      φ ‖p - q‖₊ ≤ (⟪p - q, (x - p) - (y - q)⟫_ℝ : EReal) :=
    hA.ineq hpA hqA
  have hsum :
      ((‖p - q‖ ^ 2 : ℝ) : EReal) + φ ‖p - q‖₊ ≤
        ((‖p - q‖ ^ 2 : ℝ) : EReal) + (⟪p - q, (x - p) - (y - q)⟫_ℝ : EReal) := by
    simpa using add_le_add_right hmono (((‖p - q‖ ^ 2 : ℝ) : EReal))
  have hrewrite :
      ((‖p - q‖ ^ 2 : ℝ) : EReal) + (⟪p - q, (x - p) - (y - q)⟫_ℝ : EReal) =
        (⟪x - y, p - q⟫_ℝ : EReal) := by
    exact_mod_cast residual_pairing_add_eq (x := x) (y := y) (p := p) (q := q)
  -- Rewrite the right-hand side into the textbook pairing.
  calc
    ((‖p - q‖ ^ 2 : ℝ) : EReal) + φ ‖p - q‖₊
        ≤ ((‖p - q‖ ^ 2 : ℝ) : EReal) + (⟪p - q, (x - p) - (y - q)⟫_ℝ : EReal) := hsum
    _ = (⟪x - y, p - q⟫_ℝ : EReal) := hrewrite

/-- Proposition 23.12: if `A` is uniformly monotone with modulus `φ`, then any resolvent witnesses
`p ∈ J[A] x` and `q ∈ J[A] y` satisfy the source inequality `(23.13)`,
`‖p - q‖^2 + φ ‖p - q‖₊ ≤ ⟪x - y, p - q⟫_ℝ`. This is the textbook statement with explicit
witnesses replacing the single-valued notation `J_A x` and `J_A y`. -/
theorem resolvent_ineq
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ)
    {x y p q : H} (hp : p ∈ J[A] x) (hq : q ∈ J[A] y) :
    ((‖p - q‖ ^ 2 : ℝ) : EReal) + φ ‖p - q‖₊ ≤ (⟪x - y, p - q⟫_ℝ : EReal) := by
  -- Convert the resolvent witnesses directly into the residual memberships used by monotonicity.
  have hpA : x - p ∈ A p :=
    (mem_resolvent_iff_residual_mem).1 hp
  have hqA : y - q ∈ A q :=
    (mem_resolvent_iff_residual_mem).1 hq
  -- The residual formulation is exactly the source proof after these witness rewrites.
  exact graphResidual_ineq hA hpA hqA

end IsUniformlyMonotone

end SetValuedOperator
