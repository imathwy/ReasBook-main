import Mathlib
import BauschkeLean.Chap20.Example_20_16

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

universe u

namespace ContinuousLinearMap

/-- The quadratic potential `q_A(x) = (1 / 2) ⟪x, A x⟫_ℝ` attached to a bounded linear operator,
realized as the diagonal of the canonical sesquilinear form `toSesqForm A`. -/
noncomputable def quadraticPotential {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : H → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * A.toSesqForm x x

/- Lean cannot parse an arbitrary term as a literal subscript, so we use the bracketed surface
`q[A]` as the direct notation for the quadratic potential `q_A`. -/
scoped notation:max "q[" A:max "]" => quadraticPotential A

/-- Evaluating `quadraticPotential A` at `x` gives `(1 / 2) ⟪x, A x⟫_ℝ`. -/
@[simp] theorem quadraticPotential_apply {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : H →L[ℝ] H) (x : H) :
    q[A] x = (1 / 2 : ℝ) * ⟪x, A x⟫_ℝ := rfl

end ContinuousLinearMap

/-- Helper for Example 17 8: the quadratic form `x ↦ ⟪x, A x⟫_ℝ` is exactly the quadratic
potential of the symmetric part `A + A†`. -/
private lemma quadraticPotential_symmetricPart_eq_quadraticForm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (x : H) :
    ContinuousLinearMap.quadraticPotential (A + A†) x = ⟪x, A x⟫_ℝ := by
  have hadj : ⟪x, (A†) x⟫_ℝ = ⟪x, A x⟫_ℝ := by
    calc
      ⟪x, (A†) x⟫_ℝ = ⟪A x, x⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪x, A x⟫_ℝ := by
        rw [real_inner_comm]
  -- Expand the symmetric part and use the adjoint identity to collapse the two equal terms.
  calc
    ContinuousLinearMap.quadraticPotential (A + A†) x = (1 / 2 : ℝ) * ⟪x, (A + A†) x⟫_ℝ := by
      simp
    _ = (1 / 2 : ℝ) * ((2 : ℝ) * ⟪x, A x⟫_ℝ) := by
      congr 1
      rw [show (A + A†) x = A x + (A†) x by rfl, inner_add_right, hadj]
      ring
    _ = ⟪x, A x⟫_ℝ := by
      nlinarith

/-- Helper for Example 17 8: the quadratic potential is homogeneous of degree two. -/
private lemma quadraticPotential_smul
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H →L[ℝ] H) (a : ℝ) (x : H) :
    q[B] (a • x) = a ^ 2 * q[B] x := by
  -- Pull the scalar through both slots of the quadratic form.
  calc
    q[B] (a • x) = (1 / 2 : ℝ) * ⟪a • x, B (a • x)⟫_ℝ := by
      simp
    _ = (1 / 2 : ℝ) * (a ^ 2 * ⟪x, B x⟫_ℝ) := by
      rw [map_smul, inner_smul_left, inner_smul_right]
      simp [pow_two, mul_assoc]
    _ = a ^ 2 * q[B] x := by
      rw [ContinuousLinearMap.quadraticPotential_apply]
      ring

/-- Helper for Example 17 8: monotonicity of `B` controls the Jensen gap of the quadratic
potential `q[B]` on convex combinations. -/
private lemma quadraticPotential_convex_combo_le_of_isMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H →L[ℝ] H) (hB_mono : B.toLinearMap.IsMonotone)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x y : H) :
    q[B] (a • x + (1 - a) • y) ≤ a * q[B] x + (1 - a) * q[B] y := by
  have hmono : 0 ≤ ⟪x - y, B (x - y)⟫_ℝ := by
    simpa [real_inner_comm] using hB_mono (x - y)
  have hdecomp :
      a * q[B] x + (1 - a) * q[B] y - q[B] (a • x + (1 - a) • y) =
        (1 / 2 : ℝ) * (a * (1 - a)) * ⟪x - y, B (x - y)⟫_ℝ := by
    -- Expand the quadratic potential at the convex combination and isolate the monotone defect.
    simp [ContinuousLinearMap.quadraticPotential_apply, map_add, map_smul,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      sub_eq_add_neg]
    ring
  have hab_nonneg : 0 ≤ a * (1 - a) := mul_nonneg ha0 (sub_nonneg.mpr ha1)
  have hgap_nonneg :
      0 ≤ a * q[B] x + (1 - a) * q[B] y - q[B] (a • x + (1 - a) • y) := by
    rw [hdecomp]
    exact mul_nonneg (mul_nonneg (by norm_num) hab_nonneg) hmono
  linarith

-- Proof sketch: Example 2.57 identifies the gradient of the quadratic form
-- `x ↦ ⟪x, A x⟫_ℝ` with the linear field `x ↦ (A + A.adjoint) x`. Proposition 17.7 on
-- `Set.univ` then says that convexity is equivalent to pointwise nonnegativity of the quadratic
-- form of this second derivative, which here is exactly
-- `x ↦ ⟪(A + A†) x, x⟫_ℝ`.
/-- Example 17 8: for a bounded linear operator `A` on a real Hilbert space, the quadratic form
`x ↦ ⟪x, A x⟫_ℝ` is convex on `H` if and only if the quadratic form of the symmetric part `A + A†`
is pointwise nonnegative. -/
theorem quadraticForm_convexOn_univ_iff_symmetricPart_nonnegative
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    ConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      ∀ x : H, 0 ≤ ⟪(A + A†) x, x⟫_ℝ := by
  let B : H →L[ℝ] H := A + A†
  have hform : (fun x : H ↦ ⟪x, A x⟫_ℝ) = q[B] := by
    -- Rewrite the source quadratic form as the canonical quadratic potential of `B`.
    funext x
    simpa [B] using (quadraticPotential_symmetricPart_eq_quadraticForm A x).symm
  -- Route correction: the planned Proposition 17.7 import is broken in this workspace, so prove
  -- the criterion directly from the quadratic identity of the self-adjoint symmetric part.
  rw [hform]
  change ConvexOn ℝ Set.univ (q[B]) ↔ ∀ x : H, 0 ≤ ⟪B x, x⟫_ℝ
  constructor
  · intro hconv x
    have hmid :=
      hconv.2 (x := x) (y := 0) (by simp) (by simp)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
    have hzero : q[B] (0 : H) = 0 := by
      simp [ContinuousLinearMap.quadraticPotential_apply]
    -- Midpoint convexity and degree-two homogeneity force the diagonal quadratic form to be
    -- nonnegative.
    have hhalf : q[B] ((1 / 2 : ℝ) • x) ≤ (1 / 2 : ℝ) * q[B] x := by
      simpa [hzero, smul_eq_mul] using hmid
    rw [quadraticPotential_smul B (1 / 2 : ℝ) x] at hhalf
    have hq_nonneg : 0 ≤ q[B] x := by
      linarith
    have hscaled_nonneg : 0 ≤ (2 : ℝ) * q[B] x := by
      exact mul_nonneg (by norm_num) hq_nonneg
    simpa [ContinuousLinearMap.quadraticPotential_apply, real_inner_comm] using hscaled_nonneg
  · intro hnonneg
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have ha1 : a ≤ 1 := by
      linarith
    have hB_mono : B.toLinearMap.IsMonotone := by
      simpa [LinearMap.IsMonotone] using hnonneg
    have hcombo :
        q[B] (a • x + b • y) ≤ a * q[B] x + b * q[B] y := by
      have hb_eq : b = 1 - a := by
        linarith
      rw [hb_eq]
      exact quadraticPotential_convex_combo_le_of_isMonotone B hB_mono ha ha1 x y
    simpa [smul_eq_mul] using hcombo

-- Proof sketch: use Example 20.16 to replace monotonicity of `A + A†` by the canonical owner
-- predicate `LinearMap.IsMonotone`, then unfold that owner on the symmetric part.
/-- Canonical bridge for Example 17.8: the same convexity criterion can be expressed by saying
that `A` is monotone. -/
theorem quadraticForm_convexOn_univ_iff_isMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    ConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      A.toLinearMap.IsMonotone := by
  rw [isMonotone_iff_add_adjoint_isMonotone]
  simpa [LinearMap.IsMonotone] using
    quadraticForm_convexOn_univ_iff_symmetricPart_nonnegative A
