import Mathlib
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.
-- `lean_leansearch` was unavailable in this run; the local owner/API was checked against
-- Theorem 16.56 and Proposition 16.20.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 16.57: coercing a continuous convex real-valued function through
`toEReal` preserves convexity on its effective domain. -/
lemma convexOn_toEReal_of_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function stays finite after the canonical `toEReal` coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Effective-domain membership is automatic because the domain is all of `H`.
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    -- Rewrite the convexity inequality back to the original real-valued function.
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * f x + (1 - a) * f y : ℝ) : EReal)
    exact_mod_cast hreal

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 16.57: continuity of a real-valued function upgrades every point to a
continuity point on the effective domain of its `toEReal` coercion. -/
lemma continuousAtOnEffectiveDomain_toEReal_of_continuous
    (f : H → ℝ) (hcont : Continuous f) (x : H) :
    ContinuousAtOnEffectiveDomain f.toEReal x := by
  refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
  -- The effective domain is all of `H`, so continuity within it is ordinary continuity.
  simpa [Function.effectiveDomain_toEReal, Function.toEReal_apply] using
    hcont.continuousAt.continuousWithinAt

/-- Helper for Corollary 16.57: continuity and convexity on all of `H` guarantee a nonempty
subdifferential at every point. -/
lemma subdifferential_nonempty_toEReal_of_continuous_convexOn_univ
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) (x : H) :
    ((∂ f.toEReal) x).Nonempty := by
  have hconvE : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOn_toEReal_of_convexOn_univ f hconv
  have hxcont : ContinuousAtOnEffectiveDomain f.toEReal x :=
    continuousAtOnEffectiveDomain_toEReal_of_continuous f hcont x
  -- Proposition 16.17 supplies a subgradient at each continuity point of the effective domain.
  exact
    (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
      (f := f.toEReal) hconvE hxcont).1

omit [CompleteSpace H] in
/-- Helper for Corollary 16.57: the `IsLUB` hypothesis bounds the norm of every vector in the
range of the subdifferential. -/
lemma norm_le_beta_of_mem_range_subdifferential
    (f : H → ℝ) (β : NNReal) {u : H}
    (hu : u ∈ SetValuedOperator.range (∂ f.toEReal))
    (hβ : IsLUB ((fun v : H ↦ ‖v‖) '' SetValuedOperator.range (∂ f.toEReal)) (β : ℝ)) :
    ‖u‖ ≤ (β : ℝ) := by
  -- Apply the upper-bound part of `IsLUB` to the image point `‖u‖`.
  exact hβ.1 (Set.mem_image_of_mem (fun v : H ↦ ‖v‖) hu)

omit [CompleteSpace H] in
/-- Helper for Corollary 16.57: subgradients of `f.toEReal` can be read as ordinary real affine
minorant inequalities. -/
lemma subgradient_real_inequality_of_mem_toEReal_subdifferential
    (f : H → ℝ) {x u y : H} (hu : u ∈ (∂ f.toEReal) x) :
    inner ℝ (y - x) u + f x ≤ f y := by
  have htest :
      (inner ℝ (y - x) u : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := u)).1 hu y
  -- The real-valued coercion rewrites the subgradient inequality back to `ℝ`.
  exact EReal.coe_le_coe_iff.mp <| by
    simpa [Function.toEReal_apply, EReal.coe_add] using htest

/-- Corollary 16.57: let `f : H → ℝ` be convex and continuous. If `β` is the supremum of the
norms of the range of `∂ f.toEReal`, then `f` is Lipschitz continuous with constant `β`. -/
theorem lipschitzWith_of_continuous_convexOn_univ_of_isLUB_norm_range_subdifferential
    (f : H → ℝ) (β : NNReal) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : IsLUB ((fun u : H ↦ ‖u‖) '' SetValuedOperator.range (∂ f.toEReal)) (β : ℝ)) :
    LipschitzWith β f := by
  -- Route correction: the planned import path through Theorem 16.56 is currently broken upstream,
  -- so use Proposition 16.17 to obtain endpoint subgradients and then compare the two affine
  -- minorant inequalities directly.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  obtain ⟨u, hu⟩ :=
    subdifferential_nonempty_toEReal_of_continuous_convexOn_univ f hcont hconv x
  obtain ⟨v, hv⟩ :=
    subdifferential_nonempty_toEReal_of_continuous_convexOn_univ f hcont hconv y
  have hu_range : u ∈ SetValuedOperator.range (∂ f.toEReal) := by
    rw [SetValuedOperator.mem_range_iff]
    exact ⟨x, hu⟩
  have hv_range : v ∈ SetValuedOperator.range (∂ f.toEReal) := by
    rw [SetValuedOperator.mem_range_iff]
    exact ⟨y, hv⟩
  have huβ : ‖u‖ ≤ (β : ℝ) :=
    norm_le_beta_of_mem_range_subdifferential f β hu_range hβ
  have hvβ : ‖v‖ ≤ (β : ℝ) :=
    norm_le_beta_of_mem_range_subdifferential f β hv_range hβ
  have hxu :
      ⟪y - x, u⟫_ℝ + f x ≤ f y :=
    subgradient_real_inequality_of_mem_toEReal_subdifferential (f := f) (u := u) (y := y) hu
  have hyv :
      ⟪x - y, v⟫_ℝ + f y ≤ f x :=
    subgradient_real_inequality_of_mem_toEReal_subdifferential (f := f) (u := v) (y := x) hv
  have hxy :
      f x - f y ≤ (β : ℝ) * ‖x - y‖ := by
    have hinner_lower : -((β : ℝ) * ‖x - y‖) ≤ ⟪y - x, u⟫_ℝ := by
      have hinner_abs : |⟪y - x, u⟫_ℝ| ≤ (β : ℝ) * ‖x - y‖ := by
        calc
          |⟪y - x, u⟫_ℝ| ≤ ‖y - x‖ * ‖u‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖y - x‖ * (β : ℝ) := by
            exact mul_le_mul_of_nonneg_left huβ (norm_nonneg _)
          _ = (β : ℝ) * ‖x - y‖ := by rw [norm_sub_rev, mul_comm]
      exact le_trans (neg_le_neg hinner_abs) (neg_abs_le _)
    have hsub : f x + -((β : ℝ) * ‖x - y‖) ≤ f y := by
      calc
        f x + -((β : ℝ) * ‖x - y‖) ≤ f x + ⟪y - x, u⟫_ℝ := by
          simpa [add_comm] using add_le_add_left hinner_lower (f x)
        _ ≤ f y := by simpa [add_comm] using hxu
    linarith
  have hyx :
      f y - f x ≤ (β : ℝ) * ‖x - y‖ := by
    have hinner_lower : -((β : ℝ) * ‖x - y‖) ≤ ⟪x - y, v⟫_ℝ := by
      have hinner_abs : |⟪x - y, v⟫_ℝ| ≤ (β : ℝ) * ‖x - y‖ := by
        calc
          |⟪x - y, v⟫_ℝ| ≤ ‖x - y‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖x - y‖ * (β : ℝ) := by
            exact mul_le_mul_of_nonneg_left hvβ (norm_nonneg _)
          _ = (β : ℝ) * ‖x - y‖ := by rw [mul_comm]
      exact le_trans (neg_le_neg hinner_abs) (neg_abs_le _)
    have hsub : f y + -((β : ℝ) * ‖x - y‖) ≤ f x := by
      calc
        f y + -((β : ℝ) * ‖x - y‖) ≤ f y + ⟪x - y, v⟫_ℝ := by
          simpa [add_comm] using add_le_add_left hinner_lower (f y)
        _ ≤ f x := by simpa [add_comm] using hyv
    linarith
  have habs : |f x - f y| ≤ (β : ℝ) * ‖x - y‖ := (abs_sub_le_iff.2 ⟨hxy, hyx⟩)
  -- The paired one-sided estimates are exactly the metric Lipschitz bound.
  simpa [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg] using habs

end SubdifferentialCalculus

end ERealFunction
