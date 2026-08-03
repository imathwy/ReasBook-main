import BauschkeLean.Chap23.Corollary_23_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.31 compares the single-valued resolvent points `J_{γ A} x` and
  `J_{(λγ) A} x` for a maximally monotone operator.
- `core/canonical`: the owner abstractions already live upstream as the set-valued resolvent
  `J[((γ : ℝ) • A)]`, its graph criterion `mem_resolvent_smul_iff_mem_graph`, and the canonical
  single-valued realizer `resolventMap`, together with the firm/nonexpansive consequences of
  Corollary 23.11.
- `bridge/view`: this file keeps the textbook pointwise `resolventMap` surface and derives the
  comparison estimates from the canonical graph criterion together with firm/nonexpansive
  consequences of Corollary 23.11. -/

/-- Helper for Proposition 23.31: resolvent maps of maximally monotone operators are
nonexpansive on the Chapter 23 `resolventMap` surface. -/
private theorem norm_resolventMap_sub_le_norm_sub
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) (x y : H) :
    ‖resolventMap A hA γ x - resolventMap A hA γ y‖ ≤ ‖x - y‖ := by
  let T : H → H := resolventMap A hA γ
  -- Apply Corollary 23.11 directly to the resolvent realizer `T`.
  have hsq : ‖T x - T y‖ ^ (2 : ℕ) ≤ ‖T x - T y‖ * ‖x - y‖ := by
    have hfirmxy : ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
      simpa [T] using
        (resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
          A hA γ T (resolventMap_toSetValuedOperator_eq A hA γ)) x y
    exact hfirmxy.trans (real_inner_le_norm _ _)
  -- Cancel the common nonnegative norm factor to reach the `1`-Lipschitz estimate.
  have hle : ‖T x - T y‖ ≤ ‖x - y‖ := by
    nlinarith [hsq, norm_nonneg (T x - T y), norm_nonneg (x - y)]
  change ‖T x - T y‖ ≤ ‖x - y‖
  exact hle

/-- Proposition 23.31 (1): if `A : H → 2^H` is maximally monotone, `γ, λ ∈ ℝ_{++}`, and
`x : H`, then `J_{γ A} x` is also the value of `J_{(λγ) A}` at the affine combination
`λ x + (1 - λ) J_{γ A} x`, realized on the Chapter 23 single-valued resolvent surface. -/
theorem resolventMap_eq_resolventMap_mul_affine_combo
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ lam : PosReal) (x : H) :
    resolventMap A hA γ x =
      resolventMap A hA (lam * γ)
        ((lam : ℝ) • x + (1 - (lam : ℝ)) • resolventMap A hA γ x) := by
  let y := resolventMap A hA γ x
  have hy_mem :
      y ∈ J[(((lam * γ : PosReal) : ℝ) • A)] ((lam : ℝ) • x + (1 - (lam : ℝ)) • y) := by
    refine (mem_resolvent_smul_iff_mem_graph A (lam * γ) _ y).2 ?_
    have hresidual :
        (((lam * γ : PosReal) : ℝ)⁻¹) • (((lam : ℝ) • x + (1 - (lam : ℝ)) • y) - y) =
          (γ : ℝ)⁻¹ • (x - y) := by
      have hdiff : ((lam : ℝ) • x + (1 - (lam : ℝ)) • y) - y = (lam : ℝ) • (x - y) := by
        rw [smul_sub]
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_smul]
      calc
        (((lam * γ : PosReal) : ℝ)⁻¹) • (((lam : ℝ) • x + (1 - (lam : ℝ)) • y) - y)
            = (((lam * γ : PosReal) : ℝ)⁻¹) • ((lam : ℝ) • (x - y)) := by
                rw [hdiff]
        _ = ((((lam * γ : PosReal) : ℝ)⁻¹ : ℝ) * (lam : ℝ)) • (x - y) := by
              rw [smul_smul]
        _ = ((γ : ℝ)⁻¹ : ℝ) • (x - y) := by
              congr 1
              change (((lam : ℝ) * (γ : ℝ))⁻¹ * (lam : ℝ)) = (γ : ℝ)⁻¹
              field_simp [lam.2.ne', γ.2.ne']
    rw [hresidual]
    have hy :
        y ∈ J[((γ : ℝ) • A)] x := by
      rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]
      simp [y]
    exact (mem_resolvent_smul_iff_mem_graph A γ x y).1 hy
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA (lam * γ)
    ((lam : ℝ) • x + (1 - (lam : ℝ)) • y)] at hy_mem
  simpa [y] using hy_mem

/-- Proposition 23.31 (2): if `A : H → 2^H` is maximally monotone, `γ, λ ∈ ℝ_{++}`, `x : H`,
and `(λ : ℝ) ≤ 1`, then the displacement of `x` under `J_{(λγ) A}` is bounded by
`(2 - λ) ‖J_{γ A} x - x‖`. -/
theorem norm_resolventMap_mul_sub_le_two_sub_mul_norm_resolventMap_sub
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ lam : PosReal) (x : H)
    (hlam : (lam : ℝ) ≤ 1) :
    ‖resolventMap A hA (lam * γ) x - x‖ ≤
      (2 - (lam : ℝ)) * ‖resolventMap A hA γ x - x‖ := by
  let y := resolventMap A hA γ x
  let z := (lam : ℝ) • x + (1 - (lam : ℝ)) • y
  have hy : y = resolventMap A hA (lam * γ) z :=
    resolventMap_eq_resolventMap_mul_affine_combo hA γ lam x
  have hz_sub : z - x = (1 - (lam : ℝ)) • (y - x) := by
    rw [← one_smul ℝ x, smul_sub]
    simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul]
  calc
    ‖resolventMap A hA (lam * γ) x - x‖
        ≤ ‖resolventMap A hA (lam * γ) x - y‖ + ‖y - x‖ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            norm_add_le (resolventMap A hA (lam * γ) x - y) (y - x)
    _ = ‖resolventMap A hA (lam * γ) x - resolventMap A hA (lam * γ) z‖ + ‖y - x‖ := by
          rw [hy]
    _ ≤ ‖x - z‖ + ‖y - x‖ := by
          exact add_le_add (norm_resolventMap_sub_le_norm_sub hA (lam * γ) x z) le_rfl
    _ = |1 - (lam : ℝ)| * ‖y - x‖ + ‖y - x‖ := by
          rw [norm_sub_rev, hz_sub, norm_smul, Real.norm_eq_abs]
    _ = (2 - (lam : ℝ)) * ‖y - x‖ := by
          rw [abs_of_nonneg (sub_nonneg.mpr hlam)]
          ring
    _ = (2 - (lam : ℝ)) * ‖resolventMap A hA γ x - x‖ := by
          simp [y]

/-- Proposition 23.31 (3): if `A : H → 2^H` is maximally monotone, `γ, λ ∈ ℝ_{++}`, and
`x : H`, then the resolvent values at `γ` and `λγ` differ by at most
`|1 - λ| ‖J_{γ A} x - x‖`. -/
theorem norm_resolventMap_sub_resolventMap_mul_le_abs_one_sub_mul_norm_resolventMap_sub
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ lam : PosReal) (x : H) :
    ‖resolventMap A hA γ x - resolventMap A hA (lam * γ) x‖ ≤
      |1 - (lam : ℝ)| * ‖resolventMap A hA γ x - x‖ := by
  let y := resolventMap A hA γ x
  let z := (lam : ℝ) • x + (1 - (lam : ℝ)) • y
  have hy : y = resolventMap A hA (lam * γ) z :=
    resolventMap_eq_resolventMap_mul_affine_combo hA γ lam x
  have hz_sub : z - x = (1 - (lam : ℝ)) • (y - x) := by
    rw [← one_smul ℝ x, smul_sub]
    simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul]
  calc
    ‖resolventMap A hA γ x - resolventMap A hA (lam * γ) x‖
        = ‖resolventMap A hA (lam * γ) z - resolventMap A hA (lam * γ) x‖ := by
          rw [← hy]
    _ ≤ ‖z - x‖ := norm_resolventMap_sub_le_norm_sub hA (lam * γ) z x
    _ = |1 - (lam : ℝ)| * ‖y - x‖ := by
          rw [hz_sub, norm_smul, Real.norm_eq_abs]
    _ = |1 - (lam : ℝ)| * ‖resolventMap A hA γ x - x‖ := by
          simp [y]

end SetValuedOperator
