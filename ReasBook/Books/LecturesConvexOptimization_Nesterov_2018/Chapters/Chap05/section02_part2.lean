import Mathlib
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_2_4 (from Chap05) -/
open InnerProductSpace
open scoped Gradient NewtonDecrement

noncomputable section

/- Definition 5.2.4 lies in the Chapter 5 self-concordant path-following / tilted-objective
Newton-decrement domain.

Source/core/bridge triage:
* source-facing: the shifted-objective decrement `λ_{ψ(t; ·)}(y)`
* core/canonical: `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* bridge/view: the shifted-gradient/Hessian identities and the determinant-based Hessian
  invertibility bridge

Mandatory domain-style sampling before refinement:
* `auxiliaryCentralPathObjective` in `Chap05/Definition_5_2_3`, the chapter owner for the tilted
  objective `ψ(t; ·)`
* `newtonDecrement` in `Chap05/Definition_5_0_24`, the chapter owner for Newton decrements
* `newtonDecrement_def` in `Chap05/Definition_5_0_24`, the canonical inverse-Hessian pairing
  expansion of the Newton-decrement owner
* `HessianDualLocalNorm.ofDetNeZero` / `HessianDualLocalNorm.ofDetNeZero_def` in
  `Chap05/Definition_5_0_20`, the determinant bridge for the shifted gradient covector

Best owner abstraction:
* source-facing: the Newton decrement of the tilted objective `ψ(t; ·)`
* core/canonical: `newtonDecrement` applied to `auxiliaryCentralPathObjective f y₀ t`
* bridge/view: the shifted-gradient formula and the determinant-nondegeneracy specialization

Primitive data:
* a function `f`
* a base point `y₀`
* a path parameter `t`
* an evaluation point `y`
* Hessian positivity and nondegeneracy at `y`

Derived API:
* the source-facing notation `λψ[f; y₀; t; y](hPos; hHy)`
* the bridge to `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* the shifted-gradient and Hessian identities for the tilted objective
* the inverse-Hessian pairing formula and determinant-dual-norm specialization

This refinement makes the mathematical owner explicit: Definition 5.2.4 is a specialization of
the Chapter 5 Newton-decrement owner to the tilted objective `ψ(t; ·)`. The determinant witness
survives only in the thin bridge layer that supplies the tilted objective's Hessian
invertibility from the unchanged Hessian of `f`. -/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

/- Definition 5.2.4 recalls the Chapter 5 Newton-decrement owner specialized to the tilted
objective `auxiliaryCentralPathObjective f y₀ t`. -/
recall newtonDecrement

/-- The gradient of the tilted objective `ψ(t; ·)` is the shifted gradient
`∇ f(y) - t ∇ f(y₀)`. -/
theorem auxiliaryCentralPathObjective_gradient_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    ∇ (auxiliaryCentralPathObjective f y0 t) y =
      ∇ f y - (t : ℝ) • ∇ f (y0 : E) := sorry

/-- The linear tilt in `ψ(t; ·)` does not change the Hessian. -/
theorem auxiliaryCentralPathObjective_hessian_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    hessian (auxiliaryCentralPathObjective f y0 t) y = hessian f y := sorry

/-- Hessian positivity for `f` at `y` transfers directly to the tilted objective `ψ(t; ·)` at
the same point. -/
theorem auxiliaryCentralPathObjective_hessian_isPositive
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hPos : (hessian f y).IsPositive) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsPositive := by
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hPos

/-- Hessian nondegeneracy for `f` at `y` canonically yields Hessian invertibility for the tilted
objective `ψ(t; ·)` at `y`. -/
theorem auxiliaryCentralPathObjective_hessian_isInvertible
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hHy : (hessian f y).det ≠ 0) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsInvertible := by
  simpa [auxiliaryCentralPathObjective_hessian_eq] using
    (hessian_isInvertible_of_det_ne_zero hHy : (hessian f y).IsInvertible)

namespace AuxiliaryCentralPathNewtonDecrement

/-- Source-facing notation for the Newton decrement `λ_{ψ(t; ·)}(y)` of the tilted objective,
read through the determinant-based Hessian bridge at `y`. -/
scoped notation:max "λψ[" f "; " y0 "; " t "; " y "](" hPos "; " hHy ")" =>
  newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
    (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
    (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy)

end AuxiliaryCentralPathNewtonDecrement

open scoped AuxiliaryCentralPathNewtonDecrement

/-- The notation `λψ[f; y₀; t; y](hPos; hHy)` is exactly the Chapter 5 Newton-decrement owner
applied to the tilted objective `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_newtonDecrement
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
        (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
        (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy) := by
  rfl

/-- Expanding `λψ[f; y₀; t; y](hPos; hHy)` through the tilted-objective Newton-decrement owner
gives the inverse-Hessian pairing formula for the shifted gradient of `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      Real.sqrt
        (inner ℝ (∇ f y - (t : ℝ) • ∇ f (y0 : E))
          ((hessian f y).inverse (∇ f y - (t : ℝ) • ∇ f (y0 : E)))) := by
  simpa [auxiliaryCentralPathObjective_gradient_eq, auxiliaryCentralPathObjective_hessian_eq] using
    newtonDecrement_def (auxiliaryCentralPathObjective f y0 t) y
      (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
      (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy)

/-- The source-facing tilted-objective Newton decrement also agrees with the determinant bridge
`HessianDualLocalNorm.ofDetNeZero` applied to the shifted gradient covector. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_ofDetNeZero
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      HessianDualLocalNorm.ofDetNeZero f y hPos hHy
        ((toDual ℝ E) (∇ f y - (t : ℝ) • ∇ f (y0 : E))) := sorry

end

end

/-! ### Proposition_5_2_4 (from Chap05) -/
noncomputable section

open Asymptotics Filter
open scoped StronglyConvexHalfGapIndex
open scoped StronglyConvexScaledGap

/- Proposition 5.2.4 lies in the Chapter 5 strongly-convex complexity-threshold domain.

Sampled owner declarations in this domain:
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the source-facing owner for the textbook
  threshold index `k_p`;
* `stronglyConvexHalfGapIndex_le_of_mem` in `Definition_5_2_10`, the canonical least-element
  consequence saying that any admissible positive index bounds `k_p` from above;
* `stronglyConvexScaledGap` and its scoped notation `Δ` in `Proposition_5_2_3`, the chapter owner
  for the scaled gap `M_f * √Δ₀`;
* `Asymptotics.IsBigO.of_bound` in mathlib, the canonical asymptotic bridge from a pointwise
  estimate to `=O[atTop]`.

Source/core/bridge triage:
* source-facing: Proposition 5.2.4 itself, asserting the asymptotic growth rate of `k_p`;
* core/canonical: `stronglyConvexHalfGapIndex`, `stronglyConvexScaledGap`, and `=O[atTop]`;
* bridge/view: the passage from the explicit admissibility inequality defining `k_p` to the
  asymptotic comparison with `Δ^(1 / p)`.

Primitive data:
* the strong-convexity scaling constant `Mf`;
* the exponent `p`;
* the source-facing threshold index owner `stronglyConvexHalfGapIndex`.

Derived API:
* the asymptotic estimate
  `stronglyConvexHalfGapIndex c Mf p =O[atTop] fun Δ₀ ↦ (Δ Mf Δ₀) ^ (1 / p)`.

The target asymptotic comparison is only faithful in the nondegenerate regime `0 < Mf`: when
`Mf = 0`, the defining admissibility inequality is already true at `k = 1`, so
`stronglyConvexHalfGapIndex c 0 p Δ₀ = 1` while `Δ 0 Δ₀ = 0`.

This file stays source-facing. The only local duplicate wheel was a second `Δ` notation; the
refinement deletes that copy and reuses the chapter-owned scoped notation directly. -/

-- Proof sketch: solve the defining half-gap inequality from
-- `stronglyConvexHalfGapIndex` for the threshold index `k_p`, obtain a pointwise bound by a
-- constant multiple of `(M_f * √(f(x₀) - f*))^(1 / p)`, and then pass to the canonical asymptotic
-- bridge `=O[atTop]` using the chapter owner notation `Δ`. The public statement excludes the
-- degenerate case `M_f = 0`, since then the threshold index is constantly `1` but the comparison
-- function vanishes identically.
/-- Proposition 5.2.4: the index `k_p` from Definition 5.2.10 grows at most on the order of
`Δ_f(x₀)^(1 / p)`, expressed here as `(Δ M_f (f(x₀) - f*))^(1 / p)`. The asymptotic target is
nontrivial only in the source-relevant regime `M_f > 0`, which is therefore part of the theorem
surface.
-/
theorem stronglyConvexHalfGapIndex_isBigO_scaledGap_rpow
    (c p : ℝ) (Mf : NNReal) (hMf : 0 < Mf) (hp : 0 < p) :
    (fun initialGap ↦ (k[c, Mf; p](initialGap) : ℝ)) =O[atTop]
      (fun initialGap ↦ Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)) := by
  let A : ℝ := Real.rpow (2 : ℝ) (7 / 2 : ℝ) * max c 0
  let B : ℝ := Real.rpow A (1 / p) + 1
  refine Asymptotics.IsBigO.of_bound (B + 1) ?_
  refine Filter.eventually_atTop.2 ?_
  refine ⟨max 1 ((1 / (Mf : ℝ)) ^ (2 : ℕ)), fun initialGap hGap ↦ ?_⟩
  have hMfR : 0 < (Mf : ℝ) := hMf
  have hgap_nonneg : 0 ≤ initialGap := le_trans (by positivity) hGap
  have hgap : 0 < initialGap := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hGap)
  let gapScale : ℝ := Δ (Mf : ℝ) initialGap
  let target : ℝ := Real.rpow gapScale (1 / p)
  let n : ℕ := Nat.ceil (B * target)
  have hgapScale_nonneg : 0 ≤ gapScale := by
    dsimp [gapScale]
    exact mul_nonneg hMfR.le (Real.sqrt_nonneg _)
  have hsqrt : 1 / (Mf : ℝ) ≤ Real.sqrt initialGap := by
    refine (Real.le_sqrt (by positivity) hgap_nonneg).2 ?_
    exact le_trans (le_max_right _ _) hGap
  have hgapScale_ge_one : 1 ≤ gapScale := by
    calc
      1 = (Mf : ℝ) * (1 / (Mf : ℝ)) := by field_simp [hMfR.ne']
      _ ≤ (Mf : ℝ) * Real.sqrt initialGap := by
        gcongr
      _ = gapScale := by rfl
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    exact Real.rpow_nonneg hgapScale_nonneg _
  have htarget_ge_one : 1 ≤ target := by
    dsimp [target]
    exact Real.one_le_rpow hgapScale_ge_one (by positivity)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAroot_nonneg : 0 ≤ Real.rpow A (1 / p) := by
    exact Real.rpow_nonneg hA_nonneg _
  have hAroot_pow : Real.rpow A (1 / p) ^ p = A := by
    simpa [one_div] using Real.rpow_inv_rpow hA_nonneg (show p ≠ 0 by linarith)
  have hAroot_le_B : Real.rpow A (1 / p) ≤ B := by
    dsimp [B]
    linarith
  have hA_le_Bpow : A ≤ B ^ p := by
    rw [← hAroot_pow]
    exact Real.rpow_le_rpow hAroot_nonneg hAroot_le_B hp.le
  have htarget_pow : target ^ p = gapScale := by
    dsimp [target]
    simpa [one_div] using Real.rpow_inv_rpow hgapScale_nonneg (show p ≠ 0 by linarith)
  have hBn_nonneg : 0 ≤ B * target := mul_nonneg hB_nonneg htarget_nonneg
  have hn_pos_real : (1 : ℝ) ≤ n := by
    have hB_ge_one : 1 ≤ B := by
      linarith
    have hBtarget_ge_one : 1 ≤ B * target := by
      nlinarith [hB_ge_one, htarget_ge_one, hB_nonneg, htarget_nonneg]
    exact le_trans hBtarget_ge_one (Nat.le_ceil _)
  have hn_pos : 1 ≤ n := by
    exact_mod_cast hn_pos_real
  have hBtarget_pow_le : (B * target) ^ p ≤ (n : ℝ) ^ p := by
    exact Real.rpow_le_rpow hBn_nonneg (Nat.le_ceil _) hp.le
  have hA_gapScale_le_npow : A * gapScale ≤ (n : ℝ) ^ p := by
    calc
      A * gapScale ≤ B ^ p * gapScale := by
        gcongr
      _ = (B * target) ^ p := by
        rw [Real.mul_rpow hB_nonneg htarget_nonneg, htarget_pow]
      _ ≤ (n : ℝ) ^ p := hBtarget_pow_le
  have htwo :
      Real.rpow (2 : ℝ) (7 / 2 : ℝ) = 2 * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by
    calc
      Real.rpow (2 : ℝ) (7 / 2 : ℝ) = Real.rpow (2 : ℝ) ((5 / 2 : ℝ) + 1) := by norm_num
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * Real.rpow (2 : ℝ) (1 : ℝ) := by
        simpa using
          (Real.rpow_add (show 0 < (2 : ℝ) by positivity) (5 / 2 : ℝ) (1 : ℝ))
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * 2 := by simp
      _ = 2 * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by ring
  have hgap32 : Real.rpow initialGap (3 / 2 : ℝ) = initialGap * Real.sqrt initialGap := by
    calc
      Real.rpow initialGap (3 / 2 : ℝ) = Real.rpow initialGap ((1 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow initialGap (1 : ℝ) * Real.rpow initialGap (1 / 2 : ℝ) := by
        simpa using
          (Real.rpow_add hgap (1 : ℝ) (1 / 2 : ℝ))
      _ = initialGap * Real.sqrt initialGap := by simp [Real.sqrt_eq_rpow]
  have hnum_rewrite :
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
        initialGap / 2 * (A * gapScale) := by
    change
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
        initialGap / 2 *
          (Real.rpow (2 : ℝ) (7 / 2 : ℝ) * max c 0 * ((Mf : ℝ) * Real.sqrt initialGap))
    rw [hgap32, htwo]
    ring
  have hnpow_pos : 0 < (n : ℝ) ^ p := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn_pos) _
  have hineq_max :
      (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) *
          Real.rpow initialGap (3 / 2 : ℝ)) /
        (n : ℝ) ^ p ≤
      initialGap / 2 := by
    refine (div_le_iff₀ hnpow_pos).2 ?_
    calc
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
          initialGap / 2 * (A * gapScale) := hnum_rewrite
      _ ≤ initialGap / 2 * (n : ℝ) ^ p := by
        exact mul_le_mul_of_nonneg_left hA_gapScale_le_npow (by positivity)
  have hnum_c_le :
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) ≤
        Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) := by
    have hfactor_nonneg :
        0 ≤ Real.rpow (2 : ℝ) (5 / 2 : ℝ) * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (2 : ℝ)) _) hMfR.le)
        (Real.rpow_nonneg hgap_nonneg _)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (le_max_left c 0) hfactor_nonneg
  have hnum_mono :
      (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
          (n : ℝ) ^ p ≤
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) *
            Real.rpow initialGap (3 / 2 : ℝ)) /
          (n : ℝ) ^ p := by
    exact div_le_div_of_nonneg_right hnum_c_le hnpow_pos.le
  have hn_mem : n ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap := by
    rw [mem_stronglyConvexHalfGapAdmissibleIndices_iff]
    exact ⟨hn_pos, hnum_mono.trans hineq_max⟩
  have hk_le_n : k[c, Mf; p](initialGap) ≤ n :=
    stronglyConvexHalfGapIndex_le_of_mem c Mf p initialGap hn_mem
  have hk_bound :
      (k[c, Mf; p](initialGap) : ℝ) ≤ (B + 1) * target := by
    calc
      (k[c, Mf; p](initialGap) : ℝ) ≤ n := by exact_mod_cast hk_le_n
      _ ≤ B * target + 1 := (Nat.ceil_lt_add_one hBn_nonneg).le
      _ ≤ B * target + target := by
        gcongr
      _ = (B + 1) * target := by ring
  calc
    ‖(k[c, Mf; p](initialGap) : ℝ)‖ = (k[c, Mf; p](initialGap) : ℝ) := by
      simp
    _ ≤ (B + 1) * target := hk_bound
    _ = (B + 1) * |Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)| := by
      have htarget_expr_nonneg : 0 ≤ Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p) := by
        simpa [gapScale, target] using htarget_nonneg
      have htarget_eq_abs : target = |Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)| := by
        dsimp [target]
        simpa [gapScale] using (abs_of_nonneg htarget_expr_nonneg).symm
      rw [htarget_eq_abs]

/-! ### Theorem_5_2_4 (from Chap05) -/
open scoped Gradient SelfConcordantAuxiliaryFunction IntermediateNewtonQuadraticConvergenceRegion

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scaled suboptimality `Δ_f(x) = M_f^2 (f(x) - f^*)` used in the path-following bounds. -/
def selfConcordantScaledSuboptimality
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) : ℝ :=
  (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar)

-- Proof sketch: unfold `selfConcordantScaledSuboptimality`.
/-- Expanding `selfConcordantScaledSuboptimality f M_f x f*` gives `M_f^2 (f(x) - f*)`. -/
theorem selfConcordantScaledSuboptimality_def
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) :
    selfConcordantScaledSuboptimality f Mf x fStar =
      (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) := sorry

/-- The diameter of the initial sublevel set `{x ∈ dom | f x ≤ f(y₀)}` measured in the local norm
at the base point `y₀`. -/
def pathFollowingLevelSetDiameter
    {dom : Set E} (f : E → ℝ) (y0 : dom) : ℝ :=
  sSup
    ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
      {p : E × E |
        p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)})

-- Proof sketch: unfold `pathFollowingLevelSetDiameter`.
/-- Expanding `pathFollowingLevelSetDiameter f y₀` gives the supremum of the local-norm distances
between pairs of points in the initial sublevel set. -/
theorem pathFollowingLevelSetDiameter_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) :
    pathFollowingLevelSetDiameter f y0 =
      sSup
        ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
          {p : E × E |
            p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)}) := sorry

/-- A chosen inverse value of the self-concordant auxiliary function `ω(t) = t - log(1 + t)`. -/
noncomputable def selfConcordantOmegaInverse (s : ℝ) : Set.Ioi (-1 : ℝ) :=
  Function.invFun ω s

-- Proof sketch: unfold `selfConcordantOmegaInverse`.
/-- Expanding `selfConcordantOmegaInverse s` gives the chosen inverse value of
`selfConcordantOmega` at `s`. -/
theorem selfConcordantOmegaInverse_def (s : ℝ) :
    selfConcordantOmegaInverse s = Function.invFun ω s := sorry

/-- The path-following threshold argument
`((1 - β(τ)) (1 - 2 β(τ))) / 2` always lies in `(-1, ∞)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_mem_Ioi (τ : ℝ) :
    -1 <
      ((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2 := by
  have hsquare : 0 ≤ (4 * pathFollowingCenteringBeta τ - 3) ^ (2 : ℕ) := sq_nonneg _
  nlinarith

/-- The threshold on `t_k` ensuring that the `k`-th path-following iterate has entered the
quadratic-convergence region of the intermediate Newton method. -/
def pathFollowingQuadraticRegionTimeThreshold
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  ω
      (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
        pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
    ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
      selfConcordantOmegaInverse
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar)))

-- Proof sketch: unfold `pathFollowingQuadraticRegionTimeThreshold`.
/-- Expanding `pathFollowingQuadraticRegionTimeThreshold` gives the scalar threshold on `t_k`
obtained by rearranging the entry condition from the proof of `(5.2.22)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionTimeThreshold f Mf y0 xStar τ =
      ω
          (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
            pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
        ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
          selfConcordantOmegaInverse
            (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) := sorry

/-- The explicit lower bound on the iteration index in `(5.2.22)` forcing the path-following
iterates into the quadratic-convergence region. -/
def pathFollowingQuadraticRegionEntryBound
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  Real.sqrt
    (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
        (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
      Real.log
        (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
            selfConcordantOmegaInverse
              (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
          ω
            (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
              pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ))))

-- Proof sketch: unfold `pathFollowingQuadraticRegionEntryBound`.
/-- Expanding `pathFollowingQuadraticRegionEntryBound` recovers the square-root bound from
display `(5.2.22)`, written with `pathFollowingGammaRadius τ` and `pathFollowingKappa τ`. -/
theorem pathFollowingQuadraticRegionEntryBound_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionEntryBound f Mf y0 xStar τ =
      Real.sqrt
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
            (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
          Real.log
            (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
                selfConcordantOmegaInverse
                  (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
              ω
                (⟨((1 - pathFollowingCenteringBeta τ) *
                    (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
                  pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)))) := sorry

-- Proof sketch: if no iterate up to `N` has yet entered the quadratic-convergence region, the
-- hypothesis `hdecay` gives the exponential estimate for `t_N`. The lower bound `hN` makes this
-- estimate at most `pathFollowingQuadraticRegionTimeThreshold f Mf y₀ x* τ`, so `hentry`
-- forces `y_N` into the region, a contradiction. Therefore some earlier iterate enters the
-- region, and the forward-invariance hypothesis `hstable` propagates that membership to `y_N`.
/-- Theorem 5.2.4: for a path-following process generated by `(5.2.16)`, every index above the
bound `(5.2.22)` yields an iterate in the quadratic-convergence region of the intermediate Newton
method. The textbook statement writes `𝒬_f`; here the conclusion is formalized by the region
`𝒟[f | dom, M_f]` proved in the accompanying argument. -/
theorem selfConcordantPathFollowing_mem_intermediateNewtonQuadraticConvergenceRegion_of_large_index
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (htau : τ ≤ 0.23) (y0 : dom) (xStar : E)
    (hmin : IsMinOn f dom xStar)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (hstable :
      ∀ k : ℕ,
        process.y k ∈ 𝒟[f | dom, Mf] →
          process.y (k + 1) ∈ 𝒟[f | dom, Mf])
    (hdecay :
      ∀ m : ℕ,
        (∀ k : ℕ, k ≤ m →
          process.y k ∉ 𝒟[f | dom, Mf]) →
        (process.t m : ℝ) ≤
          Real.exp
            (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (m : ℝ) ^ (2 : ℕ) /
                selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))))
    (hentry :
      ∀ m : ℕ,
        (process.t m : ℝ) ≤ pathFollowingQuadraticRegionTimeThreshold f (Mf : NNReal) y0 xStar τ →
          process.y m ∈ 𝒟[f | dom, Mf])
    {N : ℕ}
    (hN : pathFollowingQuadraticRegionEntryBound f (Mf : NNReal) y0 xStar τ ≤ (N : ℝ)) :
    process.y N ∈ 𝒟[f | dom, Mf] := sorry

end

/-! ### Definition_5_2_5 (from Chap05) -/
/- Definition 5.2.5 lies in the Chapter 5 self-concordant path-following / shifted-dual-norm
domain.

Sampled owner declarations:
* `HessianDualLocalNorm.ofDetNeZero` in `Definition_5_0_20`, the canonical Hessian-dual-local-norm
  owner used to measure shifted gradients;
* `satisfies_approximate_centering_condition` in `Lemma_5_2_2`, the chapter source-facing owner
  for the approximate centering condition;
* `satisfies_approximate_centering_condition_iff` in `Lemma_5_2_2`, the companion specification
  theorem expanding that owner back to the textbook inequality.

Best owner abstraction:
* source-facing: the approximate centering condition for the tilted objective `ψ(t; ·)`;
* core/canonical: the shifted-gradient dual-local-norm inequality built from
  `HessianDualLocalNorm.ofDetNeZero`;
* bridge/view: `satisfies_approximate_centering_condition_iff`.

Primitive data:
* the objective `f`;
* the base point `y₀`;
* the path parameter `t`;
* the evaluation point `y`;
* Hessian positivity and nondegeneracy at `y`;
* the centering parameters `M_f` and `β`.

Derived API:
* the owner predicate `satisfies_approximate_centering_condition`;
* its expansion theorem `satisfies_approximate_centering_condition_iff`.

This file is therefore a pure recall item. Keeping a second local definition here would duplicate
the Chapter 5 owner already introduced in `Lemma_5_2_2` and split downstream vocabulary for the
same source-facing notion. -/

/- Definition 5.2.5 recalls the chapter owner for the approximate centering condition. -/
recall satisfies_approximate_centering_condition

/- The textbook inequality form is the canonical companion specification theorem. -/
recall satisfies_approximate_centering_condition_iff

/-! ### Theorem_5_2_5 (from Chap05) -/
open scoped BigOperators SelfConcordantQuadraticRegion
open scoped StronglyConvexHalfGapIndex StronglyConvexMultiStageAccelerationNotation
open scoped StronglyConvexScaledGap

noncomputable section

universe u

/- Theorem 5.2.5 lies in the Chapter 5 multistage acceleration domain for strongly convex
self-concordant objectives.

Sampled declarations in this domain:
* `stronglyConvexHalfGapIndex` from `Definition_5_2_10`, the chapter owner for the source
  positive threshold index `k_p`;
* `stronglyConvexMultiStageAccelerationStageLength`,
  `stronglyConvexMultiStageAccelerationTotalLowerLevelIterations`,
  `stronglyConvexMultiStageAccelerationOrbit`, and
  `IsStronglyConvexMultiStageAccelerationStoppingStage` from `Definition_5_2_11`, the chapter
  owners for the stage schedule, cumulative lower-level work, multistage orbit `(5.2.28)`, and
  first stopping stage;
* `one_le_stronglyConvexHalfGapIndex` and
  `one_le_stronglyConvexMultiStageAccelerationStageLength`, the derived owner API ensuring that
  the source schedule uses positive stage lengths;
* `Nat.ceil` / `Nat.le_ceil`, the canonical mathlib owner for the ceiling schedule appearing in
  the source formula for `t_k`;
* `Real.logb`, the canonical base-`2` logarithm owner used in the stopping-stage estimate.

Source/core/bridge triage:
* source-facing: Theorem 5.2.5 itself, stated for the textbook multistage strategy with stopping
  region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* core/canonical: the chapter owner orbit
  `stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0` together with the canonical
  least-stage predicate `IsStronglyConvexMultiStageAccelerationStoppingStage ... T`;
* bridge/view: the arithmetic passage from the stagewise rate bound and the ceiling schedule to
  the logarithmic bound on the stopping stage and the geometric-series bound on the total work.

Primitive data:
* the canonical positive half-gap index `k_p`;
* the source stopping region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* the recursive outer orbit `y_k`;
* the source first-stopping-stage witness `T`;
* the stagewise rate estimate inherited from the lower-level method.

Derived API:
* the total number of lower-level iterations performed before the stopping stage;
* the stage bound `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`;
* the resulting total-work bound.

This refinement restores the source theorem surface. The previous version replaced the textbook
strategy by an abstract geometric-decay lemma over an auxiliary gap observable and by an extra
terminal-region bridge hypothesis. Here the main declarations speak directly about the source
ceiling schedule and the source stopping threshold. -/

section

variable {E : Type u} {f : E → ℝ}
variable {innerIterate : ℕ → E → E} {c p fStar : ℝ} {Mf : NNReal} {x0 : E}

private theorem stoppingStageSetup
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hTpos : 0 < T) (hp : 0 < p) :
    x0 ∉ 𝒬[f | fStar, Mf] ∧
      0 < Mf ∧
      0 < f x0 - fStar ∧
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty := by
  have hx0 : x0 ∉ 𝒬[f | fStar, Mf] := by
    simpa using
      stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage hT hTpos
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hgap : 0 < f x0 - fStar :=
    gap_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hkp :
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty :=
    stronglyConvexHalfGapAdmissibleIndices_nonempty hp hgap
  exact ⟨hx0, hMf, hgap, hkp⟩

-- Proof sketch: prove by induction that
-- `f (y[innerIterate | kp; p; x0] k) - f* ≤ (1 / 2)^k * (f x₀ - f*)` for all
-- `k ≤ T - 1`, using the source
-- stagewise estimate together with the ceiling lower bound
-- `((1 / 2 : ℝ) ^ (k / (2 * p))) * kp ≤ t[kp; p] k` and the defining property of `kp`. Since
-- the
-- initial point lies outside the source quadratic-convergence region, one first derives the
-- nondegenerate regime `0 < Mf` and `0 < f x₀ - f*`, hence the admissible-index set defining
-- `k_p` is automatically nonempty. Since the preterminal stage output lies outside the source
-- quadratic-convergence region, one has
-- `1 / (8 M_f^2) < f (y[innerIterate | kp; p; x0] (T - 1)) - f*`, which rearranges to
-- `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`.
/-- Theorem 5.2.5: let `k_p = k[c, M_f; p](f(x₀) - f*)`, and consider
the multistage strategy `(5.2.28)` whose `k`-th stage (`k ≥ 1`) runs the lower-level method for
`t_k = ⌈k_p / 2^((k - 1) / (2p))⌉` steps and stops once
`f(y_k) - f* ≤ 1 / (8 M_f^2)`. If each stage output satisfies the source rate estimate
`f(y_{k+1}) - f* ≤ (2^(5/2) c M_f / t_{k+1}^p) * (f(y_k) - f*)^(3/2)`, then the total
number of stages satisfies `T ≤ 4 + log₂ ((Δ M_f (f(x₀) - f*))^2)`, equivalently
`T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`, provided that `p > 0`. -/
theorem selfConcordantStronglyConvexStrategy_totalStages_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (T : ℝ) ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
  by_cases hzero : T = 0
  · sorry
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hzero
    rcases stoppingStageSetup hT hTpos hp with ⟨hx0, hMf, hgap, hkp⟩
    sorry

-- Proof sketch: write
-- `N = ∑_{k=0}^{T-1} t k`, use `Nat.ceil x ≤ x + 1` to bound each stage length by
-- `1 + kp / 2^{k / (2p)}`, sum the geometric series, and insert the stopping-stage estimate from
-- `selfConcordantStronglyConvexStrategy_totalStages_le`.
/-- Theorem 5.2.5 also bounds the total number `N` of lower-level iterations in the multistage
strategy `(5.2.28)` by
`4 + log₂ ((Δ M_f (f(x₀) - f*))^2) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, equivalently
`4 + log₂ (M_f^2 (f(x₀) - f*)) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, assuming
`p > 0`. -/
theorem selfConcordantStronglyConvexStrategy_totalLowerLevelIterations_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
        k[c, Mf; p](f x0 - fStar) p T : ℝ) ≤
      4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) +
        (Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
        (k[c, Mf; p](f x0 - fStar) : ℝ) := by
  by_cases hzero : T = 0
  · sorry
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hzero
    rcases stoppingStageSetup hT hTpos hp with ⟨hx0, hMf, hgap, hkp⟩
    sorry

end

/-! ### Definition_5_2_6 (from Chap05) -/
noncomputable section

universe u

/- Definition 5.2.6 lies in the Chapter 5 self-concordant path-following / intermediate-Newton
update domain.

Mandatory domain-style sampling before refinement:
* `pathFollowingUpdate` in `Lemma_5_2_2`, the chapter owner for the path-following map
  `(t, y) ↦ (t₊, y₊)` and its source-facing notation
  `𝒫[f; M_f; y₀ | hy; γ](t, y)`;
* `pathFollowingUpdate_fst` in `Lemma_5_2_2`, the canonical scalar-update projection theorem;
* `pathFollowingUpdate_snd` in `Lemma_5_2_2`, the canonical second-projection theorem.

Best owner abstraction:
* source-facing: Definition 5.2.6's path-following map and its two projection formulas;
* core/canonical: `pathFollowingUpdate`;
* bridge/view: `pathFollowingUpdate_fst` and `pathFollowingUpdate_snd`.

Primitive data:
* the already-defined owner `pathFollowingUpdate`.

Derived API:
* the first-coordinate formula `pathFollowingUpdate_fst`;
* the second-coordinate formula `pathFollowingUpdate_snd`.

This file is therefore a recall/bridge file. Redefining `pathFollowingUpdate` here would duplicate
the chapter owner already introduced in `Lemma_5_2_2` and would split downstream vocabulary for
the same source-facing map. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.2.6 recalls the chapter owner for the path-following update map `𝒫_γ`. -/
recall pathFollowingUpdate

/- The scalar update `t₊` is already the canonical first-projection companion theorem. -/
recall pathFollowingUpdate_fst

/- The vector update `y₊` is already the canonical second-projection companion theorem. -/
recall pathFollowingUpdate_snd

end

/-! ### Definition_5_2_7 (from Chap05) -/
noncomputable section

universe u

open Module LinearMap
open scoped LinearMap.BilinForm.BInducedNorm

/- Definition 5.2.7 lies in the dual-valued-operator / bilinear-form / induced-seminorm domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`, the chapter owner for the
  seminorm induced by positive-definite quadratic data;
- `LinearMap.BilinForm.primalSeminorm_apply` in `Chap04/Definition_4_3_4`, the canonical
  pointwise expansion of that owner;
- `LinearMap.BilinForm.IsSymm` in `Chap04/Definition_4_2_5`, the chapter owner for the symmetry
  predicate on the same dual-valued operator data;
- mathlib `Module.Dual`, the canonical codomain `E⋆ = Dual ℝ E`.

Best owner abstraction:
- source-facing: the metric attached to a dual-valued operator `B : E →ₗ[ℝ] Dual ℝ E`,
  written on the owner surface as `B : LinearMap.BilinForm ℝ E`;
- core/canonical: the Chapter 4 bilinear-form owner `LinearMap.BilinForm.primalSeminorm`;
- bridge/view: the pointwise formula `‖x‖[B | hPos] = Real.sqrt (B x x)`.

Primitive data:
- `B : LinearMap.BilinForm ℝ E` (equivalently `B : E →ₗ[ℝ] Dual ℝ E`);
- `hPos : B.toQuadraticMap.PosDef`.

Derived API:
- the recalled seminorm owner `B.primalSeminorm hPos`;
- the source-facing norm notation `‖x‖[B | hPos]`;
- the evaluation theorem `primalSeminorm_apply B hPos`.

Source/core/bridge triage:
- source-facing: Definition 5.2.7's metric attached to `B : E → E⋆`;
- core/canonical: `LinearMap.BilinForm.primalSeminorm`;
- bridge/view: `LinearMap.BilinForm.primalSeminorm_apply`.

Because `E →ₗ[ℝ] Dual ℝ E` is already the canonical bilinear-form owner layer, this item stays on
that primitive algebraic dual surface. The continuous-dual specialization belongs only to later
analytic bridge lemmas, not to the main public declaration here. -/

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 5.2.7: the metric attached to a dual-valued operator `B : E → E⋆`, written on the
owner surface as a bilinear form `B : LinearMap.BilinForm ℝ E`, is recalled through the Chapter 4
owner `LinearMap.BilinForm.primalSeminorm`.
-/
recall LinearMap.BilinForm.primalSeminorm
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    Seminorm ℝ E

/-
Evaluating the recalled metric gives the textbook formula `√(B x x)`.
-/
recall LinearMap.BilinForm.primalSeminorm_apply
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    ∀ x : E, ‖x‖[B | hPos] = Real.sqrt (B x x)

end

/-! ### Definition_5_2_8 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 5.2.8 lies in the strongly convex smooth minimization domain.

Sampled owner-style declarations:
* `StrongConvexOn` from mathlib, the canonical owner for whole-space strong convexity;
* `HasLipschitzContinuousHessian` from `Chap04/Definition_4_2_7`, written on theorem surfaces as
  `f ∈ C22[L₃]`, the project owner for global Hessian-Lipschitz regularity;
* `HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le`, the canonical second-derivative estimate
  on normed spaces;
* `HasLipschitzContinuousHessian.norm_sub_le`, the Hilbert-space Hessian estimate derived from
  that owner;
* `IsStrongConvexSmoothObjective` with source-facing notation `f ∈ 𝓢[μ, L]¹¹` from
  `Chap02/Definition_2_17`, the chapter owner pattern for bundled optimization classes.

Source/core/bridge triage:
* source-facing: the bundled strongly convex `C³` Hessian-Lipschitz regime
  `f ∈ 𝓢[σ₂, L₃]²²`;
* core/canonical: `StrongConvexOn Set.univ σ₂ f` and `f ∈ C22[L₃]`;
* bridge/view: the companion projection to `f ∈ C22[L₃]` and the textbook Hessian-difference
  inequality.

Primitive data:
* the strong-convexity parameter `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* positivity of `σ₂`;
* whole-space strong convexity of `f`;
* the canonical smoothness owner `f ∈ C22[L₃]`;
* the extra `C³` regularity needed by the source regime.

Derived API:
* the inherited `HasLipschitzContinuousHessian L₃ f` instance;
* the source-facing theorem `objective_mem : f ∈ C22[L₃]`;
* on real Hilbert spaces, the textbook estimate `‖hessian f x - hessian f y‖ ≤ L₃ ‖x - y‖`.

This file keeps the source-facing bundled regime, but now places its primitive owner data on the
same normed-space layer as `HasLipschitzContinuousHessian`. It no longer stores a duplicate raw
field `LipschitzWith L₃ (fun x ↦ fderiv ℝ (∇ f) x)`: that data is owned upstream by
`HasLipschitzContinuousHessian`. The Hilbert-specific textbook Hessian estimate remains a derived
bridge theorem. Positivity, whole-space strong convexity, and `C³` regularity stay available
through the class projections rather than a global bundled `Fact` instance. -/

/-- Definition 5.2.8: a real-valued objective on a real normed space is in the
strongly convex `C³` minimization regime with parameters `σ₂` and `L₃` when `σ₂ > 0`, the
objective is `σ₂`-strongly convex on all of `E`, it belongs to the chapter smoothness class
`C22[L₃]`, and it is three-times continuously differentiable. -/
class IsStrongConvexC22C3Objective
    (σ2 : ℝ) (L3 : NNReal) (f : E → ℝ) : Prop
    extends HasLipschitzContinuousHessian L3 f where
  /-- The strong-convexity parameter `σ₂` is positive. -/
  sigma_pos : 0 < σ2
  /-- The objective is `σ₂`-strongly convex on the whole space. -/
  strongConvex : StrongConvexOn Set.univ σ2 f
  /-- The objective is three-times continuously differentiable. -/
  contDiffThree : ContDiff ℝ 3 f

scoped[StrongConvexC22] notation "𝓢[" σ2 ", " L3 "]²²" =>
  setOf (IsStrongConvexC22C3Objective σ2 L3)

open scoped StrongConvexC22

/-- The whole-space notation `𝓢[σ₂, L₃]²²` is the source-facing set view of the owner predicate
`IsStrongConvexC22C3Objective σ₂ L₃`. -/
theorem mem_S22_iff {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ} :
    f ∈ 𝓢[σ2, L3]²² ↔ IsStrongConvexC22C3Objective σ2 L3 f :=
  Iff.rfl

/-- The canonical self-concordance constant induced by strong convexity parameter `σ₂` and
Hessian-Lipschitz constant `L₃`. This is the owner-level `M_f = L₃ / (2 σ₂^(3 / 2))` used in
Example 5.1.6 and the strongly convex Chapter 5 quadratic-region estimates. -/
def strongConvexSelfConcordanceConstant (σ2 : ℝ) (L3 : NNReal) : NNReal :=
  Real.toNNReal ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2))

/-- Under `0 < σ₂`, the owner `strongConvexSelfConcordanceConstant σ₂ L₃` has the expected real
value `L₃ / (2 σ₂^(3 / 2))`. -/
theorem coe_strongConvexSelfConcordanceConstant
    {σ2 : ℝ} {L3 : NNReal} (hσ2 : 0 < σ2) :
    (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) =
      (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2) := by
  have hnonneg : 0 ≤ (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2) := by
    positivity
  unfold strongConvexSelfConcordanceConstant Real.toNNReal
  change max ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2)) 0 =
    (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2)
  exact max_eq_left hnonneg

/-- The doubled real value of the canonical strong-convexity-induced self-concordance constant is
`L₃ / (σ₂ √σ₂)`. This is the coefficient appearing in the operator inequality of
Example 5.1.6. -/
theorem two_mul_coe_strongConvexSelfConcordanceConstant
    {σ2 : ℝ} {L3 : NNReal} (hσ2 : 0 < σ2) :
    2 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) =
      (L3 : ℝ) / (σ2 * Real.sqrt σ2) := by
  rw [coe_strongConvexSelfConcordanceConstant hσ2]
  have hsqrt : Real.sqrt σ2 ≠ 0 := Real.sqrt_ne_zero'.2 hσ2
  field_simp [hσ2.ne', hsqrt]

namespace IsStrongConvexC22C3Objective

/-- A strongly convex `C³` objective in Definition 5.2.8 belongs to the canonical owner class
`C22[L₃]`. -/
theorem objective_mem {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ}
    (hf : f ∈ 𝓢[σ2, L3]²²) :
    f ∈ C22[L3] :=
  hf.toHasLipschitzContinuousHessian

section Hilbert

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

-- Proof sketch: apply the `LipschitzWith` field of
-- `HasLipschitzContinuousHessian`, obtained from `hf.objective_mem`, to the pair `x, y`.
/-- On a real Hilbert space, the Hessian-Lipschitz field of `f ∈ 𝓢[σ₂, L₃]²²` is the textbook
estimate `‖∇² f(x) - ∇² f(y)‖ ≤ L₃ ‖x - y‖`. -/
theorem hessian_norm_sub_le
    {σ2 : ℝ} {L3 : NNReal} {f : X → ℝ}
    (hf : f ∈ 𝓢[σ2, L3]²²) (x y : X) :
    ‖hessian f x - hessian f y‖ ≤ (L3 : ℝ) * ‖x - y‖ :=
  HasLipschitzContinuousHessian.norm_sub_le
    (IsStrongConvexC22C3Objective.objective_mem hf) x y

end Hilbert

end IsStrongConvexC22C3Objective

/-! ### Definition_5_2_9 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u}

/- Definition 5.2.9 lies in the Chapter 5 strongly-convex self-concordant quadratic-regime
domain.

Sampled owner-style declarations:
* `cubicNewtonQuadraticDecreaseRegion` in `Chap04/Text_4_2_11`, the Chapter 4 core owner for the
  corresponding quadratic-decrease region written in multiplication form;
* `mem_cubicNewtonQuadraticDecreaseRegion` in `Chap04/Text_4_2_11`, the atomic expansion of that
  Chapter 4 owner;
* `intermediateNewtonQuadraticConvergenceRegion` in `Chap05/Proposition_5_2_1`, the nearby
  Chapter 5 pattern where a source-facing quadratic region remains a public owner and notation is
  used on theorem surfaces.

Source/core/bridge triage:
* source-facing: `Q_f = {x | f x - f* ≤ 1 / (8 M_f^2)}`;
* core/canonical: the Chapter 4 region `cubicNewtonQuadraticDecreaseRegion` when a separate
  identification of thresholds is available;
* bridge/view: the membership theorem below and the comparison theorem to the Chapter 4 owner.

Primitive data:
* the objective `f`;
* the optimal value `fStar`;
* the self-concordance scaling constant `M_f`.

Derived API:
* the source-facing region `Q_f` itself;
* the textbook membership formula;
* a thin bridge to the Chapter 4 multiplication-form owner when the thresholds are identified.

This refinement restores Definition 5.2.9 as a Chapter 5 source-facing owner instead of collapsing
it into the earlier Chapter 4 owner. The Chapter 4 region remains the canonical comparison target,
but it is now downstream of the Chapter 5 surface rather than replacing it. The public owner is
written in the zero-safe multiplication form `8 M_f² (f x - f*) ≤ 1`, so the quadratic case
`M_f = 0` correctly yields the whole space; the divided threshold remains available as a positive-
parameter bridge theorem. -/

/-- Definition 5.2.9: the Chapter 5 quadratic-convergence region, written in the zero-safe
multiplication form `8 M_f² (f(x) - f*) ≤ 1`. When `M_f = 0`, this is all of `E`, matching the
degenerate quadratic regime. -/
def selfConcordantQuadraticRegion
    (f : E → ℝ) (fStar : ℝ) (Mf : NNReal) : Set E :=
  {x | (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1}

/-- Source-facing notation for the Chapter 5 quadratic-convergence region `Q_f`. -/
scoped[SelfConcordantQuadraticRegion] notation:max "𝒬[" f " | " fStar ", " Mf "]" =>
  selfConcordantQuadraticRegion f fStar Mf

open scoped SelfConcordantQuadraticRegion

-- Proof sketch: unfold `selfConcordantQuadraticRegion`.
/-- Membership in `𝒬[f | f*, M_f]` is exactly the zero-safe inequality
`8 M_f² (f(x) - f*) ≤ 1`. -/
theorem mem_selfConcordantQuadraticRegion_iff
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E} :
    x ∈ 𝒬[f | fStar, Mf] ↔
      (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1 :=
  Iff.rfl

/-- In the nondegenerate regime `M_f > 0`, the zero-safe multiplication-form owner
`𝒬[f | f*, M_f]` is equivalent to the textbook divided threshold
`f(x) - f* ≤ 1 / (8 M_f^2)`. -/
theorem mem_selfConcordantQuadraticRegion_iff_div
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} (hMf : 0 < Mf) {x : E} :
    x ∈ 𝒬[f | fStar, Mf] ↔
      f x - fStar ≤ 1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) := by
  have hMf' : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf
  have hcoeff : 0 < (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  change (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1 ↔
    f x - fStar ≤ 1 / (8 * (Mf : ℝ) ^ (2 : ℕ))
  constructor
  · intro hx
    exact (le_div_iff₀ hcoeff).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hx
  · intro hx
    have hx' : (f x - fStar) * ((8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ)) ≤ 1 :=
      (le_div_iff₀ hcoeff).1 hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using hx'

/-- If `x` lies outside the Chapter 5 quadratic-convergence region `𝒬[f | f*, M_f]`, then the
scaling constant `M_f` is necessarily positive. In the degenerate quadratic case `M_f = 0`, the
zero-safe owner `𝒬[f | f*, M_f]` is all of `E`. -/
theorem Mf_pos_of_not_mem_selfConcordantQuadraticRegion
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E}
    (hx : x ∉ 𝒬[f | fStar, Mf]) :
    0 < Mf := by
  by_contra hMf
  have hMf_zero : Mf = 0 := le_antisymm (le_of_not_gt hMf) Mf.2
  have hx_mem : x ∈ 𝒬[f | fStar, Mf] := by
    rw [mem_selfConcordantQuadraticRegion_iff]
    norm_num [hMf_zero]
  exact hx hx_mem

/-- If `x` lies outside the Chapter 5 quadratic-convergence region `𝒬[f | f*, M_f]`, then its
suboptimality gap `f(x) - f*` is positive. Nonpositive gaps automatically satisfy the zero-safe
membership inequality. -/
theorem gap_pos_of_not_mem_selfConcordantQuadraticRegion
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E}
    (hx : x ∉ 𝒬[f | fStar, Mf]) :
    0 < f x - fStar := by
  by_contra hgap
  have hcoeff : 0 ≤ (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hx_mem : x ∈ 𝒬[f | fStar, Mf] := by
    rw [mem_selfConcordantQuadraticRegion_iff]
    have hmul : (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff (le_of_not_gt hgap)
    linarith
  exact hx hx_mem

-- Proof sketch: rewrite membership in `𝒬[f | fStar, M_f]` through the positive-`M_f` divided
-- threshold bridge, rewrite the Chapter 4 region by its multiplication-form owner, and convert
-- between the two divided thresholds using the positive factor `2 * L₃^2`.
/-- If `f* = f(x^*)` and the Chapter 5 threshold `1 / (8 M_f^2)` matches the divided Chapter 4
threshold `σ^3 / (2 L₃^2)` with `L₃ > 0`, then the Chapter 5 region `Q_f` agrees pointwise with
the Chapter 4 quadratic-decrease region
`cubicNewtonQuadraticDecreaseRegion f xStar σ L3`. -/
theorem mem_selfConcordantQuadraticRegion_iff_mem_cubicNewtonQuadraticDecreaseRegion
    {f : E → ℝ} {fStar σ : ℝ} {Mf L3 : NNReal} {xStar x : E}
    (hfStar : f xStar = fStar)
    (hMf : 0 < Mf)
    (hthreshold :
      1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) = σ ^ (3 : ℕ) / (2 * (L3 : ℝ) ^ (2 : ℕ)))
    (hL3 : 0 < (L3 : ℝ)) :
    x ∈ 𝒬[f | fStar, Mf] ↔
      x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 := by
  rw [mem_selfConcordantQuadraticRegion_iff_div hMf, mem_cubicNewtonQuadraticDecreaseRegion,
    ← hfStar, hthreshold]
  have hcoeff : 0 < 2 * (L3 : ℝ) ^ (2 : ℕ) := by
    positivity
  constructor
  · intro hx
    have hx' : (f x - f xStar) * (2 * (L3 : ℝ) ^ (2 : ℕ)) ≤ σ ^ (3 : ℕ) :=
      (le_div_iff₀ hcoeff).1 hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using hx'
  · intro hx
    exact (le_div_iff₀ hcoeff).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hx

/-! ### Definition_5_2_10 (from Chap05) -/
noncomputable section

/- Definition 5.2.10 lies in the Chapter 5 strongly-convex multistage-acceleration threshold
domain.

Sampled owner-style declarations before refining:
* `IsLeast` in mathlib `Order.Bounds.Defs`, the canonical least-element owner;
* `Nat.sInf_mem` and `Nat.sInf_le` in `Mathlib/Data/Nat/Lattice`, the canonical `ℕ` API for a
  least element of a nonempty set;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the chapter's
  earlier source-facing use of `IsLeast` for a first admissible natural index.

Source/core/bridge triage:
* source-facing: the admissible half-gap index set and the textbook threshold index `k_p`;
* core/canonical: `IsLeast` for the least admissible natural number;
* bridge/view: the explicit membership formula for the admissible set.

Primitive data:
* the admissible-index set cut out by the source inequality.

Derived API:
* the least admissible index `stronglyConvexHalfGapIndex`;
* its canonical least-element certificate;
* the positivity consequence `1 ≤ stronglyConvexHalfGapIndex ...` under nonemptiness.

This refinement keeps the source-facing `k_p` object while deleting the local duplicate wheel API
for least elements in favor of the canonical `IsLeast` owner theorem. -/

/-- The set of positive iteration counts `k ≥ 1` for which the strong-convexity global-rate bound
`2^(5/2) * c * M_f * (f(x₀) - f*)^(3/2) / k^p` is already at most half of the initial
suboptimality `f(x₀) - f*`. -/
def stronglyConvexHalfGapAdmissibleIndices
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) : Set ℕ :=
  {k | 1 ≤ k ∧
    (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
        Real.rpow (k : ℝ) p ≤
      initialGap / 2}

-- Proof sketch: unfold `stronglyConvexHalfGapAdmissibleIndices`; membership is exactly the
-- displayed inequality from the definition.
/-- Membership in `stronglyConvexHalfGapAdmissibleIndices c M_f p Δ₀` is equivalent to saying
that `k` is positive and satisfies the displayed half-gap inequality. -/
@[simp] theorem mem_stronglyConvexHalfGapAdmissibleIndices_iff
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) (k : ℕ) :
    k ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap ↔
      1 ≤ k ∧
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
            Real.rpow (k : ℝ) p ≤
          initialGap / 2 :=
  Iff.rfl

-- Proof sketch: if `initialGap > 0` and `p > 0`, then `k ↦ k^p` tends to `+∞`, so the displayed
-- inequality eventually holds; the positivity side condition is handled by choosing `k ≥ 1`.
/-- For a positive initial gap and exponent `p > 0`, the half-gap admissible-index set is
nonempty. This is the canonical existence API used to discharge the auxiliary witness behind the
source threshold index `k_p`. -/
theorem stronglyConvexHalfGapAdmissibleIndices_nonempty
    {c p initialGap : ℝ} {Mf : NNReal} (hp : 0 < p) (hgap : 0 < initialGap) :
    (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty := by
  sorry

/-- Definition 5.2.10: when the positive admissible-index set is nonempty,
`stronglyConvexHalfGapIndex c M_f p (f(x₀) - f*)` is the first positive integer `k_p ≥ 1` for
which the global-rate bound
`2^(5/2) * c * M_f * (f(x₀) - f*)^(3/2) / k^p ≤ (f(x₀) - f*) / 2` holds. -/
def stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) : ℕ :=
  sInf (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap)

/- Source-facing Lean notation for the textbook threshold index `k_p`. -/
scoped[StronglyConvexHalfGapIndex] notation:max
  "k[" c ", " Mf "; " p "](" initialGap ")" =>
    stronglyConvexHalfGapIndex c Mf p initialGap

open scoped StronglyConvexHalfGapIndex

-- Proof sketch: unfold `stronglyConvexHalfGapIndex` and apply `Nat.sInf_mem` to the admissible
-- index set.
/-- If the positive admissible-index set is nonempty, then the textbook threshold index
`k[c, M_f; p](Δ₀)` is its least element. -/
theorem isLeast_stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ)
    (hnonempty : (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty) :
    IsLeast
      (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap)
      (k[c, Mf; p](initialGap)) := by
  refine ⟨Nat.sInf_mem hnonempty, fun k hk ↦ Nat.sInf_le hk⟩

-- Proof sketch: extract the positivity clause from the least-element certificate
-- `isLeast_stronglyConvexHalfGapIndex`.
/-- If the positive admissible-index set is nonempty, then the textbook threshold index
`k[c, M_f; p](Δ₀)` is itself positive. -/
theorem one_le_stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ)
    (hnonempty : (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty) :
    1 ≤ k[c, Mf; p](initialGap) := by
  exact (isLeast_stronglyConvexHalfGapIndex c Mf p initialGap hnonempty).1.1

-- Proof sketch: any admissible positive index belongs to the defining set, so the least
-- admissible index `k_p` is bounded above by it.
/-- Any admissible positive index bounds the textbook threshold index
`k[c, M_f; p](Δ₀)` from above. This is the canonical source-facing consequence of the least-index
owner API. -/
theorem stronglyConvexHalfGapIndex_le_of_mem
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) {k : ℕ}
    (hk : k ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap) :
    k[c, Mf; p](initialGap) ≤ k := by
  exact (isLeast_stronglyConvexHalfGapIndex c Mf p initialGap ⟨k, hk⟩).2 hk

/-! ### Definition_5_2_11 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u}

/- Definition 5.2.11 lies in the Chapter 5 strongly-convex multistage-acceleration domain.

Sampled owner declarations:
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the chapter owner for the source
  threshold index `k_p`;
* `conjugateGradientTrajectory` in `Chap01/Definition_1_9_3`, the chapter pattern where a
  recursive orbit is the owner and pointwise formulas are derived API;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern for first natural-number stopping stages expressed through `IsLeast`;
* `IsFirstStrongConvexAcceleratedCubicNewtonQuadraticRegionIndex` in `Chap04/Text_4_2_13`, the
  nearby Chapter 4 first-entry predicate for a multistage orbit.

Best owner abstraction:
* source-facing: the recursive outer-stage orbit `(y_k)` together with the source predicate that
  `T` is the first stage whose output lies in `Q_f`;
* core/canonical: the recursive orbit and `IsLeast` on the hit set `{n | y_n ∈ Q_f}`;
* bridge/view: the pointwise recursion formulas and the unpacking of the first-entry predicate as
  membership at `T` plus failure at all earlier stages.

Primitive data:
* the stage-length schedule `t_{k+1}`;
* the recursive outer orbit generated from `x₀` by the prescribed stage lengths.

Derived API:
* the total number of lower-level iterations performed through a given number of stages;
* the source first-stopping-stage predicate;
* entry at the stopping stage and non-entry at all earlier stages;
* positivity of the stopping stage when `x₀ ∉ Q_f`.

The previous bundled `StronglyConvexMultiStageAccelerationScheme` stored both the orbit and the
least stopping index as primitive public data. Those are canonical from the schedule and `IsLeast`
view, so this refinement keeps the recursive orbit as the owner and moves the first-entry notion
to the canonical least-stage predicate. -/

/-- The stage length `t_{k+1}` used at zero-based outer stage `k` in the multistage acceleration
schedule, namely `⌈k_p / 2^{k / (2p)}⌉`. -/
def stronglyConvexMultiStageAccelerationStageLength
    (kp : ℕ) (p : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))

namespace StronglyConvexMultiStageAccelerationNotation

/- Source-facing notation for the textbook stage length `t_k`, with the ambient threshold index
`k_p` and exponent `p` explicit because they are not inferable from `k` alone. -/
scoped notation:max "t[" kp:arg "; " p:arg "]" =>
  stronglyConvexMultiStageAccelerationStageLength kp p

end StronglyConvexMultiStageAccelerationNotation

open scoped StronglyConvexMultiStageAccelerationNotation

-- Proof sketch: if `kp ≥ 1`, then the real-valued stage-length expression is strictly positive,
-- so its ceiling is at least `1`.
/-- Positive threshold indices produce positive stage lengths throughout the multistage schedule. -/
theorem one_le_stronglyConvexMultiStageAccelerationStageLength
    {kp : ℕ} (hkp : 1 ≤ kp) (p : ℝ) (k : ℕ) :
    1 ≤ t[kp; p] k := by
  change 1 ≤ Nat.ceil ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))
  rw [Nat.one_le_ceil_iff]
  have hkp' : (0 : ℝ) < kp := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hkp
  have hrpow : 0 < Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)) :=
    Real.rpow_pos_of_pos zero_lt_two _
  exact div_pos hkp' hrpow

/-- The total number of lower-level iterations performed during the first `T` stages of the
multistage strategy. -/
def stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
    (kp : ℕ) (p : ℝ) (T : ℕ) : ℕ :=
  Finset.sum (Finset.range T) fun k ↦ t[kp; p] k

/-- The outer-stage orbit `(y_k)` of the multistage strategy `(5.2.28)`, started at `x₀` and
updated by running the inner method for the scheduled stage length
`⌈k_p / 2^{k / (2p)}⌉` at each stage. -/
def stronglyConvexMultiStageAccelerationOrbit
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      innerIterate (t[kp; p] k)
        (stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0 k)

namespace StronglyConvexMultiStageAccelerationNotation

/-- Source-facing notation for the textbook outer-stage iterate `y_k` of the multistage strategy
`(5.2.28)`, with the ambient update map and schedule parameters explicit because they are not
inferable from `k` alone. -/
scoped notation:max "y[" innerIterate:arg " | " kp:arg "; " p:arg "; " x0:arg "]" =>
  stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0

end StronglyConvexMultiStageAccelerationNotation

/-- The multistage outer orbit starts at the prescribed point `x₀`. -/
@[simp] theorem stronglyConvexMultiStageAccelerationOrbit_zero
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) :
    y[innerIterate | kp; p; x0] 0 = x0 :=
  rfl

/-- The successor stage output is obtained by applying the prescribed
`⌈k_p / 2^{k / (2p)}⌉`-step inner run to the previous stage output. -/
@[simp] theorem stronglyConvexMultiStageAccelerationOrbit_succ
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) (k : ℕ) :
    y[innerIterate | kp; p; x0] (k + 1) =
      innerIterate (t[kp; p] k) (y[innerIterate | kp; p; x0] k) :=
  rfl

/-- Definition 5.2.11: `T` is the stopping stage of the multistage acceleration strategy
`(5.2.28)` when `T` is the first outer-stage index whose output lies in the terminal region
`Q_f`. -/
def IsStronglyConvexMultiStageAccelerationStoppingStage
    (innerIterate : ℕ → E → E) (Qf : Set E) (kp : ℕ) (p : ℝ) (x0 : E) (T : ℕ) : Prop :=
  IsLeast {n : ℕ | y[innerIterate | kp; p; x0] n ∈ Qf} T

/-- Expanding `IsStronglyConvexMultiStageAccelerationStoppingStage ... T` says exactly that the
outer orbit enters `Q_f` at stage `T` and not at any earlier stage. -/
@[simp] theorem isStronglyConvexMultiStageAccelerationStoppingStage_iff
    (innerIterate : ℕ → E → E) (Qf : Set E) (kp : ℕ) (p : ℝ) (x0 : E) (T : ℕ) :
    IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T ↔
      y[innerIterate | kp; p; x0] T ∈ Qf ∧
        ∀ m : ℕ, m < T → y[innerIterate | kp; p; x0] m ∉ Qf := by
  change
    IsLeast
      {n : ℕ | y[innerIterate | kp; p; x0] n ∈ Qf}
      T ↔
        y[innerIterate | kp; p; x0] T ∈ Qf ∧
          ∀ m : ℕ, m < T → y[innerIterate | kp; p; x0] m ∉ Qf
  constructor
  · rintro ⟨hT, hleast⟩
    refine ⟨hT, fun m hm hmQf ↦ ?_⟩
    exact (not_le_of_gt hm) (hleast hmQf)
  · rintro ⟨hT, hlt⟩
    refine ⟨hT, fun m hm ↦ le_of_not_gt fun hmT ↦ ?_⟩
    exact hlt m hmT hm

/-- The stopping-stage output lies in the terminal region `Q_f`. -/
theorem stronglyConvexMultiStageAccelerationStoppingStage_mem
    {innerIterate : ℕ → E → E} {Qf : Set E} {kp : ℕ} {p : ℝ} {x0 : E} {T : ℕ}
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T) :
    y[innerIterate | kp; p; x0] T ∈ Qf :=
  hT.1

section

variable {innerIterate : ℕ → E → E} {Qf : Set E} {kp T k : ℕ} {p : ℝ} {x0 : E}

/-- Every stage strictly before a stopping stage lies outside the terminal region `Q_f`. -/
theorem stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T)
    (hk : k < T) :
    y[innerIterate | kp; p; x0] k ∉ Qf := by
  intro hkQf
  exact Nat.not_le_of_lt hk <| hT.2 hkQf

/-- If the initial point lies outside `Q_f`, then every stopping stage is positive. -/
theorem one_le_of_isStronglyConvexMultiStageAccelerationStoppingStage_of_initial_not_mem
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T)
    (hx0 : x0 ∉ Qf) :
    1 ≤ T := by
  refine Nat.succ_le_of_lt <| Nat.pos_of_ne_zero fun hzero ↦ ?_
  have hmem : y[innerIterate | kp; p; x0] 0 ∈ Qf := by
    simpa [hzero] using stronglyConvexMultiStageAccelerationStoppingStage_mem hT
  exact hx0 <| by simpa using hmem

end
