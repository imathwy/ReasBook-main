import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable
open scoped Rockafellar
open scoped Topology

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example lists six explicit extended-real-valued functions on `ℝ`, with
  `+∞` outside the natural interval where the real formula is intended.
- `core/canonical`: the owner abstractions are the chapter predicate `Function.IsConvex`, the
  codomain lift `Function.toWithBotTop`, and the canonical extension owner
  `Function.toWithBotTopOn`.
- `bridge/view`: the source extension formula `f.toWithBotTop + δ[ℝ](· | C)` remains available
  via `Function.toWithBotTopOn_eq_add_indicator`; the convexity clauses below use the canonical
  owner bridge `isConvex_toWithBotTopOn_iff`.

Domain-style sampling used here:
- the chapter owner `Function.IsConvex` from `Theorem_4_2`;
- the codomain-lift bridge `Function.toWithBotTop` from `Definition_4_4`;
- the canonical extension owner `Function.toWithBotTopOn` from `Remark_4_4_5`;
- the chapter indicator owner `indicator` from `Defintion_4_8_1`;
- mathlib's epigraph owner theorem `convexOn_iff_convex_epigraph`;
- mathlib's canonical convexity declarations `convexOn_exp` and `convexOn_rpow`;
- mathlib's canonical concavity declaration `Real.concaveOn_rpow`;
- mathlib's concavity declaration `strictConcaveOn_log_Ioi`, whose negation yields convexity of
  `x ↦ -log x` on `(0, ∞)`.

Primitive data vs derived API:
- primitive source-facing data: the six displayed formulas themselves;
- derived API: the six owner-level convexity theorems below.

Layer target: `core/canonical`; extension examples are stated with
`Function.toWithBotTopOn`, while formulas remain textbook-visible in the branch functions.
-/

section

private theorem convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x : ℝ ↦ Real.rpow x p := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact (Real.differentiableAt_rpow_const_of_ne p hx.ne').differentiableWithinAt
  · have hdiff : DifferentiableOn ℝ (fun x : ℝ ↦ x ^ (p - 1)) (Set.Ioi (0 : ℝ)) := by
        intro x hx
        exact
          (Real.differentiableAt_rpow_const_of_ne (p - 1) hx.ne').differentiableWithinAt
    simpa [Real.deriv_rpow_const'] using hdiff.const_mul p
  · intro x hx
    have hderiv2 :
        deriv^[2] (fun y : ℝ ↦ Real.rpow y p) x = p * (p - 1) * x ^ (p - 2) := by
      simpa [descPochhammer] using (Real.iter_deriv_rpow_const p x 2)
    rw [hderiv2]
    have hpp : 0 ≤ p * (p - 1) := by
      nlinarith
    exact mul_nonneg hpp (Real.rpow_nonneg hx.le _)

private theorem quadraticGap_image_Ioo (α : ℝ) (hα : 0 < α) :
    (fun x : ℝ ↦ α ^ 2 - x ^ 2) '' Set.Ioo (-α) α = Set.Ioc (0 : ℝ) (α ^ 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · nlinarith [hx.1, hx.2, hα]
    · nlinarith [sq_nonneg x]
  · intro hy
    have hnonneg : 0 ≤ α ^ 2 - y := by
      nlinarith [hy.2]
    refine ⟨Real.sqrt (α ^ 2 - y), ?_, ?_⟩
    · constructor
      · exact lt_of_lt_of_le (by linarith [hα]) (Real.sqrt_nonneg _)
      · rw [Real.sqrt_lt' hα]
        nlinarith [hy.1]
    · have hsquare : Real.sqrt (α ^ 2 - y) ^ 2 = α ^ 2 - y := Real.sq_sqrt hnonneg
      nlinarith

private theorem convexOn_inverseSqrtGap (α : ℝ) (hα : 0 < α) :
    ConvexOn ℝ (Set.Ioo (-α) α)
      (fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))) := by
  let g : ℝ → ℝ := fun y ↦ Real.rpow y (-(1 / 2 : ℝ))
  let q : ℝ → ℝ := fun x ↦ α ^ 2 - x ^ 2
  have hq_univ : ConcaveOn ℝ Set.univ q := by
    have hconst : ConcaveOn ℝ Set.univ (fun _ : ℝ ↦ α ^ 2) :=
      concaveOn_const (α ^ 2) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    have hsq : ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ (2 : ℕ)) := by
      simpa using
        (show StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ (2 : ℕ)) from
          Even.strictConvexOn_pow (by decide) (by decide)).convexOn
    simpa [q] using hconst.sub hsq
  have hq : ConcaveOn ℝ (Set.Ioo (-α) α) q :=
    hq_univ.subset (by intro x hx; simp) (convex_Ioo (-α) α)
  have hg_Ioi' : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ Real.rpow x (-(1 / 2 : ℝ))) :=
    convexOn_rpow_Ioi_of_nonpos (by norm_num)
  have hg_Ioi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) g := by
    simpa [g] using hg_Ioi'
  have hg : ConvexOn ℝ (q '' Set.Ioo (-α) α) g := by
    rw [quadraticGap_image_Ioo α hα]
    exact hg_Ioi.subset (by intro y hy; exact hy.1) (convex_Ioc 0 (α ^ 2))
  have hg_anti : AntitoneOn g (q '' Set.Ioo (-α) α) := by
    rw [quadraticGap_image_Ioo α hα]
    have hg_anti_Ioi :
        AntitoneOn (fun y : ℝ ↦ Real.rpow y (-(1 / 2 : ℝ))) (Set.Ioi (0 : ℝ)) := by
      simpa using Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
    exact
      hg_anti_Ioi.mono (by intro y hy; exact hy.1)
  simpa [g, q, Function.comp] using hg.comp_concaveOn hq hg_anti

-- Proof sketch: use mathlib's owner theorem `convexOn_exp` on `univ`, precompose with an
-- arbitrary affine map `g`, and then pass to the chapter owner `Function.IsConvex`
-- through the canonical codomain lift `.toWithTopBot`.
/-- Affine-map owner form for Example 4.4.1 (1): for any affine map `g : E →ᵃ[ℝ] ℝ`, the
function `x ↦ exp (g x)` is convex. -/
theorem expAffineMap_isConvex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E →ᵃ[ℝ] ℝ) :
    ((fun x : E ↦ Real.exp (g x)).toWithTopBot).IsConvex ℝ := by
  refine Function.isConvex_coe_of_convexOn_univ ?_
  simpa using convexOn_exp.comp_affineMap g

/-- Intrinsic owner form of Example 4.4.1 (1): for any linear functional `L : E →ₗ[ℝ] ℝ`, the
function `x ↦ exp (L x)` is convex. -/
theorem expLinear_isConvex {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L : E →ₗ[ℝ] ℝ) :
    ((fun x : E ↦ Real.exp (L x)).toWithTopBot).IsConvex ℝ := by
  refine Function.isConvex_coe_of_convexOn_univ ?_
  simpa using convexOn_exp.comp_linearMap L

-- Proof sketch: specialize `expLinear_isConvex` to `E = ℝ` and the linear map
-- `x ↦ α * x`.
/-- Example 4.4.1 (1): the function `x ↦ exp (α x)` is convex on `ℝ`. -/
theorem expAffine_isConvex (α : ℝ) :
    ((fun x : ℝ ↦ Real.exp (α * x)).toWithTopBot).IsConvex ℝ := by
  simpa [mul_comm] using expLinear_isConvex (L := LinearMap.mul ℝ ℝ α)

-- Proof sketch: reduce the extension statement to convexity of the finite branch on
-- `[0, ∞)` using `isConvex_toWithBotTopOn_iff`, then reuse mathlib's canonical
-- owner theorem `convexOn_rpow`.
/-- Example 4.4.1 (2): for `1 ≤ p`, the function `x ↦ x^p` on `[0, ∞)` extended by `+∞` to
`(-∞, 0)` is convex. -/
theorem nonnegativePowerExtension_isConvex {p : ℝ} (hp : 1 ≤ p) :
    ((fun x : ℝ ↦ Real.rpow x p).toWithBotTopOn (Set.Ici (0 : ℝ))).IsConvex ℝ := by
  exact (isConvex_toWithBotTopOn_iff).2 (by simpa using convexOn_rpow hp)

-- Proof sketch: rewrite the global extension statement through
-- `isConvex_toWithBotTopOn_iff`, then use the canonical concavity owner
-- `Real.concaveOn_rpow` on `[0, ∞)` and negate it.
/-- Example 4.4.1 (3): for `0 ≤ p ≤ 1`, the function `x ↦ -x^p` on `[0, ∞)` extended by `+∞` to
`(-∞, 0)` is convex. -/
theorem nonnegativeNegPowerExtension_isConvex {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ((fun x : ℝ ↦ -Real.rpow x p).toWithBotTopOn (Set.Ici (0 : ℝ))).IsConvex ℝ := by
  have hconv :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ -Real.rpow x p) := by
    convert (Real.concaveOn_rpow hp₀ hp₁).neg using 1
  exact (isConvex_toWithBotTopOn_iff).2 hconv

-- Proof sketch: on `(0, ∞)`, the real-valued function `x ↦ x^p` has nonnegative second
-- derivative when `p ≤ 0`. Apply the second-derivative criterion on `(0, ∞)` and then extend by
-- `+∞` to `(-∞, 0]` via `isConvex_toWithBotTopOn_iff`.
/-- Example 4.4.1 (4): for `p ≤ 0`, the function `x ↦ x^p` on `(0, ∞)` extended by `+∞` to
`(-∞, 0]` is convex. -/
theorem positivePowerExtension_isConvex {p : ℝ} (hp : p ≤ 0) :
    ((fun x : ℝ ↦ Real.rpow x p).toWithBotTopOn (Set.Ioi (0 : ℝ))).IsConvex ℝ := by
  exact (isConvex_toWithBotTopOn_iff).2 (convexOn_rpow_Ioi_of_nonpos hp)

-- Proof sketch: if `α ≤ 0`, then `Ioo (-α) α` is empty, so `Function.toWithBotTopOn` is
-- identically `⊤`, which is convex. If `α > 0`, then on `(-α, α)` the
-- real-valued function `x ↦ (α^2 - x^2)^(-1/2)` has nonnegative second derivative; apply
-- `Theorem_4_4` on that open interval and then extend with
-- `isConvex_toWithBotTopOn_iff`.
/-- Example 4.4.1 (5): for every `α`, the function `x ↦ (α^2 - x^2)^(-1/2)` on `(-α, α)`
extended by `+∞` outside is convex. -/
theorem inverseSqrtGapExtension_isConvex (α : ℝ) :
    ((fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))).toWithBotTopOn
      (Set.Ioo (-α) α)).IsConvex ℝ := by
  by_cases hα : 0 < α
  · exact (isConvex_toWithBotTopOn_iff).2 (convexOn_inverseSqrtGap α hα)
  · have hempty : Set.Ioo (-α) α = ∅ := by
      ext x
      constructor
      · intro hx
        have : 0 < α := by linarith [hx.1, hx.2]
        exact (hα this).elim
      · intro hx
        exact False.elim hx
    have hconvEmpty :
        ConvexOn ℝ (Set.Ioo (-α) α)
          (fun x : ℝ ↦ Real.rpow (α ^ 2 - x ^ 2) (-(1 / 2 : ℝ))) := by
      refine ⟨?_, ?_⟩
      · simpa [hempty] using (convex_empty : Convex ℝ (∅ : Set ℝ))
      · intro x hx
        simp [hempty] at hx
    exact (isConvex_toWithBotTopOn_iff).2 hconvEmpty

-- Proof sketch: `strictConcaveOn_log_Ioi` gives concavity of `Real.log` on `(0, ∞)`, so negating
-- it yields convexity of `x ↦ -log x` there; then use
-- `isConvex_toWithBotTopOn_iff` for the extension by `+∞`.
/-- Example 4.4.1 (6): the function `x ↦ -log x` on `(0, ∞)` extended by `+∞` to `(-∞, 0]` is
convex. -/
theorem negLogExtension_isConvex :
    ((fun x : ℝ ↦ -Real.log x).toWithBotTopOn (Set.Ioi (0 : ℝ))).IsConvex ℝ := by
  have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
    convert strictConcaveOn_log_Ioi.concaveOn.neg using 1
  exact (isConvex_toWithBotTopOn_iff).2 hconv

end
