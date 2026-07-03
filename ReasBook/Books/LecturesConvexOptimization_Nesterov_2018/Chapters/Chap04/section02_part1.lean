import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2_1 (from Chap04) -/
open Module

universe u v

/- This item is recall-only in the algebraic-duality / reflexive-module domain.

Sampled canonical owners:
- `Module.Dual`
- `Module.dualPairing`
- `Module.IsReflexive`
- `Module.evalEquiv`

Best owner abstraction:
- core/canonical: the ambient `R`-module owner `Dual R E` and its evaluation pairing
  `Module.dualPairing R E`
- for the bidual identification, the reflexive-module owner `[Module.IsReflexive R E]` with
  `Module.evalEquiv R E`

Primitive data:
- a scalar semiring `R`
- an additive commutative monoid `E` with an `R`-module structure
- for the bidual identification, the reflexivity witness on `E`

Derived API:
- the dual module `Dual R E`
- the evaluation pairing `Module.dualPairing R E`
- the canonical bidual equivalence `Module.evalEquiv R E`

Source/core/bridge triage:
- source-facing: the dual space, the evaluation pairing, and the finite-dimensional vector-space
  identification with the bidual
- core/canonical: `Module.Dual`, `Module.dualPairing`, `Module.evalEquiv`
- bridge/view: finite-dimensional vector spaces furnish `Module.IsReflexive`, so the textbook
  finite-dimensional case is a specialization of the reflexive owner `Module.evalEquiv`

The source-facing real-vector-space statements are therefore refined to the weakest owner level
already present in mathlib, with the finite-dimensional textbook case kept only as a bridge to the
canonical reflexive-module equivalence. -/

section DualSpace

variable {R : Type u} {E : Type v} [Semiring R] [AddCommMonoid E] [Module R E]

/- Definition 4.2.1: for an `R`-module `E`, the dual space `E*` is the canonical owner
`Dual R E`, i.e. the space `(E →ₗ[R] R)` of linear functionals on `E`. The textbook real-vector-
space case is the specialization `R = ℝ`. -/
recall Module.Dual

end DualSpace

section DualPairing

variable {R : Type u} {E : Type v} [CommSemiring R] [AddCommMonoid E] [Module R E]

/- The duality pairing is the canonical evaluation pairing on the module dual. -/
recall Module.dualPairing

/- Evaluating the canonical duality pairing agrees with applying the functional. -/
recall Module.dualPairing_apply

end DualPairing

section ReflexiveBidual

variable {R : Type u} {E : Type v} [CommSemiring R] [AddCommMonoid E] [Module R E]
variable [Module.IsReflexive R E]

/- The bidual identification belongs to the canonical reflexive-module owner
`Module.evalEquiv R E : E ≃ₗ[R] Dual R (Dual R E)`. -/
recall Module.evalEquiv

end ReflexiveBidual

section FiniteDimensionalBidualBridge

variable {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]

/- Finite-dimensional vector spaces supply the reflexivity hypothesis needed by
`Module.evalEquiv`, so the textbook finite-dimensional bidual identification is the direct
finite-dimensional specialization of that canonical equivalence. -/
#check (Module.evalEquiv K E : E ≃ₗ[K] Dual K (Dual K E))

end FiniteDimensionalBidualBridge

/-! ### Lemma_4_2_1 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.1 lies in the uniformly convex differentiable-analysis domain on real Hilbert
spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* `uniformConvexPowerModulus` in `Definition_4_2_8`
* `uniformConvexOn_iff_lower_tangent_power` in `Definition_4_2_8`
* `ConvexOn.of_gradient_monotone` in `Chap02/Theorem_2_3`

Best owner abstraction:
* source-facing: the power-type lower bound on the gradient monotonicity pairing
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: this theorem, which upgrades the source monotonicity inequality to the canonical
  owner predicate

Primitive data:
* the feasible set `Q`
* the objective `d`
* the power parameter `p` in the chapter regime `p ≥ 2`, and the modulus parameter `σp`
* the within-set gradient map `gradientWithin d Q`

Derived API:
* ordinary convexity of `d` on `Q`, obtainable from `ConvexOn.of_gradient_monotone`
* the power lower-tangent inequality from `uniformConvexOn_iff_lower_tangent_power`
* the uniform-convexity owner conclusion

This file therefore keeps only the source-facing monotonicity-to-owner bridge, instead of
introducing any parallel local uniform-convexity wrapper around `UniformConvexOn`. -/

section

variable {Q : Set E} {d : E → ℝ} {σp p : ℝ}

local notation "gradQ" => gradientWithin d Q

/-- Lemma 4.2.1: in the chapter regime `p ≥ 2`, if `d` is differentiable on a convex set `Q`
and its gradient satisfies the monotonicity bound
`⟪∇ d(x) - ∇ d(y), x - y⟫ ≥ σp ‖x - y‖^p`, then `d` is uniformly convex on `Q` with modulus
`r ↦ (1 / p) * σp * r^p`. -/
-- Proof sketch: integrate the monotonicity inequality along the segment from `x` to `y` to
-- recover the degree-`p` support remainder term, then use
-- `uniformConvexOn_iff_lower_tangent_power` to package the result as the canonical owner
-- predicate `UniformConvexOn`.
theorem uniformConvexOn_of_gradient_monotone
    (hp : 2 ≤ p)
    (hQ : Convex ℝ Q)
    (hd : DifferentiableOn ℝ d Q)
    (hmono :
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        σp * Real.rpow ‖x - y‖ p ≤ inner ℝ (gradQ x - gradQ y) (x - y)) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d := sorry

end

/-! ### Text_4_2_1 (from Chap04) -/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.1 lies in the real inner-product-space gradient/Fréchet-derivative domain.

Relevant owner-style declarations sampled before refinement:
- `DifferentiableAt.hasGradientAt`
- `HasGradientAt.fderiv_apply`
- `inner_gradient_left`
- `HasGradientAt.hasFDerivAt`

Best owner abstraction:
- `DifferentiableAt.hasGradientAt`

Primitive data:
- a function `f : E → ℝ`
- a base point `x : E`

Derived API:
- the canonical gradient witness `DifferentiableAt.hasGradientAt`
- the owner-side derivative evaluation formula `HasGradientAt.fderiv_apply`
- its differentiability-point specialization `inner_gradient_left`

Source/core/bridge triage:
- source-facing: the textbook statement that, at differentiability points, the gradient
  represents the derivative
- core/canonical: `DifferentiableAt.hasGradientAt`
- bridge/view: `HasGradientAt.fderiv_apply` and `inner_gradient_left`

The first sentence of Text 4.2.1 is already exactly the mathlib owner theorem, so this file
recalls the canonical owner surface directly instead of keeping parallel wrapper lemmas. The
ambient model is generalized from `EuclideanSpace ℝ (Fin n)` to an arbitrary complete real inner
product space, since the canonical owner API and the source mathematics use only that structure.
-/

recall DifferentiableAt.hasGradientAt

recall HasGradientAt.fderiv_apply

recall inner_gradient_left

/-! ### Theorem_4_2_1 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 4.2.1 lies in the chapter's constrained uniform-convexity domain on real normed spaces.

Sampled owner-style declarations:
* project `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`
* project `uniformConvexPowerModulus` in `Chap04/Definition_4_2_8`
* mathlib `UniformConvexOn`
* mathlib `exists_nat_one_div_lt`

Best owner abstraction:
* source-facing: the lower bound produced by uniform convexity at a constrained minimizer
* core/canonical: `xStar ∈ argmin[Q] d` together with
  `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the segmentwise comparison inequalities obtained by applying the owner predicate to
  convex combinations of `xStar` and `x`

Primitive data:
* the feasible set `Q`, objective `d`, and modulus parameters `σp`, `p`
* the canonical owner predicate `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* the canonical constrained minimizer witness `xStar ∈ argmin[Q] d`

Derived API:
* feasibility and minimality of `xStar` from `mem_constrainedArgmin_iff`
* convexity of `Q` from `UniformConvexOn`
* lower bounds obtained by evaluating uniform convexity along the segment from `xStar` to `x`
  and letting the segment parameter tend to `0`

Using `argmin[Q] d` is essential here: `IsMinOn d Q xStar` alone does not encode the feasibility
fact `xStar ∈ Q`, but both the textbook meaning of “minimizer on `Q`” and the owner-side proof do.
-/

/-- Theorem 4.2.1: if `xStar ∈ argmin[Q] d` and `d` is uniformly convex on `Q` with modulus
`r ↦ (1 / p) * σp * r^p`, then `d x ≥ d xStar + (σp / p) * ‖x - xStar‖^p`
for all `x ∈ Q`. -/
theorem lower_bound_at_minimizer_of_uniformConvexOn
    {σp p : ℝ} {Q : Set E} {d : E → ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    {xStar : E} (hxStar : xStar ∈ argmin[Q] d)
    (x : E) (hx : x ∈ Q) :
    d x ≥ d xStar + uniformConvexPowerModulus σp p ‖x - xStar‖ := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, hxStar_min⟩
  have hxStar_min' := isMinOn_iff.mp hxStar_min
  set c : ℝ := uniformConvexPowerModulus σp p ‖x - xStar‖
  by_cases hc : c ≤ 0
  · have hmin : d xStar ≤ d x := hxStar_min' x hx
    linarith
  · have hc0 : 0 < c := lt_of_not_ge hc
    by_contra hbound
    have hlt : d x - d xStar < c := by
      simp only [not_le] at hbound
      linarith
    have hmin : d xStar ≤ d x := hxStar_min' x hx
    have hgap_nonneg : 0 ≤ d x - d xStar := by
      linarith
    have hratio_pos : 0 < (c - (d x - d xStar)) / c := by
      exact div_pos (sub_pos.mpr hlt) hc0
    obtain ⟨n, hn⟩ :=
      exists_nat_one_div_lt hratio_pos
    let b : ℝ := 1 / (n + 1 : ℝ)
    let a : ℝ := 1 - b
    have hb0 : 0 < b := by
      dsimp [b]
      positivity
    have hb_nonneg : 0 ≤ b := hb0.le
    have hratio_le_one : (c - (d x - d xStar)) / c ≤ 1 := by
      have hnum_le : c - (d x - d xStar) ≤ c := by
        linarith
      have hnum_le' : c - (d x - d xStar) ≤ 1 * c := by
        simpa [one_mul] using hnum_le
      exact (div_le_iff₀ hc0).2 hnum_le'
    have hb_lt_one : b < 1 := by
      exact lt_of_lt_of_le (by simpa [b] using hn) hratio_le_one
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      linarith
    have hab : a + b = 1 := by
      dsimp [a]
      ring
    have hcombo_mem : a • xStar + b • x ∈ Q :=
      huniform.1 hxStar_mem hx ha_nonneg hb_nonneg hab
    have hcombo_min : d xStar ≤ d (a • xStar + b • x) :=
      hxStar_min' _ hcombo_mem
    have huniform_combo :
        d (a • xStar + b • x) ≤
          a * d xStar + b * d x - a * b * c := by
      simpa [a, b, c, norm_sub_rev, smul_eq_mul] using
        huniform.2 hxStar_mem hx ha_nonneg hb_nonneg hab
    have hsegment_bound : d x - d xStar ≥ a * c := by
      nlinarith [hcombo_min, huniform_combo, hab, hb0]
    have hb_lt : b * c < c - (d x - d xStar) := by
      exact (lt_div_iff₀ hc0).mp (by simpa [b] using hn)
    have hstrict : d x - d xStar < a * c := by
      dsimp [a] at *
      linarith
    linarith

/-! ### Definition_4_2_2 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.2 lies in the first-order differential-calculus / gradient domain on real
Hilbert spaces.

Sampled owner-style declarations:
* `gradient`, recalled in `Chap01/Definition_1_4_7`, the canonical gradient vector;
* `DifferentiableAt.hasGradientAt`, which supplies the gradient witness at differentiability
  points;
* `hasGradientAt_iff_sub_affineApproximation_isLittleO`, the Chapter 1 affine-approximation
  bridge for first-order Taylor expansion.

Best owner abstraction:
* source-facing/core: the canonical pointwise gradient `∇ f xBar`.

Primitive data:
* a function `f : E → ℝ`;
* a base point `xBar : E`.

Derived API:
* the first-order Taylor remainder estimate for `∇ f xBar` under differentiability at `xBar`;
* uniqueness of any vector satisfying that remainder estimate.

Source/core/bridge triage:
* source-facing: the vector appearing in the first-order Taylor expansion at `xBar`;
* core/canonical: `∇ f xBar`;
* bridge/view: `HasGradientAt` and the Chapter 1 little-o characterization.

This item therefore reuses the existing gradient owner directly rather than introducing a parallel
Chapter 4 definition. -/

section

variable (f : E → ℝ) (xBar : E)

set_option linter.hashCommand false in
/- Definition 4.2.2: for a differentiable real-valued function on a complete real inner-product
space, the gradient at `xBar`, denoted `∇ f xBar`, is the canonical gradient vector. -/
#check (∇ f xBar : E)

end

/-- The gradient at a differentiability point gives the first-order Taylor expansion remainder of
`f` at `xBar`. -/
-- Proof sketch: obtain `HasGradientAt f (∇ f xBar) xBar` from `hf.hasGradientAt`, then rewrite it
-- with mathlib's zero-centered little-o gradient characterization.
theorem gradient_taylorExpansion_isLittleO
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    (fun h ↦ f (xBar + h) - (f xBar + inner ℝ (∇ f xBar) h)) =o[nhds (0 : E)] fun h ↦ ‖h‖ := by
  rw [Asymptotics.isLittleO_norm_right]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hasGradientAt_iff_isLittleO_nhds_zero.mp hf.hasGradientAt)

/-- Any vector satisfying the first-order Taylor expansion remainder at `xBar` is the gradient at
that point. -/
-- Proof sketch: translate the displayed little-o assumption into `HasGradientAt f g xBar` by the
-- zero-centered little-o characterization, then use `HasGradientAt.gradient`.
theorem eq_gradient_of_taylorExpansion_isLittleO
    (f : E → ℝ) (xBar : E) (g : E)
    (hg :
      (fun h ↦ f (xBar + h) - (f xBar + inner ℝ g h)) =o[nhds (0 : E)] fun h ↦ ‖h‖) :
    g = ∇ f xBar := by
  rw [Asymptotics.isLittleO_norm_right] at hg
  have hg' :
      (fun h ↦ f (xBar + h) - f xBar - inner ℝ g h) =o[nhds (0 : E)] fun h ↦ h := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg
  have hgrad : HasGradientAt f g xBar := by
    exact hasGradientAt_iff_isLittleO_nhds_zero.mpr hg'
  simpa using hgrad.gradient.symm

end

/-! ### Lemma_4_2_2 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {Q : Set E} {d : E → ℝ} {p σp : ℝ}

local notation "gradQ" => gradientWithin d Q

/- Lemma 4.2.2 lies in the chapter's uniformly convex differentiable-analysis domain on real
Hilbert spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* `uniformConvexPowerModulus` in `Definition_4_2_8`
* `UniformConvexOn.lower_tangent_power_of_hasGradientWithinAt` in `Definition_4_2_8`
* `UniformConvexOn.lower_tangent_power` in `Definition_4_2_8`
* mathlib `Real.HolderConjugate.conjExponent` and `Real.young_inequality_of_nonneg`

Best owner abstraction:
* source-facing: the Bregman-gap upper bound from Lemma 4.2.2, with the within-gradients at
  `x` and `y`
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the stronger comparison-vector form, where the tangent model at `x` is replaced by
  an arbitrary comparison vector and only the tangent model at `y` is required to come from an
  actual within-set gradient

Primitive data:
* the feasible set `Q`
* the objective `d`
* the power parameter `p` and modulus parameter `σp`
* the canonical owner predicate `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* feasible points `x` and `y`
* the canonical within-gradients `gradientWithin d Q x` and `gradientWithin d Q y`, under
  differentiability at those points

Derived API:
* the pointwise lower-tangent inequality from
  `UniformConvexOn.lower_tangent_power_of_hasGradientWithinAt`
* the dual-exponent scalar estimate from Young's inequality, factored into a private helper
* an internal comparison-vector reduction, obtained by allowing an arbitrary `gx` at `x`

This file keeps only the source-facing two-gradient inequality as public API and treats the
arbitrary-comparison-vector estimate as private bridge/view scaffolding built on the same
owner-level uniform-convexity predicate.
-/

namespace UniformConvexOn

private theorem young_gap_le_gradient_sub_rpow
    (hp : 1 < p)
    (hσp : 0 < σp)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    a * b - ((1 / p) * σp * b ^ p) ≤
      ((p - 1) / p) * (1 / σp) ^ (1 / (p - 1)) * a ^ (p / (p - 1)) := by
  have hp_ne : p ≠ 0 := by positivity
  let q : ℝ := Real.conjExponent p
  have hpq : Real.HolderConjugate p q := Real.HolderConjugate.conjExponent hp
  let σroot : ℝ := σp ^ (1 / p)
  have hσroot_nonneg : 0 ≤ σroot := by
    dsimp [σroot]
    exact Real.rpow_nonneg hσp.le _
  have hσroot_ne : σroot ≠ 0 := by
    dsimp [σroot]
    positivity
  have hyoung := Real.young_inequality_of_nonneg
    (show 0 ≤ σroot * b by positivity)
    (show 0 ≤ a / σroot by positivity) hpq
  have hσroot_pow : σroot ^ p = σp := by
    dsimp [σroot]
    simpa [one_div] using Real.rpow_inv_rpow hσp.le hp_ne
  have hfirst : (σroot * b) ^ p / p = ((1 / p) * σp * b ^ p) := by
    rw [div_eq_mul_inv, Real.mul_rpow hσroot_nonneg hb, hσroot_pow]
    ring
  have hq_inv : q⁻¹ = (p - 1) / p := by
    dsimp [q, Real.conjExponent]
    field_simp [hp_ne, sub_ne_zero.mpr hp.ne']
  have hexp : (1 / p) * (p / (p - 1)) = 1 / (p - 1) := by
    field_simp [hp_ne, sub_ne_zero.mpr hp.ne']
  have hσroot_rpow_q : σroot ^ q = σp ^ (1 / (p - 1)) := by
    calc
      σroot ^ q = σp ^ ((1 / p) * (p / (p - 1))) := by
        dsimp [σroot, q, Real.conjExponent]
        rw [Real.rpow_mul hσp.le]
      _ = σp ^ (1 / (p - 1)) := by
        rw [hexp]
  have hinv : (σp ^ (1 / (p - 1)))⁻¹ = (1 / σp) ^ (1 / (p - 1)) := by
    simpa [one_div] using (Real.inv_rpow hσp.le (1 / (p - 1))).symm
  have hsecond : (a / σroot) ^ q / q =
      ((p - 1) / p) * (1 / σp) ^ (1 / (p - 1)) * a ^ (p / (p - 1)) := by
    rw [Real.div_rpow ha hσroot_nonneg, div_eq_mul_inv, div_eq_mul_inv,
      hq_inv, hσroot_rpow_q, hinv]
    dsimp [q, Real.conjExponent]
    ring
  have hleft : σroot * b * (a / σroot) = a * b := by
    field_simp [σroot, hσroot_ne]
  rw [hleft, hfirst, hsecond] at hyoung
  linarith

-- Internal bridge/view reduction: the tangent model at `x` is replaced by an arbitrary
-- comparison vector `gx`, while `gy` remains an actual within-set gradient at `y`.
private theorem comparison_gap_le_gradient_sub_rpow_of_hasGradientWithinAt
    (huc : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (hp : 1 < p)
    (hσp : 0 < σp)
    {x y gx gy : E}
    (hx : x ∈ Q)
    (hy : y ∈ Q)
    (hdy : HasGradientWithinAt d gy Q y) :
    d y - d x - inner ℝ gx (y - x) ≤
      ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
        Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
  have hlower :=
    huc.lower_tangent_power_of_hasGradientWithinAt y hy gy hdy x hx
  have hsub : x - y = -(y - x) := by
    simp [sub_eq_add_neg]
  rw [hsub, inner_neg_right, norm_neg] at hlower
  have hdyx :
      d y - d x ≤ inner ℝ gy (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ := by
    linarith
  have hgap :
      d y - d x - inner ℝ gx (y - x) ≤
        inner ℝ (gy - gx) (y - x) -
          uniformConvexPowerModulus σp p ‖y - x‖ := by
    calc
      d y - d x - inner ℝ gx (y - x)
          ≤ (inner ℝ gy (y - x) - uniformConvexPowerModulus σp p ‖y - x‖) -
              inner ℝ gx (y - x) := by
            linarith
      _ = inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ := by
        rw [inner_sub_left]
        ring
  have hinner :
      inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ ≤
        ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
          Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
    have hnorm :
        inner ℝ (gy - gx) (y - x) ≤ ‖gy - gx‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    calc
      inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖
          ≤ ‖gy - gx‖ * ‖y - x‖ - uniformConvexPowerModulus σp p ‖y - x‖ := by
            linarith
      _ ≤ ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
            Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
          simpa [uniformConvexPowerModulus] using
            young_gap_le_gradient_sub_rpow hp hσp (norm_nonneg _) (norm_nonneg _)
  exact hgap.trans hinner

/-- Lemma 4.2.2 in source-facing form: for a degree-`p` uniformly convex function, the Bregman
gap between two feasible points is controlled by the dual power of the difference of their
canonical within-gradients. -/
theorem tangent_gap_le_gradient_sub_rpow
    (huc : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (hp : 1 < p)
    (hσp : 0 < σp)
    {x y : E}
    (hx : x ∈ Q)
    (hy : y ∈ Q)
    (hdx : DifferentiableWithinAt ℝ d Q x)
    (hdy : DifferentiableWithinAt ℝ d Q y) :
    d y - d x - inner ℝ (gradQ x) (y - x) ≤
      ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
        Real.rpow ‖gradQ y - gradQ x‖ (p / (p - 1)) := by
  let gx := gradQ x
  let gy := gradQ y
  have hgx : HasGradientWithinAt d gx Q x := by
    simpa [gx] using hdx.hasGradientWithinAt
  have hgy : HasGradientWithinAt d gy Q y := by
    simpa [gy] using hdy.hasGradientWithinAt
  simpa [gx, gy] using
    comparison_gap_le_gradient_sub_rpow_of_hasGradientWithinAt
      huc hp hσp hx hy hgy

end UniformConvexOn

end

/-! ### Text_4_2_2 (from Chap04) -/
noncomputable section

open Module

universe u v

/-
Text 4.2.2 lies in the finite-dimensional basis-coordinate / dual-basis duality domain.

Sampled owner-style declarations:
- `Basis.equivFun`
- `Basis.sum_equivFun`
- `Basis.dualBasis_equivFun`
- `Matrix.dotProduct`
- `EuclideanSpace.inner_eq_star_dotProduct`

Best owner abstraction:
- a finite basis `B : Basis ι R E`, with the canonical coordinate map `B.equivFun`
  and the dual-coordinate bridge theorem `Basis.dualBasis_equivFun`

Primitive data:
- `B : Basis ι R E`
- `s : Dual R E`
- `x : E`

Derived API:
- the coordinate dot product `(fun i ↦ s (B i)) ⬝ᵥ B.equivFun x`
- the corresponding Euclidean inner-product form obtained by transporting those coordinate
  functions through `EuclideanSpace.equiv` in the real `Fin n` specialization

Source/core/bridge triage:
- source-facing: the coordinate formula for the duality pairing
- core/canonical: `Module.dualPairing`, `Basis.equivFun`, and the bridge theorem
  `Basis.dualBasis_equivFun`
- bridge/view: transport between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)` via
  `EuclideanSpace.equiv`

This file therefore keeps only the source-facing theorem and a thin theorem-level bridge, rather
than owning duplicate public coordinate operators built by composing the canonical maps.
-/

section CoordinateDuality

variable {R : Type v} {ι : Type*} {E : Type u}
variable [CommSemiring R] [Fintype ι] [AddCommMonoid E] [Module R E]

/-- In basis/dual-basis coordinates, the duality pairing is the standard dot product. -/
theorem dualityPairing_eq_coordinateDotProduct
    (B : Basis ι R E) (s : Dual R E) (x : E) :
    Module.dualPairing R E s x = (fun i ↦ s (B i)) ⬝ᵥ B.equivFun x := by
  classical
  rw [Module.dualPairing_apply]
  calc
    s x = s (∑ i : ι, B.equivFun x i • B i) := by
      exact congrArg s (B.sum_equivFun x).symm
    _ = ∑ i : ι, s (B i) * B.equivFun x i := by
      simp_rw [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = (fun i ↦ s (B i)) ⬝ᵥ B.equivFun x := by
      simp [dotProduct]

end CoordinateDuality

section EuclideanBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: expand `x` in the basis `B` and `s` in the dual basis `B*`; evaluation of `s`
-- on the resulting linear combination reduces to the sum of coordinatewise products, which is the
-- Euclidean dot product of the two coordinate vectors.
/-- Text 4.2.2: the duality pairing equals the Euclidean inner product of the coordinate vectors
`B* s` and `B⁻¹ x`. -/
theorem dualityPairing_eq_inner_coordinateVectors {n : ℕ}
    (B : Basis (Fin n) ℝ E) (s : Dual ℝ E) (x : E) :
    Module.dualPairing ℝ E s x =
      inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.equivFun x)) := by
  have hdual : (fun i : Fin n ↦ s (B i)) = B.dualBasis.equivFun s := by
    ext i
    rw [Basis.dualBasis_equivFun]
  calc
    Module.dualPairing ℝ E s x = (fun i : Fin n ↦ s (B i)) ⬝ᵥ B.equivFun x :=
      dualityPairing_eq_coordinateDotProduct B s x
    _ = B.dualBasis.equivFun s ⬝ᵥ B.equivFun x := by
      rw [hdual]
    _ = inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.equivFun x)) := by
      have hinner :
          ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ u v = u ⬝ᵥ v := fun u v ↦ by
            simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct u v)
      rw [hinner]
      simp [EuclideanSpace.equiv]

end EuclideanBridge

end

/-! ### Theorem_4_2_2 (from Chap04) -/
noncomputable section

open scoped LevelSetNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.2.2 lies in the whole-space cubic-Newton / Hessian-Lipschitz rate domain.

Sampled owner declarations:
* `CubicNewtonMethod` in `Algorithm_4_2_1`, the chapter owner for the iterate sequence, the
  chosen cubic Newton step, and the standing `C22[L3]` smoothness hypothesis;
* `CubicNewtonMethod.step_isMinOn` in `Algorithm_4_2_1`, the derived owner theorem recovering the
  minimizing property of each cubic Newton step on the canonical cubic model;
* `convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Text_4_2_8`, the
  chapter cubic-model comparison theorem turning convexity plus a minimizing step into one-step
  objective decrease;
* `IsMinOn` and `ConvexOn ℝ Set.univ f`, the canonical minimizer and convexity owners used on the
  theorem surface.

Source/core/bridge triage:
* source-facing: the inverse-square gap estimate for a monotone cubic Newton trajectory with a
  bounded initial sublevel set;
* core/canonical: `CubicNewtonMethod f L3 x0` together with `IsMinOn f Set.univ xStar`;
* bridge/view: the radius control on the initial sublevel set.

Primitive data:
* the objective `f`;
* the cubic Newton method owner `method`;
* the minimizer `xStar`;
* the explicit radius constant `D`;
* the bounded-sublevel radius control assumption.

Derived API:
* `ContDiff ℝ 2 f`;
* global Hessian-Lipschitz control for `hessian f`;
* positivity of `(L3 : ℝ)`;
* global minimality of each cubic Newton step on the canonical cubic model;
* the one-step decrease `f (method (k + 1)) ≤ f (method k)`, derived from convexity via
  `convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation`.

The previous theorem surface repeated those derived items as primitive hypotheses. This refinement
keeps the source-facing rate theorem, but rewrites it directly on the chapter owner
`CubicNewtonMethod` and leaves only the genuinely extra bounded-sublevel assumption public. -/

namespace CubicNewtonMethod

/-- Convexity and the cubic-model minimizing property force one-step objective decrease along a
cubic Newton method. -/
theorem objective_succ_le
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : CubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  rw [method.x_succ]
  have hdecrease :
      f (method k) - f (method.step (method k)) ≥
        ((L3 : ℝ) / 3 : ℝ) * ‖method k - method.step (method k)‖ ^ (3 : ℕ) :=
    convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation
      method.objective_mem
      hf_conv
      le_rfl
      (method.step_isMinOn (method k))
  have hnonneg :
      0 ≤ ((L3 : ℝ) / 3 : ℝ) * ‖method k - method.step (method k)‖ ^ (3 : ℕ) := by
    positivity
  linarith

end CubicNewtonMethod

section

variable {f : E → ℝ} {L3 : NNReal} {x0 xStar : E}

local notation "𝓛0" => (𝓛[f]((f x0)) : Set E)

-- Proof sketch: the derived one-step decrease theorem `method.objective_succ_le hf_conv`
-- keeps every iterate `method k` inside the canonical initial sublevel set `𝓛0`, so `hlevel`
-- gives `‖method k - xStar‖ ≤ D`. Use convexity on the segment from `method k` to `xStar`, then
-- combine the cubic-model minimizing property supplied by `method.step_isMinOn (method k)` with
-- the Taylor upper bound coming from `method.objective_mem : f ∈ C22[L3]` to obtain the scalar
-- recurrence `δ_{k+1} ≤ δ_k - τ δ_k + τ^3 (L₃ / 3) D^3` for
-- `δ_k = f (method k) - f xStar`. Optimizing in `τ` and telescoping the reciprocal square-root
-- inequality yields the inverse-square estimate.
/-- Theorem 4.2.2: for a convex objective with `L₃`-Lipschitz continuous Hessian, if the cubic
Newton initial sublevel set `𝓛[f]((f x₀))` is contained in the closed ball of radius `D`
around a minimizer `x*`, then every iterate with index `k ≥ 1` satisfies
`f(x_k) - f(x*) ≤ 9 L₃ D^3 / (k + 4)^2`. -/
theorem cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel
    (method : CubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (D : ℝ)
    (hlevel : ∀ ⦃z : E⦄, z ∈ 𝓛0 → ‖z - xStar‖ ≤ D)
    (k : ℕ) (hk : 1 ≤ k) :
    f (method k) - f xStar ≤
      (9 * (L3 : ℝ) * D ^ (3 : ℕ)) / ((k + 4 : ℝ) ^ (2 : ℕ)) := by
  sorry

end

/-! ### Definition_4_2_3 (from Chap04) -/
open Module

universe u v w

/- Definition 4.2.3 lies in the algebraic-duality / bilinear-transpose domain.

Sampled owner-style declarations:
- mathlib `LinearMap.flip`
- mathlib `LinearMap.flip_apply`
- mathlib `Module.Dual`
- mathlib `Dual.eval`

Best owner abstraction:
- core/canonical: `LinearMap.flip` for bilinear maps

Primitive data:
- a commutative semiring `R`
- `R`-modules `E₁` and `E₂`
- a dual-valued linear map `A : E₁ →ₗ[R] Dual R E₂`

Derived API:
- the pointwise transpose identity `A.flip y x = A x y`

Source/core/bridge triage:
- source-facing: the transpose `A* : E₂ → E₁*` of `A : E₁ → E₂*`
- core/canonical: `LinearMap.flip`
- bridge/view: the specialization from bilinear maps to dual-valued operators

The previous local owner `adjointOperator` was definitionally equal to `LinearMap.flip`, so this
file now recalls the canonical owner directly and keeps only the specialized pointwise companion
theorem used in the chapter.
-/

variable {R : Type u} {E₁ : Type v} {E₂ : Type w}
variable [CommSemiring R]
variable [AddCommMonoid E₁] [Module R E₁]
variable [AddCommMonoid E₂] [Module R E₂]

/- Definition 4.2.3: for a linear operator `A : E₁ → E₂*`, the adjoint operator is exactly the
canonical transpose `A.flip : E₂ → E₁*`. -/
#check (LinearMap.flip : (E₁ →ₗ[R] Dual R E₂) → E₂ →ₗ[R] Dual R E₁)

/- Evaluating the canonical transpose at `y` and then at `x` recovers the defining pairing
identity `(A x) y`. -/
#check
  (LinearMap.flip_apply :
    ∀ (A : E₁ →ₗ[R] Dual R E₂) (x : E₁) (y : E₂), A.flip y x = A x y)

/-! ### Lemma_4_2_3 (from Chap04) -/
noncomputable section

universe u

open LinearMap (BilinForm)
open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Lemma 4.2.3 lies in the chapter's `B`-induced norm geometry for
degree-`p` power functions.

Sampled owner-style declarations:
- `LinearMap.BilinForm.PrimalSpace` in `Definition_4_2_9`
- `powerFunction` in `Definition_4_2_9`
- `LinearMap.BilinForm.primalSeminorm` together with the notation `‖·‖[B]`
- `uniformConvexPowerModulus` in `Definition_4_2_8`
- mathlib `UniformConvexOn`

Best owner abstraction:
- source-facing: the degree-`p` power regularizer on the intrinsic `B`-weighted carrier together
  with its lower-tangent and derivative-monotonicity companions
- core/canonical: the bilinear-form owner `B : BilinForm ℝ E` through the weighted carrier
  `LinearMap.BilinForm.PrimalSpace B`
- bridge/view: the explicit `fderiv` / `Module.dualPairing` inequalities on that intrinsic
  carrier

Primitive data:
- `B : BilinForm ℝ E`
- `hSymm : B.IsSymm`
- `hPos : B.toQuadraticMap.PosDef`
- `p : ℝ`
- `hp : 2 ≤ p`
- `x₀ : LinearMap.BilinForm.PrimalSpace B`

Derived API:
- the owner uniform-convexity statement for `powerFunction B p x₀`
- the source monotonicity inequality
- the explicit first-order lower-support inequality, equivalently the corresponding Bregman-gap
  lower bound

Source/core/bridge triage:
- source-facing: Lemma 4.2.3's power lower bounds in the `B`-geometry
- core/canonical: the intrinsic weighted carrier `LinearMap.BilinForm.PrimalSpace B`
- bridge/view: the Fréchet-derivative formulations on that carrier

Now that `Definition_4_2_9` exposes the intrinsic `B`-weighted carrier, the nearby canonical owner
`UniformConvexOn` is the right abstraction level for the main result: its ambient norm on
`PrimalSpace B` is exactly the `B`-geometry. The explicit `fderiv` inequalities therefore become
companion bridge theorems on that owner space instead of the main public entry.
-/

section

variable (B : BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)

variable (p : ℝ)
variable (x0 x y : LinearMap.BilinForm.PrimalSpace B)

/-- Lemma 4.2.3 in owner form: on the intrinsic `B`-weighted space, the degree-`p` power
regularizer is uniformly convex with the textbook modulus `(1 / p) * (1 / 2)^(p - 2) * r^p`. -/
theorem powerFunction_uniformConvexOn (hp : 2 ≤ p) :
    by
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus (Real.rpow (1 / 2 : ℝ) (p - 2)) p)
          (powerFunction B p x0) := sorry

/-- Lemma 4.2.3 (1): for a positive-definite self-adjoint form `B`, the Fréchet derivative of the
degree-`p` power function `d_p(x) = (1 / p) * ‖x - x₀‖[B]^p` is strongly monotone with modulus
`(1 / 2)^(p - 2)` when measured in the intrinsic norm on `PrimalSpace B`, i.e. in the
`B`-induced norm. -/
-- Proof sketch: derive the derivative monotonicity estimate from the owner uniform-convexity
-- statement on the intrinsic `B`-weighted space.
theorem powerFunction_fderiv_mono_ge_primalNorm_rpow
    (hp : 2 ≤ p) :
    by
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        Module.dualPairing ℝ (LinearMap.BilinForm.PrimalSpace B)
            ((fderiv ℝ (powerFunction B p x0) x :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ) -
              (fderiv ℝ (powerFunction B p x0) y :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ))
            (x - y) ≥
          Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p := sorry

/-- Lemma 4.2.3 (2): for a positive-definite self-adjoint form `B`, the degree-`p` power
function lies above its tangent model at `y` by at least
`(1 / p) * (1 / 2)^(p - 2) * ‖x - y‖^p` in the intrinsic norm on `PrimalSpace B`; equivalently,
the Bregman gap at `y` has the same lower bound. -/
-- Proof sketch: read the source-facing inequality as the explicit first-order companion of the
-- owner uniform-convexity statement `powerFunction_uniformConvexOn`.
theorem powerFunction_lower_tangent_ge_primalNorm_rpow (hp : 2 ≤ p) :
    by
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        powerFunction B p x0 x ≥
          powerFunction B p x0 y +
            Module.dualPairing ℝ (LinearMap.BilinForm.PrimalSpace B)
              (fderiv ℝ (powerFunction B p x0) y :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ)
              (x - y) +
              (1 / p) * Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p := sorry

end

/-! ### Text_4_2_3 (from Chap04) -/
noncomputable section

open InnerProductSpace
open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.3 lies in the real-Hilbert-space Hessian domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for the intrinsic Hessian operator
* `fderiv_gradient_isSymmetric_of_contDiffAt` in `Chap01/Theorem_1_4_19`, the chapter symmetry
  bridge for `C²` Hessians
* `InnerProductSpace.toDualMap`, the canonical forward Riesz map into the strong dual
* `LinearMap.IsSymmetric.isSelfAdjoint`, the canonical bridge from symmetry to self-adjointness

Owner abstraction:
* core/canonical: `hessian f x`
* bridge/view: `toDualMap ∘ hessian f x`

Primitive data:
* `f`
* `x`
* differentiability of `∇ f` at `x`
* `ContDiffAt ℝ 2 f x`

Derived API:
* the dual-valued Hessian view `toDualMap ∘ hessian f x`
* its pointwise pairing formula
* its derivative formula for the dual-valued gradient map
* self-adjointness of `hessian f x`

This file therefore reuses the chapter owner `hessian f x` directly. The dual-valued formulation
appearing in the text is kept only as a thin bridge via the forward Riesz map `toDualMap`
(equivalently the forward direction of `toDual`), rather than as a second public Hessian owner. -/

/-- Applying the dual-valued Hessian bridge `toDualMap ∘ hessian f x` to a direction `u` and then
to a test vector `v` gives the Hessian pairing at `x`. -/
@[simp] theorem hessian_toDualMap_apply (f : E → ℝ) (x u v : E) :
    (((toDualMap ℝ E).toContinuousLinearMap.comp (hessian f x)) u) v =
      inner ℝ (hessian f x u) v := by
  simp

/-- Text 4.2.3: if `f` is twice differentiable at `x`, then the Hessian at `x` is the continuous
linear operator from the primal space `E` to the continuous dual `E⋆` obtained by differentiating
the gradient and composing with the Riesz identification `E ≃ E⋆`. -/
-- Proof sketch: view `y ↦ ∇ f y` as the first derivative of `f`, compose its derivative at `x`
-- with the forward Riesz map `InnerProductSpace.toDualMap`, and apply the chain rule.
theorem hessian_toDualMap_hasFDerivAt
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ (∇ f) x) :
    HasFDerivAt ((toDualMap ℝ E) ∘ ∇ f)
      ((toDualMap ℝ E).toContinuousLinearMap.comp (hessian f x)) x := by
  simpa [Function.comp] using
    ((toDualMap ℝ E).toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt)

/-- If `f` is `C²` at `x`, then the intrinsic Hessian operator `hessian f x` is self-adjoint. -/
-- Proof sketch: identify the Hessian with the second derivative of `f`; Schwarz symmetry for the
-- second derivative gives a symmetric bilinear form, and on a real Hilbert space this is
-- equivalent to self-adjointness of the associated continuous linear operator.
theorem hessian_isSelfAdjoint_of_contDiffAt
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessian f x) := by
  simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint

/-! ### Theorem_4_2_3 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 4.2.3 lies in the chapter accelerated cubic-Newton / estimating-sequence domain.

Sampled owner declarations:
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `f ∈ C22[L3]`, in
  `Definition_4_2_7`, the chapter owner for `C²` regularity plus global Hessian-Lipschitz
  control;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for the iterate
  sequence, estimating-function minimizers, accumulated weights, and the standing
  `C22[L3]` smoothness hypothesis;
* `AcceleratedCubicNewtonMethod.psi`, `psi_one`, and `psi_succ` in `Algorithm_4_2_2`, the
  canonical derived estimating-function surface replacing a primitive family `ψ_k`;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized at each accelerated step.

Best owner abstraction:
* source-facing: the inverse-cubic objective-gap estimate for an accelerated cubic Newton method;
* core/canonical: `AcceleratedCubicNewtonMethod`, `cubicRegularizationQuadraticApproximation`,
  and `f ∈ C22[L3]`;
* bridge/view: the owner theorems `method.x_one_isMinOn` and `method.x_succ_isMinOn` recovering
  the textbook minimizing facts for the actual cubic steps used by the algorithm.

Primitive data:
* the objective `f`;
* the accelerated method owner `method`;
* convexity of `f`;
* a global minimizer `xStar`.

Derived API:
* `ContDiff ℝ 2 f` and global `L₃`-Lipschitz control of `hessian f`, both supplied by
  `method.objective_mem`;
* the iterate sequence `x_k`, minimizing sequence `v_k`, estimating functions `ψ_k`, and weights
  `A_k`;
* the initialization `x₁ = T_{L₃}(x₀)`;
* the recursive interpolation and estimating-function update formulas.

The previous statement stored `x`, `v`, `psi`, and `A` as primitive theorem inputs even though
Chapter 4 already owns exactly that data in `AcceleratedCubicNewtonMethod`. This refinement moves
the public surface to that owner, keeps the chapter smoothness hypothesis on the owner itself
instead of splitting it off as a parallel theorem argument, makes the iterate index explicit, and
derives the two actual model-minimization facts from the method's cubic-step owner instead of
keeping them as redundant external assumptions.
-/

-- Proof sketch: prove by induction on `k` the estimating-sequence relations
-- `method.A k * f (method k) ≤ sInf (Set.range (method.psi k))` and
-- `method.psi k z ≤ method.A k * f z + (4 / 3) * L₃ * ‖z - x₀‖^3`.
-- The base step uses the initialization `method 1 = T_{L₃}(x₀)`, `method.psi_one`, and
-- `method.x_one_isMinOn`.
-- For the inductive step, combine convexity of `f`, the minimizing property of `method.v k`, the
-- recursion for `method (k + 1)` and `method.psi (k + 1)`, and the fact that the two actual
-- cubic models used by the algorithm are globally minimized at the chosen iterates via
-- `method.x_succ_isMinOn hk`. Evaluating
-- the upper bound at `xStar`, using `method.A k = k (k + 1) (k + 2) / 6`, and rearranging gives
-- the stated
-- `O(1 / k^3)` estimate.
/-- Theorem 4.2.3: let `method` be the accelerated cubic Newton method. If `f ∈ C22[L3]` is
convex, then every iterate with index `k ≥ 1` satisfies
`f(x_k) - f(x^*) ≤ 8 L₃ ‖x₀ - x^*‖^3 / (k (k + 1) (k + 2))`. -/
theorem acceleratedCubicRegularization_gap_le_inverse_cubic_rate
    {f : E → ℝ} {L3 : NNReal} {x0 xStar : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) (hk : 1 ≤ k) :
      f (method k) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  sorry

/-! ### Definition_4_2_4 (from Chap04) -/
noncomputable section

open Module
open scoped BigOperators

universe u v

/- Definition 4.2.4 lies in the finite-dimensional basis-coordinate / dual-basis domain.

Sampled owner-style declarations:
- `Basis.equivFun`
- `Basis.equivFun_symm_apply`
- `Basis.dualBasis`
- `Basis.dualBasis_equivFun`

Best owner abstraction:
- core/canonical: the basis coordinate equivalence `B.equivFun` and the dual-basis coordinate
  equivalence `B.dualBasis.equivFun`;
- bridge/view: the textbook `ℝⁿ` model via `EuclideanSpace.equiv`.

Primitive data:
- a basis `B : Basis (Fin n) ℝ E`;
- a coordinate vector `x : EuclideanSpace ℝ (Fin n)`;
- a covector `s : Dual ℝ E`.

Derived API:
- the source-facing basis operator `B : ℝⁿ → E`, canonically realized as
  `B.equivFun.symm ∘ EuclideanSpace.equiv (Fin n) ℝ`;
- the source-facing dual operator `B* : E* → ℝⁿ`, canonically realized as
  `(EuclideanSpace.equiv (Fin n) ℝ).symm ∘ B.dualBasis.equivFun`.

Source/core/bridge triage:
- source-facing: Definition 4.2.4's two maps `B` and `B*`;
- core/canonical: `Basis.equivFun`, `Basis.dualBasis`, and `Basis.dualBasis_equivFun`;
- bridge/view: transport between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)` via
  `EuclideanSpace.equiv`.

This file therefore recalls the canonical basis/dual-basis coordinate owners and keeps only the
thin Euclidean bridge theorems matching the textbook formulas. -/

section Intrinsic

/- Definition 4.2.4 uses the canonical basis coordinate equivalence `B.equivFun`, whose inverse is
the basis operator from coordinates to vectors. -/
#check Basis.equivFun

/- The forward coordinate formula is the standard theorem `Basis.equivFun_symm_apply`. -/
#check Basis.equivFun_symm_apply

/- The dual object `B*` is the canonical dual basis `B.dualBasis`. -/
#check Basis.dualBasis

/- The dual-coordinate formula is the standard theorem `Basis.dualBasis_equivFun`. -/
#check Basis.dualBasis_equivFun

end Intrinsic

section EuclideanBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ}

/-- Definition 4.2.4: in the textbook `ℝⁿ` model, the basis operator attached to `B` is the
canonical inverse coordinate map `B.equivFun.symm`, transported through `EuclideanSpace.equiv`. -/
theorem basis_equivFun_symm_apply (B : Basis (Fin n) ℝ E) (x : EuclideanSpace ℝ (Fin n)) :
    B.equivFun.symm (EuclideanSpace.equiv (Fin n) ℝ x) = ∑ i : Fin n, x i • B i := by
  rw [Basis.equivFun_symm_apply]
  simp [EuclideanSpace.equiv]

/-- Definition 4.2.4: in the textbook `ℝⁿ` model, the dual basis operator `B*` has `i`th
coordinate `⟪s, B i⟫ = s (B i)`. -/
theorem dualBasis_equivFun_apply (B : Basis (Fin n) ℝ E) (s : Dual ℝ E) (i : Fin n) :
    ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s)) i = s (B i) := by
  change B.dualBasis.equivFun s i = s (B i)
  rw [Basis.dualBasis_equivFun]

end EuclideanBridge

end

/-! ### Lemma_4_2_4 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.4 lies in the Chapter 4 norm-power / Hessian-Lipschitz domain on real Hilbert spaces.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`
* `hessian` in `Chap01/Definition_1_4_16`
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.norm_sub_le` in `Definition_4_2_7`

Best owner abstraction:
* core/canonical: the global Hessian-Lipschitz owner
  `HasLipschitzContinuousHessian L (powerDistance p x₀)`, written on theorem surfaces as
  `powerDistance p x₀ ∈ C22[L]`

Primitive data:
* the center `x₀ : E`
* the canonical cubic power function `powerDistance (3 : ℝ) x₀`

Derived API:
* the owner membership `powerDistance (3 : ℝ) x₀ ∈ C22[2]`
* the zero-centered specialization `powerDistance (3 : ℝ) (0 : E) ∈ C22[2]`
* the pointwise Hessian estimate obtained from
  `HasLipschitzContinuousHessian.norm_sub_le`

Source/core/bridge triage:
* source-facing: the textbook Hessian estimate for `d₃(x) = (1 / 3) * ‖x‖³`
* core/canonical: the owner assertion
  `powerDistance (3 : ℝ) x₀ ∈ C22[(2 : NNReal)]`
* bridge/view: specialization to `x₀ = 0` and evaluation of the owner inequality at points `x`
  and `y`

The local definition `d3` duplicated the earlier chapter owner `powerDistance`; this file reuses
that owner directly, lifts the Hessian-Lipschitz statement to the intrinsic center parameter `x₀`,
and keeps the textbook zero-centered estimate as a thin specialization.
-/

/-- The translated cubic power function `powerDistance (3 : ℝ) x₀` has globally `2`-Lipschitz
Hessian. This is the owner-level statement underlying Lemma 4.2.4 and its translated uses. -/
theorem powerDistance_three_mem_C22 (x0 : E) :
    powerDistance (3 : ℝ) x0 ∈ C22[(2 : NNReal)] := sorry

/-- The Hessians of the translated cubic power function satisfy the owner inequality
`‖∇² d₃,x₀(x) - ∇² d₃,x₀(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_hessian_norm_sub_le (x0 x y : E) :
    ‖hessian (powerDistance (3 : ℝ) x0) x -
        hessian (powerDistance (3 : ℝ) x0) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using
    HasLipschitzContinuousHessian.norm_sub_le (powerDistance_three_mem_C22 x0) x y

/-- Lemma 4.2.4: the centered cubic power function `d₃(x) = (1 / 3) * ‖x‖³`, realized as
`powerDistance (3 : ℝ) 0`, has globally `2`-Lipschitz Hessian. -/
theorem powerDistance_three_zero_mem_C22 :
    powerDistance (3 : ℝ) (0 : E) ∈ C22[(2 : NNReal)] := by
  simpa using powerDistance_three_mem_C22 (0 : E)

/-- Lemma 4.2.4, pointwise form: for any `x, y ∈ E`, the Hessian of the centered cubic power
function satisfies `‖∇² d₃(x) - ∇² d₃(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_zero_hessian_norm_sub_le (x y : E) :
    ‖hessian (powerDistance (3 : ℝ) (0 : E)) x -
        hessian (powerDistance (3 : ℝ) (0 : E)) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using powerDistance_three_hessian_norm_sub_le (0 : E) x y

end

/-! ### Text_4_2_4 (from Chap04) -/
noncomputable section

open Module LinearMap

universe u

/- Text 4.2.4 lies in the finite-dimensional bilinear-form duality domain for symmetric
positive-definite bilinear forms.

Sampled owner-style declarations:
- `LinearMap.BilinForm.dualNorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply_strongDual` in `Definition_4_2_6`

Best owner abstraction:
- core/canonical: the bilinear-form dual norm owner `LinearMap.BilinForm.dualNorm`
- bridge/view: its support-function and `B.toDual` inverse-pairing expansions

Primitive data:
- `B : BilinForm ℝ E`

Derived API:
- the support-function formula on the primal `B`-unit ball
- the coordinate-free `B.toDual` inverse-pairing formula
- the source-facing equality below, obtained by composing those two owner theorems

Source/core/bridge triage:
- source-facing: the textbook equality between the support-function and inverse-pairing formulas
- core/canonical: `LinearMap.BilinForm.dualNorm`
- bridge/view: the two owner expansions recalled from `Definition_4_3_4`
-/

namespace LinearMap.BilinForm

open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Text 4.2.4: the support-function formula for the `B`-dual norm agrees with the coordinate-free
expression `⟨s, B⁻¹ s⟩^(1/2)`, where `B⁻¹ s` is the preimage of `s` under the finite-dimensional
equivalence `B.toDual` induced by the symmetric positive-definite bilinear form `B`. -/
theorem dualNorm_eq_sqrt_dualPairing_preimage
    (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (s : Dual ℝ E) :
    sSup ((fun x : E ↦ s x) '' {x | B.primalSeminorm hPos x ≤ 1}) =
      Real.sqrt (s (B.dualPreimage hPos s)) := by
  simpa using
    (B.dualNorm_eq_sSup_primalUnitBall
        hPos
        s).symm.trans
      (B.dualNorm_apply
        hSymm
        hPos
        s)

end LinearMap.BilinForm

/-! ### Definition_4_2_5 (from Chap04) -/
universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap (BilinForm)

/- Definition 4.2.5 lies in the bilinear-form/symmetric-operator domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.IsSymm`
- `LinearMap.BilinForm.isSymm_def`
- `LinearMap.IsSymmetric`
- `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`

Best owner abstraction:
- source-facing: symmetry of the bilinear pairing associated with an operator `E → E⋆`
- core/canonical: `LinearMap.BilinForm.IsSymm`
- bridge/view: `LinearMap.IsSymmetric` and `IsSelfAdjoint` after choosing an inner product

Primitive data:
- a bilinear form `B : BilinForm R M`

Derived API:
- the pointwise symmetry characterization `B x y = B y x`

This item is therefore a direct recall of the canonical bilinear-form owner, not a new local
`selfAdjoint` wrapper. -/
/-
Definition 4.2.5: for a linear operator `B : E → E⋆` on a real vector space, the textbook
self-adjointness condition is the canonical symmetry predicate on the associated bilinear form,
equivalently `(B x) y = (B y) x` for all `x` and `y`.
-/
recall LinearMap.BilinForm.IsSymm (B : BilinForm R M) : Prop

/-
The canonical symmetry predicate on a bilinear form is exactly the pointwise equality
`B x y = B y x`.
-/
recall LinearMap.BilinForm.isSymm_def {B : BilinForm R M} :
    B.IsSymm ↔ ∀ x y : M, B x y = B y x

/-! ### Lemma_4_2_5 (from Chap04) -/
open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.5 lies in the cubic-regularization / Hessian-Lipschitz remainder domain on complete
real inner-product spaces.

Sampled owner declarations:
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`
* `hessian` in `Chap01/Definition_1_4_16`
* `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin` in `Definition_4_2_12`
* `argmin[Set.univ] (m[f; M](x))` in `Definition_4_1_3`

Best owner abstraction:
* the global Hessian-Lipschitz owner `f ∈ C22[L3]`
* the canonical cubic-step owner
  `argmin[Set.univ] (m[f; M](x))`

Primitive data:
* the owner hypothesis `hf : f ∈ C22[L3]`
* the cubic-step membership
  `T ∈ argmin[Set.univ] (m[f; M](x))`

Derived API:
* the gradient remainder bound
  `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`
* the owner radius estimate derived from
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the cubic-step first-order optimality equation
  `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin`

Source/core/bridge triage:
* source-facing: the gradient-pairing lower bound for one cubic-regularized Newton step
* core/canonical: `f ∈ C22[L3]` and `hessian f x`
* bridge/view: the first-order optimality equation extracted from the cubic-step owner

The previous theorem used a free linear operator `B : E →ₗ[ℝ] E` with pointwise axioms forcing the
cubic term back to the standard Euclidean-radius expression. In this plain real inner-product-space
setting, that extra wrapper is not the mathematical owner. This refinement keeps the source-facing
pairing estimate, but moves the step hypothesis to the canonical cubic-step owner
`argmin[Set.univ] (m[f; M](x))` and uses the intrinsic radius
`‖T - x‖` together with the owner first-order optimality equation. -/

-- Proof sketch: first derive the radius lower bound
-- `‖T - x‖² ≥ (2 / (L₃ + M)) * ‖∇ f T‖` internally from
-- `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`, using
-- `hM : 2 * L₃ ≤ M` to get `0 ≤ M`. Then apply the owner theorem
-- `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`, combine it with
-- `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin (hf.contDiff.contDiffAt x) hT`,
-- and obtain
-- `‖∇ f T + ((1 / 2) * M * ‖T - x‖) • (T - x)‖² ≤ ((L₃ / 2) * ‖T - x‖²)²`. Expanding the square
-- yields a lower bound for `⟪∇ f T, x - T⟫` in terms of
-- `‖∇ f T‖² / (M * ‖T - x‖)` and `((M² - L₃²) / (4 * M)) * ‖T - x‖³`. The assumption
-- `2 * L₃ ≤ M` makes this lower bound monotone on the feasible ray
-- `‖T - x‖² ≥ 2 ‖∇ f T‖ / (L₃ + M)`. Since `L₃ : NNReal` and `hM` force
-- `0 ≤ (L₃ : ℝ) + M`, the square-root coefficient is well-defined internally; in the degenerate
-- case `L₃ = M = 0`, the right-hand side vanishes. Evaluating the lower bound at the boundary
-- gives the stated
-- `‖∇ f T‖^(3 / 2)` estimate.
/-- Lemma 4.2.5: if `f ∈ C22[L₃]`, if `T` belongs to the canonical cubic-regularization step set
`argmin[Set.univ] (m[f; M](x))`, and if `2 L₃ ≤ M`, then
`⟪∇ f(T), x - T⟫ ≥ √(2 / (L₃ + M)) ‖∇ f(T)‖^(3 / 2)`. -/
theorem cubicRegularization_gradientPairing_ge_sqrt_mul_gradientNorm_rpow_threeHalves
    {f : E → ℝ} {L3 : NNReal} (hf : f ∈ C22[L3]) {x T : E} {M : ℝ}
    (hM : 2 * (L3 : ℝ) ≤ M)
    (hT : T ∈ argmin[Set.univ] (m[f; M](x))) :
    inner ℝ (∇ f T) (x - T) ≥
      Real.sqrt (2 / ((L3 : ℝ) + M)) * Real.rpow ‖∇ f T‖ (3 / 2 : ℝ) := sorry

/-! ### Text_4_2_5 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.5 lies in the second-order smooth optimization domain on real Hilbert spaces.

Sampled owner-style declarations:
- `HasLipschitzContinuousHessian`
- `HasLipschitzContinuousHessian.norm_sub_le`
- `HasLipschitzContinuousHessian.gradient_deviation_le`
- `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le`

Best owner abstraction:
- the Chapter 1 owner `HasLipschitzContinuousHessian M f`, written on theorem surfaces as
  `f ∈ C22[M]`

Primitive data:
- a function `f : E → ℝ`
- a Hessian-Lipschitz constant `M : NNReal`
- base and target points `x y : E`

Derived API:
- `HasLipschitzContinuousHessian.gradient_deviation_le`
- `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le`

Source/core/bridge triage:
- source-facing: the gradient and second-order Taylor remainder bounds stated in Text 4.2.5
- core/canonical: the Chapter 1 owner `HasLipschitzContinuousHessian`
- bridge/view: evaluation of the owner theorems at the points `x` and `y`

Text 4.2.5 adds no new mathematics beyond the Chapter 1 owner theorems, so this file is a pure
recall item. Keeping local wrappers here would duplicate the owner API and weaken the chapter's
canonical vocabulary. -/

recall HasLipschitzContinuousHessian.gradient_deviation_le

recall HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le

end
