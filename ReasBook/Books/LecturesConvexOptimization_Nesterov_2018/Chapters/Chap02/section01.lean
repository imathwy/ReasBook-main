import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_1 (from Chap02) -/
section

universe u

variable {α : Type u}
variable (f : α → ℝ) (xStar : α)

/- Definition 2.1: for an objective `f : ℝⁿ → ℝ`, the unconstrained minimization problem
`min_{x ∈ ℝⁿ} f(x)` is the whole-space minimization problem, and a global minimizer is
canonically expressed by `IsMinOn f Set.univ xStar`. The owner itself does not depend on the
ambient `ℝⁿ` presentation, so this file records the generic canonical recall and its textbook
`Set.univ` specialization. -/
recall IsMinOn

recall isMinOn_univ_iff

set_option linter.hashCommand false in
#check
  (show IsMinOn f Set.univ xStar ↔ ∀ x : α, f xStar ≤ f x from
    isMinOn_univ_iff)

end

/-! ### Example_2_1_1_1 (from Chap02) -/
open scoped RealInnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 2.1.1.1 lies in convex analysis of affine functionals on real inner product spaces.

Sampled owner-style declarations in this domain:
* mathlib `ConvexOn.comp_affineMap`
* mathlib `convexOn_id`
* mathlib `LinearMap.toAffineMap`
* mathlib `innerSL_apply_apply`

Best owner abstraction:
* `ConvexOn.comp_affineMap`, with the affine functional itself carried by `E →ᵃ[ℝ] ℝ`

Primitive data:
* the convex set `s`
* the affine functional `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`

Derived API:
* the source-facing convexity theorem for `x ↦ alpha + ⟪a, x⟫`, obtained by restricting the
  whole-space affine-owner convexity to `s`

Source/core/bridge triage:
* source-facing: Example 2.1.1.1's affine-inner convexity statement
* core/canonical: `ConvexOn.comp_affineMap`
* bridge/view: the affine functional
  `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`; the textbook `ℝⁿ` form
  is the Euclidean specialization of this intrinsic theorem

The previous proof decomposed the affine functional into a linear owner plus a constant-shift
lemma. This refinement keeps the same theorem, but treats the affine functional itself as the
owner object and derives convexity from `convexOn_id` via `ConvexOn.comp_affineMap`. -/

/-- Example 2.1.1.1:
Every function of the form `x ↦ α + ⟪a, x⟫` on a real inner product space is convex on a convex
set. The textbook `ℝⁿ` statement is the Euclidean specialization. -/
-- Proof sketch: package `x ↦ alpha + ⟪a, x⟫` as the affine map
-- `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`. Since `id : ℝ → ℝ` is
-- convex on `Set.univ`, its affine precomposition is convex on `Set.univ`; restricting that owner
-- theorem to `s` gives the result.
theorem convexOn_affine_inner (s : Set E)
    (hs : Convex ℝ s) (alpha : ℝ) (a : E) :
    ConvexOn ℝ s (fun x ↦ alpha + ⟪a, x⟫) := by
  let ℓ : E →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap
  have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
    simpa [Function.comp, ℓ] using
      (convexOn_id convex_univ).comp_affineMap ℓ
  refine ⟨hs, ?_⟩
  intro x hx y hy t u ht hu htu
  simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
    hℓ.2 (by simp) (by simp) ht hu htu

/-! ### Example_2_1_1_2 (from Chap02) -/
noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open scoped RealInnerProductSpace

/- Example 2.1.1.2 lies in finite-dimensional Euclidean convexity for quadratic objectives.

Sampled owner-style declarations in this domain:
* `quadraticObjective` from `Definition_1_9_1`
* `Matrix.PosSemidef` from `Definition_1_4_18`
* `Matrix.isPositive_toEuclideanLin_iff` from mathlib's positive-operator API

Best owner abstraction:
* positivity of the Euclidean linear operator `A.toEuclideanLin`, with `A.PosSemidef` as its
  canonical matrix-level realization

Primitive data:
* `alpha`, `a`, `A`, and `A.PosSemidef`

Derived API:
* the owner-derived theorem `Matrix.PosSemidef.convexOn_quadraticObjective`
  for `quadraticObjective alpha a A`

Source/core/bridge triage:
* source-facing: the textbook convexity example for a quadratic with positive-semidefinite Hessian
* core/canonical: `quadraticObjective`, `Matrix.PosSemidef`, `LinearMap.IsPositive`
* bridge/view: the owner-derived theorem `Matrix.PosSemidef.convexOn_quadraticObjective`
-/

/-- Helper for Example 2.1.1.2: every affine functional `x ↦ α + ⟪a, x⟫` on `ℝⁿ` is convex on
the whole space. -/
theorem convexOn_const_add_inner_univ (alpha : ℝ) (a : E) :
    ConvexOn ℝ Set.univ (fun x : E ↦ alpha + inner ℝ a x) := by
  let ℓ : E →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap
  -- Package the affine expression as a single affine map and pull back convexity of `id`.
  have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
    simpa [Function.comp, ℓ] using
      (convexOn_id convex_univ).comp_affineMap ℓ
  -- Expand the packaged affine map back to the textbook formula.
  simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using hℓ

namespace LinearMap.IsPositive

universe u

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A positive operator on a real inner-product space has convex quadratic form
`x ↦ (1 / 2) * ⟪T x, x⟫`. -/
theorem convexOn_half_inner_map_self {T : F →ₗ[ℝ] F} (hT : T.IsPositive) :
    ConvexOn ℝ Set.univ (fun x : F ↦ (1 / 2 : ℝ) * inner ℝ (T x) x) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ t s ht hs hts
  -- The Jensen gap is controlled by the quadratic form on `x - y`.
  have hquad : 0 ≤ inner ℝ (T (x - y)) (x - y) := hT.inner_nonneg_left (x - y)
  -- Self-adjointness turns the cross terms into a symmetric expression.
  have hsymm : ∀ u v : F, inner ℝ (T u) v = inner ℝ (T v) u := by
    intro u v
    simpa [real_inner_comm] using hT.isSymmetric u v
  have hs' : s = 1 - t := by
    linarith
  -- After normalizing `s = 1 - t`, the Jensen gap is exactly the negative PSD correction term.
  have hrewrite :
      (1 / 2 : ℝ) * inner ℝ (T (t • x + s • y)) (t • x + s • y) -
        (t * ((1 / 2 : ℝ) * inner ℝ (T x) x) +
          s * ((1 / 2 : ℝ) * inner ℝ (T y) y)) =
      -((t * s) / 2) * inner ℝ (T (x - y)) (x - y) := by
    subst hs'
    simp [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, map_add, map_sub, map_smul, hsymm x y]
    ring_nf
  -- Positivity of `T` and nonnegativity of the barycentric weights make the correction term
  -- nonpositive, which is exactly the Jensen inequality.
  have hrhs : -((t * s) / 2) * inner ℝ (T (x - y)) (x - y) ≤ 0 := by
    nlinarith [mul_nonneg ht hs, hquad]
  exact sub_nonpos.mp <| hrewrite ▸ hrhs

end LinearMap.IsPositive

namespace Matrix.PosSemidef

/-- Example 2.1.1.2: the canonical quadratic objective on `ℝ^n` with positive-semidefinite
Hessian data is convex. -/
-- Proof sketch: split the quadratic objective into its affine and quadratic pieces. The affine
-- term is convex on all of `ℝⁿ`, and the quadratic term is convex because `A.toEuclideanLin` is a
-- positive operator when `A` is positive semidefinite. Then add the two convex functions and
-- rewrite back to `quadraticObjective`.
theorem convexOn_quadraticObjective
    {A : Mat} (hA : A.PosSemidef) (alpha : ℝ) (a : E) :
    ConvexOn ℝ Set.univ (quadraticObjective alpha a A) := by
  -- The linear-plus-constant part is affine, hence convex on the whole space.
  have hAffine : ConvexOn ℝ Set.univ (fun x : E ↦ alpha + inner ℝ a x) :=
    convexOn_const_add_inner_univ alpha a
  -- The Hessian contribution is convex because `A` induces a positive operator.
  have hQuad :
      ConvexOn ℝ Set.univ (fun x : E ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x) :=
    LinearMap.IsPositive.convexOn_half_inner_map_self
      (Matrix.isPositive_toEuclideanLin_iff.mpr hA)
  -- Reassemble the affine and quadratic owners into the original quadratic objective.
  change ConvexOn ℝ Set.univ
    ((fun x : E ↦ alpha + inner ℝ a x) +
      fun x : E ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
  simpa [quadraticObjective, Pi.add_apply, add_assoc] using hAffine.add hQuad

end Matrix.PosSemidef

/-! ### Example_2_1_1_3 (from Chap02) -/
noncomputable section

open scoped ConvexC1

/-
Primary domain: first-order convex analysis of scalar functions on real convex domains.

Sampled owner-style declarations in this domain:
* Chapter 2 `ConvexC1On`, the owner abstraction for `𝓕¹(Q)`
* mathlib `Real.contDiff_exp`, the canonical smooth owner for `exp`
* mathlib `contDiff_norm_rpow`, the canonical `C¹` owner for `‖x‖^p`
* mathlib `convexOn_exp` and `convexOn_rpow`
* mathlib `ConvexOn.comp` with `Real.monotoneOn_rpow_Ici_of_exponent_nonneg`

Best owner abstraction:
* the domain-sensitive owner predicate `ConvexC1On Q f` on `ℝ`

Primitive data:
* a convex domain `Q : Set ℝ`
* a scalar function `f : ℝ → ℝ`
* `ContDiffOn ℝ 1 f Q`
* `ConvexOn ℝ Q f`

Derived API:
* `C¹` regularity on `Q` via `convexC1On_contDiffOn`
* convexity on `Q` via `convexC1On_convexOn`

Source/core/bridge triage:
* source-facing: the three textbook scalar examples in `𝓕¹(ℝ)`
* core/canonical: `ConvexC1On Q f`
* bridge/view: projection back to `ContDiffOn` and `ConvexOn`
-/

/-- Example 2.1.1.3 (1): the exponential function belongs to `𝓕¹(ℝ)`. -/
-- Proof sketch: pair mathlib's canonical declarations `Real.contDiff_exp.contDiffOn` and
-- `convexOn_exp`.
theorem exp_convexC1On_univ : Real.exp ∈ 𝓕¹(Set.univ) := by
  refine ⟨?_, ?_⟩
  · have hexp : ContDiff ℝ 1 Real.exp := Real.contDiff_exp.of_le le_top
    exact contDiffOn_univ.mpr hexp
  · simpa using convexOn_exp

/-- Example 2.1.1.3 (2): for every `p > 1`, the scalar function `t ↦ |t|^p` belongs to `𝓕¹(ℝ)`.
-/
-- Proof sketch: use `contDiff_norm_rpow hp` on `ℝ`, rewrite `‖t‖` as `|t|`, and combine
-- `convexOn_rpow hp.le` on `Ici 0` with the canonical convexity of the norm on `ℝ`.
theorem abs_rpow_convexC1On_univ (p : ℝ) (hp : 1 < p) :
    (fun t : ℝ ↦ |t| ^ p) ∈ 𝓕¹(Set.univ) := by
  refine ⟨?_, ?_⟩
  · simpa [contDiffOn_univ] using
      (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun t : ℝ ↦ ‖t‖ ^ p))
  · let g : ℝ → ℝ := fun x ↦ x ^ p
    have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
      simpa using (convexOn_norm convex_univ : ConvexOn ℝ Set.univ norm)
    have himage : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
    have hg : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) g := by
      simpa [himage] using convexOn_rpow hp.le
    have hmono : MonotoneOn g ((fun x : ℝ ↦ |x|) '' Set.univ) := by
      simpa [himage] using
        Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hp.le)
    simpa [g] using hg.comp habs hmono

/-- Example 2.1.1.3 (3): the scalar function `t ↦ |t| - log (1 + |t|)` belongs to `𝓕¹(ℝ)`. -/
-- Proof sketch: treat the example as the scalar convex `C¹` function `u ↦ u - log (1 + u)` on
-- `Ici 0` composed with `t ↦ |t|`; smoothness uses the scalar `log` calculus away from `-1`,
-- while convexity uses the same owner-side absolute-value/norm abstraction as in part (2) rather
-- than a coordinate split into `t ≥ 0` and `t ≤ 0`.
theorem abs_sub_log_one_add_abs_convexC1On_univ :
    (fun t : ℝ ↦ |t| - Real.log (1 + |t|)) ∈ 𝓕¹(Set.univ) := by
  let f : ℝ → ℝ := fun t ↦ |t| - Real.log (1 + |t|)
  let f' : ℝ → ℝ := fun x ↦ x / (1 + |x|)
  refine ⟨?_, ?_⟩
  · have hderiv : ∀ x, HasDerivAt f (f' x) x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        have hzero : HasDerivAt (fun t : ℝ ↦ |t| - Real.log (1 + |t|)) 0 0 := by
          rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_zero_iff_norm_tendsto_zero]
          refine @squeeze_zero ℝ
            (fun t : ℝ ↦ ‖t⁻¹ • (|0 + t| - Real.log (1 + |0 + t|) - (|0| - Real.log (1 + |0|)))‖)
            (fun t : ℝ ↦ |t| / 2) (nhdsWithin (0 : ℝ) {0}ᶜ) ?_ ?_ ?_
          · intro t
            exact norm_nonneg _
          · intro t
            by_cases ht : t = 0
            · simp [ht]
            · have ht_abs : 0 < |t| := abs_pos.mpr ht
              have hnonneg : 0 ≤ |t| - Real.log (1 + |t|) := by
                have hlog : Real.log (1 + |t|) ≤ |t| := by
                  simpa using (Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |t|))
                linarith
              have hlog := Real.le_log_one_add_of_nonneg (abs_nonneg t)
              have hquad : |t| - Real.log (1 + |t|) ≤ |t| ^ 2 / 2 := by
                have hstep : |t| - Real.log (1 + |t|) ≤ |t| - 2 * |t| / (|t| + 2) := by
                  linarith
                have hcalc : |t| - 2 * |t| / (|t| + 2) = |t| ^ 2 / (|t| + 2) := by
                  have hden : |t| + 2 ≠ 0 := by positivity
                  field_simp [hden]
                  ring
                rw [hcalc] at hstep
                have hle : |t| ^ 2 / (|t| + 2) ≤ |t| ^ 2 / 2 := by
                  exact div_le_div_of_nonneg_left (sq_nonneg |t|) (by positivity)
                    (by nlinarith [abs_nonneg t])
                exact hstep.trans hle
              calc
                ‖t⁻¹ • (|0 + t| - Real.log (1 + |0 + t|) - (|0| - Real.log (1 + |0|)))‖
                    = |t⁻¹ * (|t| - Real.log (1 + |t|))| := by simp [smul_eq_mul]
                _ = |t⁻¹| * (|t| - Real.log (1 + |t|)) := by rw [abs_mul, abs_of_nonneg hnonneg]
                _ = (1 / |t|) * (|t| - Real.log (1 + |t|)) := by rw [abs_inv, inv_eq_one_div]
                _ = (|t| - Real.log (1 + |t|)) / |t| := by ring
                _ ≤ |t| ^ 2 / 2 / |t| := by
                  simpa [pow_two] using (div_le_div_of_nonneg_right hquad ht_abs.le)
                _ = |t| / 2 := by field_simp [ht_abs.ne']
          · have hlim0 := by
              simpa [div_eq_mul_inv, mul_comm] using
                ((continuous_abs.continuousAt : ContinuousAt abs (0 : ℝ)).const_mul ((2 : ℝ)⁻¹)).tendsto
            exact hlim0.mono_left (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds (0 : ℝ) from
              nhdsWithin_le_nhds)
        simpa [f, f'] using hzero
      · have habs : HasDerivAt (fun t : ℝ ↦ |t|) (SignType.sign x : ℝ) x := hasDerivAt_abs hx
        have hxlog : 1 + |x| ≠ 0 := by
          have h1 : (0 : ℝ) < 1 := by norm_num
          linarith [abs_nonneg x, h1]
        have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (1 + |t|))
            ((SignType.sign x : ℝ) / (1 + |x|)) x := by
          simpa using ((hasDerivAt_const x 1).add habs).log hxlog
        have hsub := habs.sub hlog
        have hsub' : HasDerivAt (fun t : ℝ ↦ |t| - Real.log (1 + |t|))
            ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) x := by
          simpa using hsub
        rcases lt_or_gt_of_ne hx with hxneg | hxpos
        · have hval : ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) = x / (1 + |x|) := by
            have hden : 1 - x ≠ 0 := by linarith
            have hval' : x * (1 - x)⁻¹ = -1 + (1 - x)⁻¹ := by
              field_simp [hden]
              ring
            calc
              ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|))
                  = -1 + (1 - x)⁻¹ := by
                    simp [hxneg, abs_of_neg hxneg, div_eq_mul_inv, sub_eq_add_neg]
              _ = x / (1 + |x|) := by
                simpa [hxneg, abs_of_neg hxneg, div_eq_mul_inv, sub_eq_add_neg] using hval'.symm
          simpa [f'] using (hval ▸ hsub')
        · have hval : ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) = x / (1 + |x|) := by
            have hden : 1 + x ≠ 0 := by linarith
            have hval' : 1 - (1 + x)⁻¹ = x * (1 + x)⁻¹ := by
              field_simp [hden]
              ring
            simpa [hxpos, abs_of_pos hxpos, div_eq_mul_inv] using hval'
          simpa [f'] using (hval ▸ hsub')
    have hcontDiff : ContDiff ℝ 1 f := by
      rw [contDiff_one_iff_deriv]
      refine ⟨?_, ?_⟩
      · intro x
        exact (hderiv x).differentiableAt
      · have hderiv_eq : deriv f = f' := by
          funext x
          exact (hderiv x).deriv
        rw [hderiv_eq]
        simpa [f', div_eq_mul_inv] using
          (continuous_id.mul
            ((continuous_const.add continuous_abs).inv₀
              (fun x ↦ by
                have h1 : (0 : ℝ) < 1 := by norm_num
                have hne : 1 + |x| ≠ 0 := by linarith [abs_nonneg x, h1]
                simpa using hne)))
    simpa [f, contDiffOn_univ] using hcontDiff
  · have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
      simpa using (convexOn_norm convex_univ : ConvexOn ℝ Set.univ norm)
    have himageAbs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
    have hshiftConcave : ConcaveOn ℝ (Set.Ici 0) (fun u : ℝ ↦ Real.log (u + 1)) := by
      have himageShift : (fun u : ℝ ↦ u + 1) '' Set.Ici 0 = Set.Ici 1 := by
        ext y
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using add_le_add_right (show 0 ≤ u from hu) 1
        · intro hy
          refine ⟨y - 1, ?_, by ring⟩
          simpa using sub_nonneg.mpr (show 1 ≤ y from hy)
      have hlogConcave : ConcaveOn ℝ ((fun u : ℝ ↦ u + 1) '' Set.Ici 0) Real.log := by
        simpa [himageShift] using
          (strictConcaveOn_log_Ioi.concaveOn).subset
            (by
              intro y hy
              exact lt_of_lt_of_le zero_lt_one (show 1 ≤ y from hy))
            (convex_Ici 1)
      have hshift : ConcaveOn ℝ (Set.Ici 0) (fun u : ℝ ↦ u + 1) := by
        simpa using (concaveOn_id (convex_Ici (0 : ℝ))).add_const 1
      have hmono : MonotoneOn Real.log ((fun u : ℝ ↦ u + 1) '' Set.Ici 0) := by
        intro a ha b hb hab
        apply Real.strictMonoOn_log.monotoneOn
        · have ha1 : 1 ≤ a := by simpa [himageShift] using ha
          have h1 : (0 : ℝ) < 1 := by norm_num
          simpa using lt_of_lt_of_le h1 ha1
        · have hb1 : 1 ≤ b := by simpa [himageShift] using hb
          have h1 : (0 : ℝ) < 1 := by norm_num
          simpa using lt_of_lt_of_le h1 hb1
        · exact hab
      simpa [Function.comp] using hlogConcave.comp hshift hmono
    have hcore : ConvexOn ℝ (Set.Ici 0) (fun u : ℝ ↦ u - Real.log (u + 1)) := by
      simpa using (convexOn_id (convex_Ici (0 : ℝ))).sub hshiftConcave
    have hcoreContinuous : ContinuousOn (fun u : ℝ ↦ u - Real.log (u + 1)) (Set.Ici 0) := by
      refine continuousOn_id.sub ?_
      refine (continuousOn_id.add continuousOn_const).log ?_
      intro u hu
      have hu0 : 0 ≤ u := hu
      have h1 : (0 : ℝ) < 1 := by norm_num
      have hne : u + 1 ≠ 0 := by linarith
      simpa using hne
    have hmonoCore : MonotoneOn (fun u : ℝ ↦ u - Real.log (u + 1)) (Set.Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hcoreContinuous
      · intro u hu
        have hu0 : 0 < u := by simpa using hu
        have hderiv :
            HasDerivAt (fun t : ℝ ↦ t - Real.log (t + 1)) (u / (u + 1)) u := by
          have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (t + 1)) ((1 : ℝ) / (u + 1)) u := by
            have h1 : (0 : ℝ) < 1 := by norm_num
            have hne : u + 1 ≠ 0 := by linarith
            simpa using ((hasDerivAt_id u).add_const 1).log hne
          convert (hasDerivAt_id u).sub hlog using 1
          · have hden : u + 1 ≠ 0 := by linarith
            have hval : u / (u + 1) = 1 - (u + 1)⁻¹ := by
              field_simp [hden]
              ring
            simpa using hval
        exact hderiv.hasDerivWithinAt
      · intro u hu
        have hu0 : 0 < u := by simpa using hu
        positivity
    have hcoreOnAbsImage : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ)
        (fun u : ℝ ↦ u - Real.log (u + 1)) := by
      simpa [himageAbs] using hcore
    have hmonoCoreOnAbsImage :
        MonotoneOn (fun u : ℝ ↦ u - Real.log (u + 1)) ((fun x : ℝ ↦ |x|) '' Set.univ) := by
      simpa [himageAbs] using hmonoCore
    simpa [f, Function.comp, add_comm] using hcoreOnAbsImage.comp habs hmonoCoreOnAbsImage

end

/-! ### Example_2_1_1_4 (from Chap02) -/
noncomputable section

open scoped BigOperators

variable {n : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Example 2.1.1.4 is a source-facing recall in finite-dimensional convex analysis of log-sum-exp.

Sampled owner-style declarations in this domain:
* project `convexOn_log_sum_exp_of_convexOn`, the owner theorem for finite-family log-sum-exp on a
  common convex domain
* mathlib `EuclideanSpace.projₗ`, the canonical coordinate linear functional on Euclidean space
* mathlib `LinearMap.convexOn`, which derives convexity of linear maps on convex domains

Best owner abstraction:
* core/canonical: `convexOn_log_sum_exp_of_convexOn`
* source-facing bridge used here: the `Set.univ` specialization of
  `convexOn_log_sum_exp_of_convexOn`

Primitive data:
* the ambient Euclidean space `E`
* the coordinate functionals `EuclideanSpace.projₗ i`
* the positive arity `n : ℕ+`

Derived API:
* convexity of each coordinate map from `LinearMap.convexOn`
* the source-facing specialization `x ↦ log (∑ i = 1, …, n, exp (x⁽ⁱ⁾))`

Source/core/bridge triage:
* source-facing: Example 2.1.1.4 as the convexity statement for
  `x ↦ log (∑ i = 1, …, n, exp (x⁽ⁱ⁾))`
* core/canonical: `convexOn_log_sum_exp_of_convexOn`
* bridge/view: specialization of `convexOn_log_sum_exp_of_convexOn` to `Set.univ`, then to the
  canonical coordinate projections

The previous whole-space bridge theorem added no owner-level API beyond the `Set.univ`
specialization of `convexOn_log_sum_exp_of_convexOn`. This file therefore uses the owner theorem
directly and checks the coordinate-projection specialization instead of depending on a parallel
bridge name.
-/

#check
  (show ConvexOn ℝ Set.univ
      (fun x : E ↦ Real.log (∑ i : Fin n, Real.exp (x i))) from
    convexOn_log_sum_exp_of_convexOn Set.univ Finset.univ_nonempty
      (fun i _ ↦ (EuclideanSpace.projₗ i).convexOn convex_univ))

end

/-! ### Lemma_2_1 (from Chap02) -/
/- Lemma 2.1 lies in the first-order convex-analysis function-class domain for the source-facing
class `𝓕¹(Q)`.

Sampled owner-style declarations:
- mathlib `ContDiffOn.const_smul`
- mathlib `ConvexOn.smul`
- mathlib `ConvexOn.add`
- Chapter 2 `ConvexC1On` in `Definition_2_4`

Best owner abstraction:
- `ConvexC1On`, the chapter owner for the source class `𝓕¹(Q)`.

Primitive data:
- the feasible set `Q`
- the objective functions `f₁`, `f₂`
- the owner hypotheses `ConvexC1On Q f₁` and `ConvexC1On Q f₂`

Derived API:
- owner closure under nonnegative scalar multiplication and addition
- the weighted-sum closure theorem `ConvexC1On.nonneg_combo`

Source/core/bridge triage:
- source-facing: the textbook closure of `𝓕¹(Q)` under nonnegative linear combinations
- core/canonical: `ConvexC1On.nonneg_combo`
- bridge/view: the notation `𝓕¹(Q)` as the set-level source presentation of the owner predicate

This numbered item is therefore a direct owner recall rather than a second declaration site.
-/

recall ConvexC1On.nonneg_combo

/-! ### Proposition_2_1 (from Chap02) -/
/- Proposition 2.1 lies in the dual-norm domain for separated seminorms on finite-dimensional real
inner-product spaces.

Sampled owner-style declarations:
* mathlib `Seminorm.closedBall_zero_eq`
* `Seminorm.IsNorm` in `Definition_2_5`
* `Seminorm.dualNorm` in `Definition_2_5`
* `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`

Best owner abstraction:
* `Seminorm.dualNorm p`

Primitive data:
* a seminorm `p : Seminorm ℝ E`
* a finite-dimensional real inner-product-space structure on `E`
* the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* the support-function formula `Seminorm.dualNorm_apply`
* the pairing estimate `Seminorm.inner_le_dualNorm_mul`

Source/core/bridge triage:
* source-facing: Proposition 2.1, the textbook pairing estimate for a norm and its dual norm
* core/canonical: `Seminorm.inner_le_dualNorm_mul` as a direct companion theorem of
  `Seminorm.dualNorm`
* bridge/view: `Seminorm.dualNorm_apply`

The pairing estimate is derived API of the dual-norm owner, so the theorem now lives in
`Definition_2_5` next to `Seminorm.dualNorm`. This numbered item is therefore a direct recall,
not a second owner file. -/

/- Proposition 2.1 is the direct owner recall of the dual-pairing estimate attached to
`Seminorm.dualNorm`. -/
#check Seminorm.inner_le_dualNorm_mul

/-! ### Text_2_1 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: stagewise lower bounds for the simple-set estimating-sequence owner objects from
Proposition 2.22.

Owner declarations sampled for this refinement:
* `simpleSetEstimatingValue_succ` and `simpleSetEstimatingCenter_succ` in `Proposition_2_22`,
  which own the recursive stage update and center sequence;
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`, which own the projected point
  `x_Q(y_k; L)` and reduced gradient `g_Q(y_k; L)`;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`, which owns the lower bound
  `(2.2.57)` inserted in the second displayed inequality.

Best owner abstraction:
* source-facing owner stage of `simpleSetEstimatingValue` and `simpleSetEstimatingCenter`, with
  projected-gradient data used only as derived stage views; the stronger μ-retaining inequalities
  below are bridge companions, not the main public statements.

Source/core/bridge triage:
* source-facing: the two μ-free displayed bounds from Text 2.1, stated directly for
  `simpleSetEstimatingValue ... (k + 1)`;
* core/canonical: `simpleSetEstimatingValue`, `simpleSetEstimatingCenter`, `gradientMapping`, and
  `reducedGradient`;
* bridge/view: the stronger companions retaining the nonnegative strong-convexity terms dropped in
  the source display.

Primitive data:
* the feasible set `Q`, the objective `f`, the initial point `x0`, the stage index `k`, the
  simple-set recursion inputs `(μ, L, gamma0, y, α)`, and the comparison point `x_k`.

Derived API:
* the stage data `γ_k`, `γ_{k+1}`, `φ_k^*`, `φ_{k+1}^*`, and `v_k` from Proposition 2.22;
* the projected-gradient point `x_Q(y_k; L)` and reduced gradient `g_Q(y_k; L)`;
* the μ-free and μ-retaining right-hand sides factored below as internal notation only.

This file therefore keeps Text 2.1 at the source-facing owner stage and removes the parallel
free-floating scalar API from the earlier version. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)
    {k : ℕ} {xk : E}

local notation "gammaK" => estimatingSequenceCurvature μ gamma0 α k
local notation "gammaKp1" => estimatingSequenceCurvature μ gamma0 α (k + 1)

local notation "phi" =>
  simpleSetEstimatingValue Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α

local notation "v" =>
  simpleSetEstimatingCenter Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k

local notation "yK" => y k

local notation "xQ" =>
  x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](yK)

local notation "gQ" =>
  g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](yK)

local notation "gQNormSq" => ‖gQ‖ ^ (2 : ℕ)

local notation "curvatureCoeff" =>
  α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaKp1)

local notation "transportCoeff" =>
  α k * (1 - α k) * gammaK / gammaKp1

local notation "transportStrongConvexityTerm" =>
  transportCoeff * (μ / 2) * ‖yK - v‖ ^ (2 : ℕ)

local notation "objectiveStrongConvexityTerm" =>
  (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f xQ +
    curvatureCoeff * gQNormSq +
    transportCoeff * inner ℝ gQ (v - yK)

local notation "intermediateStrongRhs" =>
  intermediateRhs + transportStrongConvexityTerm

local notation "objectiveLowerRhs" =>
  f xQ +
    inner ℝ gQ (xk - yK) +
    (1 / (2 * L)) * gQNormSq

local notation "objectiveLowerStrongRhs" =>
  objectiveLowerRhs + objectiveStrongConvexityTerm

local notation "combinedShift" =>
  ((α k * gammaK) / gammaKp1) • (v - yK) + (xk - yK)

local notation "finalRhs" =>
  f xQ +
    (1 / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * gQNormSq +
    (1 - α k) * inner ℝ gQ combinedShift

local notation "finalStrongRhs" =>
  finalRhs +
    (1 - α k) * objectiveStrongConvexityTerm +
    transportStrongConvexityTerm

/-- The first displayed lower bound in Text 2.1, stated directly for the owner stage
`simpleSetEstimatingValue ... (k + 1)`: after replacing `φ_k^*` by `f(x_k)` in the Proposition
2.22 recursion and discarding the nonnegative transport strong-convexity term, one gets the
μ-free lower bound `intermediateRhs`. -/
-- Proof sketch: rewrite `phi (k + 1)` with `simpleSetEstimatingValue_succ`, use `α k ≤ 1` to
-- replace `(1 - α k) * phi k` by `(1 - α k) * f xk`, and use the sign assumptions to drop
-- `transportStrongConvexityTerm`.
theorem simple_set_phi_star_lower_bound_intermediate
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phi k) :
    phi (k + 1) ≥ intermediateRhs := by
  -- Scale the lower bound `f xk ≤ φ_k^*` by the nonnegative factor `1 - α k`.
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  have hscaled : (1 - α k) * f xk ≤ (1 - α k) * phi k := by
    exact mul_le_mul_of_nonneg_left hphi_k hcoeff_nonneg
  -- Rewrite the successor value and isolate the transport strong-convexity term.
  have hsucc :
      phi (k + 1) =
        (1 - α k) * phi k +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportStrongConvexityTerm +
          transportCoeff * inner ℝ gQ (v - yK) := by
    calc
      phi (k + 1) =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportCoeff *
              ((μ / 2) * ‖yK - v‖ ^ (2 : ℕ) + inner ℝ gQ (v - yK)) := by
              simpa using
                simpleSetEstimatingValue_succ
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      _ =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportStrongConvexityTerm +
            transportCoeff * inner ℝ gQ (v - yK) := by
              ring
  -- Then show the dropped transport strong-convexity contribution is nonnegative.
  have hμ_half : 0 ≤ μ / 2 := by
    nlinarith
  have hsq : 0 ≤ ‖yK - v‖ ^ (2 : ℕ) := by
    positivity
  have htransport_strong_nonneg : 0 ≤ transportStrongConvexityTerm := by
    exact mul_nonneg (mul_nonneg htransportCoeff hμ_half) hsq
  nlinarith

/-- The stronger bridge form of `simple_set_phi_star_lower_bound_intermediate` that keeps the
transport strong-convexity term coming from the owner Proposition 2.22 recursion. -/
-- Proof sketch: rewrite `phi (k + 1)` with `simpleSetEstimatingValue_succ` and use `α k ≤ 1` to
-- replace `(1 - α k) * phi k` by `(1 - α k) * f xk`, keeping the remaining terms unchanged.
theorem simple_set_phi_star_lower_bound_intermediate_with_strong_convexity
    (halpha_k : α k ≤ 1)
    (hphi_k : f xk ≤ phi k) :
    phi (k + 1) ≥ intermediateStrongRhs := by
  -- Scale the lower bound `f xk ≤ φ_k^*` by the nonnegative factor `1 - α k`.
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  have hscaled : (1 - α k) * f xk ≤ (1 - α k) * phi k := by
    exact mul_le_mul_of_nonneg_left hphi_k hcoeff_nonneg
  -- Rewrite the successor value so the only comparison point is the first term.
  have hsucc :
      phi (k + 1) =
        (1 - α k) * phi k +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportStrongConvexityTerm +
          transportCoeff * inner ℝ gQ (v - yK) := by
    calc
      phi (k + 1) =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportCoeff *
              ((μ / 2) * ‖yK - v‖ ^ (2 : ℕ) + inner ℝ gQ (v - yK)) := by
              simpa using
                simpleSetEstimatingValue_succ
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      _ =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportStrongConvexityTerm +
            transportCoeff * inner ℝ gQ (v - yK) := by
              ring
  -- Insert the scaled comparison into the recursion and keep the common terms unchanged.
  nlinarith

/-- Text 2.1: if `α_k ≤ 1`, the transport coefficient is nonnegative, `μ ≥ 0`,
`φ_k^* ≥ f(x_k)`, and the μ-free lower bound `(2.2.57)` holds at stage `k`, then the owner
Proposition 2.22 update yields the displayed μ-free lower bound `finalRhs` for
`simpleSetEstimatingValue ... (k + 1)`. -/
-- Proof sketch: apply `simple_set_phi_star_lower_bound_intermediate`, substitute the μ-free
-- lower bound `objectiveLowerRhs` for `f xk`, and collect the norm and inner-product terms.
theorem simple_set_phi_star_lower_bound_of_objective_lower_bound
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phi k)
    (hobjective_lower : f xk ≥ objectiveLowerRhs) :
    phi (k + 1) ≥ finalRhs := by
  -- Start from the source-faithful intermediate lower bound from Proposition 2.22.
  have hintermediate :=
    simple_set_phi_star_lower_bound_intermediate
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
      halpha_k htransportCoeff hμ hphi_k
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  -- Scale the objective lower bound `(2.2.57)` by `1 - α k`.
  have hscaled : (1 - α k) * objectiveLowerRhs ≤ (1 - α k) * f xk := by
    exact mul_le_mul_of_nonneg_left hobjective_lower hcoeff_nonneg
  -- Regroup the final displayed expression so the scaled objective bound can be inserted directly.
  have hfinal_repr :
      finalRhs =
        (1 - α k) * objectiveLowerRhs +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportCoeff * inner ℝ gQ (v - yK) := by
    rw [show inner ℝ gQ combinedShift =
        inner ℝ gQ (((α k * gammaK) / gammaKp1) • (v - yK)) +
          inner ℝ gQ (xk - yK) by
          rw [inner_add_right]]
    rw [inner_smul_right]
    ring
  nlinarith

/-- The stronger bridge form of Text 2.1 obtained by retaining the objective and transport
strong-convexity contributions instead of discarding them from the displayed μ-free formula. -/
-- Proof sketch: apply `simple_set_phi_star_lower_bound_intermediate_with_strong_convexity`,
-- substitute the stronger lower bound `objectiveLowerStrongRhs` for `f xk`, and collect the norm,
-- inner-product, and strong-convexity terms.
theorem simple_set_phi_star_lower_bound_of_objective_lower_bound_with_strong_convexity
    (halpha_k : α k ≤ 1)
    (hphi_k : f xk ≤ phi k)
    (hobjective_lower : f xk ≥ objectiveLowerStrongRhs) :
    phi (k + 1) ≥ finalStrongRhs := by
  -- Start from the version that retains both strong-convexity contributions.
  have hintermediate :=
    simple_set_phi_star_lower_bound_intermediate_with_strong_convexity
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
      halpha_k hphi_k
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  -- Scale the stronger objective lower bound before inserting it into the intermediate estimate.
  have hscaled : (1 - α k) * objectiveLowerStrongRhs ≤ (1 - α k) * f xk := by
    exact mul_le_mul_of_nonneg_left hobjective_lower hcoeff_nonneg
  -- Rewrite the final strong right-hand side in the same grouped form as the intermediate bound.
  have hfinal_repr :
      finalStrongRhs =
        (1 - α k) * objectiveLowerStrongRhs +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportCoeff * inner ℝ gQ (v - yK) +
          transportStrongConvexityTerm := by
    rw [show inner ℝ gQ combinedShift =
        inner ℝ gQ (((α k * gammaK) / gammaKp1) • (v - yK)) +
          inner ℝ gQ (xk - yK) by
          rw [inner_add_right]]
    rw [inner_smul_right]
    ring
  nlinarith

end

/-! ### Theorem_2_1 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: first-order convex minimization of differentiable objectives on real inner
product spaces.

Sampled owner-style declarations:
* `IsMinOn f Set.univ xStar` in `Definition_2_1`, the Chapter 2 minimizer owner
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the source-faithful first-order support
  inequality for convex functions
* `DifferentiableAt.differentiableWithinAt`, the bridge from ambient differentiability to the
  whole-space within-set derivative needed by `lower_tangent_plane`

Best owner abstraction:
* `ConvexOn ℝ Set.univ f` together with `IsMinOn f Set.univ xStar`

Primitive data:
* the objective `f : E → ℝ`
* the candidate minimizer `xStar : E`
* whole-space convexity of `f`
* pointwise differentiability of `f` at `xStar`
* the stationary-gradient identity `∇ f xStar = 0`

Derived API:
* the textbook pointwise lower bound `∀ x, f xStar ≤ f x`
* the minimizing conclusion `IsMinOn f Set.univ xStar`

Source/core/bridge triage:
* source-facing: Theorem 2.1 for convex objectives with a stationary differentiable point
* core/canonical: `ConvexOn.lower_tangent_plane`
* bridge/view: `isMinOn_univ_iff`, converting the pointwise inequality into `IsMinOn`
-/

/-- Helper for Theorem 2.1: the tangent-plane inequality at a stationary point gives the textbook
pointwise lower bound on the whole space. -/
-- Proof sketch: apply `ConvexOn.lower_tangent_plane` at the base point `xStar`, simplify the
-- whole-space gradient term to the ambient gradient, and then use `∇ f xStar = 0`.
lemma convex_stationary_point_pointwise_lower_bound
    {f : E → ℝ} {xStar : E} (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    ∀ x : E, f xStar ≤ f x := by
  intro x
  -- Compare `f x` against the tangent plane supported at the stationary base point `xStar`.
  have hsupport :
      f x ≥ f xStar + inner ℝ (∇ f xStar) (x - xStar) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane
        xStar (by simp) hf_diff.differentiableWithinAt x (by simp)
  -- The stationary gradient annihilates the linear correction term.
  simpa [hgrad] using hsupport

/-- Theorem 2.1: a critical point of a convex differentiable function is a global minimizer. -/
-- Proof sketch: rewrite whole-space optimality as the textbook pointwise inequality, then use the
-- supporting-hyperplane inequality at `xStar` and the stationary-gradient identity.
theorem stationaryPoint_isMinOn_of_convexOn
    {f : E → ℝ} {xStar : E} (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    IsMinOn f Set.univ xStar := by
  -- Rewrite whole-space optimality into the textbook inequality `f xStar ≤ f x` for all `x`.
  rw [isMinOn_univ_iff]
  -- The helper is exactly the lower-tangent-plane argument from the source proof.
  exact convex_stationary_point_pointwise_lower_bound hf_conv hf_diff hgrad

end
