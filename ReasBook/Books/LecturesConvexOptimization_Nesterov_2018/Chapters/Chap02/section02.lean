import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_2 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 2.2 lies in first-order convex analysis for `C¹` functions on real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `ConvexOn`
* mathlib `gradientWithin` / `HasGradientWithinAt`
* Chapter 2 `Definition_2_6` for the within-set derivative owner API
* Chapter 4 `Definition_4_2_8`, which keeps a source-facing first-order lower-support statement
  while using a canonical convexity owner underneath

Source/core/bridge triage:
* source-facing: the lower-tangent characterization of convexity for a `C¹` function on `Q`
* core/canonical: `ConvexOn ℝ Q f`
* bridge/view: the pointwise tangent-plane inequality at a feasible base point, first with an
  explicit gradient witness and then with the canonical `gradientWithin`

Primitive data:
* the feasible set `Q`
* the objective `f`
* for the source-facing theorem, `ContDiffOn ℝ 1 f Q`
* for the canonical bridge, `ConvexOn ℝ Q f`
* for pointwise tangent data, an explicit witness `HasGradientWithinAt f g Q x`

Derived API:
* `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt`
* `ConvexOn.lower_tangent_plane`
* `convexOn_iff_lower_tangent_plane`, the sharper owner bridge using `DifferentiableOn ℝ f Q`
* `convexOn_iff_lower_tangent_plane_of_contDiffOn`, the source-facing `C¹` formulation

This file therefore keeps the lower-tangent characterization as the main numbered outcome and uses
`ConvexOn` only as the canonical owner behind it. The explicit `HasGradientWithinAt` statement is
the primitive pointwise bridge; the `gradientWithin` and `ContDiffOn` forms are derived from that
owner-level bridge rather than packaged as parallel owners. -/

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ}

/-- A convex function lies above every feasible tangent plane arising from an explicit within-set
gradient witness at the base point. -/
-- Proof sketch: this is the standard first-order characterization of convexity for
-- differentiable functions on convex sets, stated at the primitive owner level
-- `HasGradientWithinAt`.
theorem lower_tangent_plane_of_hasGradientWithinAt
    (hf_conv : ConvexOn ℝ Q f)
    (x : E) (hx : x ∈ Q) (g : E) (hgrad : HasGradientWithinAt f g Q x) (y : E) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ g (y - x) := by
  -- Restrict `f` to the segment from `x` to `y` so that the multivariate statement becomes
  -- a one-dimensional convex-derivative inequality on `Icc 0 1`.
  let seg : ℝ → E := AffineMap.lineMap x y
  have hmaps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := hf_conv.1.mapsTo_lineMap hx hy
  have hseg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ seg) := by
    refine (hf_conv.comp_affineMap (AffineMap.lineMap x y)).subset ?_ (convex_Icc (0 : ℝ) 1)
    intro t ht
    exact hmaps ht
  -- Compose the gradient witness at `x = seg 0` with the segment parameterization.
  have hderiv :
      HasDerivWithinAt (f ∘ seg) (inner ℝ g (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [seg] using
      hgrad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hmaps (AffineMap.lineMap_apply_zero x y).symm
  -- The derivative at the left endpoint is bounded by the secant slope, which is exactly the
  -- desired first-order lower support inequality after simplifying the slope on `[0,1]`.
  have hslope := hseg_conv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hderiv
  have hslope' : inner ℝ g (y - x) ≤ f y - f x := by
    simpa [seg, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  linarith

/-- A convex function lies above the tangent plane determined by the canonical within-set gradient
at a feasible base point. -/
-- Proof sketch: specialize `lower_tangent_plane_of_hasGradientWithinAt` to the canonical witness
-- `gradientWithin f Q x`, using `DifferentiableWithinAt.hasGradientWithinAt`.
theorem lower_tangent_plane
    (hf_conv : ConvexOn ℝ Q f)
    (x : E) (hx : x ∈ Q) (hf_diff : DifferentiableWithinAt ℝ f Q x) (y : E) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  -- Use the canonical within-set gradient as the explicit witness in the primitive theorem.
  exact lower_tangent_plane_of_hasGradientWithinAt hf_conv x hx (gradientWithin f Q x)
    hf_diff.hasGradientWithinAt y hy

end ConvexOn

/-- On a convex set, pointwise within-set differentiability makes the canonical owner predicate
`ConvexOn ℝ Q f` equivalent to the lower-tangent-plane inequality. -/
-- Proof sketch: the forward direction is `ConvexOn.lower_tangent_plane`; the reverse direction is
-- the converse first-order criterion for convexity on convex sets.
theorem convexOn_iff_lower_tangent_plane
    {Q : Set E} {f : E → ℝ}
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q) :
    ConvexOn ℝ Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
        f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  constructor
  · intro hf_conv x hx y hy
    -- The forward implication is the canonical tangent-plane bound for convex functions.
    exact ConvexOn.lower_tangent_plane hf_conv x hx (hf_diff x hx) y hy
  · intro hlower
    -- For the converse, prove Jensen's inequality at the convex combination point `z`.
    refine ⟨hQ, ?_⟩
    intro x hx y hy a b ha hb hab
    let z : E := a • x + b • y
    have hz : z ∈ Q := hQ hx hy ha hb hab
    -- Apply the assumed lower-support inequality at the common base point `z`.
    have hx_plane : f x ≥ f z + inner ℝ (gradientWithin f Q z) (x - z) := hlower hz hx
    have hy_plane : f y ≥ f z + inner ℝ (gradientWithin f Q z) (y - z) := hlower hz hy
    -- The weighted displacements from `z` back to `x` and `y` cancel because `z = a • x + b • y`.
    have hdisp : a • (x - z) + b • (y - z) = 0 := by
      calc
        a • (x - z) + b • (y - z) = z - (a + b) • z := by
          simp [z, sub_eq_add_neg, smul_add, add_smul, add_comm, add_left_comm, add_assoc]
        _ = z - z := by simp [hab]
        _ = 0 := by simp
    have hcancel :
        a * inner ℝ (gradientWithin f Q z) (x - z) +
          b * inner ℝ (gradientWithin f Q z) (y - z) = 0 := by
      calc
        a * inner ℝ (gradientWithin f Q z) (x - z) +
            b * inner ℝ (gradientWithin f Q z) (y - z) =
            inner ℝ (gradientWithin f Q z) (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = 0 := by simp [hdisp]
    have hx_bound :
        a * f z + a * inner ℝ (gradientWithin f Q z) (x - z) ≤ a * f x := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
        mul_le_mul_of_nonneg_left hx_plane ha
    have hy_bound :
        b * f z + b * inner ℝ (gradientWithin f Q z) (y - z) ≤ b * f y := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
        mul_le_mul_of_nonneg_left hy_plane hb
    have hz_bound : f z ≤ a * f x + b * f y := by
      calc
        f z = (a + b) * f z := by rw [hab, one_mul]
        _ = a * f z + b * f z := by ring
        _ = (a * f z + b * f z) +
              (a * inner ℝ (gradientWithin f Q z) (x - z) +
                b * inner ℝ (gradientWithin f Q z) (y - z)) := by rw [hcancel, add_zero]
        _ = (a * f z + a * inner ℝ (gradientWithin f Q z) (x - z)) +
              (b * f z + b * inner ℝ (gradientWithin f Q z) (y - z)) := by ring
        _ ≤ a * f x + b * f y := add_le_add hx_bound hy_bound
    simpa [z] using hz_bound

/-- Definition 2.2: on a convex set `Q`, a `C¹` function is convex exactly when it lies above
each tangent plane determined by its within-set gradient. -/
-- Proof sketch: specialize the sharper owner bridge
-- `convexOn_iff_lower_tangent_plane` using the differentiability supplied by the `C¹` hypothesis.
theorem convexOn_iff_lower_tangent_plane_of_contDiffOn
    {Q : Set E} {f : E → ℝ}
    (hQ : Convex ℝ Q)
    (hf_C1 : ContDiffOn ℝ 1 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
        f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  exact convexOn_iff_lower_tangent_plane hQ (hf_C1.differentiableOn (by simp))

end

/-! ### Lemma_2_2 (from Chap02) -/
/- Lemma 2.2 lies in Euclidean first-order convex analysis under affine pullback.

Sampled owner-style declarations:
- mathlib `ContDiffOn.comp`
- mathlib `ConvexOn.comp_affineMap`
- Chapter 2 `ConvexC1On.comp_continuousAffineMap`
- Chapter 2 `ConvexC1On.comp_affineMap`

Best owner abstraction:
- `ConvexC1On.comp_continuousAffineMap`, the canonical owner-level precomposition theorem for the
  `ConvexC1On` owner predicate.

Primitive data:
- the source set `Q`
- the objective `f`
- the owner hypothesis `hf : ConvexC1On Q f`
- the affine map `g`

Derived API:
- the Euclidean specialization `ConvexC1On.comp_affineMap`, obtained from finite-dimensional
  continuity of affine maps.

Source/core/bridge triage:
- source-facing: Lemma 2.2's Euclidean affine pullback statement
- core/canonical: `ConvexC1On.comp_continuousAffineMap`
- bridge/view: the finite-dimensional specialization `ConvexC1On.comp_affineMap`

This item no longer keeps a parallel local theorem shell. The source-facing Euclidean statement now
lives with the `ConvexC1On` owner in `Definition_2_4`, and this file is a direct recall of that
canonical bridge.
-/

recall ConvexC1On.comp_affineMap

/-! ### Proposition_2_2 (from Chap02) -/
open scoped BigOperators Gradient SmoothConvex

noncomputable section

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "p" => normSeminorm ℝ E

/- Primary domain: Euclidean `C²` smooth-convex objectives controlled by Hessian quadratic-form
bounds.

Owner-style declarations sampled before refining this file:
* `ConvexC1SeminormSmooth` in `Theorem_2_5`
* `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` in `Theorem_2_6`
* `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`
* `smoothLowerBoundFunction_hessian_eq_tridiagonal` in `Definition_2_11`

Best owner abstraction:
`f ∈ 𝓕[L, p]¹¹` for the canonical smoothness constant `L : NNReal`.

Primitive data:
- the textbook chain quadratic form `nesterovChainQuadraticForm k`;
- the explicit Hessian quadratic-form identity for `f`.

Derived API:
- membership in the chapter owner class `𝓕[L, p]¹¹`;
- the textbook convexity and Euclidean gradient-Lipschitz consequences.

Accordingly, this file keeps the explicit chain formula but routes its consequences through the
chapter's source-facing owner notation instead of a parallel wrapper predicate and intermediate
Hessian-bounds API.
-/

/-- Restrict a vector in `ℝⁿ` to its first `k.1 + 1` coordinates. This keeps the chain
quadratic form source-facing while avoiding repeated index-transport bookkeeping. -/
private def nesterovChainPrefix (k : Fin n) (h : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ h (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Helper for Proposition 2.2: the prefix restriction reads off the corresponding coordinate of
the original vector. -/
private theorem nesterovChainPrefix_apply (k : Fin n) (h : E) (i : Fin (k.1 + 1)) :
    nesterovChainPrefix k h i = h (Fin.castLE (Nat.succ_le_of_lt k.2) i) := by
  -- The restricted vector was defined by transporting exactly these first coordinates.
  simp [nesterovChainPrefix]

/-- The chain quadratic form appearing in the Hessian identity for LecturesConvexOptimization_Nesterov_2018's function `f_k`. -/
def nesterovChainQuadraticForm (k : Fin n) (h : E) : ℝ :=
  let h' := nesterovChainPrefix k h
  h' 0 ^ 2 +
    (∑ i : Fin k.1,
      (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2) +
    h' (Fin.last k.1) ^ 2

/-- The chain quadratic form is nonnegative because it is a sum of squares. -/
-- Proof sketch: expand `nesterovChainQuadraticForm`; each summand is a square, hence nonnegative,
-- and finite sums of nonnegative terms remain nonnegative.
theorem nesterovChainQuadraticForm_nonneg (k : Fin n) (h : E) :
    0 ≤ nesterovChainQuadraticForm k h := by
  -- Expand the quadratic form so positivity can read off the square terms directly.
  simp only [nesterovChainQuadraticForm]
  positivity

/-- The chain quadratic form is bounded by four times the Euclidean squared norm. -/
-- Proof sketch: bound each difference square by `2 a^2 + 2 b^2`, sum over the chain
-- `0, …, k`, and compare the resulting coordinate sum with `‖h‖^2`.
theorem nesterovChainQuadraticForm_le_four_mul_norm_sq (k : Fin n) (h : E) :
    nesterovChainQuadraticForm k h ≤ 4 * ‖h‖ ^ 2 := by
  let h' := nesterovChainPrefix k h
  -- Each chain edge satisfies the textbook estimate `(a - b)^2 ≤ 2 a^2 + 2 b^2`.
  have hedge :
      ∀ i : Fin k.1,
        (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2
          ≤ 2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (h' (Fin.castLE (Nat.le_succ k.1) i) + h' i.succ)]
  have hsum_edges :
      (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2)
        ≤ ∑ i : Fin k.1,
            (2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hedge i
  have hsum_expand :
      (∑ i : Fin k.1,
          (2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2)) =
        2 * (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) +
          2 * (∑ i : Fin k.1, (h' i.succ) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- The endpoint and shifted-prefix sums are each controlled by the full prefix square sum.
  have hfirst_le :
      (h' 0) ^ 2 ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    have htail_nonneg : 0 ≤ ∑ i : Fin k.1, (h' i.succ) ^ 2 := by positivity
    exact le_add_of_nonneg_right htail_nonneg
  have hlast_le :
      (h' (Fin.last k.1)) ^ 2 ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    have hcast_nonneg :
        0 ≤ ∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 := by
      positivity
    exact le_add_of_nonneg_left hcast_nonneg
  have hcast_le :
      (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2)
        ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg (h' (Fin.last k.1)))
  have hsucc_le :
      (∑ i : Fin k.1, (h' i.succ) ^ 2)
        ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg (h' 0))
  -- The prefix square sum is a partial coordinate sum of `‖h‖^2`.
  have hprefix_le :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) ≤ ‖h‖ ^ 2 := by
    let g : ℕ → ℝ := fun i ↦ if hi : i < n then h ⟨i, hi⟩ ^ 2 else 0
    have hprefix_eq :
        (∑ i : Fin (k.1 + 1), (h' i) ^ 2) = ∑ i ∈ Finset.range (k.1 + 1), g i := by
      calc
        (∑ i : Fin (k.1 + 1), (h' i) ^ 2) = ∑ i : Fin (k.1 + 1), g i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (Nat.succ_le_of_lt k.2)
            have hindex : Fin.castLE (Nat.succ_le_of_lt k.2) i = ⟨(i : ℕ), hi_lt_n⟩ := by
              apply Fin.ext
              rfl
            rw [show g i = h ⟨(i : ℕ), hi_lt_n⟩ ^ 2 by simp [g, hi_lt_n]]
            rw [nesterovChainPrefix_apply]
            rw [hindex]
        _ = ∑ i ∈ Finset.range (k.1 + 1), g i := Fin.sum_univ_eq_sum_range g (k.1 + 1)
    have hnorm_eq :
        ‖h‖ ^ 2 = ∑ i ∈ Finset.range n, g i := by
      calc
        ‖h‖ ^ 2 = ∑ i : Fin n, (h i) ^ 2 := by
            simpa using EuclideanSpace.real_norm_sq_eq h
        _ = ∑ i : Fin n, g i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [g, i.2]
        _ = ∑ i ∈ Finset.range n, g i := Fin.sum_univ_eq_sum_range g n
    rw [hprefix_eq, hnorm_eq]
    have hk1 : k.1 + 1 ≤ n := Nat.succ_le_of_lt k.2
    rw [← Finset.sum_range_add_sum_Ico g hk1]
    have htail_nonneg : 0 ≤ ∑ i ∈ Finset.Ico (k.1 + 1) n, g i := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
      simpa [g, hi_lt_n] using sq_nonneg (h ⟨i, hi_lt_n⟩)
    exact le_add_of_nonneg_right htail_nonneg
  have hcast_eq :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) =
        (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
    calc
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2)
          = (∑ i : Fin k.1, (h' i.castSucc) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
              rw [Fin.sum_univ_castSucc]
      _ = (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
            congr 1
  have hsucc_eq :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) =
        (h' 0) ^ 2 + (∑ i : Fin k.1, (h' i.succ) ^ 2) := by
    rw [Fin.sum_univ_succ]
  -- Combine the edge estimate with the prefix/full norm comparison.
  calc
    nesterovChainQuadraticForm k h
        = h' 0 ^ 2 +
            (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2) +
            h' (Fin.last k.1) ^ 2 := by
              simp [nesterovChainQuadraticForm, h']
    _ ≤ 4 * ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
      nlinarith [hsum_edges, hsum_expand, hcast_eq, hsucc_eq, hcast_le, hsucc_le]
    _ ≤ 4 * ‖h‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hprefix_le (by positivity)

section

variable (L : NNReal) (k : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- Proposition 2.2 in owner form: the explicit chain Hessian formula places `f` in the chapter's
smooth-convex owner class `𝓕[L, p]¹¹`. -/
-- Proof sketch: apply
-- `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` for the Euclidean norm seminorm.
-- The lower and upper Hessian quadratic-form bounds come directly from the chain identity together
-- with `nesterovChainQuadraticForm_nonneg` and
-- `nesterovChainQuadraticForm_le_four_mul_norm_sq`.
theorem chain_hessian_formula_mem_smooth_convex_objective
    (hf_C2 : ContDiff ℝ 2 f)
    (hH : ∀ x h : E, inner ℝ (hessian f x h) h = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h)
    : ConvexC1SeminormSmooth (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) L f := by
  -- Package the chain lower and upper bounds into the chapter's Hessian criterion.
  have hquad :
      ∀ x h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
    intro x h
    constructor
    · have hEq := hH x h
      nlinarith [L.2, hEq, nesterovChainQuadraticForm_nonneg k h]
    · have hEq := hH x h
      have hupper : inner ℝ (hessian f x h) h ≤ (L : ℝ) * ‖h‖ ^ 2 := by
        nlinarith [L.2, hEq, nesterovChainQuadraticForm_le_four_mul_norm_sq k h]
      simpa using hupper
  simpa using
    (@convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
      (EuclideanSpace ℝ (Fin n)) _ _ _ _
      (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) _ L f hf_C2).2 hquad

/-- Proposition 2.2: the explicit chain formula for the Hessian quadratic form implies that `f`
is convex and that its gradient is `L`-Lipschitz in the Euclidean norm. -/
-- Proof sketch: first pass from the chain formula to the owner predicate `f ∈ 𝓕[L, p]¹¹` via
-- `chain_hessian_formula_mem_smooth_convex_objective`. Convexity is then `hf.convexOn`, while
-- the Euclidean `L`-Lipschitz bound for `∇ f` is the owner-derived theorem
-- `hf.gradient_lipschitz`.
theorem chain_hessian_formula_convexLipschitzGradient
    (hf_C2 : ContDiff ℝ 2 f)
    (hH : ∀ x h : E, inner ℝ (hessian f x h) h = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h)
    : ConvexOn ℝ Set.univ f ∧ LipschitzWith L (∇ f) := by
  have hf : ConvexC1SeminormSmooth (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) L f :=
    chain_hessian_formula_mem_smooth_convex_objective L k f hf_C2 hH
  exact ⟨hf.convexOn, hf.gradient_lipschitz⟩

end

/-! ### Text_2_2 (from Chap02) -/
open scoped Gradient StrongConvex

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Text 2.2: restricting a whole-space `𝓛^1[γ]` owner statement to a convex feasible
set preserves strong convexity with the same modulus. -/
lemma strongConvexOnWith_restrict_univ
    {Q : Set E} {f : E → ℝ} {γ : ℝ}
    (hf : StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ f)
    (hQ_convex : Convex ℝ Q) :
    StrongConvexOnWith (normSeminorm ℝ E) γ Q f := by
  refine ⟨hQ_convex, hf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  exact hf.2.2 (by simp) (by simp) ha hb hab

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*}

/-- Helper for Text 2.2: each quadratically regularized component linearization belongs to the
whole-space class `𝓛^1[γ]`. -/
lemma regularized_component_mem_L1
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∀ i : ι,
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar ∈ 𝓛^1[γ] :=
    by
  intro i
  -- Each component is an affine model plus the centered quadratic penalty.
  change
    StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar)
  rw [strongConvexOnWith_normSeminorm_iff]
  refine ⟨hγ, ?_⟩
  have hsum :
      firstOrderTaylorModelAt (fi i) xBar +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) γ xBar =
        quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar := by
    -- This identifies the regularized affine model as the sum of its affine and quadratic parts.
    ext x
    simp [quadraticallyRegularizedObjective_apply]
  rw [← hsum]
  -- Strong convexity comes from adding the convex affine model to the strongly convex quadratic.
  exact
    (quadraticallyRegularizedObjective_zero_strongConvexOn xBar γ).add_convexOn
      (firstOrderTaylorModelAt_convexOn Set.univ convex_univ (fi i) xBar)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Helper for Text 2.2: the regularized max-type model attached to the affine max approximation
at `xBar`. -/
abbrev regularizedAffineMaxModel
    (fi : ι → E → ℝ) (γ : ℝ) :
    E → E → ℝ :=
  fun xBar ↦ quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar

/-- Helper for Text 2.2: the regularized affine max model is `γ`-strongly convex on the ambient
space. -/
lemma regularized_affine_max_strongConvexOn_univ
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    StrongConvexOn (Set.univ : Set E) γ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) := by
  have hsum :
      maxTypeAffineApproximation fi xBar +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) γ xBar =
        quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar := by
    -- This puts the max-type model into the same affine-plus-quadratic form as the source proof.
    ext x
    simp [quadraticallyRegularizedObjective_apply]
  rw [← hsum]
  -- The affine max part is convex, and the quadratic part contributes the strong convexity
  -- modulus `γ`.
  exact
    (quadraticallyRegularizedObjective_zero_strongConvexOn xBar γ).add_convexOn
      (maxTypeAffineApproximation_convexOn Set.univ convex_univ fi xBar)

/-- Helper for Text 2.2: the regularized affine max model belongs to `𝓛^1[γ]`. -/
lemma regularized_affine_max_mem_L1
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar ∈ 𝓛^1[γ] := by
  change
    StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
  rw [strongConvexOnWith_normSeminorm_iff]
  exact ⟨hγ, regularized_affine_max_strongConvexOn_univ fi xBar γ⟩

/-- Helper for Text 2.2: a first-order Taylor model at a fixed base point is continuous. -/
lemma firstOrderTaylorModelAt_continuous
    (f : E → ℝ) (xBar : E) :
    Continuous (firstOrderTaylorModelAt f xBar) := by
  -- The model is a constant plus a continuous linear functional in `x`.
  simpa [firstOrderTaylorModelAt_apply] using
    continuous_const.add
      ((innerSL ℝ (∇ f xBar)).continuous.comp (continuous_id.sub continuous_const))

/-- Helper for Text 2.2: the affine max approximation is continuous as a finite maximum of
continuous affine models. -/
lemma maxTypeAffineApproximation_continuous
    (fi : ι → E → ℝ) (xBar : E) :
    Continuous (maxTypeAffineApproximation fi xBar) := by
  classical
  -- Continuity of the finite maximum follows componentwise from the affine Taylor models.
  have hcont :
      Continuous
        (fun x ↦
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : ι ↦ firstOrderTaylorModelAt (fi i) xBar x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun i _ ↦ firstOrderTaylorModelAt_continuous (fi i) xBar)
  simpa [maxTypeAffineApproximation] using hcont

/-- Helper for Text 2.2: the regularized affine max model is continuous. -/
lemma regularized_affine_max_continuous
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    Continuous (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) :=
    by
  -- Add continuity of the affine max part to continuity of the quadratic penalty.
  simpa [quadraticallyRegularizedObjective_apply] using
    (maxTypeAffineApproximation_continuous fi xBar).add
      (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow (2 : ℕ)))

/-- Helper for Text 2.2: the constrained regularized affine max subproblem has a unique minimizer
on a nonempty closed convex feasible set. -/
lemma existsUnique_isMinOn_regularized_affine_max
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∃! xPlus : E,
      xPlus ∈ Q ∧
        IsMinOn
          (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
          Q
          xPlus := by
  have hL1_univ :
      quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar ∈ 𝓛^1[γ] :=
    regularized_affine_max_mem_L1 fi xBar γ hγ
  have hL1_Q :
      StrongConvexOnWith (normSeminorm ℝ E) γ Q
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) :=
    strongConvexOnWith_restrict_univ hL1_univ hQ_convex
  -- Route correction: the earlier single-objective whole-space route is replaced by the actual
  -- constrained max-type model, then the owner existence theorem is applied on `Q`.
  exact
    hL1_Q.existsUnique_isMinOn_of_isClosed
      (regularized_affine_max_continuous fi xBar γ).continuousOn
      hQ_nonempty
      hQ_closed

/-- Helper for Text 2.2: the owner gradient-mapping set of the regularized affine max model has a
unique element. -/
lemma gradientMappingSet_singleton_of_existsUnique_isMinOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∃! xPlus : E, xPlus ∈ gradientMappingSet Q (regularizedAffineMaxModel fi γ) xBar := by
  -- Rewrite feasible minimizers of the regularized model as membership in `gradientMappingSet`.
  simpa [regularizedAffineMaxModel, mem_gradientMappingSet_iff] using
    existsUnique_isMinOn_regularized_affine_max Q hQ_nonempty hQ_closed hQ_convex fi xBar γ hγ

/-- Text 2.2: for a nonempty closed convex set `Q` and `γ > 0`, the quadratically regularized
max of the affine component linearizations at `xBar` has components in `𝓛^1[γ]` and a unique
feasible minimizer. Equivalently, the owner set `X_f(xBar; γ)` from Definition 2.41 is a
singleton, so the associated gradient mapping is well defined. -/
theorem regularizedAffineMax_gradientMapping_wellDefined
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    (∀ i : ι,
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar ∈ 𝓛^1[γ]) ∧
      ∃! xPlus : E, xPlus ∈ gradientMappingSet Q (regularizedAffineMaxModel fi γ) xBar := by
  -- First record the componentwise `𝓛^1[γ]` property from the affine-plus-quadratic structure.
  refine ⟨regularized_component_mem_L1 fi xBar γ hγ, ?_⟩
  -- Then convert the unique constrained minimizer into the singleton owner gradient-mapping set.
  exact
    gradientMappingSet_singleton_of_existsUnique_isMinOn
      Q hQ_nonempty hQ_closed hQ_convex fi xBar γ hγ

end

/-! ### Theorem_2_2 (from Chap02) -/
section

variable {𝕜 E : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/- 
Primary domain: convex analysis on affine modules over a linearly ordered ring, centered on the
owner predicate `ConvexOn 𝕜 Q f`.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `convexOn_iff_forall_pos`
* mathlib `convexOn_iff_div`
* Chapter 2 `convexOn_iff_lower_tangent_plane` in `Definition_2_2`, the chapter's matching
  owner-to-textbook bridge for first-order convexity

Source/core/bridge triage:
* source-facing: the one-parameter Jensen inequality along segments in `Q`
* core/canonical: `ConvexOn 𝕜 Q f`
* bridge/view: rewriting the owner weights `(a, b)` as the single parameter `α ∈ Icc 0 1`

Primitive data:
* the feasible set `Q`
* the objective `f`
* convexity of `Q`, supplied separately as `hQ`
* the canonical owner predicate `ConvexOn 𝕜 Q f`

Derived API:
* the one-parameter segment inequality below, obtained by taking weights `α` and `1 - α`
* the converse reconstruction of the owner theorem from that source-facing form and `hQ`

The owner abstraction is `ConvexOn 𝕜 Q f`. The source theorem is stated for `ℝⁿ`, but this
segment-normalized bridge only uses the ordered-ring/module layer already supporting
`convexOn_iff_forall_pos`; no division or inverse-based data is needed. The textbook `C¹` side
condition is redundant for this item, so the refined public API omits it. -/

variable {Q : Set E} {f : E → 𝕜}

/-- Theorem 2.2: on a convex set `Q`, convexity of `f` is exactly the usual two-point Jensen
inequality along every segment in `Q`. Specializing `𝕜` to `ℝ` recovers the textbook setting. -/
-- Proof sketch: `ConvexOn 𝕜 Q f` packages the two-weight Jensen inequality. The displayed
-- source-facing formula is its specialization `b = 1 - α`; conversely, `convexOn_iff_forall_pos`
-- recovers the owner theorem from that normalized one-parameter form and `hQ`.
theorem convexOn_iff_segment_inequality
    (hQ : Convex 𝕜 Q) :
    ConvexOn 𝕜 Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
        f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y := by
  constructor
  · intro hf x hx y hy α hα
    have hsum : α + (1 - α) = 1 := by
      abel_nf
    simpa [smul_eq_mul] using hf.2 hx hy hα.1 (sub_nonneg.mpr hα.2) hsum
  · intro h
    rw [convexOn_iff_forall_pos]
    refine ⟨hQ, ?_⟩
    intro x hx y hy a b ha hb hab
    have ha' : a ∈ Set.Icc (0 : 𝕜) 1 := by
      refine ⟨le_of_lt ha, ?_⟩
      exact (by
        have ha_lt : a < 1 := by
          simpa [hab] using lt_add_of_pos_right a hb
        exact ha_lt.le)
    have hb_eq : b = 1 - a := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hab
    simpa [smul_eq_mul, hb_eq] using h hx hy ha'

end
