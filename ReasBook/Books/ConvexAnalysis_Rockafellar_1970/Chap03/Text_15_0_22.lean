import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.22 studies the concrete function
  `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite coordinate family `ι → X`.
- `core/canonical`: the owner abstractions are the chapter predicate
  `Function.IsClosedProperConvex` and the degree-`p` homogeneity owner
  `Function.PositivelyHomogeneousOfDegree`.
- `bridge/view`: the primitive homogeneity owner is stated on the raw real-valued source
  function, while the closed-proper-convex clause and the downstream-facing homogeneity bridge are
  stated on the canonical codomain lift `(lpCoordinatePower X ι p).toWithTopBot`.
  This keeps convexity on the chapter `WithTopBot ℝ` surface while avoiding a lift-only statement
  for a property that is intrinsically scalar-scaling.

Domain-style sampling used here:
- `lpCoordinatePower` is the primitive source-facing datum in this file;
- `Function.PositivelyHomogeneousOfDegree` from Text 15.0.21 for the scaling owner;
- `strictConvexOn_rpow` and `convexOn_rpow` for the scalar building block `t ↦ t ^ p`;
- `ConvexOn.map_sum_le` for finite sums of convex terms;
- `Function.toWithTopBot` from Definition 4.4 as the canonical real-to-`WithTopBot ℝ`
  codomain lift.

Primitive data vs derived API:
- primitive source data: the concrete coordinate formula defining the function, kept as a raw
totalized real-power expression so later bridge items can reuse it definitionally;
- derived API: the closed-proper-convex statement on the canonical `WithTopBot ℝ` codomain lift,
  the primitive real-valued degree-`p` positive-homogeneity statement, and the thin codomain-lift
  homogeneity bridge used downstream; convexity is restricted to the textbook regime `1 ≤ p`,
  while the homogeneity law remains valid for every real exponent `p`.

Layer target: `source-facing`, expressed using the canonical chapter owners for convexity and
positive homogeneity: primitive on `lpCoordinatePower X ι p`, and bridged to
`(lpCoordinatePower X ι p).toWithTopBot` where Chapter 15 downstream owners require the extended
codomain. The owner parameter `X` is explicit so partially-applied surfaces avoid named-argument
noise; the scalar is intrinsically `ℝ` here because both the chapter owner
`Function.PositivelyHomogeneousOfDegree` and the exponentiation bridge `Real.rpow` are real-scalar.
-/

/-- The totalized coordinate power-sum formula `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite
coordinate family `ι → X`. The raw definition is kept for all real exponents so downstream bridge
results can reuse the formula definitionally; the source-labeled theorems below restrict to the
intended textbook regime `1 ≤ p`. -/
def lpCoordinatePower (X : Type*) [Norm X] (ι : Type*) [Fintype ι] (p : ℝ) (x : ι → X) : ℝ :=
  (1 / p) * ∑ i : ι, ‖x i‖ ^ p

-- Proof sketch: unfold `lpCoordinatePower`; this is exactly its defining coordinate
-- formula.
/-- Evaluating `lpCoordinatePower X ι p` at `x` gives `(1 / p)` times the sum of the `p`th
powers of the coordinate norms of `x`. -/
@[simp]
theorem lpCoordinatePower_apply (X : Type*) [Norm X] (ι : Type*) [Fintype ι]
    (p : ℝ) (x : ι → X) :
    lpCoordinatePower X ι p x = (1 / p) * ∑ i : ι, ‖x i‖ ^ p := rfl

-- Proof sketch: each coordinate summand `xᵢ ↦ (1 / p) * ‖xᵢ‖ ^ p`, with `1 ≤ p`, is a finite
-- closed convex real-valued profile; summing over the finitely many coordinates preserves
-- convexity and
-- lower semicontinuity, and finiteness everywhere gives properness. Coerce the resulting real
-- function to `WithTopBot ℝ` via `Function.toWithTopBot` to match
-- `Function.IsClosedProperConvex`.
/-- Text 15.0.22 (1): for `1 ≤ p`, the function
`x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p`, viewed as `WithTopBot ℝ`-valued by coercion, is closed proper
convex. -/
theorem lpCoordinatePower_isClosedProperConvex
    (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) (hp : 1 ≤ p) :
    ((lpCoordinatePower X ι p).toWithTopBot).IsClosedProperConvex (𝕜 := ℝ) := sorry

-- Proof sketch: for every positive scalar `c`, rewrite each coordinate norm of `c • x` with
-- `‖c • x i‖ = c * ‖x i‖`. Then `‖c • x i‖ ^ p = c ^ p * ‖x i‖ ^ p` for `0 < c`, so `c ^ p`
-- factors out of the finite sum and then out of the prefactor `(1 / p)`.
/-- Text 15.0.22 (2): the coordinate `ℓ_p` power-sum function is positively homogeneous of degree
`p` on its primitive real-valued owner. -/
theorem lpCoordinatePower_positivelyHomogeneousOfDegree
    (X : Type*) [Norm X] [SMul ℝ X] [NormSMulClass ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) :
    (lpCoordinatePower X ι p).PositivelyHomogeneousOfDegree p := sorry

-- Proof sketch: coerce the primitive real-valued scaling law to `WithTopBot ℝ`, so the
-- homogeneity statement can be used directly with Chapter 15 owners sharing that codomain.
/-- Text 15.0.22 (2), codomain-lift bridge: the same degree-`p` homogeneity law on the canonical
`WithTopBot ℝ` codomain surface. -/
theorem lpCoordinatePower_positivelyHomogeneousOfDegree_toWithTopBot
    (X : Type*) [Norm X] [SMul ℝ X] [NormSMulClass ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) :
    (lpCoordinatePower X ι p).toWithTopBot.PositivelyHomogeneousOfDegree p := by
  simpa using
    (lpCoordinatePower_positivelyHomogeneousOfDegree X ι p).toWithTopBot

end
