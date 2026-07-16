import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Lemma_3_1_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient Pointwise WithTopConvexAnalysis

universe u

variable {m : ℕ}

local notation "Y" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.1.17 lies in the chapter's local convex-composition / constrained-subdifferential
chain-rule domain.

Sampled owner-style declarations:
- `vectorMap` in `Lemma_3_1_16`, the chapter's existing owner for the coordinate vector
  `x ↦ (f₁(x), ..., fₘ(x))`;
- `constrainedSubdifferential` in `Definition_3_1_5`, the earlier chapter owner for local
  subgradient inequalities on a feasible set;
- `subdifferentialWithin` in `Theorem_3_44`, the later real-valued bridge/view of the same local
  notion at feasible points;
- mathlib `Monotone` and `HasGradientAt` on the coordinatewise ordered product `Fin m → ℝ`;
- the canonical finite weighted set sum `∑ i, a i • S i`.

Best owner abstractions:
- source-facing: Lemma 3.1.17's convex-composition and subdifferential chain rule;
- core/canonical: `constrainedSubdifferential`, `vectorMap`, and the full-domain coordinatewise
  monotonicity owner `Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`;
- bridge/view: the later `subdifferentialWithin` view.

Primitive data:
- the convex set `Q` in a real inner-product space `E`;
- the outer function `F : Y → ℝ`;
- the coordinate family `f : Fin m → E → ℝ`.

Derived API:
- convexity of `F ∘ vectorMap f`;
- the weighted constrained-subdifferential identity at interior points of `Q`.

This file therefore deletes the duplicate global subgradient formulation and keeps the statement at
the correct local owner layer. The public API now uses the earlier chapter owner
`constrainedSubdifferential`, the existing coordinate-vector owner `vectorMap`, and the canonical
full-domain coordinatewise monotonicity hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on the product space `Fin m → ℝ`. The
textbook input model `ℝⁿ` is not essential for these owner statements, and neither is
finite-dimensionality of the input space `E`, so the file now grows from the intrinsic
inner-product-space layer already used by `constrainedSubdifferential` and `vectorMap`. The later
`subdifferentialWithin` view should be derived from this owner statement at feasible points rather
than maintained as a parallel root theorem here.
-/

section Convexity

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Lemma 3.1.17 (convexity part): if `F` is convex and coordinatewise monotone on `ℝ^m`, and
each component function `f i` is convex on the convex set `Q`, then the composition
`x ↦ F (f₁(x), ..., fₘ(x))` is convex on `Q`; coordinatewise monotonicity is recorded by the
canonical full-domain product-order hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`. -/
-- Proof sketch: combine convexity of each `f i` with coordinatewise monotonicity and convexity
-- of `F`.
theorem convexOn_comp_coordinatewiseMonotone
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)) :
    ConvexOn ℝ Q (F ∘ vectorMap f) := by
  refine ⟨hQ_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First compare the coordinate vector at the convex combination point componentwise.
  have hcoord :
      (EuclideanSpace.equiv (Fin m) ℝ) (vectorMap f (a • x + b • y)) ≤
        (EuclideanSpace.equiv (Fin m) ℝ) (a • vectorMap f x + b • vectorMap f y) := by
    intro i
    simpa [vectorMap_apply] using (hf_conv i).2 hx hy ha hb hab
  have hmono :
      F (vectorMap f (a • x + b • y)) ≤ F (a • vectorMap f x + b • vectorMap f y) :=
    by simpa using hF_mono hcoord
  -- Then use the convexity inequality for `F` at the two endpoint coordinate vectors.
  have houter :
      F (a • vectorMap f x + b • vectorMap f y) ≤
        a * F (vectorMap f x) + b * F (vectorMap f y) := by
    simpa [Function.comp] using hF_conv.2 (by simp) (by simp) ha hb hab
  exact hmono.trans houter

end Convexity

section Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.1.17 (subdifferential part): if `F` is convex and coordinatewise monotone on `ℝ^m`,
and each component function `f i` is convex on the convex set `Q`, then at every interior
feasible point `x ∈ interior Q` and for every gradient witness
`g = ∇F (f₁(x), ..., fₘ(x))`, the constrained subdifferential
`∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x)` equals the weighted sum
`∑ᵢ gᵢ • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`. This keeps the owner notation `∂[Q]` on the
public theorem surface instead of unpacking it back to the raw set builder. -/
-- Proof sketch: compute the directional derivative of the composition using the pointwise
-- gradient witness `HasGradientAt F g (vectorMap f x)`, identify each directional
-- derivative of `f i` with its support function on
-- `∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`, and then apply the
-- support-function characterization of convex sets from Corollary 3.1.5 inside the feasible set
-- `Q`.
theorem constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    {x : E} (hx : x ∈ interior Q) {g : Y}
    (hF_grad : HasGradientAt F g (vectorMap f x)) :
    ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) =
      ∑ i : Fin m,
        (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) := by
  -- Route correction: the source proof finishes by identifying both sides through their support
  -- functions, but this file still lacks the owner-level bridge from constrained
  -- subdifferentials on `Q` to the corresponding within-set directional derivatives.
  --
  -- TODO: prove the constrained support-function bridge in this ambient owner language, then use
  -- the textbook chain-rule identity for directional derivatives together with Corollary 3.1.5.
  sorry

end Gradient

end
