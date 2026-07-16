import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_13_3_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_5

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 26.6 specializes the Legendre-transform discussion to a finite
  differentiable convex function on all of `ℝⁿ`, characterizing when the gradient is a bijection
  and then spelling out the global conjugate consequences.
- `core/canonical`: the chapter owners already present are `Function.IsLegendreTypeOn`,
  `Function.IsCofinite`, the Fenchel conjugate `f⋆`, and the gradient owner `∇`.
- `bridge/view`: the global `ℝⁿ` wording is expressed intrinsically on a finite-dimensional real
  inner-product space, with the textbook inverse-gradient formula written through
  `Function.invFun (∇ f)`.

Domain-style sampling used here:
- `Function.IsLegendreTypeOn` from `Text_26_5_0_2`;
- `convexConjugate_finite_everywhere_iff_isCofinite` from `Corollary_13_3_1`;
- `Function.IsClosedProperConvex.gradientHomeomorphInteriorDomToConvexConjugateInteriorDom` and
  the Legendre-value theorems from `Theorem_26_5`;
- `Function.IsClosedProperConvex.biconjugate_eq` from `Corollary_12_2_1`.

Primitive data vs derived API:
- primitive source inputs: a finite real-valued function `f : E → ℝ`, its global convexity, and
  its differentiability;
- primitive owner bridge data: global Legendre type on `Set.univ` and co-finiteness of
  `f.toWithBotTop`;
- source-facing conclusion: bijectivity of the global gradient map `∇ f`;
- derived API: the dual Legendre-type theorem, the separate dual co-finiteness consequence, and
  the inverse-gradient value formula; the biconjugacy identity is reused directly from the Chapter
  12 owner theorem instead of being redeclared locally.

Layer target: the labeled theorem is source-facing, while the remaining declarations are canonical
bridge companions phrased through the chapter owners `IsLegendreTypeOn`, `IsCofinite`, and `⋆`,
plus direct recall of the canonical biconjugacy theorem.
-/

variable {f : E → ℝ}

local notation "fStar" => (((f.toEReal)⋆ : E → EReal))

section GlobalDifferentiable

variable (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)

-- Proof sketch: because `f` is finite and differentiable on all of `E`, the source set is
-- `interior (dom(f.toWithBotTop)) = Set.univ`, and Definition 26.1.1 reduces to differentiability
-- together with a vacuous boundary clause. Corollary 26.3.1 identifies one-to-one-ness of the
-- subdifferential graph with strict convexity plus essential smoothness, while Corollary 13.3.1
-- identifies the dual global-domain condition with co-finiteness. Theorem 26.5 then transports
-- these data to global bijectivity of the gradient.
/-- Theorem 26.6: for a differentiable convex function on a finite-dimensional real
inner-product space, the gradient is bijective exactly when the function is strictly convex on all
of `E` and its canonical `WithBotTop` lift is co-finite. -/
theorem bijective_gradient_iff_strictConvexOn_univ_and_isCofinite :
    Bijective (∇ f) ↔ StrictConvexOn ℝ Set.univ f ∧ f.toWithBotTop.IsCofinite := sorry

-- Proof sketch: use the main equivalence to rewrite bijectivity of `∇ f` as strict convexity and
-- co-finiteness of `f`. For the finite lift `f.toWithBotTop`, the interior effective domain is
-- `Set.univ`, so Theorem 26.5 transports global Legendre type across Fenchel conjugation.
/-- Under global bijectivity of the gradient, the Fenchel conjugate has a finite real branch of
Legendre type on all of `E`. Equivalently, `f⋆` is differentiable and strictly convex
everywhere. -/
theorem convexConjugate_realBranch_isLegendreTypeOn_univ_of_bijective_gradient
    (hbij : Bijective (∇ f)) :
    IsLegendreTypeOn Set.univ (fStar).realBranch := sorry

-- Proof sketch: after the dual Legendre-type theorem, Theorem 26.5 identifies the inverse of the
-- global gradient map with the gradient of the conjugate real branch. Substitute this inverse
-- point into the global Legendre-value identity to rewrite `f⋆(xStar)` as the affine defect
-- evaluated at `(∇ f)⁻¹ xStar`, implemented canonically by `Function.invFun (∇ f)`.
/-- Under global bijectivity of the gradient, the Fenchel conjugate satisfies the classical
Legendre formula
`f⋆(xStar) = ⟪(∇ f)⁻¹ xStar, xStar⟫ - f ((∇ f)⁻¹ xStar)` for every `xStar`. -/
theorem convexConjugate_realBranch_eq_inner_invGradient_sub_of_bijective_gradient
    (hbij : Bijective (∇ f)) (xStar : E) :
    (fStar).realBranch xStar =
      (⟪invFun (∇ f) xStar, xStar⟫ - f (invFun (∇ f) xStar) : ℝ) := sorry

end GlobalDifferentiable

-- Proof sketch: the biconjugate of `f.toWithBotTop` is again `f.toWithBotTop` by Chapter 12,
-- because a finite convex real-valued function has a closed proper convex lift. Since `f`
-- already takes real values everywhere, Corollary 13.3.1 identifies the Fenchel conjugate of
-- `f.toWithBotTop` as co-finite.
/-- The Fenchel conjugate of the canonical `WithBotTop` lift of a globally convex real-valued
function is co-finite. This is the dual global-domain clause in Theorem 26.6, stated directly on
the Chapter 3 owner `IsCofinite`. -/
theorem convexConjugate_toWithBotTop_isCofinite
    (hf_convex : ConvexOn ℝ Set.univ f) :
    (fStar).IsCofinite := sorry

/- The biconjugacy consequence used in Theorem 26.6 already exists upstream with the canonical
closed-proper-convex owner interface. -/
recall Function.IsClosedProperConvex.biconjugate_eq

end Function

end
