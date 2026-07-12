import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

universe u v

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {ι : Type v} [Finite ι]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.3 identifies the conjugate of the pointwise supremum of a finite
  family of proper convex functions with the convex hull of the conjugate family, under pairwise
  equality of closure of effective domains. It also gives the convex-combination infimum formula
  and the corresponding attainment statement (with nonempty index type for attainment).
- `core/canonical`: the owner abstractions already present are Theorem 16.5.2 for the closed-side
  conjugacy identity, Corollary 9.8.3.1 for the common-recession-function closedness/attainment
  package of `conv(⨅ i, g i)`, and Theorem 5.6 for the canonical owner
  `Function.convexCombinationValues`.
- `bridge/view`: Rockafellar's `sup {f_i}` is rendered by `⨆ i, f i`; the common-closure
  hypothesis on `cl (dom f_i)` is written directly with the chapter effective-domain notation
  `dom(f i)`; and the common-closure assumption is converted into the owner-side common recession
  function of the conjugate family through Theorem 13.3 together with `supportFunction_closure`.

Domain-style sampling used here:
- `convexConjugate_iSup_cl_eq_cl_conv_iInf_convexConjugate_of_convex`;
- `lowerSemicontinuous_convexHull_iInf_of_pairwise_recessionFunction`;
- `exists_finite_convex_combination_eq_convexHull_iInf_of_pairwise_recessionFunction`;
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate`;
- `supportFunction_closure`;
- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`.

Primitive data vs derived API:
- primitive inputs: a finite family `f : ι → E → WithBotTop 𝕜`, convexity and
  properness of each `f i`, and the pairwise common-closure condition
  `Pairwise (fun i j ↦ closure dom(f i) = closure dom(f j))`;
- derived API: the conjugacy identity, the convex-combination infimum formula for the conjugate of
  the supremum, and the corresponding attainment statement.

Layer target: `source-facing`, stated directly through the canonical owner
`conv(⨅ i, (f i)⋆)` and Fenchel conjugation on the pairing owner layer, with no extra wrapper
around the family or around the common-domain hypothesis. The finite-convex-combination
companions are kept in the canonical owner interface
`Function.convexCombinationValues`.
-/

-- Proof sketch: Theorem 16.5.2 gives the identity for `⨆ i, lowerSemicontinuousHull (f i)`. The
-- common closure-of-domain hypothesis lets Theorem 9.4 identify
-- `lowerSemicontinuousHull (⨆ i, f i)`
-- with that supremum of closures. On the dual side, Theorem 13.3 identifies the recession
-- function of each `convexConjugate (f i)` with `supportFunction dom(f i)`, and
-- `supportFunction_closure` turns the pairwise common-closure hypothesis into pairwise equality
-- of recession functions.
-- Corollary 9.8.3.1 therefore shows that `conv(⨅ i, (f i)⋆)` is already lower semicontinuous, so
-- the closure on the right side of Theorem 16.5.2 drops out.
/-- Theorem 16.5.3 (1): if a finite family `fᵢ` of proper convex functions on a
finite-dimensional scalar-field pairing space has pairwise-equal closures of effective domains,
then the conjugate of its pointwise supremum is the convex hull of the conjugate family. -/
theorem convexConjugate_iSup_eq_conv_iInf_convexConjugate_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j)))) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) = conv(⨅ i, (f i)⋆) := sorry

-- Proof sketch: combine clause (1) with Theorem 5.6 at owner level,
-- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`, applied to
-- `fun i ↦ (f i)⋆`.
/-- Theorem 16.5.3 (2): under the same hypotheses, for each `x⋆` the value of
`(sup_i f_i)⋆(x⋆)` is the infimum over canonical convex-combination values of the conjugate
family owner `⨅ i, (f i)⋆`. -/
theorem convexConjugate_iSup_apply_eq_sInf_convexCombinationValues_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j))))
    (xStar : E) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) xStar =
      sInf (Function.convexCombinationValues (⨅ i, (f i)⋆) xStar) := sorry

-- Proof sketch: by Theorem 13.3 and `supportFunction_closure`, the conjugate family has pairwise
-- equal recession functions because the closures `closure dom(f i)` agree pairwise.
-- Corollary 9.8.3.1 then applies directly to the family `fun i ↦ (f i)⋆`, producing a witness in
-- `Function.convexCombinationValues (⨅ i, (f i)⋆) x⋆` for the value `conv(⨅ i, (f i)⋆) x⋆`.
-- Clause (1) identifies that value with `(⨆ i, f i)⋆ x⋆`.
/-- Theorem 16.5.3 (3): under the same hypotheses, for every `x⋆` the infimum in clause (2) is
attained, expressed canonically by membership in
`Function.convexCombinationValues (⨅ i, (f i)⋆) x⋆`. -/
theorem convexConjugate_iSup_apply_mem_convexCombinationValues_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j))))
    [Nonempty ι] (xStar : E) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) xStar ∈
      Function.convexCombinationValues (⨅ i, (f i)⋆) xStar := sorry

end
