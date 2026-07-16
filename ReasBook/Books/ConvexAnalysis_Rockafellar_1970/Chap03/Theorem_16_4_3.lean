import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_2_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_16_2_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Rockafellar

noncomputable section

section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.3 is the closure-free refinement of Theorem 16.4.2 for a finite
  nonempty family of proper convex functions on a finite-dimensional pairing space.
  Under a common relative-interior point of the effective domains, it removes both outer closure
  operators and adds attainment of the defining infimum.
- `core/canonical`: the owner abstractions already present are `convexConjugate` for Fenchel
  conjugation, `finiteInfimalConvolution` for the finite infimal convolution, and
  `riDom[𝕜](f)` for `ri (dom f)`.
- `bridge/view`: the source formula is rendered directly by those owners, so no surrogate package
  or auxiliary wrapper is introduced.

Domain-style sampling used here:
- the closure-level conjugacy theorem from `Theorem_16_4_2`;
- `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom`
  from `Theorem_9_3`;
- `common_riDom_nonempty_iff_no_zero_sum_asymmetric_conjugate_recession`
  from `Corollary_16_2_2`;
- `exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession`
  from `Corollary_9_2_1`.

Primitive data vs derived API:
- primitive inputs: the finite nonempty family `f`;
- owner hypotheses: convexity and properness of each `f i`, together with a common point of the
  relative interiors `riDom[𝕜](f i)`;
- derived API: the closure-free conjugacy identity and the attainment statement for the defining
  infimum of the conjugate-side finite infimal convolution.

Layer target: `source-facing`, expressed directly in the canonical finite-family conjugacy API.
-/

-- Proof sketch: start from Theorem 16.4.2, which identifies the conjugate of the sum of the
-- lower-semicontinuous hulls with the lower-semicontinuous hull of the finite infimal convolution
-- of the conjugates. The common-relative-interior hypothesis removes the closure on the primal
-- sum by
-- `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom`,
-- and Corollary 16.2.2 plus
-- Corollary 9.2.1 remove the closure on the dual infimal convolution.
/-- Theorem 16.4.3: if a finite nonempty family of proper convex functions on a
finite-dimensional pairing space has a common relative-interior point in the effective domains
`ri (dom f_i)`, then the closure operations in Theorem 16.4.2 are unnecessary:
`(f₁ + ··· + f_m)⋆ = f₁⋆ □ ··· □ f_m⋆`, rendered by `convexConjugate` and
`finiteInfimalConvolution`. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior
    (f : ι → E → WithBotTop 𝕜)
    (_ : ∀ i, (f i).IsConvex 𝕜)
    (_ : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty) :
    convexConjugate (fun x ↦ ∑ i, f i x) =
      finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) := sorry

-- Proof sketch: once the dual function is identified with
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i))`, apply the attainment clause of
-- Corollary 9.2.1 to the conjugate family. Corollary 16.2.2 supplies exactly the recession
-- hypothesis needed for that attainment statement under the same common-relative-interior
-- assumption.
/-- Under the common-relative-interior hypothesis of Theorem 16.4.3, the infimum defining the
dual finite infimal convolution `f₁⋆ □ ··· □ f_m⋆` is attained at every `x⋆`. -/
theorem exists_sum_eq_finiteInfimalConvolution_conjugates_of_common_intrinsicInterior
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty)
    (xStar : E) :
    ∃ xs : ι → E,
      (∑ i, xs i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) xStar =
          ∑ i, ((f i)⋆ : E → WithBotTop 𝕜) (xs i) := sorry

end
