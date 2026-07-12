import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {m : ℕ}
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 20.1.1 says that if `f₁, …, f_m` are closed proper convex
  functions, with the first `k` polyhedral, and if the domains of the conjugates meet as
  `dom f₁* ∩ ··· ∩ dom f_k* ∩ ri(dom f_{k+1}*) ∩ ··· ∩
  ri(dom f_m*) ≠ ∅`, then the finite infimal convolution is again closed proper convex and its
  defining infimum is attained.
- `core/canonical`: the chapter owner abstractions are `finiteInfimalConvolution`,
  `f⋆`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the source conjugate-domain intersection condition is stated directly on the
  canonical Chapter 20 owner `HasMixedPrefixDomainPoint` applied to the conjugate family
  `fun i ↦ (f i)⋆`, with no parallel wrapper owner.

Domain-style sampling used here:
- `finiteInfimalConvolution` from `Text_5_4_1`;
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `Function.IsClosedProperConvex.convexConjugate` from `Corollary_12_2_1`;
- `convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedralPrefix_mixedDomain` from
  `Theorem_20_1`;
- the source-facing owner hypotheses `f.HasPolyhedralPrefix k` and
  `(fun i ↦ (f i)⋆).HasMixedPrefixDomainPoint k`.

Primitive data vs derived API:
- primitive inputs: a finite family `f : Fin m → E → WithTopBot 𝕜`, the owner hypothesis
  `∀ i, IsClosedProperConvex[𝕜] (f i)`, the polyhedral-prefix condition
  `f.HasPolyhedralPrefix k`, and the conjugate-domain compatibility condition on the conjugate
  family `(fun i ↦ (f i)⋆).HasMixedPrefixDomainPoint k`;
- derived API: the main owner conclusion
  `IsClosedProperConvex[𝕜] (finiteInfimalConvolution f)`; the pointwise attainment statement is
  the only declaration here that additionally requires a nonempty index family.
- ambient refinement: the public statements only use the Chapter 12/19/20 owner APIs for
  conjugation, polyhedrality, and biconjugacy, so they live on the same finite-dimensional
  scalar-generic topological vector-space layer with continuous linear self-pairing,
  rather than the more concrete inner-product model.
-/

variable (f : Fin m → E → WithTopBot 𝕜)

namespace Function

-- Proof sketch: apply Theorem 20.1 to the conjugate family `fun i ↦ (f i)⋆`. The source-side
-- prefix hypothesis is transported to that family by the polyhedral-conjugate bridge, while
-- `hconj` is already the required mixed domain hypothesis on the biconjugate domains. The left-hand
-- side is the Fenchel conjugate of the proper convex finite sum `∑ i, (f i)⋆`, hence closed
-- proper convex by Theorem 12.2; biconjugacy then identifies the right-hand side with
-- `finiteInfimalConvolution f`.
/-- Corollary 20.1.1 (1): if closed proper convex functions `f₁, …, f_m` have the stated
polyhedral-prefix and conjugate-domain compatibility property, then their finite infimal
convolution is again a closed proper convex function. -/
theorem
    finiteInfimalConvolution_isClosedProperConvex
    (k : ℕ)
    (hconj : (fun i : Fin m ↦ (f i)⋆).HasMixedPrefixDomainPoint k)
    (hf : ∀ i : Fin m, IsClosedProperConvex[𝕜] (f i))
    (hpoly : f.HasPolyhedralPrefix k)
    :
    IsClosedProperConvex[𝕜] (finiteInfimalConvolution f) := by
  sorry

-- Proof sketch: after identifying the finite infimal convolution with the dual object produced by
-- the conjugate-sum theorem, use the corresponding equality case in Fenchel duality to obtain an
-- optimizing decomposition `x = ∑ i, xs i` realizing the defining infimum.
section

variable [NeZero m]

/-- Corollary 20.1.1 (2): under the same hypotheses, the infimum in the definition of the finite
infimal convolution is attained at every point. -/
theorem exists_sum_eq_finiteInfimalConvolution
    (k : ℕ)
    (hconj : (fun i : Fin m ↦ (f i)⋆).HasMixedPrefixDomainPoint k)
    (hf : ∀ i : Fin m, IsClosedProperConvex[𝕜] (f i))
    (hpoly : f.HasPolyhedralPrefix k)
    (x : E) :
    ∃ xs : Fin m → E,
      (∑ i, xs i) = x ∧ finiteInfimalConvolution f x = ∑ i, f i (xs i) := by
  sorry

end

end Function

end
