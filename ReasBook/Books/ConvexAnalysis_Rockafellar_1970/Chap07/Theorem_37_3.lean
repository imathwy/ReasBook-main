import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

noncomputable section

universe u v

open Bifunction
open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 37.3 gives two one-sided slice-recession criteria implying existence
  of an ambient saddle-value for a closed proper concave-convex saddle-function, and says that if
  both criteria hold then the common saddle-value is finite.
- `core/canonical`: the existing owner layer is the Chapter 36 ambient saddle-value predicate
  `HasSaddleValue K`, together with the canonical ambient value `maximinValue K`.
- `bridge/view`: Corollary 37.2.1 turns the two source criteria into the conjugate-domain
  relative-interior conditions at the origin, while Corollary 37.3.1 is the canonical Chapter 36
  bridge from those conditions to ambient saddle-value existence.

Primary mathematical domain:
- minimax theory for closed proper concave-convex saddle-functions via slice recession geometry.

Domain-style sampling used here:
- `IsClosed`, `IsProper`, `dom₁`, `dom₂`, and `ri[𝕜](·)` from
  `Chap07.Corollary_34_2_1`;
- `Function.RecedesInDirection` from `Chap06.Definition_6_27_4`;
- `zero_mem_ri_dom₂_lowerConjugate_iff_no_common_recession_direction` and
  `zero_mem_ri_dom₁_lowerConjugate_iff_no_common_recession_direction` from
  `Chap07.Corollary_37_2_1`;
- `HasSaddleValue` and `maximinValue` from `Chap07.Definition_36_0_1`.

Primitive data vs derived API:
- primitive source data: the saddle-function `K` with hypotheses `IsClosed K`, `IsProper K`, and
  `IsConcaveConvex 𝕜 K`;
- primitive source-facing conditions: absence of a common recession direction for the slice family
  `K(u, ·)` on `ri[𝕜](dom₁ K)` and for the slice family `-K(·, v)` on `ri[𝕜](dom₂ K)`;
- derived API in this file: the ambient saddle-value existence theorem and the finite-value
  consequence when both one-sided criteria hold.

Layer target: `source-facing`, stated directly on the existing Chapter 36 owner rather than by
introducing a parallel local saddle-value package.
-/

-- Proof sketch: use Corollary 37.2.1 to convert either source condition into the corresponding
-- origin-relative-interior statement for `dom₂ (lowerConjugate K)` or `dom₁ (lowerConjugate K)`.
-- Then apply the Chapter 37 owner-level bridge from conjugate-domain relative interior to ambient
-- saddle-value existence.
/-- Theorem 37.3 (1): let `K` be a closed proper concave-convex saddle-function. If either
(a) the convex slices `K(u, ·)` for `u ∈ ri[𝕜](dom₁ K)` have no common recession direction, or
(b) the convex slices `-K(·, v)` for `v ∈ ri[𝕜](dom₂ K)` have no common recession direction,
then `K` has an ambient saddle-value. -/
theorem
    hasSaddleValue_of_no_common_second_recession_direction_or_no_common_first_recession_direction
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K)
    (h_recession :
      (¬ ∃ y : X, ∀ u ∈ ri[𝕜](dom₁ K), (K u).RecedesInDirection 𝕜 y) ∨
        ¬ ∃ y : U, ∀ v ∈ ri[𝕜](dom₂ K), (fun u ↦ -K u v).RecedesInDirection 𝕜 y) :
    HasSaddleValue K := sorry

-- Proof sketch: first obtain `HasSaddleValue K` from the preceding theorem.
-- Then combine the two one-sided criteria through the conjugate-domain relative-interior
-- equalities of Corollary 37.2.1 and the Chapter 37 zero-basepoint conjugate identities to show
-- the common saddle-value is strictly between `⊥` and `⊤`.
/-- Theorem 37.3 (2): if both one-sided no-common-recession-direction criteria from
Theorem 37.3 hold, then the ambient Chapter 36 saddle value of `K` is finite. -/
theorem
    finite_saddleValue_of_no_common_second_and_first_recession_direction
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K)
    (h_second : ¬ ∃ y : X, ∀ u ∈ ri[𝕜](dom₁ K), (K u).RecedesInDirection 𝕜 y)
    (h_first : ¬ ∃ y : U, ∀ v ∈ ri[𝕜](dom₂ K), (fun u ↦ -K u v).RecedesInDirection 𝕜 y) :
    ⊥ < maximinValue K ∧ maximinValue K < ⊤ := sorry

end

end SaddleFunction
