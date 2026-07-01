import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Set
open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.5 replaces the recession-direction hypothesis in Helly's theorem by
  a weaker hypothesis: a finite subfamily is polyhedral, and every vector in the common recession
  cone of the whole family lies in the lineality space of all remaining members.
- `core/canonical`: the existing owner abstractions are `Set.IsPolyhedral`,
  `0⁺`, `lin[ℝ](·)`, arbitrary intersections `⋂ i, C i`, and the finite-subfamily intersections
  `⋂ i ∈ J, C i`.
- `bridge/view`: the source phrase "is linear in the direction `y`" is rendered canonically by
  membership `y ∈ lin[ℝ](C i)`, while common recession directions are expressed by owner-side
  membership `y ∈ 0⁺[ℝ] (C i)` and `y ∈ ⋂ i, 0⁺[ℝ] (C i)`.

Domain-style sampling used here:
- the set-side owner `Set.IsPolyhedral`;
- the chapter owner `recessionCone`, used through the notation `0⁺`;
- the source-facing lineality owner `Set.lineal`, used through the notation `lin[ℝ](·)`;
- the indicator-function bridge `Set.indicatorFunction_lineal_eq_lineal`;
- the existing Helly statement
  `helly_theorem_of_trivial_common_recessionCone`.

Primitive data vs derived API:
- primitive inputs: the family `C`, the finite polyhedral core `I₀`, closedness and convexity of
  the non-core remainder `i ∉ I₀`, the common-recession-to-lineality hypothesis outside `I₀`, and
  the `Module.finrank ℝ E + 1` intersection property;
- derived output: nonemptiness of the total intersection.

Ambient refinement:
- the theorem uses no coordinate-level or inner-product-specific structure beyond the Chapter 1
  polyhedral owner, so its public ambient layer should be an arbitrary finite-dimensional real
  normed space rather than the display model `EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`, stated directly for the family of sets and the displayed finite
polyhedral-core hypothesis at the operational `Finset` layer, rather than through a parallel
local wrapper around that hypothesis.
-/

-- Proof sketch: for each `i ∈ I₀`, express the polyhedral set `C i` as a finite intersection of
-- closed half-spaces and enlarge the family by all those half-spaces. This preserves the
-- `Module.finrank ℝ E + 1` intersection property and turns the finite polyhedral core into a
-- finite half-space core. Apply the half-space version obtained from Theorem 21.4 by passing to
-- indicator functions; the resulting nonempty total intersection is unchanged from the original
-- family.
/-- Theorem 21.5: in Helly's theorem for a family of closed convex subsets of `R^n`, the usual
recession hypothesis may be replaced by the weaker assumption that some finite subfamily is
polyhedral, that the remaining members are closed and convex, and that every vector in the common
recession cone of the whole family lies in the lineality space of each member outside that finite
polyhedral core. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement with threshold `n + 1`. -/
theorem helly_theorem_of_finite_polyhedral_core
    (C : I → Set E)
    (hpolyhedral_core :
      ∃ I₀ : Finset I,
        (∀ i ∈ I₀, (C i).IsPolyhedral ℝ) ∧
          (∀ i ∉ I₀, IsClosed (C i)) ∧
          (∀ i ∉ I₀, Convex ℝ (C i)) ∧
          ∀ ⦃y : E⦄ ⦃i : I⦄, y ∈ ⋂ j, 0⁺[ℝ](C j) → i ∉ I₀ → y ∈ lin[ℝ](C i))
    (h_small_intersection :
      ∀ J : Finset I, J.card ≤ Module.finrank ℝ E + 1 →
        (⋂ i ∈ (J : Set I), C i).Nonempty) :
    (⋂ i, C i).Nonempty := sorry

end
