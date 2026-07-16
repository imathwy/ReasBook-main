import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.29.6 says that if one slice of a convex bifunction has infimum
  `-∞`, then every parameter in `ri (dom F)` has slice infimum `-∞`; outside `dom F`, the slice
  infimum is `+∞`.
- `core/canonical`: the Chapter 6 owners already present are `perturbationFunction`, `dom F`, and
  the convexity theorem `perturbationFunction_isConvex` from Theorem 6.29.1. The Chapter 2 owner
  theorem `Function.IsConvex.eq_bot_of_mem_riDom` is the canonical `-∞` propagation statement for
  convex extended-valued functions.
- `bridge/view`: Rockafellar's `inf F_u` is the owner value `perturbationFunction F u`, while
  `ri (dom F)` is the chapter surface `ri[𝕜](dom F)`, bridged to
  `riDom[𝕜](perturbationFunction F)` by Definition 6.29.8.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.perturbationFunction_isConvex` from `Theorem_6_29_1`;
- `Bifunction.dom` and `Bifunction.mem_ri_dom_iff_mem_riDom_perturbationFunction`
  from `Definition_6_29_8`;
- `Function.IsConvex.eq_bot_of_mem_riDom` from `Chap02.Theorem_7_2`.

Primitive data vs derived API:
- primitive input for clause `(1)`: owner convexity of `perturbationFunction F`, together with the
  source hypothesis that some slice infimum is `⊥`;
- source-facing bridge for clause `(1)`: convexity of `Function.uncurry F`, converted to owner
  convexity by `perturbationFunction_isConvex`;
- primitive input for clause `(2)`: a parameter outside `dom(perturbationFunction F)`;
- source-facing bridge for clause `(2)`: outside-domain membership for `dom F`, converted by
  `mem_dom_perturbationFunction_iff_mem_dom`.

Layer target: each clause is first exposed at the primitive owner layer for
`perturbationFunction`, with source-facing `dom F` / `ri[𝕜](dom F)` forms kept as thin wrappers.
-/

section RelativeInteriorOwner

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]

-- Proof sketch: an equality `perturbationFunction F u₀ = ⊥` shows this owner function is
-- improper. Then apply the Chapter 2 owner theorem `Function.IsConvex.eq_bot_of_mem_riDom`
-- directly on `perturbationFunction F`.
/-- Owner form of Corollary 6.29.6 (1): if `perturbationFunction F` is convex and equals `⊥` at
some parameter, then it equals `⊥` at every point of `riDom[𝕜](perturbationFunction F)`. -/
theorem perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex
    {F : U → X → WithBotTop 𝕜}
    (hp_convex : (perturbationFunction F).IsConvex 𝕜)
    (hbot : ∃ u0 : U, perturbationFunction F u0 = ⊥)
    {u : U} (hu : u ∈ riDom[𝕜](perturbationFunction F)) :
    perturbationFunction F u = ⊥ := by
  have hp_not_proper : ¬ (perturbationFunction F).IsProper := by
    intro hp
    rcases hbot with ⟨u0, hu0⟩
    exact (hp.ne_bot u0) hu0
  exact hp_convex.eq_bot_of_mem_riDom hp_not_proper hu

end RelativeInteriorOwner

section RelativeInterior

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: Theorem 6.29.1 makes `perturbationFunction F` convex. Transport
-- `u ∈ ri[𝕜](dom F)` to `u ∈ riDom[𝕜](perturbationFunction F)` via Definition 6.29.8, then apply
-- the owner theorem
-- `perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex`.
/-- Corollary 6.29.6 (1): if some slice of a convex bifunction `F` has infimum `⊥`, then every
parameter in `ri[𝕜](dom F)` has slice infimum `⊥`. -/
theorem perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜}
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hbot : ∃ u0 : U, perturbationFunction F u0 = ⊥)
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    perturbationFunction F u = ⊥ := by
  have hu' : u ∈ riDom[𝕜](perturbationFunction F) := by
    simpa using (mem_ri_dom_iff_mem_riDom_perturbationFunction).1 hu
  exact perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex
    (F := F) (hp_convex := perturbationFunction_isConvex hF) hbot hu'

end RelativeInterior

section OutsidePerturbationDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [InfSet β] [PartialOrder β] [OrderTop β]

-- Proof sketch: `u ∉ dom(perturbationFunction F)` is exactly
-- `¬ perturbationFunction F u < ⊤`; rewrite with `not_lt_top_iff`.
/-- Owner form of Corollary 6.29.6 (2): if `u` lies outside
`dom(perturbationFunction F)`, then `perturbationFunction F u = ⊤`. -/
theorem perturbationFunction_eq_top_of_not_mem_dom_perturbationFunction
    {F : U → X → β} {u : U}
    (hu : u ∉ dom(perturbationFunction F)) :
    perturbationFunction F u = ⊤ := by
  have hpu_not : ¬ perturbationFunction F u < ⊤ := by
    intro hpu
    exact hu ((_root_.mem_effectiveDomain (f := perturbationFunction F) (x := u)).2 hpu)
  exact (not_lt_top_iff).1 hpu_not

end OutsidePerturbationDomain

section OutsideDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

-- Proof sketch: by definition, `u ∉ dom F` means that every slice value `F u x` is `⊤`. The
-- perturbation function is the infimum of that slice, so its value at `u` is also `⊤`.
/-- Corollary 6.29.6 (2): if a parameter `u` lies outside the bifunction domain `dom F`, then the
slice infimum at `u` is `⊤`. -/
theorem perturbationFunction_eq_top_of_not_mem_dom
    {F : U → X → β} {u : U} (hu : u ∉ dom F) :
    perturbationFunction F u = ⊤ := by
  have hu' : u ∉ dom(perturbationFunction F) := by
    intro hpu
    exact hu ((mem_dom_perturbationFunction_iff_mem_dom).1 hpu)
  exact perturbationFunction_eq_top_of_not_mem_dom_perturbationFunction
    (F := F) hu'

end OutsideDomain

end Bifunction
