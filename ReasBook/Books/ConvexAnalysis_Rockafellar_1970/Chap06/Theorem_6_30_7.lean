import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.7 says that for a concave bifunction `G`, the perturbation
  function `sup G` is concave and its effective domain is exactly the set of parameters whose
  slices are not identically `-∞`.
- `core/canonical`: the chapter owners already present are `concᵇ[𝕜](G)` for the
  bifunction hypothesis, `upperPerturbationFunction G` for the perturbation function, and the
  Chapter 1 concave-side effective-domain owner `dom(-f)` for a function `f`.
- `bridge/view`: the textbook phrase “`G u` is not identically `-∞`” is rendered directly by the
  slice-wise existence condition `∃ x, ⊥ < G u x`, rather than by reusing the convex-side
  bifunction-domain owner `dom G`, whose meaning is tied to the `+∞` / infimum orientation.

Domain-style sampling used here:
- `concᵇ[𝕜](G)` from `Definition_6_30_8`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Function.IsConcave` from `Definition_6_30_2`, which is the owner of the conclusion in part
  (1);
- `dom(-f)` and `mem_dom_neg_iff` from `Definition_6_30_1`, which give the canonical
  effective-domain surface for concave functions.

Primitive data vs derived API:
- primitive source data: a bifunction `G : U → X → WithBotTop α`;
- primitive owner hypothesis: `concᵇ[𝕜](G)`;
- derived owner in part (1): `(supᵇ(G)).IsConcave 𝕜`;
- derived owner in part (2): `dom(- supᵇ(G))`, with the source-facing slice
  criterion `∃ x, ⊥ < G u x`.

Layer target:
- part (1): `source-facing`, stated directly on the canonical upper-perturbation owner;
- part (2): `bridge/view`, expressing the textbook `dom(sup G) = dom G` as the canonical
  effective-domain equality for `supᵇ(G)` and the source slice criterion.
-/

section

variable {𝕜 : Type z} [Semiring 𝕜] [PartialOrder 𝕜]
variable {U : Type u} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {α : Type w} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]

/-- Theorem 6.30.7 (1): if `G` is a concave bifunction, then its perturbation function `sup G`,
rendered canonically as `supᵇ(G)`, is concave on the parameter space. -/
theorem upperPerturbationFunction_isConcave_of_isConcave
    (G : U → X → WithBotTop α) (hG : concᵇ[𝕜](G)) :
    (supᵇ(G)).IsConcave 𝕜 := by
  sorry

end

-- Proof sketch: use the Chapter 6 domain bridge `u ∈ dom(-f) ↔ ⊥ < f u` with
-- `f := supᵇ(G)`, then rewrite
-- `supᵇ(G) u = ⨆ x, G u x`. The indexed supremum is strictly above `⊥`
-- exactly when some slice value is strictly above `⊥`, which is the source condition that
-- `G u` is not identically `-∞`.
/- Theorem 6.30.7 (2): the effective domain of `sup G`, rendered canonically as
`dom(- supᵇ(G))`, is exactly the set of parameters `u` for which the slice
`G u` is not identically `-∞`, i.e. for which some `x` satisfies `⊥ < G u x`. This is the
source equality `dom(sup G) = dom G`.

This clause only uses the order and negation structure on the codomain together with the base
types `U` and `X`, so the additive/module hypotheses from part `(1)` are intentionally omitted
here. -/
section

variable {α : Type w} [ConditionallyCompleteLattice α]
variable {U : Type u} {X : Type v}

theorem bot_lt_upperPerturbationFunction_iff_exists_bot_lt
    (G : U → X → WithBotTop α) (u : U) :
    ⊥ < supᵇ(G) u ↔ ∃ x : X, ⊥ < G u x := by
  rw [upperPerturbationFunction_apply]
  exact (bot_lt_iSup : (⊥ < ⨆ x : X, G u x) ↔ ∃ x : X, ⊥ < G u x)

variable [Neg α]

theorem effectiveDomain_neg_upperPerturbationFunction_eq_setOf_exists_bot_lt
    (G : U → X → WithBotTop α) :
    dom(- supᵇ(G)) = {u : U | ∃ x : X, ⊥ < G u x} := by
  rw [dom_neg_eq_setOf_bot_lt (supᵇ(G))]
  ext u
  exact bot_lt_upperPerturbationFunction_iff_exists_bot_lt (G := G) (u := u)

end

end Bifunction
