import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis

/-
Definition 3.2 is a source-facing recall of the finite-value domain of an extended-real-valued
function together with the standing assumption that this domain is nonempty.

Primary domain:
- convex analysis of `EReal`-valued functions through their finite-value domain.

Relevant declarations and owner-style recall sampled before refinement:
- `extendedRealEffectiveDomain`
- `extendedRealEffectiveDomain_nonempty_iff`
- `mem_extendedRealEffectiveDomain_iff`
- `(dom f).Nonempty`
- `Set.Nonempty`

Best owner abstraction:
- `extendedRealEffectiveDomain`

Primitive data:
- the owner set `dom f`

Derived API:
- `(dom f).Nonempty`
- `extendedRealEffectiveDomain_nonempty_iff`
- `mem_extendedRealEffectiveDomain_iff`
- the existential expansion of `Set.Nonempty`

Source/core/bridge triage:
- source-facing: the domain object `dom f` together with its standing nonemptiness assumption
- core/canonical: `extendedRealEffectiveDomain`
- bridge/view: `mem_extendedRealEffectiveDomain_iff`, `extendedRealEffectiveDomain_nonempty_iff`

This item therefore targets the source-facing owner layer directly: it recalls
`extendedRealEffectiveDomain` as the main entry and keeps the nonemptiness condition only as the
companion standing assumption. Since neither declaration uses Euclidean structure, the public
surface stays at the owner's arbitrary-domain level.
-/

recall extendedRealEffectiveDomain
    {X : Type _} (f : X → EReal) :
    Set X

recall extendedRealEffectiveDomain_nonempty_iff
    {X : Type _} {f : X → EReal} :
    (dom f).Nonempty ↔ ∃ x, f x ≠ ⊤ ∧ f x ≠ ⊥

section

variable {X : Type _} (f : X → EReal)

#check (dom f).Nonempty

end
