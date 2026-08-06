import Mathlib.Tactic.Recall
import Mathlib.Topology.CompactOpen

universe u v w

-- Semantic recall: `ContinuousMap.curry`, `ContinuousMap.uncurry`, and `Homeomorph.curry`.

/- Principle 6.1.2: the Eckmann-Hilton style duality between cofibrations and fibrations in
this chapter is organized by the canonical adjunction between cartesian products and function
spaces, formalized in mathlib by currying and uncurrying for continuous maps together with the
resulting homeomorphism of compact-open mapping spaces. -/
recall ContinuousMap.curry
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
      C(X × Y, Z) → C(X, C(Y, Z))

recall ContinuousMap.uncurry
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace Y] :
      C(X, C(Y, Z)) → C(X × Y, Z)

recall Homeomorph.curry
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] :
      C(X × Y, Z) ≃ₜ C(X, C(Y, Z))
