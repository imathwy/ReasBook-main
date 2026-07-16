import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_30

noncomputable section

universe u v r

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.0.2 identifies the adjoint bifunction of the singleton-graph
  indicator equation with the singleton-graph concave-indicator equation attached to a dual
  companion map.
- `core/canonical`: this equation is already owned by the Chapter 33 theorem
  `pairingEquation_graphIndicator_of_isPairingCompanion`.
- `bridge/view`: map compatibility is represented by the Chapter 33 owner
  `IsPairingCompanion`.

Primary mathematical domain:
- bifunction adjoints and singleton-graph indicator kernels of maps.

Domain-style sampling used here:
- `graphIndicator` and `graphConcaveIndicator` from `Chap06.Definition_6_29_9`;
- `IsPairingCompanion` and
  `pairingEquation_graphIndicator_of_isPairingCompanion` from `Chap07.Lemma33_0_30`;
- the pairing notations `⟪·, ·⟫ᶠ`, `⟪·, ·⟫ᶜ`, and `⟪·, ·⟫ₚ`.

Primitive data vs derived API:
- primitive source data: a map `A` and a dual companion map `Astar`;
- primitive owner expression:
  `pairingEquation_graphIndicator_of_isPairingCompanion`;
- derived API: the source-labeled proposition theorem below.

Layer target:
- `source-facing` as a thin source-label bridge over the canonical Chapter 33 owner theorem.
-/

section PairingEquation

variable {𝕜 : Type r} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [AddGroup 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

local instance : HasPairing UStar U 𝕜 := HasPairing.swap

-- Proof sketch: Proposition 38.0.2 is exactly the Chapter 33 singleton-graph pairing equation
-- under the global companion hypothesis, so this file keeps only a source-labeled bridge.
/-- Proposition 38.0.2: if `Astar` is a pairing companion of `A`, then the singleton-graph
pairing equation holds at every point. -/
theorem proposition_38_0_2
    (A : U → X) (Astar : XStar → UStar)
    (hA : IsPairingCompanion A Astar)
    (u : U) (xStar : XStar) :
    ⟪graphIndicator 𝕜 A u, xStar⟫ᶠ = ⟪u, graphConcaveIndicator 𝕜 Astar xStar⟫ᶜ := by
  exact pairingEquation_graphIndicator_of_isPairingCompanion A Astar hA u xStar

end PairingEquation

end Bifunction
