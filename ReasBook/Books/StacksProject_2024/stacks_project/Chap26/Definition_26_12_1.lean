import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Source/core/bridge triage for Definition 26.12.1:
- primary domain: reduced schemes.
- inspected owner declarations: `IsReduced`, `isReduced_stalk_of_isReduced`, and
  `isReduced_of_isReduced_stalk`.
- best owner abstraction: the canonical scheme property `IsReduced`, with the stalkwise bridge
  theorems as immediate source-facing companions.
- layer: `core/canonical`; this numbered item is a direct recall of the ambient reducedness owner.
-/

/- Definition 26.12.1: the canonical notion of a reduced scheme is `AlgebraicGeometry.IsReduced`.
-/
recall IsReduced

/- Companion recalls: a scheme is reduced exactly when its stalks are reduced. -/
recall isReduced_stalk_of_isReduced
recall isReduced_of_isReduced_stalk

end AlgebraicGeometry
