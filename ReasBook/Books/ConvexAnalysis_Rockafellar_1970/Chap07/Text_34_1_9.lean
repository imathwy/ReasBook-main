import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.9 identifies closed saddle-functions by the two mixed closure
  identities `cl₁ (cl₂ K) = cl₁ K` and `cl₂ (cl₁ K) = cl₂ K`.
- `core/canonical`: the natural owner abstraction is the Chapter 34 closedness predicate
  `SaddleFunction.IsClosed` together with its canonical characterization theorem
  `SaddleFunction.isClosed_iff`.
- `bridge/view`: this item is therefore a pure recall of that canonical owner theorem, rather than
  a second local reconstruction of the partial-closure operators or equivalence relation.

Primary mathematical domain:
- saddle-functions, partial closures, and closedness in minimax theory.

Domain-style sampling used here:
- `Bifunction.closure1` and `Bifunction.closure2` from `Chap07.Definition33_0_4`;
- `SaddleFunction.IsClosed` from `Chap07.Defn_34_2`;
- `SaddleFunction.isClosed_iff` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → X → WithBotTop 𝕜`;
- primitive owner layer already provided upstream: the partial closures `cl₁`, `cl₂` and the
  closedness predicate `SaddleFunction.IsClosed` on the canonical extended codomain layer;
- derived API for this item: the mixed-closure characterization of that owner predicate.

Layer target: `bridge/view`, via direct reuse of the existing canonical Chapter 34 theorem.
-/

/- Text 34.1.9: the Chapter 34 closedness criterion says that a saddle-function is closed exactly
when the mixed closure identities `cl₁ (cl₂ K) = cl₁ K` and `cl₂ (cl₁ K) = cl₂ K` hold. -/
recall SaddleFunction.isClosed_iff
