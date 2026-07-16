import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.6: a bifunction is proper exactly when its graph
function is proper. -/
scoped[Rockafellar] notation:70 "properᵇ(" F ")" =>
  Function.IsProper (Function.uncurry F)

end Rockafellar

section

open Function
open scoped Rockafellar

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [Bot β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.6 calls a bifunction proper when its graph function is proper.
- `core/canonical`: Definition 6.29.2 already identifies the graph function of `F` with the
  canonical uncurried map `uncurry F`, and Chapter 1 already owns properness for codomain values
  with `⊤`, `⊥`, and `<` through `Function.IsProper`, whose short owner surface is `f.IsProper`.
- `bridge/view`: later source-facing bifunction properness notions built from slice domains are
  different chapter-level owners and should not replace this graph-function properness definition.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `uncurry` as the graph-function owner from `Definition_6_29_2`;
- scoped notation `properᵇ(F)`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → β`;
- canonical owner surface: `(uncurry F).IsProper`;
- source-facing notation surface: `properᵇ(F)`;
- no extra wrapper declaration is needed, because the source definition is exactly this canonical
  owner usage.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → β)

/- Definition 6.29.6: a bifunction is proper exactly when its graph function from
Definition 6.29.2, namely `uncurry F`, is proper. The canonical owner expression for this notion
is `(uncurry F).IsProper`, with source-facing notation `properᵇ(F)`. -/
#check (properᵇ(F) : Prop)

end
