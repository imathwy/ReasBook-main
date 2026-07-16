import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Order.WithBotTop
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Function

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.5: a bifunction is graph-closed exactly when its
graph function is lower semicontinuous. -/
scoped[Rockafellar] notation:70 "closedᵇ(" F ")" =>
  LowerSemicontinuous (Function.uncurry F)

end Rockafellar

namespace Bifunction

section

open scoped Rockafellar

variable {U : Type u} {X : Type v} {α : Type w}
variable [TopologicalSpace (U × X)]
variable [Preorder α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.5 calls a bifunction closed when its graph function is closed.
- `core/canonical`: the graph function is already the canonical uncurried map
  `uncurry F`, and the project's closedness owner for ordered-valued functions is
  `LowerSemicontinuous`; the primitive ambient structure is only a topology on the graph space
  `U × X`.
- `bridge/view`: later slice-wise closedness notions are downstream bridges from this global
  graph-function closedness and should not replace it here.

Domain-style sampling used here:
- `uncurry` (from `Function.uncurry`) as the graph-function owner from Definition 6.29.2;
- `LowerSemicontinuous` as the canonical closedness predicate for ordered-valued functions;
- `Bifunction.lowerSemicontinuous_slice_of_closedb` and
  `Bifunction.IsConvexClosed` in Chapter 7 as later bridges from the uncurried owner to slice-wise
  closedness.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop α`;
- primitive ambient structure: a topology on `U × X` (not separately on each factor);
- canonical owner surface: `LowerSemicontinuous (uncurry F)`;
- source-facing notation surface: `closedᵇ(F)`;
- derived bridge API: any slice-wise closedness consequences belong in later companion results,
  not in the owner for this definition.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → WithBotTop α)

/- Definition 6.29.5: a bifunction is graph-closed exactly when its graph function from
Definition 6.29.2, namely `uncurry F`, is lower semicontinuous on `U × X`. The canonical owner
expression for this notion is `LowerSemicontinuous (uncurry F)`, with source-facing notation
`closedᵇ(F)`. -/
#check (closedᵇ(F) : Prop)

end

end Bifunction
