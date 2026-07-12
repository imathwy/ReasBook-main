import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar] [Zero XStar]
variable [HasPairing (U × X) (UStar × XStar) L]
variable (F : U → X → L)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.16 says that the dual program attached to a bifunction `F`
  uses as objective the zero slice of the adjoint bifunction `F⋆`.
- `core/canonical`: the owner abstractions are already `adjoint XStar UStar F` for `F⋆` and
  `(·)₀` / `objective` for the zero-slice objective.
- `bridge/view`: there is no second owner here. The source dual objective is exactly the existing
  composite owner `((adjoint XStar UStar F)₀)`, equivalently `(F⋆)₀` on the theorem
  surface when the ambient dual types are already determined.

Primary mathematical domain:
- convex duality for bifunctions, specifically the adjoint-dual objective in Chapter 6.

Domain-style sampling used here:
- `Bifunction.objective` and `(·)₀` from `Definition_6_29_12`;
- `Bifunction.objective_apply` from `Definition_6_29_12`;
- `Bifunction.adjoint` and `(·)⋆` from `Definition_6_30_14`;
- `Bifunction.objective_adjoint_apply` from `Definition_6_30_14`.

Best owner abstraction:
- the canonical owner expression `((adjoint XStar UStar F)₀) :
    UStar → L`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- primitive owner reused directly: `adjoint XStar UStar F`;
- derived/source-facing view: its zero slice `((adjoint XStar UStar F)₀)`, written
  suggestively as `(F⋆)₀` when the dual ambient parameters are inferable.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.30.16 is the existing Chapter 6 owner expression for the zero-slice objective of
the adjoint bifunction. No separate `dualObjective` declaration is introduced here. -/
#check (((F⋆ : XStar → UStar → L)₀) : UStar → L)

end

end Bifunction
