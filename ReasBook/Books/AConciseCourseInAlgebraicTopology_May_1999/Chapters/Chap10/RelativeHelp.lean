import Mathlib.Topology.Homotopy.Basic

universe u v w

open Set

variable {W : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map `e : C(Y, Z)` has the relative HELP with respect to an inclusion
`i : C(A, X)` when every compatible boundary map `A → Y` and ambient map `X → Z` admit a lift
`X → Y` together with a homotopy rel `range i`. -/
def HasRelativeHelp {A X : Set W} (i : C(A, X)) (e : C(Y, Z)) : Prop :=
  ∀ (fA : C(A, Y)) (gX : C(X, Z)),
    e.comp fA = gX.comp i →
      ∃ (F : C(X, Y)) (_ : (e.comp F).HomotopyRel gX (range i)),
        F.comp i = fA
