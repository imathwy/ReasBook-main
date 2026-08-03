module

public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap

public section

universe u v

open FundamentalGroup.LeftToRight

/- Notation 52.3: For `h : C(X, Y)` and a chosen basepoint `x₀ : X`, the
textbook homomorphism `(h₍x₀₎)₊` is `FundamentalGroup.LeftToRight.map h x₀`, with
codomain basepoint determined as `h x₀`. Fundamental groups at different basepoints
remain distinct types even when an explicit path induces an isomorphism between them. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X, Y)) (x₀ : X) ↦ (h₍x₀₎)₊
