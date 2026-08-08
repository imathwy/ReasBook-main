import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 1.4.3: for a homotopy `H : p.Homotopy q` and a basepoint `x : X`, the basepoint
track is the path `H.evalAt x : Path (p x) (q x)` obtained by following the point `x` through the
homotopy, namely `t ↦ H (t, x)`. -/
recall ContinuousMap.Homotopy.evalAt {p q : C(X, Y)} (H : p.Homotopy q) (x : X) :
    Path (p x) (q x)

/- Evaluating a homotopy track at time `t` gives the value of the homotopy at `(t, x)`. -/
recall ContinuousMap.Homotopy.evalAt_apply {p q : C(X, Y)} (H : p.Homotopy q) (x : X)
    (t : ↑unitInterval) :
    (H.evalAt x) t = H (t, x)
