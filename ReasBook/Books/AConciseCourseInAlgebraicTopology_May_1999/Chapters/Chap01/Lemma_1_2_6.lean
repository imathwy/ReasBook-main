import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {w x y z : X}

/- Lemma 1.2.6: composition of path classes is associative; for composable endpoint-fixed
homotopy classes `f`, `g`, and `h`, the classes of `(f.trans g).trans h` and
`f.trans (g.trans h)` coincide. -/
recall trans_assoc (f : Path.Homotopic.Quotient w x) (g : Path.Homotopic.Quotient x y)
    (h : Path.Homotopic.Quotient y z) :
    (f.trans g).trans h = f.trans (g.trans h)
