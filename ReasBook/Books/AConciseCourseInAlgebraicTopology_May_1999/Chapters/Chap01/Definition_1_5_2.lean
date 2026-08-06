module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.5.2: the circle `S^1` is the unit circle in `ℂ`, represented in mathlib by
`Circle`; it is used with its multiplicative topological group structure and with chosen
basepoint `1`. -/
recall Circle : Type

/- Elements of `Circle` are complex numbers of norm `1`. -/
recall Circle.norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1

/- The circle has its canonical multiplicative commutative group structure. -/
recall Circle.instCommGroup : CommGroup Circle

/- The circle has its canonical topological group structure under multiplication. -/
recall Circle.instIsTopologicalGroup : IsTopologicalGroup Circle

/- The chosen basepoint on the circle is the unit complex number `1`. -/
recall Circle.coe_one : ((1 : Circle) : ℂ) = (1 : ℂ)
