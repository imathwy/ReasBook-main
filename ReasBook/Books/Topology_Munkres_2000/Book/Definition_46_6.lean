module

public import Mathlib.Topology.CompactOpen

public section

/-
Definition 46.6. Joint continuity of evaluation means that `(f, x) ↦ f x` is
continuous in the bundled map `f` and the point `x` simultaneously. Mathlib
expresses this property by `ContinuousEval`.
-/
#check ContinuousEval
#check continuous_eval
