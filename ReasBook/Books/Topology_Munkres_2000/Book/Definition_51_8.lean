module

public import Mathlib.Topology.Path

public section

/- Definition 51.8: The textbook product of composable paths `f` and `g`,
identified with `f.trans g` in Definition 51.4, follows `f` on the first half of
`unitInterval` using the positive affine map `t ↦ 2 * t`, and follows `g` on the
second half using the positive affine map `t ↦ 2 * t - 1`. -/
#check Path.trans_apply
