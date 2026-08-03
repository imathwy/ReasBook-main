module

public import Mathlib.Algebra.Group.Action.Basic

public section

/- Definition 81.7: For a group action of `G` on `X`, fixed-point freeness is the
canonical `IsCancelSMul G X` condition. Its pointwise characterization says that
`g • x = x` implies `g = 1`. -/
#check IsCancelSMul
#check isCancelSMul_iff_eq_one_of_smul_eq
