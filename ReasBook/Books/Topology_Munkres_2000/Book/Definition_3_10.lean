module

import Mathlib.Order.Cover

universe u

public section

variable {X : Type u} [LinearOrder X] (a b : X)

/- Definition 3.10 (1): The open interval from `a` to `b` is the set of
elements `x` satisfying `a < x` and `x < b`. -/
#check Set.Ioo a b

/- Definition 3.10 (2): Under the standing assumption `a < b`, saying that
`a` is the immediate predecessor of `b` (equivalently, that `b` is the
immediate successor of `a`) is represented by the covering relation `a ⋖ b`. -/
#check (a ⋖ b)

end
