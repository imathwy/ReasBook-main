import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (X : Type u) (Y : Type v)

/- Definition 1.7.2 is `core/canonical`: an application from a set `X` to a set `Y` is the
function type `X → Y`, whose elements assign to each element of `X` a unique element of `Y`; when
`Y` is a set of numbers one also calls such an application a function. -/
#check (X → Y)

/- In the special case `X = Y`, the textbook term "transformation of `X`" is the canonical
endomorphism owner `Function.End X`. -/
#check Function.End X
