import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (S : Type u)

/- Definition 1.1.4: a binary operation on a type `S` is a curried map `S → S → S`,
equivalently a product map `S × S → S`. -/
#check (S → S → S)

/- The product-map presentation of a binary operation is converted to the curried presentation by
`Function.curry`. -/
#check (Function.curry : (S × S → S) → S → S → S)

/- The curried presentation of a binary operation is converted to the product-map presentation by
`Function.uncurry`. -/
#check (Function.uncurry : (S → S → S) → S × S → S)

/- Currying and then uncurrying a product-map binary operation recovers the original map. -/
#check (Function.uncurry_curry : ∀ f : S × S → S, Function.uncurry (Function.curry f) = f)

/- Uncurrying and then currying a curried binary operation recovers the original operation. -/
#check (Function.curry_uncurry : ∀ f : S → S → S, Function.curry (Function.uncurry f) = f)
