module

import Init

universe u

section

variable {A : Type u} (f : A × A → A)

local infixl:70 " ⋆ " => Function.curry f

/- Notation 4.1. A binary operation `f : A × A → A` is conventionally written
with a symbol between its inputs, as in `a ⋆ a'`. Lean obtains the corresponding
two-argument operation as `Function.curry f`, and `a ⋆ a'` reduces to
`f (a, a')`. Common operation symbols include `+`, `·`, `∘`, and `*`. -/
#check fun (a a' : A) ↦ a ⋆ a'

example (a a' : A) : a ⋆ a' = f (a, a') := rfl

end
