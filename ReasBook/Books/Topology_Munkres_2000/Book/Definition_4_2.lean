module

import Init

universe u

/- Definition 4.2: A binary operation on a type `A` is a function from `A × A` to
`A`. -/
#check (fun (A : Type u) ↦ A × A → A)
