module

import Mathlib.Logic.Function.Basic

universe u v

variable {J : Type u} (X : J → Type v) (β : J)

/- Definition 19.8: The projection mapping associated with `β : J` sends an
element `x : (α : J) → X α` of the product to its `β`-coordinate `x β`. -/
#check (Function.eval β : ((α : J) → X α) → X β)
