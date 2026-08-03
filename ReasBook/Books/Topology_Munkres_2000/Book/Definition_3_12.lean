module

import Mathlib.Order.Hom.Basic

universe u v

section

variable (A : Type u) (B : Type v) [LinearOrder A] [LinearOrder B]

/- Definition 3.12: Two linearly ordered types `A` and `B` have the same order
type when there exists a bijective correspondence between them preserving the
strict order, represented canonically by `Nonempty (A ≃o B)`. -/
#check Nonempty (A ≃o B)

end
