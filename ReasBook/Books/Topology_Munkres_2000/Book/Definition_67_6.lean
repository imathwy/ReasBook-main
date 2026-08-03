module

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

universe u v

/- Definition 67.6. If `G` is a free abelian group with a finite basis, its rank is
`Module.finrank ℤ G`; `Module.finrank_eq_card_basis` identifies this rank with the
number of elements in any finite basis. -/
#check fun (G : Type u) [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] ↦
  Module.finrank ℤ G
#check fun {G : Type u} [AddCommGroup G] {ι : Type v} [Fintype ι]
    (b : Module.Basis ι ℤ G) ↦ Module.finrank_eq_card_basis b
