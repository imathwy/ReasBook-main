module

import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

universe u v w

open scoped DirectSum

/- Notation 67.2: If `i α : Gα α →+ G` exhibits `G` as an external direct sum,
the source informally writes `G = ⨁ α, Gα α` and identifies each `Gα α` with
the subgroup `(i α).range`. Lean retains the maps `i α` and their ranges explicitly.
The canonical realization uses `DirectSum.inclusion Gα α`. -/
#check AddMonoidHom.IsExternalDirectSum
#check AddMonoidHom.IsExternalDirectSum.injective
#check fun {ι : Type u} {G : Type w} [AddCommGroup G]
    (Gα : ι → Type v) [∀ α, AddCommGroup (Gα α)]
    (i : ∀ α, Gα α →+ G) [AddMonoidHom.IsExternalDirectSum i] (α : ι) ↦ (i α).range
#check fun {ι : Type u} (Gα : ι → Type v) [∀ α, AddCommGroup (Gα α)] ↦ (⨁ α, Gα α)
#check DirectSum.inclusion
#check DirectSum.inclusion_injective
#check DirectSum.instIsExternalDirectSum
