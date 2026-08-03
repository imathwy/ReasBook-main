module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.RelClasses

public section

universe u

/- Definition 11.5: A strict partial order determines a partial order by
adjoining equality; set inclusion is the partial order corresponding to proper
inclusion. -/
#check partialOrderOfSO
#check le_iff_lt_or_eq
#check fun (α : Type u) ↦ (inferInstance : PartialOrder (Set α))
#check fun (α : Type u) ↦ (inferInstance : IsStrictOrder (Set α) (· ⊂ ·))
#check Set.ssubset_iff_subset_ne

end
