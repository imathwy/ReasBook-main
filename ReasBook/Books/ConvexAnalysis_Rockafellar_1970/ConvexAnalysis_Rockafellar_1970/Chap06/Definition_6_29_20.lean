import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/-- Definition 6.29.20, canonical source-facing statement: the generalized convex program
associated with a bifunction `F` is consistent exactly when the base perturbation belongs to the
bifunction domain. -/
@[simp] theorem isConsistent_iff (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom F :=
  isConsistent_iff_zero_mem_dom (F := F)

/-- Bridge to the zero-slice effective-domain wording: the source-facing condition `0 ∈ dom F`
is exactly nonemptiness of `dom (F 0)`. -/
@[simp] theorem isConsistent_iff_dom_zero_nonempty (F : U → X → β) :
    IsConsistent F ↔ (effectiveDomain (F 0)).Nonempty := by
  simp [IsConsistent]

end

end Bifunction
