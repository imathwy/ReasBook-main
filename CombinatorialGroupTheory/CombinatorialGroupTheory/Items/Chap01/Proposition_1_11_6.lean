import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {U : Type u} (G : Type v) [Group G]
variable (R₁ R₂ : Set (FreeGroup U))

/- Proposition 1-11-6: saying that `G` has presentation `(U; R₁, R₂)` adds no new owner beyond
mathlib's canonical presented-group construction. Accordingly, the file keeps the direct recall
`PresentedGroup (R₁ ∪ R₂) ≃* G` rather than a parallel local wrapper for “`G` has presentation
`(U; R₁, R₂)`”. -/
#check (PresentedGroup (R₁ ∪ R₂) ≃* G)

end
