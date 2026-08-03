module

public import Mathlib.Data.Set.Card

public section

universe u

namespace Set

/-- Corollary 6.3. If `A` is finite, then it is not equivalent to any proper subset
`B` of itself. -/
theorem Finite.not_equiv_ssubset {α : Type u} {A B : Set α} (hA : A.Finite)
    (hBA : B ⊂ A) : ¬ Nonempty (A ≃ B) := by
  rintro ⟨e⟩
  exact ((hA.subset hBA.subset).encard_lt_encard hBA).ne (encard_congr e).symm

end Set
