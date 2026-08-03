module

public import Mathlib.GroupTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Free

public section

universe u

namespace Group

/-- Every finitely generated group is countable. -/
instance instCountableOfFG (G : Type u) [Group G] [FG G] : Countable G := by
  obtain ⟨S, hS, φ, hφ⟩ := fg_iff_exists_freeGroup_hom_surjective.mp (inferInstance : FG G)
  -- Local instance justification (proof-local temporary data): `hS` counts only the source of `φ`.
  letI : Countable S := hS.to_countable
  exact hφ.countable

end Group

end
