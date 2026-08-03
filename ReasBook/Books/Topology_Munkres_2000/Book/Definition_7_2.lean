module

public import Topology_Munkres_2000.Book.Definition_7_1

public section

universe u

/-- Definition 7.2 (1). A set is countable exactly when it is finite or countably
infinite. -/
theorem Set.countable_iff_finite_or_countablyInfinite {α : Type u} (s : Set α) :
    s.Countable ↔ s.Finite ∨ s.CountablyInfinite := by
  constructor
  · intro hs
    rcases s.finite_or_infinite with hsfin | hsinf
    · exact Or.inl hsfin
    · exact Or.inr ((Set.countablyInfinite_iff_countable_and_infinite s).2 ⟨hs, hsinf⟩)
  · rintro (hsfin | hsinf)
    · exact hsfin.countable
    · exact ((Set.countablyInfinite_iff_countable_and_infinite s).1 hsinf).1

/- Definition 7.2 (2). A set is uncountable exactly when it is not countable. -/
#check fun {α : Type u} (s : Set α) ↦
  (uncountable_iff_not_countable s : Uncountable s ↔ ¬ s.Countable)
