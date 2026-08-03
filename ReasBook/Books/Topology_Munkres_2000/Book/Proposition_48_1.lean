module

public import Mathlib.Topology.Baire.Lemmas

public section

universe u

/-- Proposition 48.1. A topological space is a Baire space if and only if every
nonempty open subset is not meagre. -/
theorem baireSpace_iff_open_not_isMeagre {X : Type u} [TopologicalSpace X] :
    BaireSpace X ↔ ∀ U : Set X, IsOpen U → U.Nonempty → ¬ IsMeagre U := by
  constructor
  · intro _ U hU hUne
    exact not_isMeagre_of_isOpen hU hUne
  · intro h
    constructor
    intro f hopen hdense
    rw [dense_iff_inter_open]
    intro U hU hUne
    by_contra hinter
    apply h U hU hUne
    have hsubset : U ⊆ ⋃ n : ℕ, (f n)ᶜ := by
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_compl_iff]
      by_contra hxcompl
      push Not at hxcompl
      exact hinter ⟨x, hx, Set.mem_iInter.mpr hxcompl⟩
    have hunion : IsMeagre (⋃ n : ℕ, (f n)ᶜ) := by
      apply isMeagre_iUnion
      intro n
      apply IsNowhereDense.isMeagre
      rw [(hopen n).isClosed_compl.isNowhereDense_iff]
      exact (hdense n).interior_compl
    exact hunion.mono hsubset

end
