module

public import Mathlib.Logic.Equiv.Fin.Basic

public section

universe u

/-- Lemma 6.1: A type `A` is equivalent to `Fin (n + 1)` if and only if the subtype
obtained by removing a distinguished element `a₀` is equivalent to `Fin n`. -/
theorem equivFinSucc_iff_equivSubtypeNe {A : Type u} (a₀ : A) (n : ℕ) :
    Nonempty (A ≃ Fin (n + 1)) ↔ Nonempty ({a : A // a ≠ a₀} ≃ Fin n) := by
  classical
  constructor
  · rintro ⟨e⟩
    let E : Option {a : A // a ≠ a₀} ≃ Option (Fin n) :=
      (Equiv.optionSubtypeNe a₀).trans (e.trans (finSuccEquiv' (e a₀)))
    exact ⟨E.removeNone⟩
  · rintro ⟨e⟩
    exact ⟨(Equiv.optionSubtypeNe a₀).symm.trans
      ((Equiv.optionCongr e).trans (finSuccEquiv n).symm)⟩
