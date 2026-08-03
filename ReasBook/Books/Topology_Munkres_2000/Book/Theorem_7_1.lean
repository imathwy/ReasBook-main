module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.PNat.Basic

public section

universe u

open Equiv

/-- Theorem 7.1 (1). A nonempty type is countable if and only if it is the
surjective image of the positive integers `ℕ+`. -/
theorem countable_iff_exists_surjective_pnat (B : Type u) [Nonempty B] :
    Countable B ↔ ∃ f : ℕ+ → B, Function.Surjective f := by
  rw [countable_iff_exists_surjective]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f ∘ pnatEquivNat, hf.comp pnatEquivNat.surjective⟩
  · rintro ⟨f, hf⟩
    exact ⟨f ∘ pnatEquivNat.symm, hf.comp pnatEquivNat.symm.surjective⟩

/-- Theorem 7.1 (2). A type is countable if and only if it injects into the
positive integers `ℕ+`. -/
theorem countable_iff_exists_injective_pnat (B : Type u) :
    Countable B ↔ ∃ g : B → ℕ+, Function.Injective g := by
  rw [countable_iff_exists_injective]
  constructor
  · rintro ⟨g, hg⟩
    have h_pnat : Function.Injective pnatEquivNat.symm := pnatEquivNat.symm.injective
    exact ⟨pnatEquivNat.symm ∘ g, h_pnat.comp hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨pnatEquivNat ∘ g, pnatEquivNat.injective.comp hg⟩
