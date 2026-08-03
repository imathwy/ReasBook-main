module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE

public section

universe u

/-- Helper for Corollary 6.7: a nonempty finite type is equivalent to a
nonempty finite section `Fin (n + 1)`. -/
private lemma existsEquivFinSucc (B : Type u) [Finite B] [Nonempty B] :
    ∃ n : ℕ, Nonempty (B ≃ Fin (n + 1)) := by
  -- Equip `B` with a finite enumeration and write its positive cardinal as a successor.
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨n, hcard⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := B))
  -- The cardinal equality gives the required equivalence with the finite section.
  exact ⟨n, ⟨Fintype.equivFinOfCardEq hcard⟩⟩

/-- Corollary 6.7. For a nonempty type `B`, finiteness, being a surjective image
of some nonempty `Fin (n + 1)`, and admitting an injection into some nonempty
`Fin (n + 1)` are equivalent. -/
theorem finite_surjective_injective_fin_tfae (B : Type u) [Nonempty B] :
    List.TFAE [
      Finite B,
      ∃ n : ℕ, ∃ f : Fin (n + 1) → B, Function.Surjective f,
      ∃ n : ℕ, ∃ f : B → Fin (n + 1), Function.Injective f] := by
  -- A finite nonempty type is the surjective image of a suitable finite section.
  tfae_have 1 → 2 := by
    intro hFinite
    letI : Finite B := hFinite
    obtain ⟨n, ⟨e⟩⟩ := existsEquivFinSucc B
    exact ⟨n, e.symm, e.symm.surjective⟩
  -- A right inverse of a surjection supplies the required injection.
  tfae_have 2 → 3 := by
    rintro ⟨n, f, hf⟩
    classical
    exact ⟨n, Function.surjInv hf, Function.injective_surjInv hf⟩
  -- An injection into a finite section makes the domain finite.
  tfae_have 3 → 1 := by
    rintro ⟨n, f, hf⟩
    exact Finite.of_injective f hf
  -- The three implications form the desired equivalence cycle.
  tfae_finish

/-- A nonempty type is finite if and only if it is the surjective image of some
nonempty finite section `Fin (n + 1)`. -/
theorem finite_iff_exists_surjective_fin (B : Type u) [Nonempty B] :
    Finite B ↔ ∃ n : ℕ, ∃ f : Fin (n + 1) → B, Function.Surjective f := by
  -- Project the first two conditions from the established three-way equivalence.
  exact (finite_surjective_injective_fin_tfae B).out 0 1

/-- A nonempty type is finite if and only if it injects into some nonempty finite
section `Fin (n + 1)`. -/
theorem finite_iff_exists_injective_fin (B : Type u) [Nonempty B] :
    Finite B ↔ ∃ n : ℕ, ∃ f : B → Fin (n + 1), Function.Injective f := by
  -- Project the first and third conditions from the established equivalence.
  exact (finite_surjective_injective_fin_tfae B).out 0 2
