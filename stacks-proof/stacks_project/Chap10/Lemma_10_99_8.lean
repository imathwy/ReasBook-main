import Mathlib

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]

-- These three helper theorems were in the deleted backup directory and need to be re-proved.
private theorem flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (n : ℕ) (_ : 1 ≤ n) :
    Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M)) := by
  sorry

private theorem tor_one_vanishes_of_annihilated_by_ideal_pow
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    {N : Type u} [AddCommGroup N] [Module R N]
    (m : ℕ) (_ : I ^ m ≤ Module.annihilator R N) :
    IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := by
  sorry

private theorem flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (_ : IsNilpotent I) :
    Module.Flat R M := by
  sorry

/-- Lemma 10.99.8: if `M / IM` is flat over `R / I` and `Tor₁^R(R / I, M)` vanishes, then
`M / I^n M` is flat over `R / I^n` for all `n ≥ 1`; for every `R`-module `N` annihilated by a
power of `I`, `Tor₁^R(N, M)` vanishes; and if `I` is nilpotent, then `M` is flat over `R`. -/
theorem flatness_and_tor_vanishing_along_ideal_powers
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))) :
    (∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M))) ∧
      (∀ {N : Type u} [AddCommGroup N] [Module R N],
        (∃ m : ℕ, I ^ m ≤ Module.annihilator R N) →
          IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))) ∧
      (IsNilpotent I → Module.Flat R M) := by
  constructor
  · intro n hn
    exact flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes hflat htor n hn
  constructor
  · intro N _ _ hN
    rcases hN with ⟨m, hm⟩
    exact tor_one_vanishes_of_annihilated_by_ideal_pow hflat htor m hm
  · intro hI
    exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hflat htor hI

end
