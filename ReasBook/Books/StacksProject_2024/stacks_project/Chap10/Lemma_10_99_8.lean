import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]

variable
  (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
  (htor :
    IsZero
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))

-- Proof sketch: first prove the Tor-vanishing statement for all modules annihilated by a power of
-- `I`; then identify `N ⊗[R / I ^ n] (M / I ^ n M)` with `N ⊗[R] M` for modules annihilated by
-- `I ^ n`, and conclude that tensoring with `M / I ^ n M` over `R / I ^ n` is exact.
/-- Lemma 10.99.8 (1): if `M / IM` is flat over `R / I` and `Tor₁^R(R / I, M)` vanishes, then
`M / I^n M` is flat over `R / I^n` for every `n ≥ 1`. -/
theorem flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (n : ℕ) (hn : 1 ≤ n) :
    Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M)) := sorry

-- Proof sketch: argue by induction on `m`; the case `m = 1` uses flatness of `M / IM` over
-- `R / I` together with the assumed vanishing of `Tor₁^R(R / I, M)`, and the induction step uses
-- the long exact sequence of `Tor` for `0 → IN → N → N / IN → 0`.
/-- Lemma 10.99.8 (2): if `M / IM` is flat over `R / I` and `Tor₁^R(R / I, M)` vanishes, then
`Tor₁^R(N, M)` vanishes for every `R`-module `N` annihilated by some power of `I`. -/
theorem tor_one_vanishes_of_annihilated_by_ideal_pow
    {N : Type u} [AddCommGroup N] [Module R N] (m : ℕ)
    (hN : I ^ m ≤ Module.annihilator R N) :
    IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := sorry

-- Proof sketch: choose `n` with `I ^ n = 0`; then the previous flatness statement gives
-- flatness of `M / I ^ n M` over `R / I ^ n`, and these identify with `M` and `R` respectively.
/-- Lemma 10.99.8 (3): if `I` is nilpotent, `M / IM` is flat over `R / I`, and
`Tor₁^R(R / I, M)` vanishes, then `M` is flat over `R`. -/
theorem flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    (hI : IsNilpotent I) :
    Module.Flat R M := sorry

end
