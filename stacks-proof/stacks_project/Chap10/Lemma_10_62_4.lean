import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

-- Proof sketch: rewrite `support R M` as `zeroLocus (annihilator R M)` via
-- `support_eq_zeroLocus`; then `zeroLocus_subset_zeroLocus_iff` identifies the support inclusion
-- with `I ≤ (annihilator R M).radical`. Since `I` is finitely generated, this is equivalent to the
-- existence of `n` such that `I ^ n ≤ annihilator R M`; `Submodule.le_annihilator_iff` then
-- condition as the textbook criterion `(I ^ n) • (⊤ : Submodule R M) = ⊥`.
/-- Lemma 10.62.4, owner-facing form: for a finite module `M` and a finitely generated ideal `I`,
support of `M` is contained in `V(I)` if and only if some power of `I` is contained in the
annihilator of `M`. -/
theorem exists_pow_le_annihilator_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, I ^ n ≤ annihilator R M) ↔ support R M ⊆ zeroLocus I := by
  rw [support_eq_zeroLocus, zeroLocus_subset_zeroLocus_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        rw [pow_zero] at hn
        have htop : annihilator R M = ⊤ := by
          simpa [Ideal.one_eq_top] using hn
        simp [htop, Ideal.radical_top]
    | succ n =>
        calc
          I ≤ (I ^ (n + 1)).radical := by
            simpa [I.radical_pow n.succ_ne_zero] using (Ideal.le_radical : I ≤ I.radical)
          _ ≤ (annihilator R M).radical := Ideal.radical_mono hn
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h hI

/-- Lemma 10.62.4, textbook form: the same support criterion expressed by the vanishing condition
`(I ^ n) • (⊤ : Submodule R M) = ⊥`. -/
theorem exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = ⊥) ↔ support R M ⊆ zeroLocus I := by
  rw [← exists_pow_le_annihilator_iff_support_subset_zeroLocus I hI]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      simpa [Submodule.annihilator_top] using
        (Submodule.le_annihilator_iff.mpr hn : I ^ n ≤ (⊤ : Submodule R M).annihilator)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [Submodule.annihilator_top] using
      (Submodule.le_annihilator_iff.mp <| by
        simpa [Submodule.annihilator_top] using
          (hn : I ^ n ≤ annihilator R M) : I ^ n • (⊤ : Submodule R M) = ⊥)⟩

end Module

end
