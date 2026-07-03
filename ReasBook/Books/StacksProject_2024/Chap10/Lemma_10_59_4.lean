import Mathlib
import StacksProject_2024.Chap10.Definition_10_59_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Ideal

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

namespace Ideal

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {I I' : Ideal R}

/-- Helper for Lemma 10.59.4: two ideals of definition in a Noetherian local ring compare by a
positive power inclusion. -/
private theorem exists_pos_pow_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ d : ℕ, 1 ≤ d ∧ I' ^ d ≤ I := by
  -- The common radical description puts `I'` inside `√I`, so a power of `I'` lands in `I`.
  have hleRad : I' ≤ I.radical := by
    calc
      I' ≤ I'.radical := Ideal.le_radical
      _ = IsLocalRing.maximalIdeal R := hI'
      _ = I.radical := hI.symm
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad I'.fg_of_isNoetherianRing
  refine ⟨c + 1, Nat.succ_le_succ (Nat.zero_le c), ?_⟩
  -- Replacing `c` by `c + 1` packages the witness as a positive exponent.
  calc
    I' ^ (c + 1) ≤ I' ^ c := Ideal.pow_le_pow_right (Nat.le_succ c)
    _ ≤ I := hc

/-- Helper for Lemma 10.59.4: the linear reindexing `n ↦ (2d - 1) n` makes the `I'`-power
quotient map surject onto the `I`-power quotient. -/
private theorem pow_smul_top_le_of_reindex
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {I I' : Ideal R} {d n : ℕ} (hd : I' ^ d ≤ I) (hdpos : 1 ≤ d) (hn : 1 ≤ n) :
    (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M)) ≤ I ^ (n + 1) • ⊤ := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hdpos)
  -- The arithmetic bound converts the positive-power containment into the exact smul inclusion
  -- needed for the quotient factor map.
  have hdecomp : 2 * Nat.succ c - 1 = 2 * c + 1 := by
    omega
  have hcn : c ≤ c * n := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_left c hn
  have hlast : c + 1 ≤ c * n + 1 := Nat.add_le_add_right hcn 1
  have hexp : Nat.succ c * (n + 1) ≤ ((2 * Nat.succ c - 1) * n) + 1 := by
    rw [hdecomp]
    calc
      Nat.succ c * (n + 1) = c * n + n + (c + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.succ_mul]
      _ ≤ c * n + n + (c * n + 1) := Nat.add_le_add_left hlast (c * n + n)
      _ = (2 * c + 1) * n + 1 := by
        calc
          c * n + n + (c * n + 1) = c * n + c * n + n + 1 := by
            ac_rfl
          _ = (c + c) * n + n + 1 := by rw [Nat.add_mul]
          _ = (2 * c) * n + n + 1 := by rw [two_mul]
          _ = (2 * c + 1) * n + 1 := by
            rw [Nat.add_mul, Nat.one_mul]
  have hpow : I' ^ (((2 * Nat.succ c - 1) * n) + 1) ≤ I ^ (n + 1) := by
    calc
      I' ^ (((2 * Nat.succ c - 1) * n) + 1) ≤ I' ^ (Nat.succ c * (n + 1)) :=
        Ideal.pow_le_pow_right hexp
      _ = (I' ^ Nat.succ c) ^ (n + 1) := by rw [pow_mul]
      _ ≤ I ^ (n + 1) := Ideal.pow_right_mono hd (n + 1)
  exact Submodule.smul_mono_left hpow

/-- Helper for Lemma 10.59.4: quotient length decreases when the quotient submodule gets larger. -/
private theorem length_quotient_le_of_submodule_le
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (h : N ≤ N') :
    Module.length R (M ⧸ N') ≤ Module.length R (M ⧸ N) := by
  -- The factor map `M ⧸ N → M ⧸ N'` is surjective, so module length can only decrease.
  exact Module.length_le_of_surjective
    (g := Submodule.factor h) (Submodule.factor_surjective h)

-- Proof sketch: since `I` and `I'` are ideals of definition, their radicals agree with the
-- maximal ideal, so mathlib's owner theorem `Ideal.exists_pow_le_of_le_radical_of_fg` gives a
-- power of `I'` contained in `I`. Then the quotient maps
-- `M / (I')^(c * (n + 1)) M → M / I^(n + 1) M`
-- compare the two `χ`-functions by surjectivity of the induced map on quotients. Rewriting
-- `c * (n + 1)` as `(2 * c - 1) * n + 1` for `n ≥ 1` gives the stated linear reindexing, with a
-- positive reindexing constant `a = 2 * c - 1`.
/-- Lemma 10.59.4: if `I` and `I'` are ideals of definition of the Noetherian local ring `R` and
`M` is a finite `R`-module, then the Hilbert-Samuel `χ`-function for `I` is eventually bounded
above by the Hilbert-Samuel `χ`-function for `I'` after multiplication by a positive integer. -/
theorem exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ ⦃n : ℕ⦄, 1 ≤ n →
      χ_ I M n ≤ χ_ I' M (a * n) := by
  -- First compare the two ideals of definition by a positive power containment.
  rcases exists_pos_pow_le_of_isIdealOfDefinition (I := I) (I' := I') hI hI'
    with ⟨d, hdpos, hd⟩
  refine ⟨2 * d - 1, ?_, ?_⟩
  · -- The source reindexing constant is positive because the witness exponent is positive.
    omega
  · intro n hn
    -- The quotient by the larger `I`-power is a quotient of the corresponding `I'`-power quotient.
    have hsmul :
        (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M)) ≤ I ^ (n + 1) • ⊤ :=
      pow_smul_top_le_of_reindex (M := M) (I := I) (I' := I') hd hdpos hn
    -- Compare the Hilbert-Samuel lengths through the induced surjective factor map.
    calc
      χ_ I M n = Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := rfl
      _ ≤ Module.length R (M ⧸ (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M))) :=
        length_quotient_le_of_submodule_le (M := M) hsmul
      _ = χ_ I' M ((2 * d - 1) * n) := rfl

/-- Canonical `atTop` reformulation of Lemma 10.59.4: after multiplying the index by a fixed
positive integer, the Hilbert-Samuel `χ`-function for one ideal of definition is eventually
bounded above by that for the other. This is the bridge from the source-facing `n ≥ 1`
formulation to the chapter's eventual-value API. -/
theorem exists_eventually_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      χ_ I M n ≤ χ_ I' M (a * n) := by
  rcases exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition M hI hI' with
    ⟨a, ha, hle⟩
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hle hn

end Ideal

end
