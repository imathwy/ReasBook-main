import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [Invertible (Nat.card G : k)]

-- Source/core/bridge triage:
-- * source-facing: a character supported at the identity is a multiple of the regular character.
-- * core/canonical owners: `Representation.character`,
--   `Representation.card_inv_mul_sum_char_eq_finrank`, and `leftRegular_character_eq_ite`.
-- * bridge/view: the support hypothesis collapses the character average to the identity term, and
--   `Representation.char_one` together with the companion lemmas
--   `leftRegular_character_one` and `leftRegular_character_eq_zero_of_ne_one` converts that scalar
--   identity into the claimed pointwise equality of characters.
-- Proof sketch: the canonical averaging formula
-- `Representation.card_inv_mul_sum_char_eq_finrank` identifies the normalized average of
-- `ρ.character` with `dim ρ.invariants`. Because `ρ.character` vanishes off `1`, that average is
-- exactly `ρ.character 1 / |G|`. Proposition `leftRegular_character_eq_ite` and its companion
-- lemmas identify `(leftRegular k G).character` as the function supported at `1` with value `|G|`,
-- so `ρ.character` is precisely `dim ρ.invariants` copies of the regular character.
/-- Exercise 2-2.4-5: over a field in which `|G|` is invertible, a character that vanishes on
every nonidentity element of a finite group is the `dim V^G`-fold multiple of the regular
character `(leftRegular k G).character`, hence in particular a natural-number multiple of it. -/
theorem character_eq_nsmul_leftRegular_character_of_eq_zero_off_one
    (ρ : Representation k G V) (hχ : ∀ s : G, s ≠ 1 → ρ.character s = 0) :
    ρ.character = Module.finrank k ρ.invariants • (leftRegular k G).character := by
  letI : Fintype G := Fintype.ofFinite G
  have hsum : ∑ t : G, ρ.character t = ρ.character 1 := by
    classical
    rw [Finset.sum_eq_single 1]
    · intro t _ ht
      exact hχ t ht
    · intro h
      exact False.elim <| h (Finset.mem_univ 1)
  have havg :
      (Nat.card G : k)⁻¹ * Module.finrank k V = Module.finrank k ρ.invariants := by
    simpa [hsum, ρ.char_one] using ρ.card_inv_mul_sum_char_eq_finrank
  have hdim :
      (Module.finrank k V : k) =
        (Nat.card G : k) * Module.finrank k ρ.invariants := by
    have hcard : (Nat.card G : k) ≠ 0 := NeZero.ne (Nat.card G : k)
    exact (inv_mul_eq_iff_eq_mul₀ hcard).mp <| by simpa using havg
  ext s
  by_cases hs : s = 1
  · subst hs
    simpa [Pi.smul_apply, leftRegular_character_one, nsmul_eq_mul, ρ.char_one, mul_comm] using
      hdim
  · rw [hχ s hs, Pi.smul_apply, leftRegular_character_eq_zero_of_ne_one hs, nsmul_eq_mul]
    simp

end

end

end Representation
