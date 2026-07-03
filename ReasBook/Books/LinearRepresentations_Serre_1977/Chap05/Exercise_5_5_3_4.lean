import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_3
import LinearRepresentations_Serre_1977.Chap05.Proposition_5_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section
open scoped DihedralCharacter

/- Source/core/bridge triage:
- `source-facing`: the Chapter 5 character identities for `χ_h`, `ψ₁`, and `ψ₂`;
- `core/canonical`: the existing owners `ρ[n] ^ h`, `Representation.character`, `Sym²`, `Alt²`,
  and `Representation.char_symmetricSquare_add_char_alternatingSquare`;
- `bridge/view`: this file only identifies the source-facing dihedral characters with the canonical
  symmetric- and alternating-square character owners.

Primitive data already lives in `Proposition_5_5_3_2` and `Proposition_2_2_1_3`. This file should
therefore keep only source-facing consequences and direct reuse of those owners, without adding a
parallel wrapper API. -/

section

variable (n : ℕ) [NeZero n]

-- Proof sketch: evaluate both sides on rotations and reflections using the explicit formulas from
-- Proposition 5-5.3-2 and the multiplicativity relation for the cyclic characters appearing on the
-- rotation subgroup.
/-- Exercise 5-5.3-4: the product of the dihedral characters `χ_h` and `χ_{h'}` is
`χ_{h + h'} + χ_{h - h'}`. -/
theorem dihedralTwoDimensionalCharacter_mul (h h' : ZMod n) :
    χ_ h * χ_ h' = χ_ (h + h') + χ_ (h - h') := by
  ext g
  cases g with
  | r k =>
      -- On rotations, expand every `χ` into the two cyclic characters from Proposition 5-5.3-2.
      simp only [Pi.mul_apply, Pi.add_apply, dihedralTwoDimensionalCharacter_apply_r]
      -- The four target summands are exactly the additive-character products indexed by
      -- `h + h'`, `h - h'`, `-(h + h')`, and `-(h - h')`.
      have hadd :
          AddChar.zmodAddEquiv (h + h') k =
            AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv h' k := by
        simpa using congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h h')
      have hsub :
          AddChar.zmodAddEquiv (h - h') k =
            AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h') k := by
        simpa [sub_eq_add_neg] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h (-h')))
      have hnegadd :
          AddChar.zmodAddEquiv (-(h + h')) k =
            AddChar.zmodAddEquiv (-h) k * AddChar.zmodAddEquiv (-h') k := by
        simpa [add_comm] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv (-h) (-h')))
      have hnegsub :
          AddChar.zmodAddEquiv (-(h - h')) k =
            AddChar.zmodAddEquiv (-h) k * AddChar.zmodAddEquiv h' k := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv (-h) h'))
      rw [hadd, hsub, hnegadd, hnegsub]
      ring
  | sr k =>
      -- On reflections, every two-dimensional dihedral character vanishes.
      simp [Pi.mul_apply, Pi.add_apply, dihedralTwoDimensionalCharacter_apply_sr]

-- Proof sketch: specialize `dihedralTwoDimensionalCharacter_mul` to `h' = h` and simplify the
-- two indices `h + h` and `h - h`.
/-- Squaring `χ_h` gives `χ_{2h} + χ_0` in LinearRepresentations_Serre_1977's notation. -/
theorem dihedralTwoDimensionalCharacter_mul_self (h : ZMod n) :
    χ_ h * χ_ h = χ_ (h + h) + χ_ (0 : ZMod n) := by
  simpa using dihedralTwoDimensionalCharacter_mul n h h

-- Proof sketch: evaluate `χ_0` on rotations and reflections from the explicit formulas in
-- Proposition 5-5.3-2 and compare with the values of the trivial and reflection-sign characters.
/-- The character `χ_0` decomposes as the sum `ψ₁ + ψ₂`. -/
theorem dihedralTwoDimensionalCharacter_zero_eq_trivial_add_reflectionSign :
    χ_ (0 : ZMod n) = ψ₁[n] + ψ₂[n] := by
  ext g
  cases g with
  | r k =>
      -- On rotations, `χ_0` and `ψ₁ + ψ₂` both reduce to `1 + 1`.
      rw [Pi.add_apply, dihedralTwoDimensionalCharacter_apply_r, dihedralTrivialCharacter_apply,
        dihedralReflectionSignCharacter_apply_r]
      simp [AddChar.circleEquivComplex]
  | sr k =>
      -- On reflections, `χ_0` is zero and `ψ₁ + ψ₂` is `1 + (-1)`.
      rw [Pi.add_apply, dihedralTwoDimensionalCharacter_apply_sr, dihedralTrivialCharacter_apply,
        dihedralReflectionSignCharacter_apply_sr]
      norm_num

section SymmetricAlternatingSquareCharacters

variable (h : ZMod n)

-- Proof sketch: apply the alternating-square character formula from Proposition 2-2.1-3 to
-- `ρ^h`, then use the explicit values of `χ_h` on rotations and reflections to identify the
-- resulting one-dimensional character.
/-- The reflection-sign character `ψ₂` is the character of the alternating square of `ρ^h`. -/
theorem dihedralAlternatingSquare_character_eq_reflectionSign :
    (Alt² (ρ[n] ^ h)).character = ψ₂[n] := by
  ext g
  cases g with
  | r k =>
      -- On rotations, the alternating-square character is the half-difference formula from
      -- Proposition 2-2.1-3 applied to the explicit values of `χ_h`.
      rw [Representation.char_alternatingSquare]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      rw [show (DihedralGroup.r k : DihedralGroup n) ^ 2 = DihedralGroup.r (k + k) by
        simp [pow_two]]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      -- The two cyclic summands are inverse to each other, so the half-difference collapses to `1`.
      have hzero :
          AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h) k = 1 := by
        have hsum :
            AddChar.zmodAddEquiv (h + -h) k =
              AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h) k := by
          simpa using congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h (-h))
        simpa [AddChar.circleEquivComplex] using hsum.symm
      have hsq :
          AddChar.zmodAddEquiv h (k + k) = AddChar.zmodAddEquiv h k ^ 2 := by
        simpa [pow_two] using AddChar.map_add_eq_mul (AddChar.zmodAddEquiv h) k k
      have hsq_neg :
          AddChar.zmodAddEquiv (-h) (k + k) = AddChar.zmodAddEquiv (-h) k ^ 2 := by
        simpa [pow_two] using AddChar.map_add_eq_mul (AddChar.zmodAddEquiv (-h)) k k
      rw [hsq, hsq_neg]
      -- After rewriting `χ_h(r^{2k})` as the sum of squares, the half-difference reduces to `1`.
      field_simp [two_ne_zero]
      ring_nf
      rw [hzero]
      have hψ : ψ₂[n] (DihedralGroup.r k) = 1 := dihedralReflectionSignCharacter_apply_r (n := n) k
      norm_num [hψ]
  | sr k =>
      -- On reflections, the same half-difference formula uses `sr^k * sr^k = 1` and yields `-1`.
      rw [Representation.char_alternatingSquare]
      rw [dihedralTwoDimensionalCharacter_apply_sr]
      rw [show (DihedralGroup.sr k : DihedralGroup n) ^ 2 = DihedralGroup.r 0 by simp [pow_two]]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      norm_num [AddChar.circleEquivComplex]
      simpa using (dihedralReflectionSignCharacter_apply_sr (n := n) k).symm

-- Proof sketch: use the canonical identity
-- `Representation.char_symmetricSquare_add_char_alternatingSquare` and substitute the source-facing
-- Chapter 5 descriptions of `χ_h * χ_h`, `χ_0`, and `Alt²(ρ^h)`.
/-- The character of the symmetric square of `ρ^h` is `χ_{2h} + ψ₁`. -/
theorem dihedralSymmetricSquare_character_eq_double_add_trivial :
    (Sym² (ρ[n] ^ h)).character = χ_ (h + h) + ψ₁[n] := by
  ext g
  have hchar :
      ((Sym² (ρ[n] ^ h)).character + (Alt² (ρ[n] ^ h)).character) g =
        ((ρ[n] ^ h).character * (ρ[n] ^ h).character) g := by
    simpa [pow_two, Pi.add_apply, Pi.mul_apply] using
      congr_fun (Representation.char_symmetricSquare_add_char_alternatingSquare (ρ[n] ^ h)) g
  rw [dihedralAlternatingSquare_character_eq_reflectionSign,
    dihedralTwoDimensionalCharacter_mul_self,
    dihedralTwoDimensionalCharacter_zero_eq_trivial_add_reflectionSign] at hchar
  simp only [Pi.add_apply] at hchar ⊢
  have hchar' :
      ψ₂[n] g + (Sym² (ρ[n] ^ h)).character g = ψ₂[n] g + (χ_ (h + h) g + ψ₁[n] g) := by
    simpa [add_assoc, add_left_comm, add_comm] using hchar
  exact add_left_cancel hchar'

end SymmetricAlternatingSquareCharacters

end
