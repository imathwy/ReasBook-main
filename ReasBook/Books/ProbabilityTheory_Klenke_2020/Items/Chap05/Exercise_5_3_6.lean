import Mathlib
import AchimKlenkeLean.Items.Chap05.Exercise_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- The 26 letters of the Latin alphabet used in the Morse-code table of the exercise. -/
inductive MorseLetter
  | A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  deriving DecidableEq, Fintype

/-- The German letter frequencies from the Morse-code table in Exercise 5.3.6. -/
noncomputable def morseGermanWeight : MorseLetter → ENNReal
  | .A => 651 / 10000
  | .B => 189 / 10000
  | .C => 306 / 10000
  | .D => 508 / 10000
  | .E => 1740 / 10000
  | .F => 166 / 10000
  | .G => 301 / 10000
  | .H => 476 / 10000
  | .I => 755 / 10000
  | .J => 27 / 10000
  | .K => 121 / 10000
  | .L => 344 / 10000
  | .M => 253 / 10000
  | .N => 978 / 10000
  | .O => 251 / 10000
  | .P => 79 / 10000
  | .Q => 2 / 10000
  | .R => 7 / 100
  | .S => 727 / 10000
  | .T => 615 / 10000
  | .U => 435 / 10000
  | .V => 67 / 10000
  | .W => 189 / 10000
  | .X => 3 / 10000
  | .Y => 4 / 10000
  | .Z => 113 / 10000

-- Proof sketch: expand the finite sum over all 26 letters and check that the listed decimal
-- frequencies add up to `1`.
/-- The Morse-code frequency table defines a probability mass function on the alphabet. -/
theorem morseGermanWeight_sum : ∑ a : MorseLetter, morseGermanWeight a = 1 := sorry

/-- The German letter-frequency law from Exercise 5.3.6 as a probability mass function. -/
noncomputable def morseGermanPMF : PMF MorseLetter :=
  PMF.ofFintype morseGermanWeight morseGermanWeight_sum

/-- The ternary Morse code from Exercise 5.3.6, with `0 = dot`, `1 = dash`, and `2` the
terminating pause symbol. -/
def morseCodeWord : MorseLetter → List (Fin 3)
  | .A => [0, 1, 2]
  | .B => [1, 0, 0, 0, 2]
  | .C => [1, 0, 1, 0, 2]
  | .D => [1, 0, 0, 2]
  | .E => [0, 2]
  | .F => [0, 0, 1, 0, 2]
  | .G => [1, 1, 0, 2]
  | .H => [0, 0, 0, 0, 2]
  | .I => [0, 0, 2]
  | .J => [0, 1, 1, 1, 2]
  | .K => [1, 0, 1, 2]
  | .L => [0, 1, 0, 0, 2]
  | .M => [1, 1, 2]
  | .N => [1, 0, 2]
  | .O => [1, 1, 1, 2]
  | .P => [0, 1, 1, 0, 2]
  | .Q => [1, 1, 0, 1, 2]
  | .R => [0, 1, 0, 2]
  | .S => [0, 0, 0, 2]
  | .T => [1, 2]
  | .U => [0, 0, 1, 2]
  | .V => [0, 0, 0, 1, 2]
  | .W => [0, 1, 1, 2]
  | .X => [1, 0, 0, 1, 2]
  | .Y => [1, 0, 1, 1, 2]
  | .Z => [1, 1, 0, 0, 2]

/-- The Morse code is prefix-free once the terminating pause symbol is included. -/
theorem morseCodeWord_prefix_free :
    Pairwise fun a b : MorseLetter ↦ ¬ (morseCodeWord a <+: morseCodeWord b) := by
  simpa [Pairwise] using
    (show ∀ a b : MorseLetter, a ≠ b → ¬ (morseCodeWord a <+: morseCodeWord b) by
      decide)

/-- The ternary Morse code as a prefix code over the digit alphabet `Fin 3`. -/
def morseCode : PrefixCode (Fin 3) MorseLetter where
  encode := morseCodeWord
  prefix_free := morseCodeWord_prefix_free

-- Proof sketch: unfold `PrefixCode.expectedLength`, substitute the 26 values from the table, and
-- evaluate the resulting rational sum.
/-- The average ternary Morse-code length for the German frequency table is `3.4429`. -/
theorem morseAverageCodeLength_eq :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 := sorry

-- Proof sketch: use `morseAverageCodeLength_eq` for the explicit average length, then compare it
-- with the base-`3` entropy sum for `morseGermanPMF`.
/-- Exercise 5.3.6: For the German letter frequencies, the Morse code has average ternary length
`3.4429`, and the ternary entropy `H₃` is bounded above by this average length. -/
theorem morse_code_average_length_and_entropy_comparison :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 ∧
      (entropyInBase (nat_base 3 (show 2 ≤ 3 by norm_num)) morseGermanPMF).toReal ≤
        morseCode.expectedLength
        morseGermanPMF := by
  refine ⟨morseAverageCodeLength_eq, ?_⟩
  simpa using
    entropy_in_nat_base_le_expected_length_of_b_adic_prefix_code 3
      (show 2 ≤ 3 by norm_num) morseGermanPMF morseCode
