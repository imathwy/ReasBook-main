import Mathlib.FieldTheory.PrimeField
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (F : Type u) [Field F]

/- Source/core/bridge triage for Definition 9.5.1:
- `source-facing`: the characteristic of a field and its prime subfield
- `core/canonical`: `ringChar` and `(⊥ : Subfield F)`
- `bridge/view`: `CharP.char_is_prime_or_zero`, `ringChar.Nat.cast_ringChar`,
  `Subfield.bot_eq_of_charZero`, and `Subfield.bot_eq_of_zMod_algebra`

Primitive data are only the field `F`, its canonical characteristic, and its smallest subfield.
The characteristic-zero and characteristic-`p` descriptions of the prime subfield are derived
bridge theorems, so this file should recall those owner declarations directly rather than introduce
parallel local wrappers.
-/

/- Definition 9.5.1: the characteristic of a field is the canonical mathlib function
`ringChar F`; for a field it is `0` in characteristic zero, and otherwise it is a prime number. -/
recall ringChar

/- For a field, the canonical characteristic `ringChar F` is either `0` or a prime number. -/
#check (CharP.char_is_prime_or_zero F (ringChar F) :
  Nat.Prime (ringChar F) ∨ ringChar F = 0)

/- The canonical characteristic vanishes in `F`, i.e. `(ringChar F : F) = 0`. -/
#check (ringChar.Nat.cast_ringChar : (ringChar F : F) = 0)

/- Definition 9.5.1: the prime subfield of `F` is the smallest subfield of `F`,
namely the bottom subfield `(⊥ : Subfield F)`. -/
#check (⊥ : Subfield F)

/- In characteristic zero, the prime subfield of `F` is the image of `ℚ`. -/
recall Subfield.bot_eq_of_charZero

/- In characteristic `p`, the prime subfield of `F` is the image of `ZMod p`. -/
recall Subfield.bot_eq_of_zMod_algebra
