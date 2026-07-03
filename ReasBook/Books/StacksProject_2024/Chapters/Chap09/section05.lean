import Mathlib
import Mathlib.FieldTheory.PrimeField
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_5_1 (from Chap09) -/
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

/-! ### Example_9_5_2 (from Chap09) -/
/- Domain-style sampling:
* primary domain: ring characteristic computations for standard fields via the canonical
  `ringChar` owner;
* sampled owner declarations:
  `ringChar`,
  `ringChar.eq_zero`,
  `ZMod.ringChar_zmod_n`,
  `Rat.instCharZero`;
* best owner abstraction: `ringChar`, with concrete characteristic computations derived from that
  owner;
* primitive data: a semiring or field together with the characteristic structure (`CharP` or
  `CharZero`);
* derived API: concrete formulas such as `ringChar (ZMod n) = n` and the specialization
  `ringChar ℚ = 0`.

Source/core/bridge triage:
* `source-facing`: the two textbook characteristic computations for `𝔽_p` and `ℚ`;
* `core/canonical`: `ringChar`;
* `bridge/view`: `ZMod.ringChar_zmod_n` and `ringChar.eq_zero` as the canonical owner-level
  computations, with `Rat.instCharZero` serving only as supporting instance data. -/

/- Example 9.5.2: for a prime `p`, the field `𝔽_p`, modeled in Lean by `ZMod p`, has
characteristic `p`. This is the prime-field specialization of the canonical characteristic
computation `ZMod.ringChar_zmod_n`, whose statement already covers every `ZMod n`. -/
recall ZMod.ringChar_zmod_n

/- Example 9.5.2: the rational numbers `ℚ` have characteristic `0`. The canonical owner-level
statement is the specialization of `ringChar.eq_zero` to `ℚ`, using the standard instance
`Rat.instCharZero`. -/
#check (ringChar.eq_zero : ringChar ℚ = 0)
