import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_91
import chapter1_reference_format.Chap01.Proposition_1_1_92

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Example 1.1.107: `13` is prime, so `ZMod 13` is the finite field used in the
congruence calculation. -/
private theorem prime_thirteen : Nat.Prime 13 := by
  decide

/-- Helper for Example 1.1.107: Euler's totient for `13` is `12`, matching the order of
`(ZMod 13)ˣ`. -/
private theorem totient_thirteen : Nat.totient 13 = 12 := by
  decide

local instance : Fact (Nat.Prime 13) := ⟨prime_thirteen⟩

open Polynomial

/-- Helper for Example 1.1.107: the residue class `2` generates the nonzero classes of
`ZMod 13`. -/
private lemma two_is_primitive_root_mod_thirteen : IsPrimitiveRoot (2 : ZMod 13) 12 := by
  -- Check the primitive-root conditions directly on the twelve nonzero residue classes.
  refine IsPrimitiveRoot.mk_of_lt (ζ := (2 : ZMod 13)) ?_ ?_ ?_
  · norm_num
  · decide
  · intro l hl0 hlt
    interval_cases l <;> decide

/-- Helper for Example 1.1.107: the textbook index statement `ind₂(3) = 4` is the identity
`2 ^ 4 = 3` in `ZMod 13`. -/
private lemma two_pow_four_eq_three_mod_thirteen : (2 : ZMod 13) ^ 4 = (3 : ZMod 13) := by
  -- This is the concrete value needed on the right-hand side of the index congruence.
  decide

/-- Helper for Example 1.1.107: solving `8y = 4` in `ZMod 12` gives exactly the four residue
classes `2`, `5`, `8`, and `11`. -/
private lemma zmod12_eight_mul_eq_four_iff (y : ZMod 12) :
    ((8 : ZMod 12) * y = 4) ↔ y = 2 ∨ y = 5 ∨ y = 8 ∨ y = 11 := by
  -- Reduce to the canonical representatives `0, ..., 11`, then inspect those twelve cases.
  rw [← ZMod.natCast_zmod_val y]
  have hy_lt : y.val < 12 := ZMod.val_lt y
  interval_cases y.val <;> decide

/-- Helper for Example 1.1.107: the same linear congruence written in the index type
`ZMod (φ 13)`. -/
private lemma totient_thirteen_eight_mul_eq_four_iff (y : ZMod (Nat.totient 13)) :
    8 * y = 4 ↔ y = 2 ∨ y = 5 ∨ y = 8 ∨ y = 11 := by
  -- Rewrite `φ 13` as `12` so the finite congruence lemma applies verbatim.
  simpa [totient_thirteen] using zmod12_eight_mul_eq_four_iff (y := y)

/-- Helper for Example 1.1.107: the four admissible index classes correspond exactly to the four
matching powers of the primitive root. -/
private lemma index_eq_two_five_eight_eleven_iff {g u : (ZMod 13)ˣ} (hg : IsPrimitiveRoot g 12) :
    ind_{hg} u = 2 ∨ ind_{hg} u = 5 ∨ ind_{hg} u = 8 ∨ ind_{hg} u = 11 ↔
      u = g ^ 2 ∨ u = g ^ 5 ∨ u = g ^ 8 ∨ u = g ^ 11 := by
  constructor
  · intro hu
    rcases hu with h2 | h5 | h8 | h11
    · left
      -- Equal indices force equal units, so index `2` means `u = g ^ 2`.
      exact (hg.index_eq_iff (u := u) (v := g ^ 2)).1 <| by
        calc
          ind_{hg} u = 2 := h2
          _ = ind_{hg} (g ^ 2) := by
            symm
            calc
              ind_{hg} (g ^ 2) = 2 * ind_{hg} g := by
                simpa using hg.index_pow (u := g) (m := 2)
              _ = 2 := by
                rw [hg.index_generator]
                norm_num [totient_thirteen]
    · right
      left
      -- The same argument identifies the exponent class `5`.
      exact (hg.index_eq_iff (u := u) (v := g ^ 5)).1 <| by
        calc
          ind_{hg} u = 5 := h5
          _ = ind_{hg} (g ^ 5) := by
            symm
            calc
              ind_{hg} (g ^ 5) = 5 * ind_{hg} g := by
                simpa using hg.index_pow (u := g) (m := 5)
              _ = 5 := by
                rw [hg.index_generator]
                norm_num [totient_thirteen]
    · right
      right
      left
      -- The source proof's third exponent class is `8`.
      exact (hg.index_eq_iff (u := u) (v := g ^ 8)).1 <| by
        calc
          ind_{hg} u = 8 := h8
          _ = ind_{hg} (g ^ 8) := by
            symm
            calc
              ind_{hg} (g ^ 8) = 8 * ind_{hg} g := by
                simpa using hg.index_pow (u := g) (m := 8)
              _ = 8 := by
                rw [hg.index_generator]
                norm_num [totient_thirteen]
    · right
      right
      right
      -- The last congruence class gives the last power.
      exact (hg.index_eq_iff (u := u) (v := g ^ 11)).1 <| by
        calc
          ind_{hg} u = 11 := h11
          _ = ind_{hg} (g ^ 11) := by
            symm
            calc
              ind_{hg} (g ^ 11) = 11 * ind_{hg} g := by
                simpa using hg.index_pow (u := g) (m := 11)
              _ = 11 := by
                rw [hg.index_generator]
                norm_num [totient_thirteen]
  · intro hu
    rcases hu with h2 | h5 | h8 | h11
    · left
      -- Reading the same calculation backward recovers the index value from the power.
      calc
        ind_{hg} u = ind_{hg} (g ^ 2) := by rw [h2]
        _ = 2 * ind_{hg} g := by
          simpa using hg.index_pow (u := g) (m := 2)
        _ = 2 := by
          rw [hg.index_generator]
          norm_num [totient_thirteen]
    · right
      left
      calc
        ind_{hg} u = ind_{hg} (g ^ 5) := by rw [h5]
        _ = 5 * ind_{hg} g := by
          simpa using hg.index_pow (u := g) (m := 5)
        _ = 5 := by
          rw [hg.index_generator]
          norm_num [totient_thirteen]
    · right
      right
      left
      calc
        ind_{hg} u = ind_{hg} (g ^ 8) := by rw [h8]
        _ = 8 * ind_{hg} g := by
          simpa using hg.index_pow (u := g) (m := 8)
        _ = 8 := by
          rw [hg.index_generator]
          norm_num [totient_thirteen]
    · right
      right
      right
      calc
        ind_{hg} u = ind_{hg} (g ^ 11) := by rw [h11]
        _ = 11 * ind_{hg} g := by
          simpa using hg.index_pow (u := g) (m := 11)
        _ = 11 := by
          rw [hg.index_generator]
          norm_num [totient_thirteen]

private theorem zmod13_pow_eight_eq_three_iff_all :
    ∀ x : ZMod 13, x ^ 8 = (3 : ZMod 13) ↔ x = 4 ∨ x = 6 ∨ x = 7 ∨ x = 9 := by
  intro x
  -- Route correction: replace the previous finite `decide` proof with the primitive-root/index
  -- argument from the textbook.
  have h12ne0 : 12 ≠ 0 := by
    decide
  let g : (ZMod 13)ˣ := (two_is_primitive_root_mod_thirteen.isUnit h12ne0).unit'
  have hg : IsPrimitiveRoot g 12 := by
    -- Pass from the primitive root in `ZMod 13` to the corresponding primitive root unit.
    simpa [g] using two_is_primitive_root_mod_thirteen.isUnit_unit' h12ne0
  constructor
  · intro hx
    -- First rule out the zero class so that the equation can be interpreted in the unit group.
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0] at hx
      have h03 : (0 : ZMod 13) ≠ 3 := by
        decide
      exact h03 hx
    have hthree0 : (3 : ZMod 13) ≠ 0 := by
      decide
    let u : (ZMod 13)ˣ := Units.mk0 x hx0
    let a : (ZMod 13)ˣ := Units.mk0 (3 : ZMod 13) hthree0
    -- Rewrite the original congruence as an equality in the cyclic unit group.
    have hu_pow : u ^ 8 = a := by
      apply Units.ext
      simp [u, a, hx, Units.val_pow_eq_pow_val]
    have ha_pow : a = g ^ 4 := by
      apply Units.ext
      simp [a, g, two_pow_four_eq_three_mod_thirteen, Units.val_pow_eq_pow_val]
    -- Applying the index map turns the multiplicative equation into the linear congruence
    -- `8 * ind(u) = 4` in `ZMod 12`.
    have hindex : 8 * ind_{hg} u = 4 := by
      calc
        8 * ind_{hg} u = ind_{hg} (u ^ 8) := by
          symm
          simpa using hg.index_pow (u := u) (m := 8)
        _ = ind_{hg} a := by
          rw [hu_pow]
        _ = ind_{hg} (g ^ 4) := by
          rw [ha_pow]
        _ = 4 * ind_{hg} g := by
          simpa using hg.index_pow (u := g) (m := 4)
        _ = 4 := by
          rw [hg.index_generator]
          norm_num [totient_thirteen]
    have hu_cases : u = g ^ 2 ∨ u = g ^ 5 ∨ u = g ^ 8 ∨ u = g ^ 11 := by
      -- Solve the index congruence and translate the resulting exponents back to powers of `g`.
      exact (index_eq_two_five_eight_eleven_iff hg).1 <|
        (totient_thirteen_eight_mul_eq_four_iff (ind_{hg} u)).1 hindex
    -- Evaluate the four powers of the primitive root to recover the stated residue classes.
    rcases hu_cases with h2 | h5 | h8 | h11
    · left
      have hx_eq : x = 4 := by
        have hval : (u : ZMod 13) = ((g ^ 2 : (ZMod 13)ˣ) : ZMod 13) := by
          exact congrArg (fun z : (ZMod 13)ˣ ↦ (z : ZMod 13)) h2
        simpa [u, g, Units.val_pow_eq_pow_val] using hval
      exact hx_eq
    · right
      left
      have hx_eq : x = 6 := by
        have hval : (u : ZMod 13) = ((g ^ 5 : (ZMod 13)ˣ) : ZMod 13) := by
          exact congrArg (fun z : (ZMod 13)ˣ ↦ (z : ZMod 13)) h5
        simpa [u, g, Units.val_pow_eq_pow_val] using hval
      exact hx_eq
    · right
      right
      right
      have hx_eq : x = 9 := by
        have hval : (u : ZMod 13) = ((g ^ 8 : (ZMod 13)ˣ) : ZMod 13) := by
          exact congrArg (fun z : (ZMod 13)ˣ ↦ (z : ZMod 13)) h8
        simpa [u, g, Units.val_pow_eq_pow_val] using hval
      exact hx_eq
    · right
      right
      left
      have hx_eq : x = 7 := by
        have hval : (u : ZMod 13) = ((g ^ 11 : (ZMod 13)ˣ) : ZMod 13) := by
          exact congrArg (fun z : (ZMod 13)ˣ ↦ (z : ZMod 13)) h11
        simpa [u, g, Units.val_pow_eq_pow_val] using hval
      exact hx_eq
  · -- The converse is a direct verification of the four listed residues.
    rintro (rfl | rfl | rfl | rfl) <;> decide

/-- Example 1.1.107: the canonical `8`th-root finset of `3` in `ZMod 13` is exactly
`{4, 6, 7, 9}`. -/
theorem zmod13_nthRootsFinset_eight_three :
    nthRootsFinset 8 (3 : ZMod 13) = ({4, 6, 7, 9} : Finset (ZMod 13)) := by
  -- Membership in the `nthRootsFinset` is exactly the defining power equation.
  have h8pos : 0 < 8 := by
    norm_num
  ext x
  rw [mem_nthRootsFinset h8pos]
  simpa using zmod13_pow_eight_eq_three_iff_all x

/-- Example 1.1.107: in `ZMod 13`, the congruence `x^8 ≡ 3` has exactly the four solutions
`4`, `6`, `7`, and `9`. -/
-- Proof sketch: use that `2` is a primitive root modulo `13`, rewrite every nonzero class as a
-- power of `2`, and translate `x ^ 8 = 3` into the linear congruence
-- `8 * ind₂(x) ≡ 4 [ZMOD 12]`; solving that congruence gives the exponent classes
-- `2`, `5`, `8`, and `11`, corresponding to the residue classes `4`, `6`, `9`, and `7`.
theorem zmod13_pow_eight_eq_three_iff (x : ZMod 13) :
    x ^ 8 = (3 : ZMod 13) ↔ x = 4 ∨ x = 6 ∨ x = 7 ∨ x = 9 :=
  zmod13_pow_eight_eq_three_iff_all x
