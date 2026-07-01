import Mathlib
import AchimKlenkeLean.Items.Chap05.Theorem_5_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

/-- Helper for the base-`b` source-coding exercise: a natural base `b ≥ 2` gives a real
logarithmic base `> 1`. -/
private theorem nat_base_one_lt (b : ℕ) (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have h : (1 : ℕ) < b := lt_of_lt_of_le one_lt_two hb
  exact_mod_cast h

/-- The logarithmic base attached to a natural base `b ≥ 2`. -/
def nat_base (b : ℕ) (hb : 2 ≤ b) : LogBase :=
  ⟨b, by positivity, ne_of_gt (nat_base_one_lt b hb)⟩

variable {E : Type u}

-- Proof sketch: apply the same Kraft-inequality and cross-entropy argument as in the binary case,
-- replacing the binary weights `2 ^ (-length)` by the `b`-ary weights `b ^ (-length)` and the
-- logarithm base `2` by base `b`.
/-- Exercise 5.3.5 (1): for a finite alphabet, the expected length of a prefix code over the digit
alphabet `Fin b` is
bounded below by the real value of the base-`b` entropy `H_b(p)` of the source law. -/
theorem entropy_in_nat_base_le_expected_length_of_b_adic_prefix_code [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (C : PrefixCode (Fin b) E) :
    (entropyInBase (nat_base b hb) p).toReal ≤ C.expectedLength p := sorry

-- Proof sketch: choose Shannon lengths `l(e) = ⌈-log_b p(e)⌉`, verify the `b`-ary Kraft
-- inequality, and build a `b`-adic prefix code with these lengths to obtain the usual `+ 1`
-- overhead bound.
/-- Exercise 5.3.5 (2): for a finite alphabet, there exists a prefix code over `Fin b` whose
expected length is at most the base-`b` entropy `H_b(p)` plus `1`. -/
theorem exists_b_adic_prefix_code_expected_length_le_entropy_in_nat_base_add_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    ∃ C : PrefixCode (Fin b) E,
      C.expectedLength p ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := sorry
