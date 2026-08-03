import Mathlib

open scoped BigOperators

-- Semantic search tooling was unavailable in this environment; the API choice here was checked
-- against mathlib's existing `Rat.num`/`Rat.den` and matrix denominator conventions.

/-- A bit-length style encoding size for a rational number, given by the sizes of its normalized
numerator and denominator. -/
def rational_encoding_size (q : ℚ) : ℕ :=
  (Nat.log2 (q.num.natAbs + 1) + 1) + (Nat.log2 (q.den + 1) + 1)

/-- The least common multiple of the denominators of the coordinates of a rational vector. -/
def rational_vector_common_denominator {n : ℕ} (v : Fin n → ℚ) : ℕ :=
  Finset.univ.lcm fun i : Fin n ↦ (v i).den

/-- The integer vector obtained by scaling a rational vector by the least common multiple of its
coordinate denominators. -/
def common_denominator_scaled_vector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℤ :=
  fun i ↦ (((rational_vector_common_denominator v : ℚ) * v i).num)

/-- A bit-length style encoding size for a rational vector, obtained by summing the sizes of the
numerator and denominator of each coordinate. -/
def rational_vector_encoding_size {n : ℕ} (v : Fin n → ℚ) : ℕ :=
  ∑ i, rational_encoding_size (v i)

/-- A bit-length style encoding size for an integer vector, obtained by summing the sizes of its
coordinates. -/
def integer_vector_encoding_size {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  ∑ i, (Nat.log2 ((v i).natAbs + 1) + 1)

/-- Each coordinate denominator divides the common denominator of the whole vector. -/
theorem dvd_rational_vector_common_denominator {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    (v i).den ∣ rational_vector_common_denominator v := sorry

/-- Remark 1.1 (1): scaling a rational vector by the least common multiple of its coordinate
denominators produces an integer vector whose rational realization is exactly the scaled vector. -/
theorem common_denominator_scaled_vector_eq_smul {n : ℕ} (v : Fin n → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℚ)) =
      (rational_vector_common_denominator v : ℚ) • v := sorry

/-- Remark 1.1 (2): the encoding size of the scaled integer vector is at most `n` times the
encoding size of the original rational vector. -/
theorem common_denominator_scaled_vector_encoding_size_le {n : ℕ} (v : Fin n → ℚ) :
    integer_vector_encoding_size (common_denominator_scaled_vector v) ≤
      n * rational_vector_encoding_size v := sorry
