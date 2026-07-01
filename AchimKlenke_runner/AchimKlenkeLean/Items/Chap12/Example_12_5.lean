import AchimKlenkeLean.Items.Chap12.Definition_12_6
import AchimKlenkeLean.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators ENNReal

universe u v

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: reindex the finite sum over `Fin n` by the permutation `σ`; the value of the
-- arithmetic mean is unchanged because the numerator is permutation-invariant. Use the owner
-- theorem `exchangeableAverage_isNSymmetric` together with
-- `exchangeableAverage_apply_zero`.
/-- Example 12.5 (1): Item (i). The `n`th arithmetic mean is `n`-symmetric for positive `n`. -/
theorem arithmeticMean_isNSymmetric (n : ℕ+) :
    IsNSymmetricSequenceMap (n : ℕ)
      (fun x : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), x i) / (n : ℝ)) := by
  simpa [exchangeableAverage_apply_zero n] using
    (exchangeableAverage_isNSymmetric (n : ℕ) (fun x : ℕ → ℝ ↦ x 0))

-- Proof sketch: choose a sequence that is zero on the first `n` coordinates and nonzero at one
-- extra coordinate below `m`; a permutation of the first `m` coordinates can move that value into
-- the averaging window and change the mean.
/-- Example 12.5 (2): Item (i). For positive prefix lengths, the `n`th arithmetic mean is not
`m`-symmetric for any `m > n`. -/
theorem arithmeticMean_not_isNSymmetric_of_lt {n m : ℕ+} (hnm : n < m) :
    ¬ IsNSymmetricSequenceMap (m : ℕ)
      (fun x : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), x i) / (n : ℝ)) := sorry

-- Proof sketch: permuting the first `n` coordinates changes only finitely many terms of the
-- sequence of arithmetic means, so the limsup at `atTop` is unchanged; since `n` was arbitrary,
-- the map is symmetric in the sense of Definition 12.4.
/-- Example 12.5 (3): Item (i). The limsup of the arithmetic means defines a symmetric map
`ℝ^ℕ → ℝ ∪ {-∞, +∞}`. -/
theorem limsupArithmeticMean_isSymmetric :
    IsSymmetricSequenceMap
      (fun x : ℕ → ℝ ↦
        Filter.limsup
          (fun n ↦
            (((∑ i : Fin (Nat.succPNat n : ℕ), x i) / (Nat.succPNat n : ℝ)) : EReal))
          Filter.atTop) := sorry

-- Proof sketch: permuting any finite prefix only reindexes finitely many terms of the nonnegative
-- series `∑' n, |x n|`, so the `tsum` is unchanged at every stage.
/-- Example 12.5 (4): Item (ii). The map `x ↦ ∑' n, |x n|` is symmetric. -/
theorem absoluteSeries_isSymmetric :
    IsSymmetricSequenceMap (fun x : ℕ → ℝ ↦ ∑' n, ENNReal.ofReal |x n|) := sorry

-- Proof sketch: permuting the first `n` coordinates only reorders the finite sum of Dirac masses
-- defining the empirical distribution of the first `n` coordinates, so the resulting probability
-- measure is unchanged.
/-- Example 12.5 (5): Item (iii). The empirical distribution of the first `n` coordinates,
realized as the deterministic specialization of Definition 12.25, is `n`-symmetric. -/
theorem empiricalDistribution_isNSymmetric (n : ℕ+) :
    IsNSymmetricSequenceMap (n : ℕ)
      (fun x : ℕ → E ↦ empiricalDistributionTuple (fun i : Fin n ↦ x i)) := sorry

-- Proof sketch: average `φ` over all permutations of `Fin n`; left-multiplication by a fixed
-- permutation merely reindexes the finite sum over `Equiv.Perm (Fin n)`. This is the same owner
-- symmetry theorem for `exchangeableAverage`, now specialized to the finite-coordinate functional
-- induced by `φ`.
/-- Example 12.5 (6): Item (iv). The `n`th symmetrized average associated with `φ : E^k → ℝ` is
`n`-symmetric. -/
theorem symmetrizedAverage_isNSymmetric (n k : ℕ) (φ : (Fin k → E) → ℝ) :
    IsNSymmetricSequenceMap n (exchangeableAverage n (fun x ↦ φ (fun i ↦ x i))) := by
  simpa using exchangeableAverage_isNSymmetric n (fun x ↦ φ (fun i ↦ x i))
