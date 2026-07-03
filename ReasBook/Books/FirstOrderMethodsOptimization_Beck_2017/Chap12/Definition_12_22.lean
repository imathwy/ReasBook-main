import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {m n : ℕ}

local notation "PixelIndex" => Fin m × Fin n
local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

namespace IsotropicTwoDimensionalTotalVariation

/-
Definition 12.22 is `source-facing`: it repartitions the isotropic two-dimensional total
variation into three sums indexed by residue classes of matrix diagonals.

Domain sampling against the nearby Chapter 12 owners gives:
- `source-facing`: the diagonal index sets `D_k`, the residue classes `K_i`, and the
  corresponding component family `ψ_i`;
- `core/canonical`: the existing regularizer `TV_I` from Definition 12.13 on
  `Matrix (Fin m) (Fin n) ℝ`;
- `bridge/view`: a decomposition of `TV_I` into three diagonal-indexed components.

The source does not define a new optimization problem or wrapper structure. The right public API
therefore keeps `TV_I` as the owner and adds the diagonal partition together with the component
functional that realizes the textbook `ψ_i`. -/

/-- The diagonal offset `k = j - i` of a matrix index `(i, j)`, using zero-based indices on
`Fin m × Fin n`. -/
private def diagonalOffset (ij : PixelIndex) : ℤ :=
  (ij.2 : ℤ) - ij.1

/-- The set `D_k` of matrix indices lying on the diagonal with offset `k = j - i`. -/
def D (m n : ℕ) (k : ℤ) : Finset (Fin m × Fin n) :=
  (Finset.univ : Finset (Fin m × Fin n)).filter fun ij ↦ diagonalOffset ij = k

/-- The residue-class block `K_(i+1)` in the partition of diagonal offsets
`{1 - m, ..., n - 1}` consisting of the offsets congruent to `i [ZMOD 3]`, with
`i : Fin 3` representing the textbook labels `1`, `2`, and `3` shifted to `0`, `1`, and `2`. -/
def K (m n : ℕ) (i : Fin 3) : Finset ℤ :=
  (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).filter fun k ↦
    k ≡ (i : ℤ) [ZMOD 3]

/-- Definition 12.22: the diagonal component `ψ_(i+1)` of `TV_I` is the sum of the isotropic cell
terms over all diagonals `D_k` whose offsets belong to the residue class `K_(i+1)`. -/
def ψ (m n : ℕ) (i : Fin 3) (x : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (K m n i).sum fun k ↦
    (D m n k).sum fun ij ↦
      isotropic_two_dimensional_total_variation_site_term x ij

end IsotropicTwoDimensionalTotalVariation

open IsotropicTwoDimensionalTotalVariation

local notation "D[" k "]" => D m n k
local notation "K[" i "]" => K m n i
local notation "ψ[" i "]" => ψ m n i

-- Proof sketch: unfold `ψ`; the statement is exactly its defining double sum over the
-- residue-class diagonal block `K_(i+1)`.
/-- Expanding the diagonal component `ψ_(i+1)` gives the double sum over the diagonal blocks
`D_k` with `k ∈ K_(i+1)`. -/
@[simp] theorem ψ_def
    (i : Fin 3) (x : Mmn) :
    ψ[i] x =
      K[i].sum fun k ↦
        D[k].sum fun ij ↦
          isotropic_two_dimensional_total_variation_site_term x ij := rfl

/-- Helper for Definition 12.22: the integer representative of a residue class `i : Fin 3`
is unchanged by reduction modulo `3`. -/
private lemma fin_cast_emod_three (i : Fin 3) : ((i : ℤ) % 3) = i := by
  -- There are only three residue representatives to check.
  fin_cases i <;> norm_num

/-- Helper for Definition 12.22: every matrix index lies on a diagonal whose offset belongs to
the textbook interval `{1 - m, ..., n - 1}`. -/
private lemma diagonalOffset_mem_Icc (ij : PixelIndex) :
    diagonalOffset ij ∈ Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1) := by
  -- Bound the zero-based row and column coordinates by their `Fin` ranges.
  rw [Finset.mem_Icc]
  dsimp [diagonalOffset]
  have hi_nonneg : (0 : ℤ) ≤ (ij.1 : ℤ) := by
    exact_mod_cast (Nat.zero_le ij.1.1)
  have hj_nonneg : (0 : ℤ) ≤ (ij.2 : ℤ) := by
    exact_mod_cast (Nat.zero_le ij.2.1)
  have hi_lt : (ij.1 : ℤ) < m := by
    exact_mod_cast ij.1.2
  have hj_lt : (ij.2 : ℤ) < n := by
    exact_mod_cast ij.2.2
  omega

/-- Helper for Definition 12.22: summing over all matrix entries can be regrouped fiberwise by
their diagonal offset `j - i`. -/
private lemma sum_pixels_by_diagonal_offset (F : PixelIndex → ℝ) :
    (∑ ij : PixelIndex, F ij) =
      ∑ k in Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1), ∑ ij in D[k], F ij := by
  -- Regroup the full pixel sum by the map `ij ↦ diagonalOffset ij`.
  simpa [D] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset PixelIndex))
      (t := Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1))
      (g := diagonalOffset)
      (fun ij _ ↦ diagonalOffset_mem_Icc ij)
      F).symm

/-- Helper for Definition 12.22: the textbook block `K_(i+1)` is the filter of diagonal offsets
whose remainder modulo `3` equals the residue representative `i`. -/
private lemma K_eq_filter_emod (i : Fin 3) :
    K[i] = (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).filter fun k ↦ k % 3 = (i : ℤ) := by
  -- Rewrite congruence modulo `3` into equality of integer remainders.
  ext k
  simp [K, Int.ModEq, fin_cast_emod_three]

/-- Helper for Definition 12.22: every integer remainder modulo `3` lies in the residue interval
`{0, 1, 2}`. -/
private lemma emod_three_mem_Icc (k : ℤ) : k % 3 ∈ Finset.Icc (0 : ℤ) 2 := by
  -- The Euclidean remainder modulo `3` is always nonnegative and strictly less than `3`.
  rw [Finset.mem_Icc]
  constructor
  · exact Int.emod_nonneg _ (by norm_num)
  · have hk_lt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega

/-- Helper for Definition 12.22: the diagonal-offset interval splits into the three residue-class
blocks `K[0]`, `K[1]`, and `K[2]`. -/
private lemma sum_diagonal_offsets_by_residue_class (F : ℤ → ℝ) :
    (∑ k in Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1), F k) =
      ∑ i : Fin 3, ∑ k in K[i], F k := by
  let interval : Finset ℤ := Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)
  calc
    ∑ k in interval, F k
      = ∑ r in Finset.Icc (0 : ℤ) 2, ∑ k in interval with k % 3 = r, F k := by
          -- Partition the offset interval by the remainder map `k ↦ k % 3`.
          simpa [interval] using
            (Finset.sum_fiberwise_of_maps_to
              (s := interval)
              (t := Finset.Icc (0 : ℤ) 2)
              (g := fun k : ℤ ↦ k % 3)
              (fun k _ ↦ emod_three_mem_Icc k)
              F).symm
    _ = (∑ k in interval with k % 3 = 0, F k) +
        (∑ k in interval with k % 3 = 1, F k) +
        (∑ k in interval with k % 3 = 2, F k) := by
          -- The codomain interval `{0, 1, 2}` has exactly the three expected residues.
          rw [show Finset.Icc (0 : ℤ) 2 = ({0, 1, 2} : Finset ℤ) by decide]
          simp [add_assoc]
    _ = ∑ i : Fin 3, ∑ k in K[i], F k := by
          -- Identify each residue filter with the corresponding textbook block `K[i]`.
          rw [Fin.sum_univ_three]
          simp [K_eq_filter_emod, interval]

-- Proof sketch: regroup the textbook site-sum for `TV_I` by the three diagonal residue classes
-- `K[0]`, `K[1]`, and `K[2]`; this keeps the same decomposition in the `Fin 3` family form used
-- by the Chapter 12.14 finite-sum owner.
/-- The isotropic total variation is also the finite sum of the family of diagonal components
`i ↦ ψ_(i+1)`. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_ψ
    (x : Mmn) :
    TV_I x = ∑ i : Fin 3, ψ[i] x := by
  -- Regroup the site-sum globally first by diagonal offsets and then by residue classes mod `3`.
  calc
    TV_I x
      = ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij := by
          simpa using isotropic_two_dimensional_total_variation_eq_sum_site_terms x
    _ = ∑ k in Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1),
          ∑ ij in D[k], isotropic_two_dimensional_total_variation_site_term x ij := by
          simpa using
            sum_pixels_by_diagonal_offset
              (m := m) (n := n)
              (F := fun ij ↦ isotropic_two_dimensional_total_variation_site_term x ij)
    _ = ∑ i : Fin 3,
          ∑ k in K[i], ∑ ij in D[k], isotropic_two_dimensional_total_variation_site_term x ij := by
          simpa using
            sum_diagonal_offsets_by_residue_class
              (m := m) (n := n)
              (F := fun k ↦
                ∑ ij in D[k], isotropic_two_dimensional_total_variation_site_term x ij)
    _ = ∑ i : Fin 3, ψ[i] x := by
          -- Fold the residue-class blocks back into the defining formula for `ψ`.
          simp [ψ_def]

-- Proof sketch: apply `isotropic_two_dimensional_total_variation_eq_sum_ψ` and expand the
-- three-term `Fin 3` sum with `Fin.sum_univ_three`.
/-- The isotropic total variation splits as the sum of the three diagonal components
`ψ[0] + ψ[1] + ψ[2]`. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_ψ_components
    (x : Mmn) :
    TV_I x = ψ[0] x + ψ[1] x + ψ[2] x := by
  simpa [Fin.sum_univ_three] using isotropic_two_dimensional_total_variation_eq_sum_ψ x

end
