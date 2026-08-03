import Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_7
import Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v w x

-- The statements below use mathlib's canonical `Matrix.IsTotallyUnimodular` API together with the
-- Chapter 4 owners `HasZeroOneNegOneEntries` and `is_equitable_row_bicoloring`, plus a
-- source-facing square-submatrix obstruction phrased in the chapter's standard finite-index
-- embedding language.

section Theorem59

variable {m : Type u} {n : Type v}

/-- A square integer matrix has even nonzero support in every row and column when each row and
each column contains an even number of nonzero entries. -/
def HasEvenNonzeroSupportInRowsAndCols {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) : Prop :=
  (∀ i, Even (Function.support (B i)).ncard) ∧
    ∀ j, Even (Function.support fun i ↦ B i j).ncard

/-- The half-sum of the entries of a square integer matrix is odd when the total sum of its
entries is twice an odd integer. -/
def HasOddHalfEntrySum {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) : Prop :=
  ∃ t : ℤ, (∑ i, ∑ j, B i j) = 2 * t ∧ Odd t

/-- Helper for Theorem 4.59: `HasOddHalfEntrySum B` is equivalent to the total entry sum of `B`
being congruent to `2` modulo `4`. -/
lemma hasOddHalfEntrySum_iff_totalEqTwoModFour
    {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) :
    HasOddHalfEntrySum B ↔ ∃ u : ℤ, (∑ i, ∑ j, B i j) = 2 + 4 * u := by
  constructor
  · rintro ⟨t, ht, hOdd⟩
    rcases hOdd with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    calc
      (∑ i, ∑ j, B i j) = 2 * t := ht
      _ = 2 * (u + u + 1) := by
        rw [hu]
        ring
      _ = 2 + 4 * u := by ring
  · rintro ⟨u, hu⟩
    refine ⟨2 * u + 1, ?_, ?_⟩
    · calc
        (∑ i, ∑ j, B i j) = 2 + 4 * u := hu
        _ = 2 * (2 * u + 1) := by ring
    · refine ⟨u, ?_⟩
      ring

/-- A matrix contains an even-support odd-half-sum square submatrix when some square submatrix has
an even number of nonzero entries in each row and column and has odd half entry sum. -/
def HasEvenSupportOddHalfSumSquareSubmatrix
    (A : Matrix m n ℤ) : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (row : ι ↪ m) (col : ι ↪ n),
    HasEvenNonzeroSupportInRowsAndCols (A.submatrix row col) ∧
      HasOddHalfEntrySum (A.submatrix row col)

/-- Helper for Theorem 4.59: multiplying a `(0, ±1)` entry by a sign keeps it in `{0, 1, -1}`. -/
lemma signed_zero_one_neg_one
    (s : Bool) {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    (if s then (1 : ℤ) else -1) * z = 0 ∨
      (if s then (1 : ℤ) else -1) * z = 1 ∨
      (if s then (1 : ℤ) else -1) * z = -1 := by
  -- Reduce to the three possible values of `z`.
  rcases hz with rfl | rfl | rfl <;> cases s <;> norm_num

/-- Helper for Theorem 4.59: modulo `2`, the values `1` and `-1` both reduce to `1`. -/
lemma zmod_two_cast_eq_indicator_of_zero_one_neg_one
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    ((z : ℤ) : ZMod 2) = if z = 0 then 0 else 1 := by
  -- Reduce to the three allowed integer values.
  rcases hz with rfl | rfl | rfl
  · norm_num
  · norm_num
  · simpa using (ZMod.neg_eq_self_mod_two (1 : ZMod 2))

/-- Helper for Theorem 4.59: a finite sum of `(0, ±1)` integers
with even nonzero support is even. -/
lemma even_sum_of_zero_one_neg_one_even_support
    {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1 ∨ f i = -1)
    (hs : Even (Function.support f).ncard) :
    Even (∑ i, f i) := by
  classical
  have hIndicator :
      (∑ i, if f i = 0 then (0 : ZMod 2) else 1) =
        ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hfi : f i = 0 <;> simp [hfi]
  have hsToFinset : Even ({i | f i ≠ 0}.toFinset.card) := by
    rw [← Set.ncard_eq_toFinset_card']
    simpa [Function.support] using hs
  have hs' : Even ((Finset.univ.filter fun i ↦ f i ≠ 0).card) := by
    simpa [Set.toFinset_setOf] using hsToFinset
  -- Work modulo `2`, where every nonzero `(0, ±1)` entry becomes `1`.
  rw [← ZMod.intCast_eq_zero_iff_even]
  calc
    ((∑ i, f i : ℤ) : ZMod 2)
        = ∑ i, (((f i : ℤ) : ZMod 2)) := by
            simp
    _ = ∑ i, (if f i = 0 then 0 else 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using zmod_two_cast_eq_indicator_of_zero_one_neg_one (hf i)
    _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := hIndicator
    _ = Finset.sum (Finset.univ.filter (fun i ↦ f i ≠ 0)) (fun _ ↦ (1 : ZMod 2)) := by
          rw [← Finset.sum_filter]
    _ = (((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2) := by
          symm
          rw [Finset.card_eq_sum_ones]
          simp
    _ = 0 := Even.natCast_zmod_two hs'

/-- Helper for Theorem 4.59: every row of an even-support `(0, ±1)` square matrix has even sum. -/
lemma even_row_sum_of_even_support
    {ι : Type*} [Fintype ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B) :
    ∀ i, Even (∑ j, B i j) := by
  -- Apply the finite-family parity lemma to each row.
  intro i
  exact
    even_sum_of_zero_one_neg_one_even_support
      (B i) (fun j ↦ HasZeroOneNegOneEntries.apply hB i j) (hEven.1 i)

/-- Helper for Theorem 4.59: an equitable row-bicoloring on an even-support square matrix forces
every row-bicoloring difference to vanish. -/
lemma row_bicoloring_difference_eq_zero_of_even_column_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B)
    {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring B red blue) :
    ∀ j, row_bicoloring_difference B red blue j = 0 := by
  -- Each column-difference is one of `0`, `1`, `-1`; even column support forces it to be even.
  rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, hBalance⟩
  intro j
  have hColumnEven :
      Even (∑ i, B i j) := by
    exact
      even_sum_of_zero_one_neg_one_even_support
        (fun i ↦ B i j) (fun i ↦ HasZeroOneNegOneEntries.apply hB i j) (hEven.2 j)
  have hDiffEven :
      Even (row_bicoloring_difference B red blue j) := by
    have hSum :
        red.sum (fun i ↦ B i j) + blue.sum (fun i ↦ B i j) = ∑ i, B i j := by
      rw [← hCover, Finset.sum_union hDisj]
    rw [row_bicoloring_difference_apply]
    have hTwoBlue : Even (2 * blue.sum (fun i ↦ B i j)) := by
      exact even_two_mul _
    have hRewrite :
        red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j) =
          (∑ i, B i j) - 2 * blue.sum (fun i ↦ B i j) := by
      linarith
    rw [hRewrite]
    exact hColumnEven.sub hTwoBlue
  rcases hBalance j with hZero | hOne | hNegOne
  · exact hZero
  · exfalso
    have : Even (1 : ℤ) := hOne ▸ hDiffEven
    norm_num at this
  · exfalso
    have : Even (-1 : ℤ) := hNegOne ▸ hDiffEven
    norm_num at this

/-- Helper for Theorem 4.59: an equitable row-bicoloring rules out odd half entry sum on an
even-support `(0, ±1)` square matrix. -/
lemma odd_half_entry_sum_not_of_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B)
    (hColor : ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue) :
    ¬ HasOddHalfEntrySum B := by
  -- The column balances force the red and blue total row sums to agree.
  rintro ⟨t, ht, hOddt⟩
  rcases hColor with ⟨red, blue, hColor⟩
  rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, _hBalance⟩
  have hDiffZero := row_bicoloring_difference_eq_zero_of_even_column_support hB hEven hColor
  have hRowEven := even_row_sum_of_even_support hB hEven
  have hPartition :
      (∑ i, ∑ j, B i j) =
        red.sum (fun i ↦ ∑ j, B i j) + blue.sum (fun i ↦ ∑ j, B i j) := by
    -- Split the total row-sum according to the red/blue partition of the rows.
    rw [← hCover, Finset.sum_union hDisj]
  have hRedEqBlue :
      red.sum (fun i ↦ ∑ j, B i j) = blue.sum (fun i ↦ ∑ j, B i j) := by
    -- Summing the zero column-differences over all columns identifies the two totals.
    have hSumDiff :
        ∑ j, row_bicoloring_difference B red blue j =
          red.sum (fun i ↦ ∑ j, B i j) - blue.sum (fun i ↦ ∑ j, B i j) := by
      calc
        ∑ j, row_bicoloring_difference B red blue j
            = ∑ j, (red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j)) := by
                simp [row_bicoloring_difference_apply]
        _ = (∑ j, red.sum (fun i ↦ B i j)) - ∑ j, blue.sum (fun i ↦ B i j) := by
              rw [Finset.sum_sub_distrib]
        _ = red.sum (fun i ↦ ∑ j, B i j) - ∑ j, blue.sum (fun i ↦ B i j) := by
              rw [Finset.sum_comm]
        _ = red.sum (fun i ↦ ∑ j, B i j) - blue.sum (fun i ↦ ∑ j, B i j) := by
              congr 1
              rw [Finset.sum_comm]
    have hZeroDiff : ∑ j, row_bicoloring_difference B red blue j = 0 := by
      -- Every summand vanishes because each column-difference is zero.
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact hDiffZero j
    linarith
  have hRedEven :
      Even (red.sum (fun i ↦ ∑ j, B i j)) := by
    -- The sum of even row-sums over the red rows is again even.
    refine Finset.induction_on red ?_ ?_
    · simpa using (show Even (0 : ℤ) by simp)
    · intro i s hi hsEven
      simpa [Finset.sum_insert hi] using (hRowEven i).add hsEven
  have hTotalTwo :
      (∑ i, ∑ j, B i j) = 2 * red.sum (fun i ↦ ∑ j, B i j) := by
    -- Replacing the blue total by the red total makes the total sum twice the red total.
    calc
      (∑ i, ∑ j, B i j)
          = red.sum (fun i ↦ ∑ j, B i j) + blue.sum (fun i ↦ ∑ j, B i j) := hPartition
      _ = red.sum (fun i ↦ ∑ j, B i j) + red.sum (fun i ↦ ∑ j, B i j) := by rw [hRedEqBlue]
      _ = 2 * red.sum (fun i ↦ ∑ j, B i j) := by ring
  have htEq :
      t = red.sum (fun i ↦ ∑ j, B i j) := by
    linarith [ht, hTotalTwo]
  have hEvenT : Even t := by
    rw [htEq]
    exact hRedEven
  exact ((Int.not_even_iff_odd).2 hOddt) hEvenT

/-- Helper for Theorem 4.59: an even-support square submatrix of a totally unimodular matrix
cannot have odd half entry sum. -/
lemma odd_half_entry_sum_not_of_totally_unimodular_square
    {ι : Type*} [Fintype ι] {B : Matrix ι ι ℤ}
    (hTU : B.IsTotallyUnimodular)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B) :
    ¬ HasOddHalfEntrySum B := by
  classical
  have hEntries : HasZeroOneNegOneEntries B :=
    Matrix.IsTotallyUnimodular.hasZeroOneNegOneEntries hTU
  have hColor :
      ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue := by
    -- Apply Corollary 4.7 to the square matrix itself through the identity row embedding.
    simpa using
      ((totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring B).1 hTU)
        (Function.Embedding.refl ι)
  -- The previously proved parity contradiction finishes once the equitable coloring exists.
  exact odd_half_entry_sum_not_of_equitable_row_bicoloring hEntries hEven hColor

/-- Helper for Theorem 4.59: a forbidden square submatrix inside a row submatrix is already a
forbidden square submatrix of the ambient matrix. -/
lemma even_support_odd_half_sum_square_submatrix_of_row_submatrix
    {ρ : Type w} {A : Matrix m n ℤ} (row : ρ ↪ m)
    (hSub : HasEvenSupportOddHalfSumSquareSubmatrix.{w, v, x} (A.submatrix row id)) :
    HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, x} A := by
  -- Reuse the same square witness and compose its row embedding with the ambient row embedding.
  rcases hSub with ⟨ι, _, row', col, hEven, hOdd⟩
  refine ⟨ι, inferInstance, row'.trans row, col, ?_, ?_⟩
  · simpa [Matrix.submatrix_submatrix, Function.comp_id] using hEven
  · simpa [Matrix.submatrix_submatrix, Function.comp_id] using hOdd

/-- Helper for Theorem 4.59: the Boolean `±1` signing induced by a red/blue partition computes the
row-bicoloring difference. -/
lemma boolean_signed_sum_eq_row_bicoloring_difference
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {red blue : Finset ι}
    (hDisj : Disjoint red blue) (hCover : red ∪ blue = Finset.univ) :
    ∀ j,
      (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
        row_bicoloring_difference B red blue j := by
  -- Split the universal row sum along the red/blue partition and simplify each side separately.
  intro j
  calc
    (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j)
        = (red ∪ blue).sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) := by
            rw [hCover]
    _ = red.sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) +
          blue.sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) := by
            rw [Finset.sum_union hDisj]
    _ = red.sum (fun i ↦ B i j) + blue.sum (fun i ↦ -B i j) := by
          -- On red rows the sign is `+1`, while disjointness forces blue rows to contribute `-1`.
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hi]
          · refine Finset.sum_congr rfl ?_
            intro i hi
            have hNotRed : i ∉ red := fun hiRed ↦ Finset.disjoint_left.mp hDisj hiRed hi
            simp [hNotRed]
    _ = red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j) := by
          rw [show blue.sum (fun i ↦ -B i j) = -(blue.sum (fun i ↦ B i j)) by
            rw [Finset.sum_neg_distrib]]
          ring
    _ = row_bicoloring_difference B red blue j := by
          rw [row_bicoloring_difference_apply]

/-- Helper for Theorem 4.59: row-bicoloring differences are invariant under row reindexing. -/
lemma row_bicoloring_difference_reindex_rows
    {ι κ : Type*}
    (B : Matrix κ n ℤ) (e : ι ≃ κ) (red blue : Finset ι) (j : n) :
    row_bicoloring_difference (B.reindex e.symm (Equiv.refl n)) red blue j =
      row_bicoloring_difference B (red.map e.toEmbedding) (blue.map e.toEmbedding) j := by
  -- Both transported row sums are the original sums rewritten along the row equivalence.
  rw [row_bicoloring_difference_apply, row_bicoloring_difference_apply]
  simp [Matrix.reindex_apply, Finset.sum_map]

/-- Helper for Theorem 4.59: an equitable row-bicoloring transports across a row reindexing
equivalence. -/
lemma is_equitable_row_bicoloring_reindex_rows
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ n ℤ) (e : ι ≃ κ) {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring (B.reindex e.symm (Equiv.refl n)) red blue) :
    is_equitable_row_bicoloring B (red.map e.toEmbedding) (blue.map e.toEmbedding) := by
  -- Unfold the predicate so disjointness, coverage, and each column balance transport separately.
  rw [is_equitable_row_bicoloring_iff] at hColor ⊢
  rcases hColor with ⟨hDisj, hCover, hBalance⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.disjoint_map e.toEmbedding).2 hDisj
  · calc
      red.map e.toEmbedding ∪ blue.map e.toEmbedding
          = (red ∪ blue).map e.toEmbedding := by
              rw [Finset.map_union]
      _ = Finset.univ.map e.toEmbedding := by rw [hCover]
      _ = Finset.univ := Finset.map_univ_equiv e
  · intro j
    -- The column-balance condition is exactly the reindexed difference identity above.
    rw [← row_bicoloring_difference_reindex_rows B e red blue j]
    exact hBalance j

/-- Helper for Theorem 4.59: existence of an equitable row-bicoloring is invariant under a row
reindexing equivalence. -/
lemma exists_equitable_row_bicoloring_reindex_rows_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ n ℤ) (e : ι ≃ κ) :
    (∃ red blue : Finset ι,
      is_equitable_row_bicoloring (B.reindex e.symm (Equiv.refl n)) red blue) ↔
      ∃ red blue : Finset κ, is_equitable_row_bicoloring B red blue := by
  constructor
  · rintro ⟨red, blue, hColor⟩
    -- Map a coloring of the reindexed matrix forward along the row equivalence.
    exact
      ⟨red.map e.toEmbedding, blue.map e.toEmbedding,
        is_equitable_row_bicoloring_reindex_rows B e hColor⟩
  · rintro ⟨red, blue, hColor⟩
    let B' : Matrix ι n ℤ := B.reindex e.symm (Equiv.refl n)
    have hColor' :
        is_equitable_row_bicoloring (B'.reindex e (Equiv.refl n)) red blue := by
      -- Reindexing `B'` back along the inverse equivalence recovers `B`.
      simpa [B', Matrix.reindex_apply] using hColor
    refine ⟨red.map e.symm.toEmbedding, blue.map e.symm.toEmbedding, ?_⟩
    -- Now transport the recovered coloring forward to the once-reindexed matrix.
    exact is_equitable_row_bicoloring_reindex_rows B' e.symm hColor'

/-- Helper for Theorem 4.59: equitable row-bicolorings are equivalent to Boolean `±1` row-signings
whose signed column sums lie in `{0, 1, -1}`. -/
lemma equitable_row_bicoloring_iff_exists_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) :
    (∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue) ↔
      ∃ s : ι → Bool,
        ∀ j,
          (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1 := by
  constructor
  · rintro ⟨red, blue, hColor⟩
    rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, hBalance⟩
    refine ⟨fun i ↦ i ∈ red, ?_⟩
    intro j
    -- Rewrite the signed column sum back to the row-bicoloring difference from the equitable
    -- partition, then reuse the balance clause already present in `hColor`.
    have hRewrite :
        (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
          row_bicoloring_difference B red blue j :=
      boolean_signed_sum_eq_row_bicoloring_difference B hDisj hCover j
    have hRewrite' :
        (∑ i, if i ∈ red then B i j else -B i j) =
          row_bicoloring_difference B red blue j := by
      simpa using hRewrite
    simpa [hRewrite'] using hBalance j
  · rintro ⟨s, hSigned⟩
    let red : Finset ι := Finset.univ.filter fun i ↦ s i
    let blue : Finset ι := Finset.univ.filter fun i ↦ ¬ s i
    refine ⟨red, blue, ?_⟩
    rw [is_equitable_row_bicoloring_iff]
    have hDisj : Disjoint red blue := by
      -- The Boolean choice prevents a row from being both red and blue.
      rw [Finset.disjoint_left]
      intro i hiRed hiBlue
      have hs : s i := by simpa [red] using hiRed
      have hns : ¬ s i := by simpa [blue] using hiBlue
      exact hns hs
    have hCover : red ∪ blue = Finset.univ := by
      -- Every row is colored by its Boolean sign.
      ext i
      by_cases hs : s i
      · simp [red, blue, hs]
      · simp [red, blue, hs]
    refine ⟨?_, ?_, ?_⟩
    · exact hDisj
    · exact hCover
    · intro j
      -- Replace the row-bicoloring difference by the Boolean signed sum supplied by `hSigned`.
      have hSignRewrite :
          (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
            ∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hs : s i <;> simp [red, hs]
      have hRewrite :
          row_bicoloring_difference B red blue j =
            ∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
        calc
          row_bicoloring_difference B red blue j
              = ∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j := by
                  symm
                  exact
                    boolean_signed_sum_eq_row_bicoloring_difference B hDisj hCover j
          _ = ∑ i, (if s i then (1 : ℤ) else -1) * B i j := hSignRewrite
      rw [hRewrite]
      exact hSigned j

/-- Helper for Theorem 4.59: an equitable row-bicoloring on a fixed matrix can be used directly
as a Boolean `±1` row-signing on that same matrix spelling. -/
lemma exists_row_signing_of_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring B red blue) :
    ∃ s : ι → Bool,
      ∀ j,
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1 := by
  -- Repackage the given coloring through the signing equivalence without changing the matrix.
  exact (equitable_row_bicoloring_iff_exists_row_signing B).1 ⟨red, blue, hColor⟩

/-- Helper for Theorem 4.59: `BadRowSet B R` means the row restriction of `B` to `R` admits no
equitable row-bicoloring. -/
def BadRowSet {ρ : Type*} [DecidableEq ρ] (B : Matrix ρ n ℤ) (R : Finset ρ) : Prop :=
  ¬ ∃ red blue : Finset {i // i ∈ R},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id) red blue

/-- Helper for Theorem 4.59: the full row set is bad exactly when the original matrix has no
equitable row-bicoloring. -/
lemma bad_row_set_univ_iff
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ) :
    BadRowSet B (Finset.univ : Finset ρ) ↔
      ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue := by
  let e : {i // i ∈ (Finset.univ : Finset ρ)} ≃ ρ :=
    Equiv.subtypeUnivEquiv fun _ ↦ Finset.mem_univ _
  -- Reindex the universal-row restriction back to `B` and then compare the existential statements.
  simpa [BadRowSet, e, Matrix.reindex_apply] using
    not_congr (exists_equitable_row_bicoloring_reindex_rows_iff B e)

/-- Helper for Theorem 4.59: among the bad row sets of `B`, there is one of minimal cardinality,
and every one-row deletion of that minimal bad row set is colorable. -/
lemma exists_minimal_bad_row_set_with_colorable_row_deletions
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ)
    (hNoColor : ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue) :
    ∃ R : Finset ρ,
      BadRowSet B R ∧
        (∀ ⦃S : Finset ρ⦄, BadRowSet B S → R.card ≤ S.card) ∧
        ∀ r : {i // i ∈ R},
          ∃ red blue : Finset {i // i ∈ R.erase r.1},
            is_equitable_row_bicoloring
              (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id)
              red blue := by
  classical
  let s : Set (Finset ρ) := {R | BadRowSet B R}
  have hsNonempty : s.Nonempty := by
    -- The full row set is bad because the original matrix was assumed to have no coloring.
    exact ⟨Finset.univ, (bad_row_set_univ_iff B).2 hNoColor⟩
  let R : Finset ρ := Function.argminOn Finset.card s hsNonempty
  refine ⟨R, ?_, ?_, ?_⟩
  · -- Record that the chosen row set is indeed bad.
    exact Function.argminOn_mem Finset.card s hsNonempty
  · intro S hBadS
    -- Cardinal minimality is built into the `argminOn` choice of `R`.
    exact Function.argminOn_le Finset.card s hBadS
  · intro r
    by_contra hNoDeletedColor
    have hBadErase : BadRowSet B (R.erase r.1) := by
      simpa [BadRowSet] using hNoDeletedColor
    have hMinCard : R.card ≤ (R.erase r.1).card := by
      exact Function.argminOn_le Finset.card s hBadErase
    have hStrictCard : (R.erase r.1).card < R.card := by
      -- Erasing a row from the chosen row set strictly decreases its cardinality.
      rw [Finset.card_erase_of_mem r.2]
      have hPos : 0 < R.card := Finset.card_pos.mpr ⟨r.1, r.2⟩
      omega
    exact (not_lt_of_ge hMinCard) hStrictCard

/-- Helper for Theorem 4.59: every proper subset of a cardinal-minimal bad row set is colorable. -/
lemma proper_row_subset_colorable_of_minimal_bad_row_set
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ) {R : Finset ρ}
    (hMinBad : ∀ ⦃S : Finset ρ⦄, BadRowSet B S → R.card ≤ S.card)
    {S : Finset ρ} (hSub : S ⊂ R) :
    ∃ red blue : Finset {i // i ∈ S},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ S) id) red blue := by
  by_contra hNoColor
  have hBadS : BadRowSet B S := by
    -- The definition of `BadRowSet` is exactly the negated coloring statement.
    simpa [BadRowSet] using hNoColor
  have hCardLe : R.card ≤ S.card := hMinBad hBadS
  have hCardLt : S.card < R.card := Finset.card_lt_card hSub
  exact (not_lt_of_ge hCardLe) hCardLt

/-- Helper for Theorem 4.59: deleting `r` from the ambient row set `R` is equivalent to deleting
`r` from the restricted row type `R.attach`. -/
def erased_row_subtype_equiv
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (r : {i // i ∈ R}) :
    {i // i ∈ R.erase r.1} ≃ {i : {j // j ∈ R} // i ≠ r} where
  toFun i :=
    ⟨⟨i.1, (Finset.mem_erase.mp i.2).2⟩,
      fun h ↦ (Finset.mem_erase.mp i.2).1 (congrArg (fun x : {j // j ∈ R} ↦ x.1) h)⟩
  invFun i :=
    ⟨i.1.1, Finset.mem_erase.mpr ⟨fun h ↦ i.2 (Subtype.ext h), i.1.2⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: the deleted-row restriction `R.erase r.1` is just a row-reindexing
of the bad restriction `B.submatrix rowR id` with the distinguished row removed. -/
lemma deleted_row_submatrix_eq_reindex
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (r : {i // i ∈ R}) :
    B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id =
      (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
          (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id)).reindex
        (erased_row_subtype_equiv r).symm (Equiv.refl n) := by
  -- Both matrices read off the same ambient entry of `B`.
  ext i j
  rfl

/-- Helper for Theorem 4.59: rows of `A.image Subtype.val` are exactly the rows of `A`, viewed
inside the ambient restriction to `R`. -/
private noncomputable def imageSubtypeRowsEquiv
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ}
    (A : Finset {i // i ∈ R}) :
    {i // i ∈ A.image Subtype.val} ≃ {i : {j // j ∈ R} // i ∈ A} where
  toFun i := by
    classical
    let hmem : ∃ r ∈ A, (r : ρ) = i.1 := Finset.mem_image.mp i.2
    let r : {i // i ∈ R} := Classical.choose hmem
    have hrA : r ∈ A := (Classical.choose_spec hmem).1
    have hrEq : (r : ρ) = i.1 := (Classical.choose_spec hmem).2
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · simpa [hrEq] using r.2
    · have hEqSubtype :
          (⟨i.1, by simpa [hrEq] using r.2⟩ : {j // j ∈ R}) = r := by
        apply Subtype.ext
        exact hrEq.symm
      simpa [hEqSubtype] using hrA
  invFun i :=
    ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: restricting the ambient matrix directly to `A.image Subtype.val`
matches restricting the `R`-row submatrix further to `A`. -/
private lemma imageSubtypeRowsSubmatrixEqReindex
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (A : Finset {i // i ∈ R}) :
    B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id =
      (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
          (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id)).reindex
        (imageSubtypeRowsEquiv A).symm (Equiv.refl n) := by
  -- Both row restrictions evaluate the same ambient entry of `B`.
  ext i j
  have hRow :
      ((imageSubtypeRowsEquiv A i).1 : ρ) = i.1 := rfl
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, hRow]

/-- Helper for Theorem 4.59: equitable row-bicolorings transport between the direct restriction to
`A.image Subtype.val` and the corresponding row submatrix inside the `R`-restriction. -/
private lemma existsEquitableRowBicoloringImageSubtypeRows_iff
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (A : Finset {i // i ∈ R}) :
    (∃ red blue : Finset {i // i ∈ A.image Subtype.val},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id)
        red blue) ↔
      ∃ red blue : Finset {i : {j // j ∈ R} // i ∈ A},
        is_equitable_row_bicoloring
          ((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
            (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id)
          red blue := by
  let B_A : Matrix {i : {j // j ∈ R} // i ∈ A} n ℤ :=
    (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
      (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id
  let e : {i // i ∈ A.image Subtype.val} ≃ {i : {j // j ∈ R} // i ∈ A} :=
    imageSubtypeRowsEquiv A
  have hMatrix :
      B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id =
        B_A.reindex e.symm (Equiv.refl n) := by
    simpa [B_A, e] using imageSubtypeRowsSubmatrixEqReindex B A
  constructor
  · rintro ⟨red, blue, hColor⟩
    have hColor' :
        is_equitable_row_bicoloring (B_A.reindex e.symm (Equiv.refl n)) red blue := by
      -- Rewrite the direct ambient restriction to the `B_A`-reindexed spelling used by the
      -- row-reindexing transport lemma.
      rw [← hMatrix]
      exact hColor
    exact (exists_equitable_row_bicoloring_reindex_rows_iff B_A e).1 ⟨red, blue, hColor'⟩
  · rintro ⟨red, blue, hColor⟩
    rcases (exists_equitable_row_bicoloring_reindex_rows_iff B_A e).2 ⟨red, blue, hColor⟩ with
      ⟨red', blue', hColor'⟩
    refine ⟨red', blue', ?_⟩
    -- Undo the same matrix rewrite to return to the ambient direct restriction.
    rw [hMatrix]
    exact hColor'

/-- Helper for Theorem 4.59: a coloring of the deleted ambient rows becomes a Boolean signing on
the deleted rows of the bad restriction itself. -/
lemma exists_deleted_row_signing_of_colorable_row_deletion
    {ρ : Type u} [DecidableEq ρ] (B : Matrix ρ n ℤ)
    {R : Finset ρ} (r : {i // i ∈ R})
    (hDeleted :
      ∃ red blue : Finset {i // i ∈ R.erase r.1},
        is_equitable_row_bicoloring
          (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id)
          red blue) :
    ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool,
      ∀ j,
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
              (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
              (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
                (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = -1 := by
  let Bdel : Matrix {i : {j // j ∈ R} // i ≠ r} n ℤ :=
    ((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
      (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id)
  have hColorReindexed :
      ∃ red blue : Finset {i // i ∈ R.erase r.1},
        is_equitable_row_bicoloring
          (Bdel.reindex (erased_row_subtype_equiv r).symm (Equiv.refl n))
          red blue := by
    -- Rewrite the ambient deleted-row matrix as the reindexed restriction matrix.
    simpa [Bdel, deleted_row_submatrix_eq_reindex B r] using hDeleted
  have hColorBdel :
      ∃ red blue : Finset {i : {j // j ∈ R} // i ≠ r},
        is_equitable_row_bicoloring Bdel red blue :=
    (exists_equitable_row_bicoloring_reindex_rows_iff Bdel
      (erased_row_subtype_equiv r)).1 hColorReindexed
  -- Convert the deleted-row coloring into the equivalent Boolean `±1` signing.
  simpa [Bdel] using (equitable_row_bicoloring_iff_exists_row_signing Bdel).1 hColorBdel

/-- Helper for Theorem 4.59: extend a deleted-row signing by assigning the missing row the sign
`σ`. -/
def extend_deleted_row_signing
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    ι → Bool :=
  fun i ↦ if h : i = r then σ else s ⟨i, h⟩

/-- Helper for Theorem 4.59: the extension really assigns the chosen sign to the missing row. -/
lemma extend_deleted_row_signing_apply_self
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    extend_deleted_row_signing r σ s r = σ := by
  -- Unfold the extension at the distinguished row.
  simp [extend_deleted_row_signing]

/-- Helper for Theorem 4.59: away from the missing row, the extension agrees with the deleted-row
signing. -/
lemma extend_deleted_row_signing_apply_ne
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool)
    {i : ι} (hi : i ≠ r) :
    extend_deleted_row_signing r σ s i = s ⟨i, hi⟩ := by
  -- Unfold the extension away from the distinguished row.
  simp [extend_deleted_row_signing, hi]

/-- Helper for Theorem 4.59: a row distinct from `r₁` and `r₂` belongs to the exact
double-deleted finset `((Finset.univ : Finset ι).erase r₁).erase r₂`. -/
lemma mem_double_erase_univ_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r₁ r₂ i : ι}
    (hi₂ : i ≠ r₂) (hi₁ : i ≠ r₁) :
    i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂ := by
  simp [hi₂, hi₁]

/-- Helper for Theorem 4.59: the exact double-deleted row set is equivalent to deleting `r₂`
inside the once-deleted row subtype `{i // i ≠ r₁}`. -/
private def doubleErasedRowsEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r₁ r₂ : ι) (hNe : r₁ ≠ r₂) :
    {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} ≃
      {i : {j // j ≠ r₁} // i ≠ ⟨r₂, Ne.symm hNe⟩} where
  toFun i :=
    ⟨⟨i.1, by
        exact (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1⟩,
      fun h ↦ (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val h)⟩
  invFun i :=
    ⟨i.1.1, by
      refine Finset.mem_erase.mpr ?_
      refine ⟨?_, ?_⟩
      · intro hEq
        exact i.2 (Subtype.ext hEq)
      · exact Finset.mem_erase.mpr ⟨i.1.2, Finset.mem_univ _⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: extend a signing on the exact double-deleted row set by prescribing
the signs on the two deleted rows. -/
def extend_double_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    ι → Bool :=
  fun i ↦
    if hi₁ : i = r₁ then σ₁ else
      if hi₂ : i = r₂ then σ₂ else
        tA ⟨i, mem_double_erase_univ_of_ne hi₂ hi₁⟩

/-- Helper for Theorem 4.59: the double-deleted extension uses the prescribed sign on `r₁`. -/
lemma extend_double_deleted_row_signing_apply_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA r₁ = σ₁ := by
  -- Unfold the extension at the first deleted row.
  simp [extend_double_deleted_row_signing]

/-- Helper for Theorem 4.59: the double-deleted extension uses the prescribed sign on `r₂`. -/
lemma extend_double_deleted_row_signing_apply_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA r₂ = σ₂ := by
  -- Unfold the extension at the second deleted row and use `r₂ ≠ r₁`.
  simp [extend_double_deleted_row_signing, hNe]

/-- Helper for Theorem 4.59: away from `r₁` and `r₂`, the double-deleted extension agrees with the
signing on the exact double-deleted row set. -/
lemma extend_double_deleted_row_signing_apply_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r₁ r₂ i : ι} (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool)
    (hi₁ : i ≠ r₁) (hi₂ : i ≠ r₂) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i =
      tA ⟨i, mem_double_erase_univ_of_ne hi₂ hi₁⟩ := by
  -- Unfold the extension away from both deleted rows.
  simp [extend_double_deleted_row_signing, hi₁, hi₂]

/-- Helper for Theorem 4.59: extending a signing on the exact double-deleted row set splits the
full signed column sum into the double-deleted core and the two prescribed row terms. -/
private lemma extendDoubleDeletedSigning_sum_eq_core_plus_pivots
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ) :
    (∑ i, (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) +
        ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let f : ι → ℤ := fun i ↦
    (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j
  have hSplit₁ :
      (∑ i, f i) = Finset.sum (Finset.univ.erase r₁) f + f r₁ := by
    -- Separate the first deleted row from the ambient finite sum.
    have hr₁ : r₁ ∈ (Finset.univ : Finset ι) := by simp
    exact ((Finset.univ : Finset ι).sum_erase_add f hr₁).symm
  have hSplit₂ :
      Finset.sum (Finset.univ.erase r₁) f = Finset.sum A f + f r₂ := by
    -- Remove the second deleted row from the once-deleted sum.
    have hr₂ : r₂ ∈ Finset.univ.erase r₁ := by simp [hNe]
    exact ((Finset.univ.erase r₁).sum_erase_add f hr₂).symm
  have hCore :
      Finset.sum A f =
        ∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) := by
    -- Away from the two deleted rows, the full extension agrees with the `A`-signing itself.
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi₂ : i.1 ≠ r₂ := by
      exact (Finset.mem_erase.mp i.2).1
    have hi₁ : i.1 ≠ r₁ := by
      exact (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1
    have ht_mem :
        extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i.1 = tA i := by
      simpa [A] using
        (extend_double_deleted_row_signing_apply_mem σ₁ σ₂ tA hi₁ hi₂)
    simp [f, Matrix.submatrix_apply, ht_mem]
  calc
    (∑ i, f i) = Finset.sum (Finset.univ.erase r₁) f + f r₁ := hSplit₁
    _ = (Finset.sum A f + f r₂) + f r₁ := by rw [hSplit₂]
    _ = (Finset.sum A f + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j)) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      rw [show f r₂ = ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) by
        simp [f, extend_double_deleted_row_signing_apply_right, hNe]]
      rw [show f r₁ = ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) by
        simp [f, extend_double_deleted_row_signing_apply_left]]
    _ = ((∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if σ₂ then (1 : ℤ) else -1) * B r₂ j)) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      rw [hCore]
    _ = (∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      ring

/-- Helper for Theorem 4.59: on a shared critical column, the two normalized pivot contributions
collapse the double-deleted extension sum to the `A`-core plus `2`. -/
private lemma extendDoubleDeletedSigning_sharedColumn_sum_eq_core_plus_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (hRow₁ : ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = 1)
    (hRow₂ : ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = 1) :
    (∑ i, (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) + 2 := by
  -- Rewrite the full sum through the double-deleted core and substitute the two forced pivots.
  rw [extendDoubleDeletedSigning_sum_eq_core_plus_pivots B r₁ r₂ hNe σ₁ σ₂ tA j, hRow₂, hRow₁]
  ring

/-- Helper for Theorem 4.59: on an even-support column, the signed sum over the exact
double-deleted row set is even whenever the two deleted entries are nonzero. -/
private lemma doubleDeletedCore_even_of_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hr₁ : B r₁ j ≠ 0) (hr₂ : B r₂ j ≠ 0) :
    Even (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix
          (Function.Embedding.subtype
            fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let fullSigned : ι → ℤ := fun i ↦
    (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j
  let core : ℤ :=
    ∑ i : {x // x ∈ A},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)
  have hFullValues :
      ∀ i, fullSigned i = 0 ∨ fullSigned i = 1 ∨ fullSigned i = -1 := by
    intro i
    -- Each signed ambient column entry is still a `(0, ±1)` value.
    simpa [fullSigned] using
      signed_zero_one_neg_one (extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hSupportEq :
      Function.support fullSigned = Function.support fun i ↦ B i j := by
    ext i
    -- Multiplying by a Boolean sign does not change whether a column entry is zero.
    dsimp [fullSigned]
    cases hsi : extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i <;>
      by_cases hBij : B i j = 0 <;> simp [hsi, hBij]
  have hFullEven : Even (∑ i, fullSigned i) := by
    -- The ambient signed column inherits even parity from the even support of the original column.
    apply even_sum_of_zero_one_neg_one_even_support fullSigned hFullValues
    simpa [hSupportEq] using hEvenSupport
  have hRow₁Value :
      ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = 1 ∨
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = -1 := by
    rcases HasZeroOneNegOneEntries.apply hB r₁ j with hZero | hOne | hNegOne
    · exact (hr₁ hZero).elim
    · cases σ₁ <;> simp [hOne]
    · cases σ₁ <;> simp [hNegOne]
  have hRow₂Value :
      ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = 1 ∨
        ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = -1 := by
    rcases HasZeroOneNegOneEntries.apply hB r₂ j with hZero | hOne | hNegOne
    · exact (hr₂ hZero).elim
    · cases σ₂ <;> simp [hOne]
    · cases σ₂ <;> simp [hNegOne]
  have hPivotsEven :
      Even (((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j)) := by
    rcases hRow₂Value with hRow₂One | hRow₂NegOne
    · rcases hRow₁Value with hRow₁One | hRow₁NegOne
      · rw [hRow₂One, hRow₁One]
        norm_num
      · rw [hRow₂One, hRow₁NegOne]
        norm_num
    · rcases hRow₁Value with hRow₁One | hRow₁NegOne
      · rw [hRow₂NegOne, hRow₁One]
        norm_num
      · rw [hRow₂NegOne, hRow₁NegOne]
        norm_num
  have hSplit :
      (∑ i, fullSigned i) =
        core + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
    -- Rewrite the ambient signed column into the exact double-deleted core plus the two pivots.
    simpa [A, core, fullSigned] using
      extendDoubleDeletedSigning_sum_eq_core_plus_pivots B r₁ r₂ hNe σ₁ σ₂ tA j
  have hCorePlusPivotsEven :
      Even (core + (((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j))) := by
    -- Reassociate the split so the even pivot contribution can be subtracted in one step.
    have hFullEven' :
        Even
          (core + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
            ((if σ₁ then (1 : ℤ) else -1) * B r₁ j)) := by
      rw [← hSplit]
      exact hFullEven
    simpa [add_assoc] using hFullEven'
  -- Subtract the even two-pivot contribution from the even ambient signed sum.
  simpa [A, core] using hCorePlusPivotsEven.sub hPivotsEven

/-- Helper for Theorem 4.59: on an even-support shared critical column, any balanced signing of the
exact double-deleted row set has core sum `0`. -/
private lemma doubleDeletedCore_eq_zero_of_balanced_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (htA :
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 0 ∨
        (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype
                fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 1 ∨
          (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
            (if tA i then (1 : ℤ) else -1) *
              ((B.submatrix
                (Function.Embedding.subtype
                  fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hr₁ : B r₁ j ≠ 0) (hr₂ : B r₂ j ≠ 0) :
    (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix
          (Function.Embedding.subtype
            fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 0 := by
  have hCoreEven :
      Even (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) :=
    doubleDeletedCore_even_of_evenSupport hB r₁ r₂ hNe σ₁ σ₂ tA j hEvenSupport hr₁ hr₂
  rcases htA with hZero | hOne | hNegOne
  · exact hZero
  · exfalso
    rw [hOne] at hCoreEven
    norm_num at hCoreEven
  · exfalso
    rw [hNegOne] at hCoreEven
    norm_num at hCoreEven

/-- Helper for Theorem 4.59: flipping every Boolean sign flips the value of the extension as well. -/
lemma extend_deleted_row_signing_compl
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    extend_deleted_row_signing r (!σ) (fun i ↦ !(s i)) =
      fun i ↦ !(extend_deleted_row_signing r σ s i) := by
  -- Check the distinguished row and the deleted rows separately.
  funext i
  by_cases hi : i = r
  · simp [extend_deleted_row_signing, hi]
  · simp [extend_deleted_row_signing, hi]

/-- Helper for Theorem 4.59: negating a value in `{0, 1, -1}` keeps it in `{0, 1, -1}`. -/
lemma neg_eq_zero_one_neg_one_of_zero_one_neg_one
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    -z = 0 ∨ -z = 1 ∨ -z = -1 := by
  -- Reduce to the three allowed values of `z`.
  rcases hz with rfl | rfl | rfl <;> norm_num

/-- Helper for Theorem 4.59: complementing every Boolean sign negates the signed column sum. -/
lemma signed_column_sum_compl_eq_neg
    {ι : Type*} [Fintype ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (s : ι → Bool) (j : κ) :
    (∑ i, (if !s i then (1 : ℤ) else -1) * B i j) =
      -∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
  -- Rewrite each complemented term as the negative of the original term and sum.
  calc
    (∑ i, (if !s i then (1 : ℤ) else -1) * B i j)
        = ∑ i, -((if s i then (1 : ℤ) else -1) * B i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            cases hs : s i <;> simp [hs]
    _ = -∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
          rw [Finset.sum_neg_distrib]

/-- Helper for Theorem 4.59: complementing a deleted-row signing preserves the
`{0, 1, -1}`-valued deleted-column balance family. -/
private lemma deletedRowBalanceFamily_compl
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} {r : ι} (s : {i // i ≠ r} → Bool)
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) :
    ∀ j',
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
        (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
          (∑ i, (if (!s i) then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
  intro j'
  have hNegDeleted :
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) := by
    -- Complementing every deleted-row sign negates the deleted signed column sum.
    simpa using
      signed_column_sum_compl_eq_neg
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j'
  rcases hs j' with hZero | hOne | hNegOne
  · left
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = 0 := by rw [hZero]; norm_num
  · right
    right
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = -1 := by rw [hOne]
  · right
    left
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = 1 := by rw [hNegOne]; norm_num

/-- Helper for Theorem 4.59: extending across the missing row splits the full signed column sum
into the deleted-row contribution plus the missing-row term. -/
lemma extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ) :
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {i // i ≠ r},
        (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
        ((if σ then (1 : ℤ) else -1) * B r j) := by
  let f : ι → ℤ := fun i ↦
    (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  -- Split the finite row sum into the distinguished row and the deleted-row subtype.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j)
        = ((if extend_deleted_row_signing r σ s r then (1 : ℤ) else -1) * B r j) +
            ∑ i : {i // i ≠ r},
              (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j := by
            simpa [f] using Fintype.sum_eq_add_sum_subtype_ne f r
    _ = ((if σ then (1 : ℤ) else -1) * B r j) +
          ∑ i : {i // i ≠ r},
            (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j := by
          congr 1
          · simp [extend_deleted_row_signing]
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simp [extend_deleted_row_signing, Matrix.submatrix_apply, i.2]
    _ = (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
          ((if σ then (1 : ℤ) else -1) * B r j) := by
            rw [add_comm]

/-- Helper for Theorem 4.59: a signing on a bad row restriction must be unbalanced in some
column. -/
lemma exists_unbalanced_column_of_signing_of_no_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (s : ι → Bool) :
    ∃ j,
      ¬ ((∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1) := by
  -- Otherwise the signing itself would produce an equitable row-bicoloring.
  by_contra hNoColumn
  apply hBad
  refine (equitable_row_bicoloring_iff_exists_row_signing B).2 ?_
  refine ⟨s, ?_⟩
  intro j
  by_contra hj
  exact hNoColumn ⟨j, hj⟩

/-- Helper for Theorem 4.59: every deleted-row signing extension on a bad row restriction is
unbalanced in some column. -/
lemma exists_unbalanced_column_of_extended_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    ∃ j,
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1) := by
  -- Apply the bad-column witness to the extended full-row signing.
  exact
    exists_unbalanced_column_of_signing_of_no_equitable_row_bicoloring B hBad
      (extend_deleted_row_signing r σ s)

/-- Helper for Theorem 4.59: once two `{0, 1, -1}` contributions add to an unbalanced value, the
sum must already be `2` or `-2`. -/
lemma full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hBad : ¬ (a + b = 0 ∨ a + b = 1 ∨ a + b = -1)) :
    a + b = 2 ∨ a + b = -2 := by
  -- Exhaust the nine possible `(0, ±1)` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exfalso; simpa using hBad

/-- Helper for Theorem 4.59: a bad column for an extended deleted-row signing can be normalized,
possibly by complementing the signing, into a genuine critical column with signed pivot value `1`.
-/
private lemma normalizeUnbalancedDeletedRowExtensionAtColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) {j : κ}
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1)
    (hBad :
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1)) :
    ∃ s' : {i // i ≠ r} → Bool, ∃ σ' : Bool,
      (∀ j',
        (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ' s' i then (1 : ℤ) else -1) * B i j) = 2 ∧
      (((if σ' then (1 : ℤ) else -1) * B r j) = 1) := sorry
/- Proof attempt retained for later proof-stage repair.
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the bad full sum into its deleted contribution and the distinguished row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    simpa [deletedSum] using hs j
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished row contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hBadSplit :
      ¬ (deletedSum + rowTerm = 0 ∨ deletedSum + rowTerm = 1 ∨ deletedSum + rowTerm = -1) := by
    intro hBalanced
    apply hBad
    rcases hBalanced with hZero | hOne | hNegOne
    · left
      rw [hSplit]
      exact hZero
    · right
      left
      rw [hSplit]
      exact hOne
    · right
      right
      rw [hSplit]
      exact hNegOne
  have hTwoOrNegTwo :
      deletedSum + rowTerm = 2 ∨ deletedSum + rowTerm = -2 := by
    exact
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
        hDeletedValue hRowValue hBadSplit
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · have hPair :
        deletedSum = 1 ∧ rowTerm = 1 := by
      -- Exhaust the finitely many `{0, 1, -1}` possibilities for the two summands.
      rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedZero, hRowZero] at hTwo
          norm_num at hTwo
        · rw [hDeletedZero, hRowOne] at hTwo
          norm_num at hTwo
        · rw [hDeletedZero, hRowNegOne] at hTwo
          norm_num at hTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedOne, hRowZero] at hTwo
          norm_num at hTwo
        · exact ⟨hDeletedOne, hRowOne⟩
        · rw [hDeletedOne, hRowNegOne] at hTwo
          norm_num at hTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedNegOne, hRowZero] at hTwo
          norm_num at hTwo
        · rw [hDeletedNegOne, hRowOne] at hTwo
          norm_num at hTwo
        · rw [hDeletedNegOne, hRowNegOne] at hTwo
          norm_num at hTwo
    refine ⟨s, σ, hs, ?_, ?_⟩
    · rw [hSplit]
      exact hTwo
    · simpa [rowTerm] using hPair.2
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !(s i)
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
      -- Complement the deleted witness once so the same bad column becomes positive.
      simpa [s'] using deletedRowBalanceFamily_compl s hs
    have hPair :
        deletedSum = -1 ∧ rowTerm = -1 := by
      -- The same finite case split isolates the unique way to sum to `-2`.
      rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedZero, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedZero, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedZero, hRowNegOne] at hNegTwo
          norm_num at hNegTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedOne, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedOne, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedOne, hRowNegOne] at hNegTwo
          norm_num at hNegTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedNegOne, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedNegOne, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · exact ⟨hDeletedNegOne, hRowNegOne⟩
    have hCompl :
        extend_deleted_row_signing r (!σ) s' =
          fun i ↦ !(extend_deleted_row_signing r σ s i) := by
      -- Flipping both the deleted signs and the distinguished-row sign flips the full extension.
      simpa [s'] using extend_deleted_row_signing_compl r σ s
    refine ⟨s', !σ, hs', ?_, ?_⟩
    · calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r σ s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r σ s) j
        _ = -(deletedSum + rowTerm) := by rw [hSplit]
        _ = -(-2 : ℤ) := by rw [hNegTwo]
        _ = 2 := by norm_num
    · have hRowCompl :
          ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := by
        cases σ <;> simp [rowTerm]
      calc
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := hRowCompl
        _ = -(-1 : ℤ) := by rw [hPair.2]
        _ = 1 := by norm_num
-/

/-- Helper for Theorem 4.59: a bad extended deleted-row signing can be normalized using either the
original deleted witness or its global complement, and the chosen branch is recorded explicitly. -/
private lemma normalizeUnbalancedDeletedRowExtensionAtColumn_withOrigin
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) {j : κ}
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1)
    (hBad :
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1)) :
    ∃ s' : {i // i ≠ r} → Bool, ∃ σ' : Bool,
      ((s' = s ∧ σ' = σ) ∨ (s' = (fun i ↦ !s i) ∧ σ' = !σ)) ∧
      (∀ j',
        (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ' s' i then (1 : ℤ) else -1) * B i j) = 2 ∧
      (((if σ' then (1 : ℤ) else -1) * B r j) = 1) := sorry
/- Proof attempt retained for later proof-stage repair.
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the bad full-column sum into the deleted contribution and the distinguished row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hs j
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished-row contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hBadSplit :
      ¬ (deletedSum + rowTerm = 0 ∨ deletedSum + rowTerm = 1 ∨ deletedSum + rowTerm = -1) := by
    intro hBalanced
    apply hBad
    rcases hBalanced with hZero | hOne | hNegOne
    · left
      rw [hSplit]
      exact hZero
    · right
      left
      rw [hSplit]
      exact hOne
    · right
      right
      rw [hSplit]
      exact hNegOne
  have hTwoOrNegTwo :
      deletedSum + rowTerm = 2 ∨ deletedSum + rowTerm = -2 := by
    -- A bad full column has to take one of the two exceptional values `±2`.
    exact
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
        hDeletedValue hRowValue hBadSplit
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
      -- The positive branch forces both summands to be `1`.
      exact summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowValue hTwo
    refine ⟨s, σ, ?_⟩
    refine ⟨Or.inl ⟨rfl, rfl⟩, hs, ?_, ?_⟩
    · rw [hSplit]
      exact hTwo
    · simpa [rowTerm] using hPair.2
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !s i
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
      -- Complementing the deleted-row signs preserves the balance family.
      simpa [s'] using deletedRowBalanceFamily_compl s hs
    have hPair : deletedSum = -1 ∧ rowTerm = -1 := by
      -- The negative branch forces both summands to be `-1`.
      exact
        summands_eq_neg_one_of_zero_one_neg_one_add_eq_neg_two hDeletedValue hRowValue hNegTwo
    have hCompl :
        extend_deleted_row_signing r (!σ) s' =
          fun i ↦ !(extend_deleted_row_signing r σ s i) := by
      -- Flipping the deleted signs and the distinguished-row sign flips the whole extension.
      simpa [s'] using extend_deleted_row_signing_compl r σ s
    have hFlippedSum :
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j) =
          -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
      -- The complemented extension negates the bad full-column sum.
      calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r σ s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r σ s) j
    have hRowCompl :
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := by
      cases σ <;> simp [rowTerm]
    refine ⟨s', !σ, ?_⟩
    refine ⟨Or.inr ⟨rfl, rfl⟩, hs', ?_, ?_⟩
    · calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) :=
              hFlippedSum
        _ = -(deletedSum + rowTerm) := by rw [hSplit]
        _ = -(-2 : ℤ) := by rw [hNegTwo]
        _ = 2 := by norm_num
    · calc
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := hRowCompl
        _ = -(-1 : ℤ) := by rw [hPair.2]
        _ = 1 := by norm_num
-/

/-- Helper for Theorem 4.59: a deleted-row signing on a bad row restriction can be normalized so
that some extended signed column sum is exactly `2`. -/
lemma exists_normalized_critical_column_of_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (hB : HasZeroOneNegOneEntries B)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (r : ι)
    (hDeleted :
      ∃ s : {i // i ≠ r} → Bool,
        ∀ j,
          (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1) :
    ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool, ∃ j : κ,
      (∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2 := by
  classical
  rcases hDeleted with ⟨s, hs⟩
  rcases exists_unbalanced_column_of_extended_deleted_row_signing B hBad r true s with
    ⟨j, hj⟩
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) =
        (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j := by
    -- With `σ = true`, the missing-row term is exactly the original matrix entry.
    simpa using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r true s j
  have hRowValue :
      B r j = 0 ∨ B r j = 1 ∨ B r j = -1 := by
    -- The distinguished row entry is still a `(0, ±1)` value.
    simpa using HasZeroOneNegOneEntries.apply hB r j
  have hTwoOrNegTwo :
      (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) = 2 ∨
        (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) = -2 := by
    -- Rewrite the bad full sum as deleted contribution plus the missing-row term.
    have hBadSum :
        ¬ (((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = 0 ∨
          ((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = 1 ∨
          ((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = -1) := by
      -- Transfer the bad-column witness through the previously established sum split.
      intro hBalanced
      apply hj
      rw [hSplit]
      exact hBalanced
    have hDeletedValue :
        (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
          (∑ i : {i // i ≠ r},
            (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
            (∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1 :=
      hs j
    have hSum :=
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one hDeletedValue hRowValue hBadSum
    rcases hSum with hSum | hSum
    · left
      rw [hSplit]
      exact hSum
    · right
      rw [hSplit]
      exact hSum
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · -- The positive critical column already has the desired normalization.
    exact ⟨s, true, j, hs, hTwo⟩
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !(s i)
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = -1 := by
      intro j'
      -- Complementing all deleted-row signs negates the deleted signed sum.
      have hNegDeleted :
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') := by
        simpa [s'] using
          signed_column_sum_compl_eq_neg
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j'
      rcases hs j' with hZero | hOne | hNegOne
      · left
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = 0 := by rw [hZero]; norm_num
      · right
        right
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = -1 := by rw [hOne]
      · right
        left
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = 1 := by rw [hNegOne]; norm_num
    have hCompl :
        extend_deleted_row_signing r false s' =
          fun i ↦ !(extend_deleted_row_signing r true s i) := by
      -- Flipping the deleted-row signs and the missing-row sign flips the whole extension.
      simpa [s'] using extend_deleted_row_signing_compl r true s
    have hFlippedSum :
        (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j) =
          -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) := by
      -- Apply the global sign-flip identity to the extended signing itself.
      calc
        (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r true s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r true s) j
    refine ⟨s', false, j, hs', ?_⟩
    -- The complemented full signing turns the `-2` witness into the required `2`.
    calc
      (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j)
          = -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) :=
            hFlippedSum
      _ = -(-2 : ℤ) := by rw [hNegTwo]
      _ = 2 := by norm_num

/-- Helper for Theorem 4.59: if two `{0, 1, -1}` integers add up to `2`, then both are `1`. -/
lemma summands_eq_one_of_zero_one_neg_one_add_eq_two
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (h : a + b = 2) :
    a = 1 ∧ b = 1 := by
  -- Exhaust the finitely many possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at h
  exact ⟨rfl, rfl⟩

/-- Helper for Theorem 4.59: if two `{0, 1, -1}` integers add up to `-2`, then both are `-1`. -/
lemma summands_eq_neg_one_of_zero_one_neg_one_add_eq_neg_two
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (h : a + b = -2) :
    a = -1 ∧ b = -1 := by
  -- Exhaust the finitely many possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at h
  exact ⟨rfl, rfl⟩

/-- Helper for Theorem 4.59: a finite `(0, ±1)`-family with even total sum has even nonzero
support. -/
lemma even_support_of_zero_one_neg_one_even_sum
    {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1 ∨ f i = -1)
    (hs : Even (∑ i, f i)) :
    Even (Function.support f).ncard := by
  classical
  have hIndicator :
      (∑ i, (((f i : ℤ) : ZMod 2))) =
        ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
    calc
      (∑ i, (((f i : ℤ) : ZMod 2)))
          = ∑ i, (if f i = 0 then 0 else 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using zmod_two_cast_eq_indicator_of_zero_one_neg_one (hf i)
      _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hfi : f i = 0 <;> simp [hfi]
  have hCardZero :
      ((((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2)) = 0 := by
    calc
      ((((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2))
          = Finset.sum (Finset.univ.filter (fun i ↦ f i ≠ 0)) (fun _ ↦ (1 : ZMod 2)) := by
              symm
              rw [Finset.card_eq_sum_ones]
              simp
      _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ i, (((f i : ℤ) : ZMod 2)) := hIndicator.symm
      _ = (((∑ i, f i : ℤ) : ZMod 2)) := by simp
      _ = 0 := Even.intCast_zmod_two hs
  have hEvenToFinset : Even ({i | f i ≠ 0}.toFinset.card) := by
    simpa [Set.toFinset_setOf] using (ZMod.natCast_eq_zero_iff_even.1 hCardZero)
  -- Convert the finitary support cardinality back to `Function.support`.
  simpa [Function.support, Set.ncard_eq_toFinset_card'] using hEvenToFinset

/-- Helper for Theorem 4.59: signing a full column by an extended deleted-row Boolean assignment
preserves even column sums when the underlying column has even nonzero support. -/
lemma even_extended_signed_column_sum_of_even_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    Even (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
  let signedColumn : ι → ℤ := fun i ↦
    (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  have hValues : ∀ i, signedColumn i = 0 ∨ signedColumn i = 1 ∨ signedColumn i = -1 := by
    intro i
    -- Each signed entry is still a `(0, ±1)` value.
    simpa [signedColumn] using
      signed_zero_one_neg_one (extend_deleted_row_signing r σ s i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hSupport :
      Function.support signedColumn = Function.support fun i ↦ B i j := by
    ext i
    -- Multiplying by the Boolean sign does not change whether the entry is zero.
    by_cases hi : extend_deleted_row_signing r σ s i
    · simp [signedColumn, hi]
    · simp [signedColumn, hi]
  -- Transfer the even-support parity lemma to the signed full column.
  simpa [signedColumn, hSupport] using
    even_sum_of_zero_one_neg_one_even_support signedColumn hValues
      (by simpa [hSupport] using hEvenSupport)

/-- Helper for Theorem 4.59: for a fixed deleted-row signing on an even-support column, the
deleted signed sum vanishes exactly when the distinguished row entry vanishes. -/
lemma deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ↔
      B r j = 0 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hFullEven :
      Even (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
    -- The extended signed full column inherits even parity from the original even-support column.
    exact even_extended_signed_column_sum_of_even_support hB r σ s j hEvenSupport
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the full signed column into the deleted part and the distinguished-row contribution.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted witness already restricts the deleted sum to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished-row contribution is a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  constructor
  · intro hZero
    have hZero' : deletedSum = 0 := by
      simpa [deletedSum] using hZero
    have hRowEven : Even rowTerm := by
      -- If the deleted part vanishes, the full even sum is exactly the row term.
      have hFullEq :
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = rowTerm := by
        rw [hSplit, hZero', zero_add]
      rw [← hFullEq]
      exact hFullEven
    rcases hRowValue with hRowZero | hRowOne | hRowNegOne
    · have hEntryValue : B r j = 0 ∨ B r j = 1 ∨ B r j = -1 := HasZeroOneNegOneEntries.apply hB r j
      rcases hEntryValue with hEntryZero | hEntryOne | hEntryNegOne
      · exact hEntryZero
      · exfalso
        cases σ <;> simp [rowTerm, hEntryOne] at hRowZero
      · exfalso
        cases σ <;> simp [rowTerm, hEntryNegOne] at hRowZero
    · rw [hRowOne] at hRowEven
      norm_num at hRowEven
    · rw [hRowNegOne] at hRowEven
      norm_num at hRowEven
  · intro hEntryZero
    have hRowZero : rowTerm = 0 := by
      simp [rowTerm, hEntryZero]
    have hDeletedEven : Even deletedSum := by
      -- If the row entry vanishes, the deleted sum is the full even signed column sum.
      have hFullEq :
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = deletedSum := by
        rw [hSplit, hRowZero, add_zero]
      rw [← hFullEq]
      exact hFullEven
    rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
    · simpa [deletedSum] using hDeletedZero
    · rw [hDeletedOne] at hDeletedEven
      norm_num at hDeletedEven
    · rw [hDeletedNegOne] at hDeletedEven
      norm_num at hDeletedEven

/-- Helper for Theorem 4.59: on an even-support column, a deleted-row witness with deleted sum
`1` or `-1` forces the distinguished row entry to be nonzero. -/
private lemma missingRow_nonzero_of_deletedSum_eq_one_or_negOne_of_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    B r j ≠ 0 := by
  intro hZero
  have hDeletedZero :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 := by
    have hDeletedValue :
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1 := by
      rcases hDeletedEq with hOne | hNegOne
      · exact Or.inr (Or.inl hOne)
      · exact Or.inr (Or.inr hNegOne)
    -- Convert the zero row entry into a vanishing deleted sum through the even-support parity API.
    exact
      (deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
        hB r σ s j hDeletedValue hEvenSupport).2 hZero
  rcases hDeletedEq with hOne | hNegOne
  · rw [hOne] at hDeletedZero
    norm_num at hDeletedZero
  · rw [hNegOne] at hDeletedZero
    norm_num at hDeletedZero

/-- Helper for Theorem 4.59: any nonzero `(0, ±1)` entry admits a Boolean sign making its signed
contribution equal to `1`. -/
private lemma exists_bool_sign_mul_eq_one_of_zeroOneNegOne_nonzero
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) (hne : z ≠ 0) :
    ∃ σ : Bool, ((if σ then (1 : ℤ) else -1) * z) = 1 := by
  rcases hz with hZero | hOne | hNegOne
  · exact (hne hZero).elim
  · refine ⟨true, ?_⟩
    simp [hOne]
  · refine ⟨false, ?_⟩
    simp [hNegOne]

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
vanishes, then the exact common-core contribution is `-1`. -/
private lemma commonCore_eq_neg_one_of_deleted_eq_zero_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hDeleted : core + rowTerm = 0)
    (hRow : rowTerm = 1) :
    core = -1 := by
  -- Solve the common-core value by subtracting the normalized kept-row contribution.
  linarith

/-- Helper for Theorem 4.59: complementing a signing on an exact row-restricted submatrix negates
its signed column sum. -/
private lemma restrictedSignedColumnSum_compl_eq_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (s : {i // i ∈ A} → Bool) (j : κ) :
    (∑ i : {x // x ∈ A},
        (if !s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      -(∑ i : {x // x ∈ A},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
  -- This is the exact-core version of the global complement identity, specialized once so later
  -- bad-column arguments can stay in the stable `A`-restricted spelling.
  simpa using
    signed_column_sum_compl_eq_neg
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) s j

/-- Helper for Theorem 4.59: `sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j` records the
fixed-column common-core overlap premise that the two signings have the same `±1` coefficient on
every supported row of the exact `A`-restricted column. -/
private def sharedCriticalOverlapCoeffEqOnBadSupport
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ) : Prop :=
  ∀ i : {x // x ∈ A},
    ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
      (if s₁ i then (1 : ℤ) else -1) = (if s₂ i then (1 : ℤ) else -1)

/-- Helper for Theorem 4.59: `sharedCriticalBadSupport B A j` is the support of the fixed column
`j`, viewed inside the exact common-core row type `{i // i ∈ A}`. -/
private def sharedCriticalBadSupport
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (j : κ) :=
  {i : {x // x ∈ A} //
    ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0}

/-- Helper for Theorem 4.59: proving sign agreement on the support subtype of a fixed
exact-common-core column is equivalent to proving it rowwise with the support hypothesis as an
explicit premise. -/
private lemma sharedCriticalSignEqOnBadSupport_of_restricted
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (j : κ)
    (s₁ s₂ : {i // i ∈ A} → Bool)
    (hRestricted :
      ∀ i : sharedCriticalBadSupport B A j, s₁ i.1 = s₂ i.1) :
    ∀ i : {x // x ∈ A},
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
        s₁ i = s₂ i := by
  intro i hBij
  -- Package the supported row into the fixed support subtype, then project the restricted
  -- sign-equality statement back to the original rowwise formulation.
  exact hRestricted ⟨i, hBij⟩

/-- Helper for Theorem 4.59: two exact-row-restricted signings give the same signed column sum
whenever their coefficients agree on every row where the column entry is nonzero. -/
private lemma restrictedSignedColumnSum_eq_of_coeffEq_on_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff :
      ∀ i : {x // x ∈ A},
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
          (if s₁ i then (1 : ℤ) else -1) =
            (if s₂ i then (1 : ℤ) else -1)) :
    (∑ i : {x // x ∈ A},
        (if s₁ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      (∑ i : {x // x ∈ A},
        (if s₂ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := sorry
/- Proof attempt retained for later proof-stage repair.
  -- Reduce the restricted signed-sum equality to the rows where the fixed column is actually
  -- supported; zero entries contribute `0` regardless of the chosen Boolean sign.
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hBij :
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) = 0
  · simp [hBij]
  · rw [hCoeff i hBij]
-/

/-- Helper for Theorem 4.59: agreement of two Boolean signings on the supported rows of a fixed
exact-common-core column upgrades immediately to agreement of their `±1` coefficients there. -/
private lemma sharedCriticalOverlapCoeffEqOnBadSupport_of_signEq
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hSignEq :
      ∀ i : {x // x ∈ A},
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
          s₁ i = s₂ i) :
    sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j := by
  intro i hBij
  -- Once the Boolean signs agree on the supported rows, the corresponding `±1` coefficients are
  -- literally the same.
  simp [hSignEq i hBij]

/-- Helper for Theorem 4.59: the packaged fixed-column overlap premise upgrades immediately to the
corresponding equality of exact-common-core signed sums. -/
private lemma sharedCriticalCoreSumsEq_of_overlapCoeffEqOnBadSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff : sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j) :
    (∑ i : {x // x ∈ A},
        (if s₁ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      (∑ i : {x // x ∈ A},
        (if s₂ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
  -- This is the exact-core wrapper around the supportwise coefficient premise.
  exact restrictedSignedColumnSum_eq_of_coeffEq_on_support B A s₁ s₂ j hCoeff

/-- Helper for Theorem 4.59: once the bad and aligned exact-core sums are identified, the zero
branch values `1` and `-1` are incompatible. -/
private lemma sharedCriticalZeroBranchContradiction
    {badCore alignedCore : ℤ}
    (hEq : badCore = alignedCore)
    (hBad : badCore = 1)
    (hAligned : alignedCore = -1) :
    False := by
  -- Equal exact-core sums cannot simultaneously take the normalized zero-branch values `1` and
  -- `-1`.
  linarith

/-- Helper for Theorem 4.59: if two exact-common-core signings have the same `±1` coefficients on
the supported rows of the fixed bad column, then the aligned zero branch contradicts the
normalized core values `1` and `-1`. -/
private lemma sharedCriticalAlignedZeroBranchImpossible_of_overlapCoeffEq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (sBad sAligned : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff : sharedCriticalOverlapCoeffEqOnBadSupport B A sBad sAligned j)
    (hBadCore :
      (∑ i : {x // x ∈ A},
          (if sBad i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) = 1)
    (hAlignedCore :
      (∑ i : {x // x ∈ A},
          (if sAligned i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) = -1) :
    False := by
  have hCoreEq :
      (∑ i : {x // x ∈ A},
          (if sBad i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
        (∑ i : {x // x ∈ A},
          (if sAligned i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
    -- Upgrade the fixed-column overlap premise to equality of the two exact-core signed sums.
    exact
      sharedCriticalCoreSumsEq_of_overlapCoeffEqOnBadSupport
        B A sBad sAligned j hCoeff
  -- The generic zero-branch contradiction now closes the normalized `1 = -1` clash.
  exact sharedCriticalZeroBranchContradiction hCoreEq hBadCore hAlignedCore

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
equals `1` or `-1`, then the exact common-core contribution is `0` or `-2`. -/
private lemma commonCore_eq_zero_or_negTwo_of_deleted_eq_one_or_negOne_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hDeleted : core + rowTerm = 1 ∨ core + rowTerm = -1)
    (hRow : rowTerm = 1) :
    core = 0 ∨ core = -2 := by
  -- Normalize the deleted-row value against the fixed kept-row contribution `1`.
  rcases hDeleted with hDeleted | hDeleted
  · left
    linarith
  · right
    linarith

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
has exact common-core contribution `-2`, then the deleted-row sum itself is `-1`. -/
private lemma deleted_eq_neg_one_of_commonCore_eq_negTwo_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hCore : core = -2)
    (hRow : rowTerm = 1) :
    core + rowTerm = -1 := by
  -- Substitute the normalized common-core and kept-row values and simplify.
  linarith

/-- Helper for Theorem 4.59: once the deleted-row sum is `1`, a nonzero distinguished row entry
can be signed so that the full extended signed column sum becomes `2`. -/
private lemma exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1)
    (hne : B r j ≠ 0) :
    ∃ σ : Bool,
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2 := by
  rcases
      exists_bool_sign_mul_eq_one_of_zeroOneNegOne_nonzero
        (HasZeroOneNegOneEntries.apply hB r j) hne with
    ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  -- Split the full signed column into the deleted-row contribution and the chosen pivot term.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j)
        =
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
        ((if σ then (1 : ℤ) else -1) * B r j) := by
            simpa using extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
    _ = 1 + 1 := by rw [hDeletedEq, hσ]
    _ = 2 := by norm_num

/-- Helper for Theorem 4.59: if a deleted-row sum is `-1`, then complementing the deleted-row
signing turns it into a normalized critical full-column witness. -/
private lemma exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_negOne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hne : B r j ≠ 0) :
    ∃ σ : Bool,
      (∑ i, (if extend_deleted_row_signing r σ (fun i ↦ !s i) i then (1 : ℤ) else -1) * B i j) = 2 := by
  have hDeletedComplEq :
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 := by
    -- Complementing every deleted-row sign negates the deleted signed column sum.
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
          =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) := by
              simpa using
                signed_column_sum_compl_eq_neg
                  (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j
      _ = 1 := by
        rw [hDeletedEq]
        norm_num
  -- After the complement rewrite, reuse the existing `deleted sum = 1` witness API.
  exact
    exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
      hB r (fun i ↦ !s i) j hDeletedComplEq hne

/-- Helper for Theorem 4.59: a normalized critical column has a nonzero pivot entry and even full
column support. -/
lemma criticalColumn_deletedSum_and_signedPivot_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∧
      ((if σ then (1 : ℤ) else -1) * B r j) = 1 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the critical full-column sum into the deleted-row part and the pivot-row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness already constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The pivot term is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Since the full signed critical column sums to `2`, both summands must be `1`.
    apply summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowTermValue
    calc
      deletedSum + rowTerm
          = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j := by
              rw [hSplit]
      _ = 2 := hCritical
  simpa [deletedSum, rowTerm] using hPair

/-- Helper for Theorem 4.59: a normalized critical column has a nonzero pivot entry and even full
column support. -/
lemma criticalColumn_hasNonzeroPivot_and_evenColumnSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    B r j ≠ 0 ∧ Even (Function.support fun i ↦ B i j).ncard := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  let signedColumn : ι → ℤ :=
    fun i ↦ (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  have hSplit :
      (∑ i, signedColumn i) = deletedSum + rowTerm := by
    -- Split the full signed sum into the deleted-row contribution and the pivot-row term.
    simpa [deletedSum, rowTerm, signedColumn] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The pivot contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hOnePair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Reuse the extracted `1 + 1` split for this critical column.
    simpa [deletedSum, rowTerm] using
      criticalColumn_deletedSum_and_signedPivot_eq_one hB r s σ j hDeleted hCritical
  have hNonzero : B r j ≠ 0 := by
    -- A pivot contribution equal to `1` cannot come from a zero matrix entry.
    intro hZero
    have hRowTermZero : rowTerm = 0 := by simp [rowTerm, hZero]
    rw [hRowTermZero] at hOnePair
    norm_num at hOnePair
  have hSignedValues :
      ∀ i, signedColumn i = 0 ∨ signedColumn i = 1 ∨ signedColumn i = -1 := by
    intro i
    -- Every full signed-column entry is still in `{0, 1, -1}`.
    simpa [signedColumn] using
      signed_zero_one_neg_one (extend_deleted_row_signing r σ s i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hEvenSignedSupport :
      Even (Function.support signedColumn).ncard := by
    -- The normalized sum `2` is even, so the signed-column support has even cardinality.
    apply even_support_of_zero_one_neg_one_even_sum signedColumn hSignedValues
    rw [show (∑ i, signedColumn i) = 2 by simpa [signedColumn] using hCritical]
    norm_num
  have hSupportEq :
      Function.support signedColumn = Function.support (fun i ↦ B i j) := by
    -- Multiplying by a Boolean sign does not change which entries are zero.
    ext i
    dsimp [signedColumn]
    cases hsi : extend_deleted_row_signing r σ s i <;> by_cases hBij : B i j = 0 <;>
      simp [hsi, hBij]
  exact ⟨hNonzero, by simpa [hSupportEq] using hEvenSignedSupport⟩

/-- Helper for Theorem 4.59: encode a `(0, ±1)` column entry in a three-valued finite pattern
codomain. -/
def zeroOneNegOneCode (z : ℤ) : Fin 3 :=
  if z = 0 then 0 else if z = 1 then 1 else 2

/-- Helper for Theorem 4.59: the row-restricted pattern of a column is a finite object, so Hall's
theorem can be applied without assuming the ambient column type is finite. -/
def zeroOneNegOneColumnPattern
    {ι : Type*} {κ : Type*} (B : Matrix ι κ ℤ) (j : κ) : ι → Fin 3 :=
  fun i ↦ zeroOneNegOneCode (B i j)

/-- Helper for Theorem 4.59: on `{0, 1, -1}`, the finite code `zeroOneNegOneCode` loses no
information. -/
lemma zeroOneNegOneCode_eq_iff_of_zero_one_neg_one
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    zeroOneNegOneCode a = zeroOneNegOneCode b ↔ a = b := by
  -- Exhaust the nine possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp [zeroOneNegOneCode]

/-- Helper for Theorem 4.59: two `(0, ±1)` columns have the same finite pattern exactly when they
agree entrywise. -/
lemma zeroOneNegOneColumnPattern_eq_iff
    {ι : Type*} {κ : Type*} {B : Matrix ι κ ℤ}
    (hB : HasZeroOneNegOneEntries B) {j₁ j₂ : κ} :
    zeroOneNegOneColumnPattern B j₁ = zeroOneNegOneColumnPattern B j₂ ↔
      ∀ i, B i j₁ = B i j₂ := by
  constructor
  · intro hPattern i
    -- Evaluate the pattern equality at row `i` and decode the resulting three-valued code.
    have hi : zeroOneNegOneCode (B i j₁) = zeroOneNegOneCode (B i j₂) :=
      congrArg (fun f ↦ f i) hPattern
    exact
      (zeroOneNegOneCode_eq_iff_of_zero_one_neg_one
        (HasZeroOneNegOneEntries.apply hB i j₁)
        (HasZeroOneNegOneEntries.apply hB i j₂)).mp hi
  · intro hEntries
    -- Re-encode the entrywise equality row by row.
    funext i
    simp [zeroOneNegOneColumnPattern, hEntries i]

/-- Helper for Theorem 4.59: a critical witness can be transported across two actual columns with
the same three-valued row pattern. -/
lemma criticalWitness_of_columnPatternEq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r : ι} {j₁ j₂ : κ}
    (hCritical :
      ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
        (∀ j',
          (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₁) = 2)
    (hPattern : zeroOneNegOneColumnPattern B j₂ = zeroOneNegOneColumnPattern B j₁) :
    ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
      (∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₂) = 2 := by
  rcases hCritical with ⟨s, σ, hs, hSumTwo⟩
  refine ⟨s, σ, hs, ?_⟩
  have hEntries : ∀ i, B i j₂ = B i j₁ :=
    (zeroOneNegOneColumnPattern_eq_iff hB).1 hPattern
  -- Rewrite the critical full-column sum entrywise along the pattern equality.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₂)
        = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₁ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hEntries i]
    _ = 2 := hSumTwo

/-- Helper for Theorem 4.59: deleting a second row from a deleted-row witness splits the original
deleted-row sum into the exact double-deleted core plus the second row term. -/
private lemma sharedCriticalWitnessCoreSplit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₁} → Bool) (j : κ) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    (∑ i : {i // i ≠ r₁},
        (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) =
      (∑ i : {i // i ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let r₂' : {i // i ≠ r₁} := ⟨r₂, Ne.symm hNe⟩
  let coreNested : {i : {k // k ≠ r₁} // i ≠ r₂'} → ℤ := fun i ↦
    (if s i.1 then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i.1 j)
  have hSplit :
      (∑ i : {i // i ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) =
        ((if s r₂' then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) r₂' j)) +
          ∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i := by
    -- Separate the `r₂` row from the once-deleted witness sum.
    simpa [r₂', coreNested] using
      (Fintype.sum_eq_add_sum_subtype_ne
        (fun i : {i // i ≠ r₁} ↦
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j))
        r₂')
  have hCore :
      (∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i) =
        ∑ i : {x // x ∈ A},
          (if s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1 then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) := by
    -- Reindex the exact double-deleted core through the canonical equivalence of row types.
    symm
    refine Fintype.sum_equiv (doubleErasedRowsEquiv r₁ r₂ hNe) _ _ ?_
    intro i
    rfl
  -- Combine the `r₂` split with the exact-core reindexing.
  calc
    (∑ i : {i // i ≠ r₁},
        (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j))
        = ((if s r₂' then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) r₂' j)) +
            ∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i := hSplit
    _ = ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) +
          (∑ i : {x // x ∈ A},
            (if (fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1) i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
      rw [hCore]
      simp [r₂', Matrix.submatrix_apply]
    _ = (∑ i : {x // x ∈ A},
          (if (fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1) i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) := by
      rw [add_comm]

/-- Helper for Theorem 4.59: on a shared critical column, the witness for `r₁` rewrites on the
exact double-deleted row set to a core-plus-`r₂` equation equal to `1`, while the `r₁` pivot term
itself is also `1`. -/
private lemma sharedCriticalWitnessNormalizedSplit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r₁ r₂ : ι} (hNe : r₁ ≠ r₂) {j : κ}
    (s : {i // i ≠ r₁} → Bool) (σ : Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r₁ σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    ((∑ i : {x // x ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) = 1) ∧
      (((if σ then (1 : ℤ) else -1) * B r₁ j) = 1) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
  have hPair :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) = 1 ∧
        ((if σ then (1 : ℤ) else -1) * B r₁ j) = 1 := by
    -- Normalize the critical witness on its own deleted-row domain first.
    simpa using
      criticalColumn_deletedSum_and_signedPivot_eq_one hB r₁ s σ j (hDeleted j) hCritical
  constructor
  · -- Rewrite the deleted-row equation onto the exact double-deleted core plus the `r₂` term.
    calc
      (∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j)
          =
        ∑ i : {x // x ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j) := by
              simpa [A, sA] using (sharedCriticalWitnessCoreSplit B hNe s j).symm
      _ = 1 := hPair.1
  · -- Keep the `r₁` pivot normalization in its explicit ambient-row form.
    exact hPair.2

/-- Helper for Theorem 4.59: the deleted-row balance family for a shared witness rewrites on the
exact double-deleted row set to the common-core sum plus the opposite-row term. -/
private lemma sharedCriticalWitnessDeletedBalanceOnCommonCore
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₁} → Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = -1) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    ∀ j',
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = 0 ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
            ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = 1 ∨
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
              ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = -1 := by
  intro A sA j'
  -- Rewrite the deleted-row sum once onto the exact double-deleted core spelling, then reuse the
  -- existing deleted balance hypothesis without any further transport.
  have hRewrite :
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) =
        ∑ i : {x // x ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j') := by
    simpa [A, sA] using (sharedCriticalWitnessCoreSplit B hNe s j').symm
  -- After the rewrite, the target is exactly the original deleted witness balance statement.
  rw [hRewrite]
  exact hDeleted j'

/-- Helper for Theorem 4.59: after aligning the kept-row sign with `τ`, the deleted-row balance
family for the second witness specializes at a fixed column on the exact
`A := ((Finset.univ : Finset ι).erase r₁).erase r₂` spelling. -/
private lemma sharedCriticalAlignedDeletedBalanceAtColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₂} → Bool) (τ : Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = -1)
    (hτ : τ = s ⟨r₁, hNe⟩) (j : κ) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
    ((∑ i : {x // x ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 0 ∨
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 1 ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B r₁ j)) = -1 := sorry
/- Proof attempt retained for later proof-stage repair.
  -- Rewrite the second deleted witness onto the exact common core once, then align the kept-row
  -- sign by substitution.
  simpa [A, Finset.erase_comm, sA, hτ] using
    sharedCriticalWitnessDeletedBalanceOnCommonCore B (Ne.symm hNe) s hDeleted j
-/

/-- Helper for Theorem 4.59: in the aligned zero branch on the exact common core, the deleted row
entry must vanish on the chosen column. -/
private lemma sharedCriticalAlignedDeletedZeroGivesMissingRowZero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₂} → Bool) (τ : Bool) (j : κ)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = -1)
    (hτ : τ = s ⟨r₁, hNe⟩)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hZero :
      let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
      let sA : {i // i ∈ A} → Bool := fun i ↦ s ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 0) :
    B r₂ j = 0 := sorry
/- Proof attempt retained for later proof-stage repair.
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let sA : {i // i ∈ A} → Bool := fun i ↦ s ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
  have hDeletedZero :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j)) = 0 := by
    -- Move the zero branch back to the once-deleted witness before applying the even-support API.
    simpa [A, sA, hτ] using hZero
  exact
    (deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
      hB r₂ τ s j (hDeleted j) hEvenSupport).1 hDeletedZero
-/

/-- Helper for Theorem 4.59: a nonzero aligned common-core branch rewrites back to a nonzero
deleted-row witness. -/
private lemma deletedRow_nonzero_of_commonCore_eq_one_or_negOne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {rKeep rDel : ι} (hNe : rKeep ≠ rDel)
    (s : {i // i ≠ rDel} → Bool) (τ : Bool) (j : κ)
    (hCommonCore :
      let A : Finset ι := ((Finset.univ : Finset ι).erase rDel).erase rKeep
      let sA : {i // i ∈ A} → Bool := fun i ↦
        s ⟨i.1, (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1⟩
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B rKeep j) = 1) ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B rKeep j) = -1))
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    B rDel j ≠ 0 := sorry
/- Proof attempt retained for later proof-stage repair.
  let A : Finset ι := ((Finset.univ : Finset ι).erase rDel).erase rKeep
  let sA : {i // i ∈ A} → Bool := fun i ↦ s ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
  have hRewrite :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) =
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B rKeep j)) := by
    -- Rewrite the deleted-row sum through the exact common core plus the kept-row term.
    simpa [A, sA] using sharedCriticalWitnessCoreSplit B (Ne.symm hNe) s j
  have hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) = -1 := by
    -- Rewrite the common-core branch back to the once-deleted witness before applying parity.
    rcases hCommonCore with hOne | hNegOne
    · left
      calc
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j))
            =
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B rKeep j)) := hRewrite
        _ = 1 := hOne
    · right
      calc
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j))
            =
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B rKeep j)) := hRewrite
        _ = -1 := hNegOne
  -- Even-support parity turns a nonzero deleted witness into a nonzero deleted-row entry.
  exact
    missingRow_nonzero_of_deletedSum_eq_one_or_negOne_of_evenSupport
      hB rDel τ s j hDeletedEq hEvenSupport
-/

/-- Helper for Theorem 4.59: a Hall matching on finite row-restricted column patterns can be
realized by an injective choice of actual columns with distinct selected patterns. -/
lemma exists_injective_columnChoice_of_patternHall
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (criticalPattern : ι → (ι → Fin 3) → Prop)
    (criticalWitness : ι → κ → Prop)
    (hHall :
      ∀ A : Finset ι,
        Nat.card A ≤ Nat.card {p // ∃ r ∈ A, criticalPattern r p})
    (hRealize :
      ∀ r p, criticalPattern r p →
        ∃ j : κ, zeroOneNegOneColumnPattern B j = p ∧ criticalWitness r j) :
    ∃ col : ι ↪ κ,
      Function.Injective (fun r ↦ zeroOneNegOneColumnPattern B (col r)) ∧
      ∀ r,
        criticalPattern r (zeroOneNegOneColumnPattern B (col r)) ∧ criticalWitness r (col r) := by
  classical
  have hPatternChoice :
      ∃ f : ι → (ι → Fin 3), Function.Injective f ∧ ∀ r, criticalPattern r (f r) := by
    -- Apply finite Hall directly to the pattern codomain rather than the ambient column type.
    let t : ι → Finset (ι → Fin 3) := fun r ↦ {p | criticalPattern r p}
    have hHall' : ∀ A : Finset ι, A.card ≤ (A.biUnion t).card := by
      intro A
      have hUnion :
          ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)) = A.biUnion t := by
        ext p
        simp [t]
      have hHallA :
          A.card ≤ ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)).card := by
        calc
          A.card = Fintype.card A := by
            exact (Fintype.card_ofFinset A (fun _ ↦ Iff.rfl)).symm
          _ = Nat.card A := by
            rw [Nat.card_eq_fintype_card]
          _ ≤ Nat.card {p // ∃ r ∈ A, criticalPattern r p} := hHall A
          _ = ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)).card := by
            classical
            exact Nat.subtype_card _ (by intro p; simp)
      simpa [hUnion] using hHallA
    simpa [t] using (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall'
  rcases hPatternChoice with ⟨f, hf, hfRel⟩
  choose col hcolPattern hcolWitness using
    fun r ↦ hRealize r (f r) (hfRel r)
  have hcol_injective : Function.Injective col := by
    -- If two realized columns coincide, their selected patterns coincide, so Hall injectivity
    -- forces the corresponding rows to be equal.
    intro r₁ r₂ hEq
    apply hf
    calc
      f r₁ = zeroOneNegOneColumnPattern B (col r₁) := (hcolPattern r₁).symm
      _ = zeroOneNegOneColumnPattern B (col r₂) := by rw [hEq]
      _ = f r₂ := hcolPattern r₂
  have hpattern_injective :
      Function.Injective (fun r ↦ zeroOneNegOneColumnPattern B (col r)) := by
    -- Rewriting through the realized patterns reduces distinctness of selected patterns to the
    -- Hall-selected injective pattern family.
    intro r₁ r₂ hEq
    apply hf
    calc
      f r₁ = zeroOneNegOneColumnPattern B (col r₁) := (hcolPattern r₁).symm
      _ = zeroOneNegOneColumnPattern B (col r₂) := hEq
      _ = f r₂ := hcolPattern r₂
  refine ⟨⟨col, hcol_injective⟩, hpattern_injective, ?_⟩
  intro r
  constructor
  · -- Rewriting through the realized pattern restores the Hall-selected relation.
    simpa [hcolPattern r] using hfRel r
  · exact hcolWitness r

/-- Helper for Theorem 4.59: after Hall chooses the columns, each critical witness rewrites
directly into the fixed square `C := B.submatrix id col`. -/
lemma selectedCriticalSquare_hasCriticalDiagonalWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} {B : Matrix ι κ ℤ}
    (col : ι ↪ κ)
    (hcolCritical :
      ∀ r : ι,
        ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
          (∀ j : κ,
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = -1) ∧
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i (col r)) = 2) :
    let C : Matrix ι ι ℤ := B.submatrix id col
    ∀ r : ι,
      ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
        (∀ j : ι,
          (∑ i, (if s i then (1 : ℤ) else -1) *
              ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = -1) ∧
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i r) = 2 := by
  intro C r
  rcases hcolCritical r with ⟨s, σ, hs, hSumTwo⟩
  refine ⟨s, σ, ?_, ?_⟩
  · intro j
    -- The deleted-row balance statement is unchanged after rewriting the chosen column `col j`
    -- into the fixed square `C`.
    simpa [C, Matrix.submatrix_apply] using hs (col j)
  · -- The distinguished critical column becomes the diagonal column of the fixed square.
    simpa [C, Matrix.submatrix_apply] using hSumTwo

/-- Helper for Theorem 4.59: on the distinguished diagonal column of a normalized critical
witness, the deleted-row contribution and the signed diagonal entry are both equal to `1`. -/
lemma normalizedCriticalDiagonal_deletedSum_and_signedPivot_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r) = 2) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 1 ∧
      ((if σ then (1 : ℤ) else -1) * B r r) = 1 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r r
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r) =
        deletedSum + rowTerm := by
    -- Split the critical full-column sum into the deleted-row part and the diagonal entry.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s r
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness already constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The diagonal term is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r r)
  have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Since the full signed diagonal column sums to `2`, both summands must be `1`.
    apply summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowTermValue
    calc
      deletedSum + rowTerm
          = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r := by
              rw [hSplit]
      _ = 2 := hCritical
  simpa [deletedSum, rowTerm] using hPair

/-- Helper for Theorem 4.59: a row submatrix without an equitable row-bicoloring contains the
Camion parity obstruction as a square submatrix. -/
lemma exists_even_support_odd_half_sum_square_submatrix_of_not_equitable_row_bicoloring
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ)
    (hB : HasZeroOneNegOneEntries B)
    (hNoColor : ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue) :
    HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} B := sorry
/- Proof attempt retained for later proof-stage repair.
  -- Route correction: the signing bridge is now explicit, so the remaining source-faithful blocker
  -- is the concrete Camion step on a cardinal-minimal bad row set inside the ambient row type.
  classical
  rcases exists_minimal_bad_row_set_with_colorable_row_deletions B hNoColor with
    ⟨R, hBadR, hMinBadR, hDeletedColor⟩
  let rowR : {i // i ∈ R} ↪ ρ := Function.Embedding.subtype fun i : ρ ↦ i ∈ R
  let B_R : Matrix {i // i ∈ R} n ℤ := B.submatrix rowR id
  have hBadRestriction :
      ¬ ∃ red blue : Finset {i // i ∈ R},
          is_equitable_row_bicoloring B_R red blue := hBadR
  have hProperColorable :
      ∀ {S : Finset ρ}, S ⊂ R →
        ∃ red blue : Finset {i // i ∈ S},
          is_equitable_row_bicoloring
            (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ S) id) red blue := by
    intro S hSub
    -- The strengthened minimality package already gives colorings on every proper row subset.
    exact proper_row_subset_colorable_of_minimal_bad_row_set B hMinBadR hSub
  have hDeletedSigning :
      ∀ r : {i // i ∈ R},
        ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool,
          ∀ j,
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = -1 := by
    intro r
    -- Transport each deleted-row coloring to a signing on the deleted rows of `B_R`.
    simpa [B_R, rowR] using
      exists_deleted_row_signing_of_colorable_row_deletion B r (hDeletedColor r)
  have hCritical :
      ∀ r : {i // i ∈ R},
        ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool, ∃ σ : Bool, ∃ j : n,
          (∀ j',
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = -1) ∧
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B_R i j) = 2 := by
    intro r
    -- The source-faithful extension step now yields a normalized rowwise critical column.
    exact
      exists_normalized_critical_column_of_deleted_row_signing
        B_R (hB.submatrix rowR id) hBadRestriction r (hDeletedSigning r)
  have hCriticalColumnData :
      ∀ r : {i // i ∈ R},
        ∃ j : n, B_R r j ≠ 0 ∧ Even (Function.support fun i ↦ B_R i j).ncard := by
    intro r
    rcases hCritical r with ⟨s, σ, j, hs, hSumTwo⟩
    -- Package each normalized witness as the parity data needed for the later Hall family.
    exact
      ⟨j,
        criticalColumn_hasNonzeroPivot_and_evenColumnSupport
          (hB.submatrix rowR id) r s σ j (hs j) hSumTwo⟩
  let criticalWitness : {i // i ∈ R} → n → Prop := fun r j ↦
    ∃ s : {i : {k // k ∈ R} // i ≠ r} → Bool, ∃ σ : Bool,
      (∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B_R.submatrix
              (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B_R.submatrix
              (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B_R.submatrix
                (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = -1) ∧
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B_R i j) = 2
  let criticalPattern : {i // i ∈ R} → ({i // i ∈ R} → Fin 3) → Prop := fun r p ↦
    ∃ j : n, zeroOneNegOneColumnPattern B_R j = p ∧ criticalWitness r j
  have hCriticalWitness :
      ∀ r : {i // i ∈ R}, ∃ j : n, criticalWitness r j := by
    intro r
    rcases hCritical r with ⟨s, σ, j, hs, hSumTwo⟩
    -- Repackage the normalized critical-column witness in the theorem-local bridge relation.
    exact ⟨j, s, σ, hs, hSumTwo⟩
  have hCriticalPatternRealize :
      ∀ r p, criticalPattern r p →
        ∃ j : n, zeroOneNegOneColumnPattern B_R j = p ∧ criticalWitness r j := by
    intro r p hp
    exact hp
  have hImageRows_subset :
      ∀ A : Finset {i // i ∈ R}, A.image Subtype.val ⊆ R := by
    intro A i hi
    rcases Finset.mem_image.mp hi with ⟨r, hr, rfl⟩
    exact r.2
  have hImageRows_card :
      ∀ A : Finset {i // i ∈ R}, (A.image Subtype.val).card = A.card := by
    intro A
    exact Finset.card_image_of_injective A Subtype.val_injective
  have hRows_eq_univ_of_image_eq :
      ∀ {A : Finset {i // i ∈ R}}, A.image Subtype.val = R → A = Finset.univ := by
    intro A hA
    ext r
    constructor
    · intro hr
      simp
    · intro _hr
      have hrImage : r.1 ∈ A.image Subtype.val := by
        rw [hA]
        exact r.2
      rcases Finset.mem_image.mp hrImage with ⟨r', hr', hrEq⟩
      simpa [Subtype.ext hrEq] using hr'
  have hImageRows_ssubset :
      ∀ {A : Finset {i // i ∈ R}}, A ≠ Finset.univ → A.image Subtype.val ⊂ R := by
    intro A hA
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hImageRows_subset A, ?_⟩
    intro hEq
    exact hA (hRows_eq_univ_of_image_eq hEq)
  have hProperColorableOnRows :
      ∀ {A : Finset {i // i ∈ R}}, A ≠ Finset.univ →
        ∃ red blue : Finset {i : {j // j ∈ R} // i ∈ A},
          is_equitable_row_bicoloring
            (B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
            red blue := by
    intro A hA
    have hSub : A.image Subtype.val ⊂ R := hImageRows_ssubset hA
    have hColorAmbient := hProperColorable hSub
    -- Reindex the ambient proper-subset coloring back to the `B_R` spelling used in the Hall step.
    simpa [B_R, rowR] using
      (existsEquitableRowBicoloringImageSubtypeRows_iff B A).1 hColorAmbient
  have hCriticalPatternSeparatedGlobally :
      ∀ {r₁ r₂ : {i // i ∈ R}} {p},
        criticalPattern r₁ p → criticalPattern r₂ p → r₁ = r₂ := by
    intro r₁ r₂ p hp₁ hp₂
    rcases hp₁ with ⟨j₁, rfl, hj₁⟩
    rcases hp₂ with ⟨j₂, hj₂Pattern, hj₂⟩
    have hj₂' : criticalWitness r₂ j₁ := by
      -- First move the second witness onto the same actual column `j₁`.
      exact
        criticalWitness_of_columnPatternEq (hB.submatrix rowR id) hj₂
          (by simpa using hj₂Pattern.symm)
    by_contra hNe
    rcases hj₁ with ⟨s₁, σ₁, hs₁, hCritical₁⟩
    rcases hj₂' with ⟨s₂, σ₂, hs₂, hCritical₂⟩
    let A : Finset {i // i ∈ R} := ((Finset.univ : Finset {i // i ∈ R}).erase r₁).erase r₂
    let s₁A : {i // i ∈ A} → Bool :=
      fun i ↦ s₁ ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    let s₂A : {i // i ∈ A} → Bool :=
      fun i ↦ s₂ ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
    let s₂ACompl : {i // i ∈ A} → Bool :=
      fun i ↦ !(s₂ ⟨i.1, (Finset.mem_erase.mp i.2).1⟩)
    have hNormalized₁ :
        ((∑ i : {x // x ∈ A},
            (if s₁A i then (1 : ℤ) else -1) *
              ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j₁)) +
            ((if s₁ ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j₁) = 1) ∧
          (((if σ₁ then (1 : ℤ) else -1) * B_R r₁ j₁) = 1) := by
      -- Normalize the first shared witness on the exact common double-deleted domain.
      simpa [A, s₁A, B_R, rowR] using
        sharedCriticalWitnessNormalizedSplit
          (hB.submatrix rowR id) hNe s₁ σ₁ hs₁ hCritical₁
    have hNormalized₂ :
        ((∑ i : {x // x ∈ A},
            (if s₂A i then (1 : ℤ) else -1) *
              ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j₁)) +
          ((if s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j₁) = 1) ∧
          (((if σ₂ then (1 : ℤ) else -1) * B_R r₂ j₁) = 1) := by
      -- Normalize the second shared witness on the same actual column and the same exact
      -- double-deleted core spelling used for the first witness.
      simpa [A, Finset.erase_comm, s₂A, B_R, rowR] using
        sharedCriticalWitnessNormalizedSplit
          (hB.submatrix rowR id) (Ne.symm hNe) s₂ σ₂ hs₂ hCritical₂
    have hBalanced₁Common :
        ∀ j' : n,
          ((∑ i : {x // x ∈ A},
              (if s₁A i then (1 : ℤ) else -1) *
                ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                  i j')) +
              ((if s₁ ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j')) = 0 ∨
            ((∑ i : {x // x ∈ A},
                (if s₁A i then (1 : ℤ) else -1) *
                  ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                    i j')) +
                ((if s₁ ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j')) = 1 ∨
              ((∑ i : {x // x ∈ A},
                  (if s₁A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
              ((if s₁ ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j')) = -1 := by
      -- Rewrite the first deleted witness once onto the exact common core, so every later use can
      -- stay in that spelling world.
      simpa [A, s₁A] using sharedCriticalWitnessDeletedBalanceOnCommonCore B_R hNe s₁ hs₁
    have hBalanced₂Common :
        ∀ j' : n,
          ((∑ i : {x // x ∈ A},
              (if s₂A i then (1 : ℤ) else -1) *
                ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                  i j')) +
              ((if s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = 0 ∨
            ((∑ i : {x // x ∈ A},
                (if s₂A i then (1 : ℤ) else -1) *
                  ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                    i j')) +
                ((if s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = 1 ∨
              ((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
      -- The same rewrite puts the second deleted witness on the identical common-core spelling.
      simpa [A, Finset.erase_comm, s₂A] using
        sharedCriticalWitnessDeletedBalanceOnCommonCore B_R (Ne.symm hNe) s₂ hs₂
    have hSharedBalanced :
        ∃ t : {i // i ∈ R} → Bool,
          ∀ j' : n,
            (∑ i, (if t i then (1 : ℤ) else -1) * B_R i j') = 0 ∨
              (∑ i, (if t i then (1 : ℤ) else -1) * B_R i j') = 1 ∨
                (∑ i, (if t i then (1 : ℤ) else -1) * B_R i j') = -1 := by
      let τ₁ : Bool := s₂ ⟨r₁, hNe⟩
      let t : {i // i ∈ R} → Bool := extend_deleted_row_signing r₁ τ₁ s₁
      refine ⟨t, ?_⟩
      intro j'
      by_contra hBad
      rcases
          normalizeUnbalancedDeletedRowExtensionAtColumn_withOrigin
            (hB.submatrix rowR id) r₁ s₁ τ₁ hs₁ (by simpa [t, τ₁] using hBad) with
        ⟨sBad, τBad, hBadOrigin, hsBad, hCriticalBad, hRowBad⟩
      have hCriticalData :
          B_R r₁ j' ≠ 0 ∧ Even (Function.support fun i ↦ B_R i j').ncard := by
        -- The normalized bad column is now a genuine critical witness for `r₁`.
        exact
          criticalColumn_hasNonzeroPivot_and_evenColumnSupport
            (hB.submatrix rowR id) r₁ sBad τBad j' (hsBad j') hCriticalBad
      have hs₂Compl :
          ∀ j' : n,
            (∑ i, (if (!s₂ i) then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = 0 ∨
              (∑ i, (if (!s₂ i) then (1 : ℤ) else -1) *
                ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = 1 ∨
                (∑ i, (if (!s₂ i) then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = -1 := by
        -- The complemented second deleted witness stays balanced on every column.
        simpa using deletedRowBalanceFamily_compl s₂ hs₂
      have hBalanced₂CommonCompl :
          ∀ j' : n,
            ((∑ i : {x // x ∈ A},
                (if s₂ACompl i then (1 : ℤ) else -1) *
                  ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                    i j')) +
                ((if !s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = 0 ∨
              ((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                      i j')) +
                  ((if !s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = 1 ∨
                ((∑ i : {x // x ∈ A},
                    (if s₂ACompl i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if !s₂ ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
      -- The same common-core rewrite also works after complementing the second deleted witness.
        simpa [A, Finset.erase_comm, s₂ACompl] using
          sharedCriticalWitnessDeletedBalanceOnCommonCore B_R (Ne.symm hNe) (fun i ↦ !s₂ i) hs₂Compl
      let sBadA : {i // i ∈ A} → Bool :=
        fun i ↦ sBad ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
      have hNormalizedBadCommon :
          ((∑ i : {x // x ∈ A},
              (if sBadA i then (1 : ℤ) else -1) *
                ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                  i j')) +
              ((if sBad ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j') = 1) ∧
            (((if τBad then (1 : ℤ) else -1) * B_R r₁ j') = 1) := by
      -- Rewrite the normalized bad column onto the exact common double-deleted core.
        simpa [A, sBadA] using
          sharedCriticalWitnessNormalizedSplit
            (hB.submatrix rowR id) hNe sBad τBad hsBad hCriticalBad
      have hτCases :
          τBad = s₂ ⟨r₁, hNe⟩ ∨ τBad = !s₂ ⟨r₁, hNe⟩ := by
        -- The aligned second witness is determined by whether `τBad` agrees with `s₂` at `r₁`.
        by_cases hτ : τBad = s₂ ⟨r₁, hNe⟩
        · exact Or.inl hτ
        · right
          cases hτBad : τBad <;> cases hs₂r₁ : s₂ ⟨r₁, hNe⟩ <;> simp [hτBad, hs₂r₁] at hτ ⊢
      have hAlignedSecondDeletedBad :
          τBad = s₂ ⟨r₁, hNe⟩ →
            ((∑ i : {x // x ∈ A},
                (if s₂A i then (1 : ℤ) else -1) *
                  ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                    i j')) +
                ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 ∨
              ((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                      i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1 ∨
                ((∑ i : {x // x ∈ A},
                    (if s₂A i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
        intro hτ
        -- Specialize the second deleted witness at the bad column on the exact common-core
        -- spelling, aligning the kept-row sign with `τBad`.
        simpa [A, s₂A] using
          sharedCriticalAlignedDeletedBalanceAtColumn B_R hNe s₂ τBad hs₂ hτ j'
      have hAlignedSecondDeletedBadCompl :
          τBad = !s₂ ⟨r₁, hNe⟩ →
            ((∑ i : {x // x ∈ A},
                (if s₂ACompl i then (1 : ℤ) else -1) *
                  ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                    i j')) +
                ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 ∨
              ((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id)
                      i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1 ∨
                ((∑ i : {x // x ∈ A},
                    (if s₂ACompl i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
        intro hτ
        -- The complemented second deleted witness specializes in the same exact-core spelling once
        -- its kept-row sign is aligned with `τBad`.
        simpa [A, s₂ACompl] using
          sharedCriticalAlignedDeletedBalanceAtColumn B_R hNe (fun i ↦ !s₂ i) τBad hs₂Compl hτ j'
      have hAlignedSecondDeletedZeroGivesRowTwoZero :
          (τBad = s₂ ⟨r₁, hNe⟩ →
              ((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 →
                B_R r₂ j' = 0) ∧
            (τBad = !s₂ ⟨r₁, hNe⟩ →
              ((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 →
                B_R r₂ j' = 0) := by
        constructor
        · intro hτ hZero
          -- Push the exact-core zero branch back to the once-deleted witness and use the
          -- even-support zero-test there.
          exact
            sharedCriticalAlignedDeletedZeroGivesMissingRowZero
              (hB.submatrix rowR id) hNe s₂ τBad j' hs₂ hτ hCriticalData.2
              (by simpa [A, s₂A] using hZero)
        · intro hτ hZero
          -- The complemented aligned zero branch reduces to the same once-deleted zero test after
          -- one complement rewrite.
          exact
            sharedCriticalAlignedDeletedZeroGivesMissingRowZero
              (hB.submatrix rowR id) hNe (fun i ↦ !s₂ i) τBad j' hs₂Compl hτ hCriticalData.2
              (by simpa [A, s₂ACompl] using hZero)
      have hAlignedSecondDeletedNonzeroGivesRowTwoNonzero :
          τBad = s₂ ⟨r₁, hNe⟩ →
            (((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1) ∨
                ((∑ i : {x // x ∈ A},
                    (if s₂A i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1) →
              B_R r₂ j' ≠ 0 := by
        intro hτ hNonzero
        -- Rewrite the aligned `±1` branch back to the once-deleted `r₂` witness shape.
        exact
          deletedRow_nonzero_of_commonCore_eq_one_or_negOne
            (hB.submatrix rowR id) hNe s₂ τBad j'
            (by simpa [A, s₂A, hτ] using hNonzero) hCriticalData.2
      have hAlignedSecondDeletedNonzeroGivesRowTwoNonzeroCompl :
          τBad = !s₂ ⟨r₁, hNe⟩ →
            (((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1) ∨
                ((∑ i : {x // x ∈ A},
                    (if s₂ACompl i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1) →
              B_R r₂ j' ≠ 0 := by
        intro hτ hNonzero
        -- The complemented alignment branch uses the same common-core rewrite.
        exact
          deletedRow_nonzero_of_commonCore_eq_one_or_negOne
            (hB.submatrix rowR id) hNe (fun i ↦ !s₂ i) τBad j'
            (by simpa [A, s₂ACompl, hτ] using hNonzero) hCriticalData.2
      have hNormalizedBadCore_eq_one_of_rowTwoZero :
          B_R r₂ j' = 0 →
            (∑ i : {x // x ∈ A},
                (if sBadA i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = 1 := by
        intro hRowTwoZero
        have hRowTwoTermZero :
            ((if sBad ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B_R r₂ j') = 0 := by
          simp [hRowTwoZero]
        -- Once the `r₂` term vanishes, the normalized bad-column identity collapses to the core sum.
        linarith [hNormalizedBadCommon.1, hRowTwoTermZero]
      have hAlignedSecondCore_eq_neg_one_of_zero :
          τBad = s₂ ⟨r₁, hNe⟩ →
            ((∑ i : {x // x ∈ A},
                (if s₂A i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 →
              (∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -1 := by
        intro hτ hZero
        -- The normalized bad-column pivot contributes `1`, so a zero aligned deleted sum forces the
        -- common-core part of the second witness to be `-1`.
        exact
          commonCore_eq_neg_one_of_deleted_eq_zero_and_signedKeep_eq_one
            hZero hNormalizedBadCommon.2
      have hAlignedSecondCoreCompl_eq_neg_one_of_zero :
          τBad = !s₂ ⟨r₁, hNe⟩ →
            ((∑ i : {x // x ∈ A},
                (if s₂ACompl i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 0 →
              (∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -1 := by
        intro hτ hZero
        -- The same single-column arithmetic works in the complemented alignment branch.
        exact
          commonCore_eq_neg_one_of_deleted_eq_zero_and_signedKeep_eq_one
            hZero hNormalizedBadCommon.2
      have hAlignedSecondCore_eq_zero_or_negTwo_of_nonzero :
          (τBad = s₂ ⟨r₁, hNe⟩ →
              (((∑ i : {x // x ∈ A},
                    (if s₂A i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1) ∨
                  ((∑ i : {x // x ∈ A},
                      (if s₂A i then (1 : ℤ) else -1) *
                        ((B_R.submatrix
                          (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                      ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1) →
                (∑ i : {x // x ∈ A},
                    (if s₂A i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = 0 ∨
                  (∑ i : {x // x ∈ A},
                      (if s₂A i then (1 : ℤ) else -1) *
                        ((B_R.submatrix
                          (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -2) ∧
            (τBad = !s₂ ⟨r₁, hNe⟩ →
              (((∑ i : {x // x ∈ A},
                    (if s₂ACompl i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                    ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1) ∨
                  ((∑ i : {x // x ∈ A},
                      (if s₂ACompl i then (1 : ℤ) else -1) *
                        ((B_R.submatrix
                          (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                      ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1) →
                (∑ i : {x // x ∈ A},
                    (if s₂ACompl i then (1 : ℤ) else -1) *
                      ((B_R.submatrix
                        (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = 0 ∨
                  (∑ i : {x // x ∈ A},
                      (if s₂ACompl i then (1 : ℤ) else -1) *
                        ((B_R.submatrix
                          (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -2) := by
        constructor
        · intro hτ hNonzero
          -- The aligned nonzero branch fixes the common-core value up to the remaining `-2`
          -- obstruction after the row-`r₁` term has been normalized to `1`.
          exact
            commonCore_eq_zero_or_negTwo_of_deleted_eq_one_or_negOne_and_signedKeep_eq_one
              hNonzero hNormalizedBadCommon.2
        · intro hτ hNonzero
          -- The complemented alignment branch has the same arithmetic normalization frontier.
          exact
            commonCore_eq_zero_or_negTwo_of_deleted_eq_one_or_negOne_and_signedKeep_eq_one
              hNonzero hNormalizedBadCommon.2
      have hAlignedZeroBranchImpossible :
          ∀ b : Bool,
            (if b then τBad = s₂ ⟨r₁, hNe⟩ else τBad = !s₂ ⟨r₁, hNe⟩) →
            B_R r₂ j' = 0 →
            (∑ i : {x // x ∈ A},
                (if sBadA i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = 1 →
            (∑ i : {x // x ∈ A},
                (if (if b then s₂A i else s₂ACompl i) then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -1 →
            False := by
        intro b hτ hRowTwoZero hBadCore hAlignedCore
        let sAlignedA : {i // i ∈ A} → Bool := fun i ↦ if b then s₂A i else s₂ACompl i
        let S :=
          sharedCriticalBadSupport B_R A j'
        have hRestrictedSignEq :
            ∀ i : S, s₁A i.1 = s₂A i.1 := by
          intro i
          -- TODO: prove the support-restricted overlap compatibility on the exact common core
          -- `A := ((Finset.univ : Finset {i // i ∈ R}).erase r₁).erase r₂`. The arithmetic and
          -- normalization layers are already fixed; what remains is the theorem-local provenance
          -- comparison showing that the two original deleted witnesses induce the same Boolean sign
          -- on each row of the fixed bad-column support subtype `S`.
          sorry
        have hRawSignEqOnBadSupport :
            ∀ i : {x // x ∈ A},
              ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j') ≠ 0 →
                s₁A i = s₂A i := by
          -- Reuse the support subtype so the remaining blocker is stated on a stable object rather
          -- than as another raw rowwise implication.
          exact
            sharedCriticalSignEqOnBadSupport_of_restricted
              B_R A j' s₁A s₂A hRestrictedSignEq
        have hRawCoeffEqOnBadSupport :
            sharedCriticalOverlapCoeffEqOnBadSupport B_R A s₁A s₂A j' :=
          sharedCriticalOverlapCoeffEqOnBadSupport_of_signEq
            B_R A s₁A s₂A j' hRawSignEqOnBadSupport
        have hAlignedZeroBranchCoeffEq :
            ∀ i : {x // x ∈ A},
              ((B_R.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j') ≠ 0 →
              (if sBadA i then (1 : ℤ) else -1) =
                (if sAlignedA i then (1 : ℤ) else -1) := by
          intro i hBij
          have hRaw := hRawCoeffEqOnBadSupport i hBij
          cases b
          · rcases hBadOrigin with hKeep | hCompl
            · rcases hKeep with ⟨hsEq, hτEq⟩
              have hImpossible : False := by
                cases hs₂r₁ : s₂ ⟨r₁, hNe⟩ <;> simp [τ₁, hs₂r₁] at hτ hτEq
              exact hImpossible.elim
            · rcases hCompl with ⟨hsEq, hτEq⟩
              have hRawCompl :
                  (if !s₁A i then (1 : ℤ) else -1) =
                    (if !s₂A i then (1 : ℤ) else -1) := by
                simpa using congrArg Neg.neg hRaw
              simpa [sBadA, sAlignedA, s₂ACompl, hsEq] using hRawCompl
          · rcases hBadOrigin with hKeep | hCompl
            · rcases hKeep with ⟨hsEq, hτEq⟩
              simpa [sBadA, sAlignedA, hsEq] using hRaw
            · rcases hCompl with ⟨hsEq, hτEq⟩
              have hImpossible : False := by
                cases hs₂r₁ : s₂ ⟨r₁, hNe⟩ <;> simp [τ₁, hs₂r₁] at hτ hτEq
              exact hImpossible.elim
        -- Once the two exact-`A` core expressions are identified, the normalized values `1` and
        -- `-1` contradict one another immediately.
        have hAlignedCore' :
            (∑ i : {x // x ∈ A},
                (if sAlignedA i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) = -1 := by
          simpa [sAlignedA] using hAlignedCore
        exact
          sharedCriticalAlignedZeroBranchImpossible_of_overlapCoeffEq
            B_R A sBadA sAlignedA j' hAlignedZeroBranchCoeffEq hBadCore hAlignedCore'
      -- Route correction: the remaining frontier is now column-local. The candidate full signing is
      -- explicit, any bad column has been normalized to a `2`-witness for `r₁`, and both the
      -- original and complemented second deleted-balance families are available on the exact common
      -- double-deleted core. The remaining step is the one-column parity contradiction that rules
      -- out this normalized bad column.
      have hCriticalPatternBad :
          criticalPattern r₁ (zeroOneNegOneColumnPattern B_R j') := by
        -- Package the normalized bad column as a concrete critical-pattern witness for `r₁`.
        exact ⟨j', rfl, ⟨sBad, τBad, hsBad, hCriticalBad⟩⟩
      rcases hτCases with hτ | hτ
      · have hAligned := hAlignedSecondDeletedBad hτ
        rcases hAligned with hZero | hNonzero
        · have hRowTwoZero :=
            hAlignedSecondDeletedZeroGivesRowTwoZero.1 hτ hZero
          have hBadCore := hNormalizedBadCore_eq_one_of_rowTwoZero hRowTwoZero
          have hAlignedCore := hAlignedSecondCore_eq_neg_one_of_zero hτ hZero
          exact hAlignedZeroBranchImpossible true hτ hRowTwoZero hBadCore (by simpa using hAlignedCore)
        · have hRowTwoNonzero :=
            hAlignedSecondDeletedNonzeroGivesRowTwoNonzero hτ hNonzero
          have hCoreCase :=
            hAlignedSecondCore_eq_zero_or_negTwo_of_nonzero.1 hτ hNonzero
          rcases hCoreCase with hCoreZero | hCoreNegTwo
          · have hAlignedDeletedEqOne :
              ((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1 := by
              -- Once the aligned common core is `0`, the normalized `r₁` contribution `1`
              -- forces the deleted-row sum for the second witness to be `1`.
              linarith [hCoreZero, hNormalizedBadCommon.2]
            have hDeletedEqOne :
                (∑ i, (if s₂ i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = 1 := by
              -- Rewrite the aligned exact-common-core identity back to the once-deleted `r₂`
              -- witness, so the existing `deleted sum = 1` API can be reused directly.
              simpa [A, s₂A, hτ] using hAlignedDeletedEqOne
            rcases
                exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
                  (hB.submatrix rowR id) r₂ s₂ j' hDeletedEqOne hRowTwoNonzero with
              ⟨σ₂Bad, hCritical₂Bad⟩
            have hCriticalPatternRowTwo :
                criticalPattern r₂ (zeroOneNegOneColumnPattern B_R j') := by
              -- The same actual bad column is now a critical-pattern witness for `r₂`.
              exact ⟨j', rfl, ⟨s₂, σ₂Bad, hs₂, hCritical₂Bad⟩⟩
            exact hNe (hCriticalPatternSeparatedGlobally hCriticalPatternBad hCriticalPatternRowTwo)
          · have hAlignedDeletedEqNegOne :
              ((∑ i : {x // x ∈ A},
                  (if s₂A i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
              -- The surviving `-2` common-core branch converts immediately to deleted sum `-1`.
              exact
                deleted_eq_neg_one_of_commonCore_eq_negTwo_and_signedKeep_eq_one
                  hCoreNegTwo hNormalizedBadCommon.2
            have hDeletedEqNegOne :
                (∑ i, (if s₂ i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = -1 := by
              -- Rewrite the aligned exact-common-core identity back to the once-deleted `r₂`
              -- witness before complementing it to a critical full-column witness.
              simpa [A, s₂A, hτ] using hAlignedDeletedEqNegOne
            rcases
                exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_negOne
                  (hB.submatrix rowR id) r₂ s₂ j' hDeletedEqNegOne hRowTwoNonzero with
              ⟨σ₂Bad, hCritical₂Bad⟩
            have hCriticalPatternRowTwo :
                criticalPattern r₂ (zeroOneNegOneColumnPattern B_R j') := by
              -- Complementing the second deleted witness turns the same bad column into a positive
              -- critical witness for `r₂`.
              exact ⟨j', rfl, ⟨(fun i ↦ !s₂ i), σ₂Bad, hs₂Compl, hCritical₂Bad⟩⟩
            exact hNe (hCriticalPatternSeparatedGlobally hCriticalPatternBad hCriticalPatternRowTwo)
      · have hAligned := hAlignedSecondDeletedBadCompl hτ
        rcases hAligned with hZero | hNonzero
        · have hRowTwoZero :=
            hAlignedSecondDeletedZeroGivesRowTwoZero.2 hτ hZero
          have hBadCore := hNormalizedBadCore_eq_one_of_rowTwoZero hRowTwoZero
          have hAlignedCore := hAlignedSecondCoreCompl_eq_neg_one_of_zero hτ hZero
          exact
            hAlignedZeroBranchImpossible false hτ hRowTwoZero hBadCore (by simpa using hAlignedCore)
        · have hRowTwoNonzero :=
            hAlignedSecondDeletedNonzeroGivesRowTwoNonzeroCompl hτ hNonzero
          have hCoreCase :=
            hAlignedSecondCore_eq_zero_or_negTwo_of_nonzero.2 hτ hNonzero
          rcases hCoreCase with hCoreZero | hCoreNegTwo
          · have hAlignedDeletedEqOne :
              ((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = 1 := by
              -- The complemented aligned common core `0` branch also forces deleted sum `1`.
              linarith [hCoreZero, hNormalizedBadCommon.2]
            have hDeletedEqOne :
                (∑ i, (if (!s₂ i) then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = 1 := by
              -- Rewrite the complemented aligned identity back to the complemented deleted witness.
              simpa [A, s₂ACompl, hτ] using hAlignedDeletedEqOne
            rcases
                exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
                  (hB.submatrix rowR id) r₂ (fun i ↦ !s₂ i) j' hDeletedEqOne hRowTwoNonzero with
              ⟨σ₂Bad, hCritical₂Bad⟩
            have hCriticalPatternRowTwo :
                criticalPattern r₂ (zeroOneNegOneColumnPattern B_R j') := by
              -- In the complemented matching branch, the raw critical witness for `r₂` already uses
              -- the complemented deleted witness.
              exact ⟨j', rfl, ⟨(fun i ↦ !s₂ i), σ₂Bad, hs₂Compl, hCritical₂Bad⟩⟩
            exact hNe (hCriticalPatternSeparatedGlobally hCriticalPatternBad hCriticalPatternRowTwo)
          · have hAlignedDeletedEqNegOne :
              ((∑ i : {x // x ∈ A},
                  (if s₂ACompl i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ∈ A) id) i j')) +
                  ((if τBad then (1 : ℤ) else -1) * B_R r₁ j')) = -1 := by
              -- The complemented surviving `-2` branch again converts to deleted sum `-1`.
              exact
                deleted_eq_neg_one_of_commonCore_eq_negTwo_and_signedKeep_eq_one
                  hCoreNegTwo hNormalizedBadCommon.2
            have hDeletedEqNegOne :
                (∑ i, (if (!s₂ i) then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r₂) id) i j')) = -1 := by
              -- Rewrite the complemented aligned identity back to the complemented deleted witness
              -- before undoing that complement through the existing normalization helper.
              simpa [A, s₂ACompl, hτ] using hAlignedDeletedEqNegOne
            rcases
                exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_negOne
                  (hB.submatrix rowR id) r₂ (fun i ↦ !s₂ i) j' hDeletedEqNegOne hRowTwoNonzero with
              ⟨σ₂Bad, hCritical₂Bad⟩
            have hCriticalPatternRowTwo :
                criticalPattern r₂ (zeroOneNegOneColumnPattern B_R j') := by
              -- Complementing the complemented deleted witness recovers a raw same-column critical
              -- witness for `r₂`.
              exact ⟨j', rfl, ⟨s₂, σ₂Bad, hs₂, hCritical₂Bad⟩⟩
            exact hNe (hCriticalPatternSeparatedGlobally hCriticalPatternBad hCriticalPatternRowTwo)
    obtain ⟨t, ht⟩ := hSharedBalanced
    rcases
        exists_unbalanced_column_of_signing_of_no_equitable_row_bicoloring
          B_R hBadRestriction t with
      ⟨jBad, hjBad⟩
    exact hjBad (ht jBad)
  choose criticalIndex hcriticalIndex using hCriticalWitness
  have hCriticalPatternHall :
      ∀ A : Finset {i // i ∈ R},
        Nat.card A ≤ Nat.card {p // ∃ r ∈ A, criticalPattern r p} := by
    intro A
    let patternChoice : A → {p // ∃ r ∈ A, criticalPattern r p} := fun r ↦
      ⟨zeroOneNegOneColumnPattern B_R (criticalIndex r.1),
        ⟨r.1, r.2, ⟨criticalIndex r.1, rfl, hcriticalIndex r.1⟩⟩⟩
    have hPatternChoiceCritical :
        ∀ r : A, criticalPattern r.1 (patternChoice r).1 := by
      intro r
      exact ⟨criticalIndex r.1, rfl, hcriticalIndex r.1⟩
    have hPatternChoiceInj : Function.Injective patternChoice := by
      intro r₁ r₂ hEq
      have hEqVal : (patternChoice r₁).1 = (patternChoice r₂).1 :=
        congrArg Subtype.val hEq
      have hPatternChoiceCriticalEq :
          criticalPattern r₂.1 (patternChoice r₁).1 := by
        -- Rewrite the second selected pattern to the first one before applying global separation.
        simpa [hEqVal] using hPatternChoiceCritical r₂
      apply Subtype.ext
      exact
        hCriticalPatternSeparatedGlobally
          (by simpa [patternChoice] using hPatternChoiceCritical r₁)
          hPatternChoiceCriticalEq
    -- Once duplicate critical patterns are ruled out globally, finite injectivity gives Hall
    -- uniformly for every finite row family `A`.
    calc
      Nat.card A = Fintype.card A := by
        rw [Nat.card_eq_fintype_card]
      _ ≤ Fintype.card {p // ∃ r ∈ A, criticalPattern r p} := by
        exact Fintype.card_le_of_injective patternChoice hPatternChoiceInj
      _ = Nat.card {p // ∃ r ∈ A, criticalPattern r p} := by
        rw [Nat.card_eq_fintype_card]
  obtain ⟨col, hcolPatternInj, hcolCritical⟩ :=
    exists_injective_columnChoice_of_patternHall
      B_R criticalPattern criticalWitness
      (fun A ↦ by simpa using hCriticalPatternHall A)
      hCriticalPatternRealize
  let C : Matrix {i // i ∈ R} {i // i ∈ R} ℤ := B_R.submatrix id col
  have hCriticalDiagonalWitness :
      ∀ r : {i // i ∈ R},
        ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool, ∃ σ : Bool,
          (∀ j : {i // i ∈ R},
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((C.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = -1) ∧
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i r) = 2 := by
    -- Repackage the selected-column witnesses once in the fixed-square spelling and stop
    -- transporting through `B_R` afterwards.
    have hcolCriticalDiag :
        ∀ r : {i // i ∈ R},
          ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool, ∃ σ : Bool,
            (∀ j : n,
              (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
                  (∑ i, (if s i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = -1) ∧
            (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B_R i (col r)) =
              2 :=
      fun r ↦ (hcolCritical r).2
    simpa [C] using
      selectedCriticalSquare_hasCriticalDiagonalWitness col hcolCriticalDiag
  have hCEntries : HasZeroOneNegOneEntries C := by
    -- The fixed square inherits the `(0, ±1)` entry condition from the ambient matrix `B`.
    simpa [C, B_R, rowR, Matrix.submatrix_submatrix, Function.comp_id] using
      (hB.submatrix rowR col)
  have hCriticalDiagonalSplit :
      ∀ r : {i // i ∈ R},
        ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool, ∃ σ : Bool,
          (∀ j : {i // i ∈ R},
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix
                  (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((C.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)) = -1) ∧
          (∑ i, (if s i then (1 : ℤ) else -1) *
              ((C.submatrix
                (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i r)) = 1 ∧
          ((if σ then (1 : ℤ) else -1) * C r r) = 1 := by
    intro r
    rcases hCriticalDiagonalWitness r with ⟨s, σ, hs, hSumTwo⟩
    refine ⟨s, σ, hs, ?_⟩
    -- Split the normalized diagonal witness once so later parity/arithmetic work can start from
    -- the concrete `1 + 1` diagonal identity rather than the original `= 2` equation.
    exact
      normalizedCriticalDiagonal_deletedSum_and_signedPivot_eq_one
        hCEntries r s σ (hs r) hSumTwo
  have hSelectedColumnData :
      ∀ r : {i // i ∈ R},
        B_R r (col r) ≠ 0 ∧ Even (Function.support fun i ↦ B_R i (col r)).ncard := by
    intro r
    rcases (hcolCritical r).2 with ⟨s, σ, hs, hSumTwo⟩
    -- Each Hall-selected column inherits the critical-column parity data from its witness.
    exact
      criticalColumn_hasNonzeroPivot_and_evenColumnSupport
        (hB.submatrix rowR id) r s σ (col r) (hs (col r)) hSumTwo
  have hCDiagNonzero : ∀ r : {i // i ∈ R}, C r r ≠ 0 := by
    intro r
    -- On the diagonal, `C` records the pivot entry of the row-selected critical column.
    simpa [C, Matrix.submatrix_apply] using (hSelectedColumnData r).1
  have hCEvenColumnSupport :
      ∀ j : {i // i ∈ R}, Even (Function.support fun i ↦ C i j).ncard := by
    intro j
    -- Rewriting the chosen square back to `B_R` exposes the even-support critical column.
    simpa [C, Matrix.submatrix_apply] using (hSelectedColumnData j).2
  have hCEvenColumnSum :
      ∀ j : {i // i ∈ R}, Even (∑ i, C i j) := by
    intro j
    -- Each column sum is even because the selected square has even nonzero support in that column.
    exact
      even_sum_of_zero_one_neg_one_even_support
        (fun i ↦ C i j)
        (fun i ↦ HasZeroOneNegOneEntries.apply hCEntries i j)
        (hCEvenColumnSupport j)
  have hCTotalEven :
      Even (∑ i, ∑ j, C i j) := by
    let colSum : {i // i ∈ R} → ℤ := fun j ↦ ∑ i, C i j
    have hColumnwise :
        Even (∑ j, colSum j) := by
      -- Summing the even column sums over all columns keeps the total even.
      refine Finset.induction_on (Finset.univ : Finset {i // i ∈ R}) ?_ ?_
      · simpa using (show Even (0 : ℤ) by simp)
      · intro j s hj hs
        simpa [colSum, Finset.sum_insert hj] using (hCEvenColumnSum j).add hs
    -- Commute the double sum back to the row-first spelling used by `HasOddHalfEntrySum`.
    have hSwap : (∑ j, colSum j) = ∑ i, ∑ j, C i j := by
      calc
        (∑ j, colSum j) = ∑ j, ∑ i, C i j := by simp [colSum]
        _ = ∑ i, ∑ j, C i j := by rw [Finset.sum_comm]
    rw [← hSwap]
    exact hColumnwise
  have hFixedCriticalSquareFullSignedColumnEqDiagonal :
      ∀ r : {i // i ∈ R},
        ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool, ∃ σ : Bool,
          ∀ j : {i // i ∈ R},
            (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) =
              if j = r then 2 else 0 := by
    intro r
    rcases (hcolCritical r).2 with ⟨s, σ, hs, hDiagTwo⟩
    refine ⟨s, σ, ?_⟩
    intro j
    by_cases hj : j = r
    · -- On the diagonal, the Hall-selected witness is already normalized to sum to `2`.
      simpa [C, Matrix.submatrix_apply, hj] using hDiagTwo
    · let deletedSum : ℤ :=
        ∑ i, (if s i then (1 : ℤ) else -1) *
          ((C.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j)
      let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * C r j
      have hSplit :
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) =
            deletedSum + rowTerm := by
        -- Split the full signed selected column into the deleted-row contribution and row `r`.
        simpa [deletedSum, rowTerm] using
          extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term C r σ s j
      have hDeletedValue :
          deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
        -- The deleted-row witness keeps every selected column balanced before the pivot row.
        simpa [C, Matrix.submatrix_apply, deletedSum] using hs (col j)
      have hRowValue :
          rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
        -- The row contribution is a signed `(0, ±1)` entry of `C`.
        simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hCEntries r j)
      have hFullEven :
          Even (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) := by
        -- Every selected column still has even support, so its fully signed sum is even.
        exact even_extended_signed_column_sum_of_even_support hCEntries r σ s j (hCEvenColumnSupport j)
      have hSumEven : Even (deletedSum + rowTerm) := by
        rw [← hSplit]
        exact hFullEven
      have hFullValue :
          deletedSum + rowTerm = 0 ∨ deletedSum + rowTerm = 2 ∨ deletedSum + rowTerm = -2 := by
        by_cases hZero : deletedSum + rowTerm = 0
        · exact Or.inl hZero
        · have hNotBalanced :
              ¬ (deletedSum + rowTerm = 0 ∨
                deletedSum + rowTerm = 1 ∨
                deletedSum + rowTerm = -1) := by
            intro hBalanced
            rcases hBalanced with hZero' | hOne | hNegOne
            · exact hZero hZero'
            · have : Even (1 : ℤ) := hOne ▸ hSumEven
              norm_num at this
            · have : Even (-1 : ℤ) := hNegOne ▸ hSumEven
              norm_num at this
          exact
            Or.inr
              (full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
                hDeletedValue hRowValue hNotBalanced)
      rcases hFullValue with hZero | hTwo | hNegTwo
      · -- Off the diagonal, the only balanced even possibility is zero.
        simpa [hj] using
          (show (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) = 0 by
            calc
              (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j)
                  = deletedSum + rowTerm := hSplit
              _ = 0 := hZero)
      · have hPatternR :
            criticalPattern r (zeroOneNegOneColumnPattern B_R (col j)) := by
          -- A positive off-diagonal full sum would make the selected column critical for row `r`.
          refine ⟨col j, rfl, ?_⟩
          refine ⟨s, σ, hs, ?_⟩
          calc
            (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B_R i (col j))
                = (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) := by
                    simp [C, Matrix.submatrix_apply]
            _ = deletedSum + rowTerm := hSplit
            _ = 2 := hTwo
        have hrj : r = j :=
          hCriticalPatternSeparatedGlobally hPatternR (hcolCritical j).1
        exact (hj hrj.symm).elim
      · let s' : {i : {j // j ∈ R} // i ≠ r} → Bool := fun i ↦ !(s i)
        have hs' :
            ∀ j' : n,
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 0 ∨
                (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = 1 ∨
                  (∑ i, (if s' i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) = -1 := by
          intro j'
          have hNegDeleted :
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) =
                -(∑ i, (if s i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) := by
            simpa [s'] using
              signed_column_sum_compl_eq_neg
                (B_R.submatrix (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id)
                s j'
          rcases hs j' with hZero' | hOne | hNegOne
          · left
            calc
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) =
                -(∑ i, (if s i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) :=
                  hNegDeleted
              _ = 0 := by rw [hZero']; norm_num
          · right
            right
            calc
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) =
                -(∑ i, (if s i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) :=
                  hNegDeleted
              _ = -1 := by rw [hOne]
          · right
            left
            calc
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                  ((B_R.submatrix
                    (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) =
                -(∑ i, (if s i then (1 : ℤ) else -1) *
                    ((B_R.submatrix
                      (Function.Embedding.subtype fun i : {k // k ∈ R} ↦ i ≠ r) id) i j')) :=
                  hNegDeleted
              _ = 1 := by rw [hNegOne]; norm_num
        have hCompl :
            extend_deleted_row_signing r (!σ) s' =
              fun i ↦ !(extend_deleted_row_signing r σ s i) := by
          -- Complementing the deleted-row signs flips the full signing on every selected column.
          simpa [s'] using extend_deleted_row_signing_compl r σ s
        have hFlipped :
            (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) *
                B_R i (col j)) = 2 := by
          have hNegBR :
              (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) *
                  B_R i (col j)) = -2 := by
            calc
              (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B_R i (col j))
                  = (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i j) := by
                      simp [C, Matrix.submatrix_apply]
              _ = deletedSum + rowTerm := hSplit
              _ = -2 := hNegTwo
          calc
            (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) *
                B_R i (col j)) =
              ∑ i, (if !(extend_deleted_row_signing r σ s i) then (1 : ℤ) else -1) *
                B_R i (col j) := by
                  simp [hCompl]
            _ = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) *
                B_R i (col j)) := by
                  simpa using
                    signed_column_sum_compl_eq_neg B_R (extend_deleted_row_signing r σ s) (col j)
            _ = -(-2 : ℤ) := by rw [hNegBR]
            _ = 2 := by norm_num
        have hPatternR :
            criticalPattern r (zeroOneNegOneColumnPattern B_R (col j)) := by
          -- The `-2` case becomes the positive critical case after complementing the full signing.
          refine ⟨col j, rfl, ?_⟩
          exact ⟨s', !σ, hs', hFlipped⟩
        have hrj : r = j :=
          hCriticalPatternSeparatedGlobally hPatternR (hcolCritical j).1
        exact (hj hrj.symm).elim
  choose rowDeletedSigns rowPivotSign hFixedDiagonal using
    hFixedCriticalSquareFullSignedColumnEqDiagonal
  set signMatrix : Matrix ↥R ↥R ℤ := fun r i ↦
    if extend_deleted_row_signing r (rowPivotSign r) (rowDeletedSigns r) i then (1 : ℤ) else -1
  have hLeftInverse :
      signMatrix * C = (2 : ℤ) • 1 := by
    ext r j
    -- The fixed diagonal equations are exactly the matrix product `signMatrix * C = 2 • 1`.
    by_cases h : r = j
    · subst h
      simpa [signMatrix, Matrix.mul_apply, Matrix.one_apply, Pi.smul_apply] using hFixedDiagonal r r
    · have h' : j ≠ r := fun hEq ↦ h hEq.symm
      simpa [signMatrix, Matrix.mul_apply, Matrix.one_apply, Pi.smul_apply, h, h'] using
        hFixedDiagonal r j
  have hRowsNonempty : Nonempty {i // i ∈ R} := by
    by_contra hEmpty
    haveI : IsEmpty {i // i ∈ R} := not_nonempty_iff.mp hEmpty
    apply hBadRestriction
    refine (equitable_row_bicoloring_iff_exists_row_signing B_R).2 ?_
    refine ⟨fun i ↦ False.elim (isEmptyElim i), ?_⟩
    intro j
    left
    simp
  rcases hRowsNonempty with ⟨r₀⟩
  let Cq : Matrix ↥R ↥R ℚ := C.map (Int.castRingHom ℚ)
  let signMatrixQ : Matrix ↥R ↥R ℚ := signMatrix.map (Int.castRingHom ℚ)
  have hLeftInverseQ :
      signMatrixQ * Cq = (2 : ℚ) • 1 := by
    -- Reprove the left inverse entrywise after casting the integral identity to `ℚ`.
    ext i j
    have hEntry :
        (signMatrix * C) i j = (((2 : ℤ) • (1 : Matrix ↥R ↥R ℤ)) i j) := by
      exact congrArg (fun M ↦ M i j) hLeftInverse
    have hEntryQ :
        (((signMatrix * C) i j : ℤ) : ℚ) =
          ((((2 : ℤ) • (1 : Matrix ↥R ↥R ℤ)) i j : ℤ) : ℚ) := by
      exact_mod_cast hEntry
    simpa [Cq, signMatrixQ, Matrix.mul_apply, Matrix.one_apply, Pi.smul_apply] using hEntryQ
  have hScaledLeft :
      ((1 / 2 : ℚ) • signMatrixQ) * Cq = 1 := by
    -- Rescale the left inverse to an honest inverse candidate over `ℚ`.
    calc
      ((1 / 2 : ℚ) • signMatrixQ) * Cq = (1 / 2 : ℚ) • (signMatrixQ * Cq) := by
        rw [Matrix.smul_mul]
      _ = (1 / 2 : ℚ) • ((2 : ℚ) • 1) := by rw [hLeftInverseQ]
      _ = 1 := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hScaledRight :
      Cq * ((1 / 2 : ℚ) • signMatrixQ) = 1 := by
    -- Over `ℚ`, a square left inverse is automatically a right inverse.
    exact mul_eq_one_comm.mp hScaledLeft
  have hRightInverseQ :
      Cq * signMatrixQ = (2 : ℚ) • 1 := by
    -- Multiply the right inverse equation by `2` to recover the integral normalization.
    simpa [Matrix.mul_smul, smul_smul] using congrArg ((2 : ℚ) • ·) hScaledRight
  have hCEvenRowSupport :
      ∀ r : {i // i ∈ R}, Even (Function.support fun j ↦ C r j).ncard := by
    intro r
    let signedRow : {i // i ∈ R} → ℤ := fun j ↦ C r j * signMatrix j r
    have hSignedRowEqTwoQ :
        (∑ j, ((signedRow j : ℤ) : ℚ)) = 2 := by
      -- The right inverse turns the `r`-th signed row sum into the diagonal value `2`.
      simpa [signedRow, Cq, signMatrixQ, Matrix.mul_apply] using
        congrArg (fun M ↦ M r r) hRightInverseQ
    have hSignedRowEqTwo :
        ∑ j, signedRow j = 2 := by
      exact_mod_cast hSignedRowEqTwoQ
    have hSignedRowValues :
        ∀ j, signedRow j = 0 ∨ signedRow j = 1 ∨ signedRow j = -1 := by
      intro j
      by_cases hs : extend_deleted_row_signing j (rowPivotSign j) (rowDeletedSigns j) r
      · -- If the sign is `+1`, the signed row entry is the original `(0, ±1)` entry.
        simpa [signedRow, signMatrix, hs] using
          HasZeroOneNegOneEntries.apply hCEntries r j
      · -- If the sign is `-1`, the signed row entry is the negation of that `(0, ±1)` entry.
        simpa [signedRow, signMatrix, hs] using
          neg_eq_zero_one_neg_one_of_zero_one_neg_one
            (HasZeroOneNegOneEntries.apply hCEntries r j)
    have hSignedRowSupport :
        Even (Function.support signedRow).ncard := by
      -- The diagonal equation gives an even signed-row total, so the signed support is even.
      apply even_support_of_zero_one_neg_one_even_sum signedRow hSignedRowValues
      rw [hSignedRowEqTwo]
      exact even_two
    have hSupportEq :
        Function.support signedRow = Function.support fun j ↦ C r j := by
      -- Multiplying by a sign never changes which row entries are zero.
      ext j
      by_cases hs : extend_deleted_row_signing j (rowPivotSign j) (rowDeletedSigns j) r
      · simp [signedRow, signMatrix, hs, Function.mem_support]
      · simp [signedRow, signMatrix, hs, Function.mem_support]
    rw [hSupportEq] at hSignedRowSupport
    simpa using hSignedRowSupport
  have hCEven : HasEvenNonzeroSupportInRowsAndCols C := ⟨hCEvenRowSupport, hCEvenColumnSupport⟩
  have hRowEven :
      ∀ r : {i // i ∈ R}, Even (∑ j, C r j) := by
    -- Once both row and column supports are even, every row sum is even as well.
    exact even_row_sum_of_even_support hCEntries hCEven
  choose halfRowSum hhalfRowSum using hRowEven
  have hSignedHalfEqOne :
      ∑ i, signMatrix r₀ i * halfRowSum i = 1 := by
    have hSignedRowTotals :
        ∑ i, signMatrix r₀ i * (∑ j, C i j) = 2 := by
      -- Sum the `r₀`-th row of `signMatrix * C = 2 • 1` to get a signed combination of row sums.
      calc
        ∑ i, signMatrix r₀ i * (∑ j, C i j)
            = ∑ i, ∑ j, signMatrix r₀ i * C i j := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, signMatrix r₀ i * C i j := by
              rw [Finset.sum_comm]
        _ = ∑ j, (signMatrix * C) r₀ j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [Matrix.mul_apply]
        _ = 2 := by
              simpa [Matrix.one_apply, Pi.smul_apply] using
                congrArg (fun M ↦ ∑ j, M r₀ j) hLeftInverse
    have hDouble :
        2 * ∑ i, signMatrix r₀ i * halfRowSum i = 2 := by
      -- Replace each even row sum by twice its half-row-sum and factor the `2` out.
      calc
        2 * ∑ i, signMatrix r₀ i * halfRowSum i
            = ∑ i, 2 * (signMatrix r₀ i * halfRowSum i) := by
                rw [Finset.mul_sum]
        _ = ∑ i, signMatrix r₀ i * (halfRowSum i + halfRowSum i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ∑ i, signMatrix r₀ i * (∑ j, C i j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hhalfRowSum i]
        _ = 2 := hSignedRowTotals
    linarith
  have hHalfParity :
      (((∑ i, signMatrix r₀ i * halfRowSum i : ℤ) : ZMod 2)) =
        (((∑ i, halfRowSum i : ℤ) : ZMod 2)) := by
    -- Modulo `2`, every sign in the distinguished row of `signMatrix` reduces to `1`.
    calc
      (((∑ i, signMatrix r₀ i * halfRowSum i : ℤ) : ZMod 2))
          = ∑ i, (((signMatrix r₀ i * halfRowSum i : ℤ) : ZMod 2)) := by
              simp
      _ = ∑ i, (((halfRowSum i : ℤ) : ZMod 2)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hs : extend_deleted_row_signing r₀ (rowPivotSign r₀) (rowDeletedSigns r₀) i
            · simp [signMatrix, hs]
            · calc
                (((signMatrix r₀ i * halfRowSum i : ℤ) : ZMod 2))
                    = -(((halfRowSum i : ℤ) : ZMod 2)) := by
                        simp [signMatrix, hs]
                _ = (((halfRowSum i : ℤ) : ZMod 2)) := by
                      simpa using
                        (ZMod.neg_eq_self_mod_two (((halfRowSum i : ℤ) : ZMod 2)))
      _ = (((∑ i, halfRowSum i : ℤ) : ZMod 2)) := by
            simp
  have hHalfOdd : Odd (∑ i, halfRowSum i) := by
    have hHalfCastOne :
        (((∑ i, halfRowSum i : ℤ) : ZMod 2)) = 1 := by
      calc
        (((∑ i, halfRowSum i : ℤ) : ZMod 2))
            = (((∑ i, signMatrix r₀ i * halfRowSum i : ℤ) : ZMod 2)) := hHalfParity.symm
        _ = ((1 : ℤ) : ZMod 2) := by rw [hSignedHalfEqOne]
        _ = 1 := by norm_num
    have hHalfNotEven : ¬ Even (∑ i, halfRowSum i) := by
      intro hEven
      have hHalfCastZero :
          (((∑ i, halfRowSum i : ℤ) : ZMod 2)) = 0 := by
        rw [ZMod.intCast_eq_zero_iff_even]
        exact hEven
      rw [hHalfCastZero] at hHalfCastOne
      norm_num at hHalfCastOne
    exact Int.not_even_iff_odd.mp hHalfNotEven
  have hOddHalfC : HasOddHalfEntrySum C := by
    refine ⟨∑ i, halfRowSum i, ?_, hHalfOdd⟩
    -- Summing the row decompositions reassembles the total entry sum of `C`.
    calc
      (∑ i, ∑ j, C i j) = ∑ i, (∑ j, C i j) := by simp
      _ = ∑ i, (halfRowSum i + halfRowSum i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hhalfRowSum i]
      _ = ∑ i, 2 * halfRowSum i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = 2 * ∑ i, halfRowSum i := by
            rw [← Finset.mul_sum]
  refine ⟨{i // i ∈ R}, inferInstance, rowR, col, ?_, ?_⟩
  · -- The Hall-selected square has even support in every row and column.
    simpa [C, B_R, rowR, Matrix.submatrix_submatrix, Function.comp_id] using hCEven
  · -- The same square has an odd half-total by the row-half-sum computation above.
    simpa [C, B_R, rowR, Matrix.submatrix_submatrix, Function.comp_id] using hOddHalfC
-/

/-- Theorem 4.59. A `(0, ±1)` matrix `A` is totally unimodular if and only if `A` does not contain
a square submatrix with an even number of nonzero entries in each row and column whose sum of the
entries divided by `2` is odd. -/
theorem totally_unimodular_iff_no_even_support_odd_half_sum_square_submatrix
    (A : Matrix m n ℤ) (hA : HasZeroOneNegOneEntries A) :
    A.IsTotallyUnimodular ↔ ¬ HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} A := by
  classical
  constructor
  · intro hTU hObstruction
    -- Specialize total unimodularity to the obstructing square submatrix.
    rcases hObstruction with ⟨ι, _, row, col, hEven, hOdd⟩
    have hSubTU : (A.submatrix row col).IsTotallyUnimodular := hTU.submatrix row col
    exact (odd_half_entry_sum_not_of_totally_unimodular_square hSubTU hEven) hOdd
  · intro hNoObstruction
    -- Route correction: the reverse implication stays on Corollary 4.7 and uses the row-submatrix
    -- transport lemma to lift any Camion obstruction back to the ambient matrix.
    have hRow :
        ∀ {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (row : ρ ↪ m),
          ∃ red blue : Finset ρ, is_equitable_row_bicoloring (A.submatrix row id) red blue := by
      intro ρ _ _ row
      by_cases hColor :
          ∃ red blue : Finset ρ, is_equitable_row_bicoloring (A.submatrix row id) red blue
      · exact hColor
      · have hSubObstruction :
            HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} (A.submatrix row id) :=
            exists_even_support_odd_half_sum_square_submatrix_of_not_equitable_row_bicoloring
              (A.submatrix row id) (hA.submatrix row id) hColor
        have hObstruction :
            HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} A :=
          even_support_odd_half_sum_square_submatrix_of_row_submatrix row hSubObstruction
        exact False.elim (hNoObstruction hObstruction)
    exact
      (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring.{u, v, u}
        A).2 hRow

end Theorem59
