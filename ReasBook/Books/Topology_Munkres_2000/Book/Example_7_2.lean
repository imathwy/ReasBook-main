module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite

public section

/-- The positive-integer pairs on or below the diagonal. -/
@[expose]
def PositiveTriangle := {p : ℕ+ × ℕ+ // p.2 ≤ p.1}

/-- Helper for Example 7.2: the diagonal reindexing has its second coordinate
below its first. -/
lemma diagonalToTriangle_second_le_first (p : ℕ+ × ℕ+) :
    p.2 ≤ p.1 + p.2 - 1 := by
  -- Positivity of the first summand makes the second coordinate strictly smaller
  -- before subtraction.
  exact PNat.le_sub_one_of_lt (PNat.lt_add_left p.2 p.1)

/-- The map `(x, y) ↦ (x + y - 1, y)` into the positive triangular region. -/
@[expose]
def diagonalToTriangle (p : ℕ+ × ℕ+) : PositiveTriangle :=
  ⟨(p.1 + p.2 - 1, p.2), diagonalToTriangle_second_le_first p⟩

/-- The value of `diagonalToTriangle` is the displayed diagonal reindexing formula. -/
@[simp]
theorem diagonalToTriangle_val (p : ℕ+ × ℕ+) :
    (diagonalToTriangle p).val = (p.1 + p.2 - 1, p.2) := rfl

/-- Helper for Example 7.2: the triangular indexing formula is positive. -/
lemma triangleIndex_pos (p : PositiveTriangle) :
    0 < ((p.val.1.val - 1) * p.val.1.val) / 2 + p.val.2.val := by
  -- The second coordinate is positive, so adding it makes the whole index positive.
  exact Nat.add_pos_right _ p.val.2.pos

/-- The triangular indexing map `(x, y) ↦ ((x - 1) * x) / 2 + y`. -/
@[expose]
def triangleIndex (p : PositiveTriangle) : ℕ+ :=
  ⟨((p.val.1.val - 1) * p.val.1.val) / 2 + p.val.2.val, triangleIndex_pos p⟩

/-- The value of `triangleIndex` is the displayed triangular indexing formula. -/
@[simp]
theorem triangleIndex_val (p : PositiveTriangle) :
    (triangleIndex p : ℕ) = ((p.val.1.val - 1) * p.val.1.val) / 2 + p.val.2.val := rfl

/-- Helper for Example 7.2: the triangular index is a binomial coefficient plus the column. -/
lemma triangleIndex_choose (p : PositiveTriangle) :
    (triangleIndex p : ℕ) = Nat.choose p.val.1.val 2 + p.val.2.val := by
  -- Commute the product to match the library formula for choosing two elements.
  rw [triangleIndex_val, Nat.choose_two_right, Nat.mul_comm]

/-- Helper for Example 7.2: the triangular index lies strictly above its row's base. -/
lemma triangleIndex_row_lower (p : PositiveTriangle) :
    Nat.choose p.val.1.val 2 < (triangleIndex p : ℕ) := by
  -- The positive second coordinate moves the index beyond the triangular base.
  rw [triangleIndex_choose]
  exact Nat.lt_add_of_pos_right p.val.2.pos

/-- Helper for Example 7.2: consecutive triangular bases differ by the row number. -/
lemma chooseTwo_succ (x : ℕ) : Nat.choose (x + 1) 2 = x + Nat.choose x 2 := by
  -- Pascal's identity specializes directly to the triangular-number recurrence.
  simpa only [Nat.choose_one_right] using Nat.choose_succ_succ x 1

/-- Helper for Example 7.2: the triangular index does not exceed the end of its row. -/
lemma triangleIndex_row_upper (p : PositiveTriangle) :
    (triangleIndex p : ℕ) ≤ Nat.choose (p.val.1.val + 1) 2 := by
  -- Pascal's identity identifies the next triangular number with the current base plus the row.
  have hbound : p.val.2.val ≤ p.val.1.val := p.property
  rw [triangleIndex_choose, chooseTwo_succ]
  omega

/-- Helper for Example 7.2: the inverse diagonal reindexing subtracts the second coordinate. -/
def triangleToDiagonal (p : PositiveTriangle) : ℕ+ × ℕ+ :=
  ((p.val.1.val - p.val.2.val).succPNat, p.val.2)

/-- Helper for Example 7.2: diagonal subtraction recovers the original first coordinate. -/
lemma triangleToDiagonal_first_diagonal (x y : ℕ+) :
    (((x + y - 1 : ℕ+) : ℕ) - (y : ℕ)).succPNat = x := by
  -- The sum is above one, so positive-natural subtraction agrees with natural subtraction.
  have hx := x.pos
  have hy := y.pos
  have hsum : (1 : ℕ+) < x + y :=
    (show (1 : ℕ+) ≤ y from bot_le).trans_lt (PNat.lt_add_left y x)
  apply PNat.eq
  rw [Nat.succPNat_coe, PNat.sub_coe, if_pos hsum, PNat.add_coe, PNat.one_coe]
  omega

/-- Helper for Example 7.2: triangular addition after natural subtraction recovers the row. -/
lemma diagonalToTriangle_first_triangle (x y : ℕ+) (hyx : y ≤ x) :
    (x.val - y.val).succPNat + y - 1 = x := by
  -- First restore the missing unit, then use cancellation in positive naturals.
  have hx := x.pos
  have hy := y.pos
  have hyx' : (y : ℕ) ≤ x := hyx
  have hsum : (x.val - y.val).succPNat + y = x + 1 := by
    apply PNat.eq
    simp only [PNat.add_coe, Nat.succPNat_coe, PNat.one_coe]
    omega
  rw [hsum, PNat.add_sub]

/-- Helper for Example 7.2: subtracting after diagonal reindexing recovers the original pair. -/
lemma triangleToDiagonal_leftInverse :
    Function.LeftInverse triangleToDiagonal diagonalToTriangle := by
  rintro ⟨x, y⟩
  -- The first-coordinate helper performs the only subtraction calculation.
  ext
  · exact triangleToDiagonal_first_diagonal x y
  · rfl

/-- Helper for Example 7.2: diagonal reindexing after subtraction recovers every
triangular point. -/
lemma triangleToDiagonal_rightInverse :
    Function.RightInverse triangleToDiagonal diagonalToTriangle := by
  rintro ⟨⟨x, y⟩, hyx⟩
  -- The subtype property supplies the exactness condition for subtraction.
  apply Subtype.ext
  ext
  · exact diagonalToTriangle_first_triangle x y hyx
  · rfl

/-- Helper for Example 7.2: the map `(x, y) ↦ (x + y - 1, y)` is a bijection
from positive-integer pairs to the positive triangular region. -/
theorem diagonalToTriangle_bijective : Function.Bijective diagonalToTriangle := by
  -- The explicit subtraction map is simultaneously a left and right inverse.
  exact ⟨triangleToDiagonal_leftInverse.injective,
    triangleToDiagonal_rightInverse.surjective⟩

/-- Helper for Example 7.2: distinct triangular points have distinct triangular indices. -/
lemma triangleIndex_injective : Function.Injective triangleIndex := by
  intro p q hpq
  -- Different rows occupy disjoint intervals between consecutive triangular numbers.
  have hpqNat : (triangleIndex p : ℕ) = triangleIndex q := congrArg PNat.val hpq
  have hrow : p.val.1 = q.val.1 := by
    apply le_antisymm
    · by_contra hle
      have hlt : q.val.1 < p.val.1 := lt_of_not_ge hle
      have hnext : q.val.1.val + 1 ≤ p.val.1.val := PNat.add_one_le_iff.mpr hlt
      have hbase : Nat.choose (q.val.1.val + 1) 2 ≤ Nat.choose p.val.1.val 2 :=
        Nat.choose_le_choose 2 hnext
      have hsep := (triangleIndex_row_upper q).trans_lt
        (hbase.trans_lt (triangleIndex_row_lower p))
      omega
    · by_contra hle
      have hlt : p.val.1 < q.val.1 := lt_of_not_ge hle
      have hnext : p.val.1.val + 1 ≤ q.val.1.val := PNat.add_one_le_iff.mpr hlt
      have hbase : Nat.choose (p.val.1.val + 1) 2 ≤ Nat.choose q.val.1.val 2 :=
        Nat.choose_le_choose 2 hnext
      have hsep := (triangleIndex_row_upper p).trans_lt
        (hbase.trans_lt (triangleIndex_row_lower q))
      omega
  -- Once the rows agree, cancellation in the normalized formula identifies the columns.
  apply Subtype.ext
  apply Prod.ext hrow
  apply PNat.eq
  rw [triangleIndex_choose, triangleIndex_choose, hrow] at hpqNat
  omega

/-- Helper for Example 7.2: every triangular point has a point with the next index. -/
lemma triangleIndex_hasSuccessor (p : PositiveTriangle) :
    ∃ q : PositiveTriangle, triangleIndex q = triangleIndex p + 1 := by
  by_cases hinner : p.val.2 < p.val.1
  · -- Inside a row, increment only the second coordinate.
    have hbound : p.val.2 + 1 ≤ p.val.1 := PNat.add_one_le_iff.mpr hinner
    let q : PositiveTriangle := ⟨(p.val.1, p.val.2 + 1), hbound⟩
    refine ⟨q, ?_⟩
    apply PNat.eq
    simp only [triangleIndex_choose, q, PNat.add_coe, PNat.one_coe]
    omega
  · -- At the row boundary, move to the first point of the next row.
    have hboundary : p.val.2 = p.val.1 := le_antisymm p.property (le_of_not_gt hinner)
    have hbound : (1 : ℕ+) ≤ p.val.1 + 1 := bot_le
    let q : PositiveTriangle := ⟨(p.val.1 + 1, 1), hbound⟩
    refine ⟨q, ?_⟩
    apply PNat.eq
    simp only [triangleIndex_choose, q, PNat.add_coe, PNat.one_coe]
    rw [chooseTwo_succ]
    have hboundaryNat : p.val.2.val = p.val.1.val := congrArg PNat.val hboundary
    omega

/-- Helper for Example 7.2: every positive integer occurs as a triangular index. -/
lemma triangleIndex_surjective : Function.Surjective triangleIndex := by
  intro n
  -- Positive-natural induction starts at `(1, 1)` and advances using the successor interface.
  induction n using PNat.recOn with
  | one =>
      have hbound : (1 : ℕ+) ≤ 1 := le_rfl
      let p : PositiveTriangle := ⟨(1, 1), hbound⟩
      refine ⟨p, ?_⟩
      apply PNat.eq
      simp only [triangleIndex_choose, p, PNat.one_coe, Nat.choose]
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨q, hq⟩ := triangleIndex_hasSuccessor p
      refine ⟨q, ?_⟩
      rw [hq, hp]

/-- Helper for Example 7.2: the triangular indexing formula is a bijection from
the positive triangular region to the positive integers. -/
theorem triangleIndex_bijective : Function.Bijective triangleIndex := by
  -- The row-interval and successor arguments provide the two components directly.
  exact ⟨triangleIndex_injective, triangleIndex_surjective⟩

/-- Helper for Example 7.2: the displayed diagonal enumeration gives a bijection
from `ℕ+ × ℕ+` to `ℕ+`. -/
theorem positiveNaturals_product_bijective :
    Function.Bijective (triangleIndex ∘ diagonalToTriangle) :=
  triangleIndex_bijective.comp diagonalToTriangle_bijective

/-- Example 7.2. The product of the positive integers with itself is countably infinite. -/
theorem positiveNaturals_product_countablyInfinite :
    (Set.univ : Set (ℕ+ × ℕ+)).CountablyInfinite := by
  apply Set.CountablyInfinite.ofEquiv
  exact (Equiv.Set.univ (ℕ+ × ℕ+)).trans
    (Equiv.ofBijective (triangleIndex ∘ diagonalToTriangle)
      positiveNaturals_product_bijective)
