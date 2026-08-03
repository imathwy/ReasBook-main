import Mathlib
import Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_2
import Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_6

open scoped BigOperators

-- This exercise reuses mathlib's canonical `Matrix.IsTotallyUnimodular` owner and the
-- Chapter 4.2 equitable column-bicoloring API.

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise410

variable {m n k : ℕ}

/-- The sum of the entries in row `i` of `A` over the columns carrying color `c`. -/
def column_color_sum
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c : Fin k)
    (i : Fin m) : ℤ :=
  (Finset.univ.filter (fun j : Fin n ↦ κ j = c)).sum (fun j ↦ A i j)

/-- The columns carrying one of the colors `c` or `d`. -/
def color_pair_columns
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ κ j = c ∨ κ j = d)

/-- The canonical enumeration of the selected `(c,d)`-columns. -/
def color_pair_embedding
    (κ : Fin n → Fin k)
    (c d : Fin k) : Fin (color_pair_columns κ c d).card ↪o Fin n :=
  (color_pair_columns κ c d).orderEmbOfFin rfl

/-- Within the selected `(c,d)`-submatrix, the columns carrying color `c`. -/
def color_pair_red
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin (color_pair_columns κ c d).card) :=
  Finset.univ.filter (fun j ↦ κ (color_pair_embedding κ c d j) = c)

/-- Within the selected `(c,d)`-submatrix, the columns carrying color `d`. -/
def color_pair_blue
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin (color_pair_columns κ c d).card) :=
  Finset.univ.filter (fun j ↦ κ (color_pair_embedding κ c d j) = d)

/-- An equitable `k`-coloring is a coloring of the columns such that, in every row, the sums over
any two distinct color classes differ by at most `1`. -/
def equitable_k_coloring
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) : Prop :=
  ∀ c d : Fin k, c ≠ d →
    ∀ i : Fin m,
      Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) ≤ 1

/-- Helper for Exercise 4.10: over `ℤ`, having absolute value at most `1` is equivalent to lying in
the image of `SignType.cast`. -/
lemma natAbs_le_one_iff_mem_signType_range {z : ℤ} :
    Int.natAbs z ≤ 1 ↔ z ∈ Set.range (SignType.cast : SignType → ℤ) := by
  rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
  constructor
  · intro hz
    have hz' : |z| ≤ 1 := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hz
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using
      (Int.abs_le_one_iff.1 hz')
  · intro hz
    have hz' : z = 0 ∨ z = 1 ∨ z = -1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hz
    have hz'' : |z| ≤ 1 := Int.abs_le_one_iff.2 hz'
    have hz''' : (Int.natAbs z : ℤ) ≤ 1 := by
      rw [← Int.abs_eq_natAbs]
      exact hz''
    exact_mod_cast hz'''

/-- Helper for Exercise 4.10: distinct colors give disjoint red and blue classes on the selected
`(c,d)`-submatrix. -/
lemma color_pair_red_disjoint_blue
    (κ : Fin n → Fin k) {c d : Fin k} (hcd : c ≠ d) :
    Disjoint (color_pair_red κ c d) (color_pair_blue κ c d) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro j hjc hjd
  have hc : κ (color_pair_embedding κ c d j) = c := (Finset.mem_filter.1 hjc).2
  have hd : κ (color_pair_embedding κ c d j) = d := (Finset.mem_filter.1 hjd).2
  exact hcd (hc.symm.trans hd)

/-- Helper for Exercise 4.10: the canonical red and blue classes cover the selected
`(c,d)`-submatrix. -/
lemma color_pair_red_union_blue
    (κ : Fin n → Fin k) (c d : Fin k) :
    color_pair_red κ c d ∪ color_pair_blue κ c d = Finset.univ := by
  classical
  ext j
  constructor
  · intro _
    simp
  · intro _
    have hjmem : color_pair_embedding κ c d j ∈ color_pair_columns κ c d :=
      Finset.orderEmbOfFin_mem (color_pair_columns κ c d) rfl j
    have hj : κ (color_pair_embedding κ c d j) = c ∨ κ (color_pair_embedding κ c d j) = d :=
      (Finset.mem_filter.1 hjmem).2
    simpa [color_pair_red, color_pair_blue] using hj

/-- Helper for Exercise 4.10: enumerating the selected red indices and mapping them back to the
ambient columns recovers exactly the ambient columns of color `c`. -/
lemma image_color_pair_red
    (κ : Fin n → Fin k)
    (c d : Fin k) :
    (color_pair_red κ c d).image (color_pair_embedding κ c d) =
      Finset.univ.filter (fun j : Fin n ↦ κ j = c) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hj', rfl⟩
    exact Finset.mem_filter.2 ⟨by simp, (Finset.mem_filter.1 hj').2⟩
  · intro hj
    have hjc : κ j = c := (Finset.mem_filter.1 hj).2
    have hjpair : j ∈ color_pair_columns κ c d := by
      exact Finset.mem_filter.2 ⟨by simp, Or.inl hjc⟩
    have hjimage : j ∈ Finset.image (color_pair_embedding κ c d) Finset.univ := by
      simpa [color_pair_embedding] using hjpair
    rcases Finset.mem_image.1 hjimage with ⟨j', -, rfl⟩
    exact Finset.mem_image.2 ⟨j', by simpa [color_pair_red, hjc], rfl⟩

/-- Helper for Exercise 4.10: enumerating the selected blue indices and mapping them back to the
ambient columns recovers exactly the ambient columns of color `d`. -/
lemma image_color_pair_blue
    (κ : Fin n → Fin k)
    (c d : Fin k) :
    (color_pair_blue κ c d).image (color_pair_embedding κ c d) =
      Finset.univ.filter (fun j : Fin n ↦ κ j = d) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hj', rfl⟩
    exact Finset.mem_filter.2 ⟨by simp, (Finset.mem_filter.1 hj').2⟩
  · intro hj
    have hjd : κ j = d := (Finset.mem_filter.1 hj).2
    have hjpair : j ∈ color_pair_columns κ c d := by
      exact Finset.mem_filter.2 ⟨by simp, Or.inr hjd⟩
    have hjimage : j ∈ Finset.image (color_pair_embedding κ c d) Finset.univ := by
      simpa [color_pair_embedding] using hjpair
    rcases Finset.mem_image.1 hjimage with ⟨j', -, rfl⟩
    exact Finset.mem_image.2 ⟨j', by simpa [color_pair_blue, hjd], rfl⟩

/-- Helper for Exercise 4.10: the Chapter 4.2 row-balance condition on the `(c,d)`-submatrix is
the ambient rowwise difference of the `c`- and `d`-column sums. -/
lemma color_pair_difference_apply
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (i : Fin m) :
    column_bicoloring_difference
        (A.submatrix id (color_pair_embedding κ c d))
        (color_pair_red κ c d)
        (color_pair_blue κ c d)
        i =
      column_color_sum A κ c i - column_color_sum A κ d i := by
  -- Rewrite the selected red and blue sums back to the ambient filtered color sums.
  rw [column_bicoloring_difference_apply]
  unfold column_color_sum
  rw [← image_color_pair_red κ c d, ← image_color_pair_blue κ c d]
  congr 1
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.submatrix_apply]
    · intro a _ b _ hab
      exact (color_pair_embedding κ c d).inj' hab
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.submatrix_apply]
    · intro a _ b _ hab
      exact (color_pair_embedding κ c d).inj' hab

/-- Bridge/view companion for Exercise 4.10: the direct pairwise row-balance condition is
equivalent to requiring the Chapter 4.2 equitable bicoloring owner on every selected
`(c,d)`-submatrix. -/
theorem equitable_k_coloring_iff_pairwise_equitable_bicoloring
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) :
    equitable_k_coloring A κ ↔
      ∀ c d : Fin k, c ≠ d →
        is_equitable_bicoloring
          (A.submatrix id (color_pair_embedding κ c d))
          (color_pair_red κ c d)
          (color_pair_blue κ c d) := by
  constructor
  · intro h c d hcd
    rw [is_equitable_bicoloring_iff]
    refine ⟨color_pair_red_disjoint_blue κ hcd, color_pair_red_union_blue κ c d, ?_⟩
    intro i
    have hi :
        Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) ≤ 1 :=
      h c d hcd i
    have hi' :
        column_bicoloring_difference
            (A.submatrix id (color_pair_embedding κ c d))
            (color_pair_red κ c d)
            (color_pair_blue κ c d)
            i ∈ Set.range (SignType.cast : SignType → ℤ) := by
      rw [color_pair_difference_apply]
      exact (natAbs_le_one_iff_mem_signType_range).1 hi
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hi'
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hi'
  · intro h c d hcd i
    have hi :
        column_bicoloring_difference
            (A.submatrix id (color_pair_embedding κ c d))
            (color_pair_red κ c d)
            (color_pair_blue κ c d)
            i ∈ Set.range (SignType.cast : SignType → ℤ) := by
      have hi' :=
        ((is_equitable_bicoloring_iff
          (A.submatrix id (color_pair_embedding κ c d))
          (color_pair_red κ c d)
          (color_pair_blue κ c d)).1 (h c d hcd)).2.2 i
      rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hi'
    rw [← color_pair_difference_apply A κ c d i]
    exact (natAbs_le_one_iff_mem_signType_range).2 hi

/-- Helper for Exercise 4.10: transport Theorem 4.6 to a chosen column set, producing the
Chapter 4.2 equitable bicoloring owner on the corresponding selected-column submatrix. -/
lemma exists_equitable_bicoloring_on_column_set
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : A.IsTotallyUnimodular)
    (s : Finset (Fin n)) :
    ∃ red blue : Finset (Fin s.card),
      is_equitable_bicoloring
        (A.submatrix id (s.orderEmbOfFin rfl))
        red blue := by
  -- This is exactly Theorem 4.6 specialized to the chosen column enumeration of `s`.
  exact
    (totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring A).1 hA
      (ι := Fin s.card)
      (s.orderEmbOfFin rfl).toEmbedding

/-- Helper for Exercise 4.10: the square-sum potential minimized in the bichromatic-exchange
argument. -/
def coloring_potential
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) : ℤ :=
  ∑ i : Fin m, ∑ c : Fin k, (column_color_sum A κ c i) ^ 2

/-- Helper for Exercise 4.10: recolor the selected `(c,d)`-columns by sending the chosen red
indices to `c` and the remaining selected columns to `d`. -/
def recolor_two_colors
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (red : Finset (Fin (color_pair_columns κ c d).card)) : Fin n → Fin k :=
  fun j ↦
    if j ∈ red.image (color_pair_embedding κ c d) then c
    else if j ∈ color_pair_columns κ c d then d
    else κ j

/-- Helper for Exercise 4.10: recoloring sends every chosen red indexed column to color `c`. -/
lemma recolor_two_colors_of_mem_red
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)}
    {j : Fin (color_pair_columns κ c d).card}
    (hj : j ∈ red) :
    recolor_two_colors κ c d red (color_pair_embedding κ c d j) = c := by
  have himage :
      color_pair_embedding κ c d j ∈ red.image (color_pair_embedding κ c d) :=
    Finset.mem_image.2 ⟨j, hj, rfl⟩
  simp [recolor_two_colors, himage]

/-- Helper for Exercise 4.10: recoloring sends every selected column outside the chosen red image
to color `d`. -/
lemma recolor_two_colors_of_mem_pair_not_mem_red
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)} {j : Fin n}
    (hjpair : j ∈ color_pair_columns κ c d)
    (hjred : j ∉ red.image (color_pair_embedding κ c d)) :
    recolor_two_colors κ c d red j = d := by
  simp [recolor_two_colors, hjred, hjpair]

/-- Helper for Exercise 4.10: recoloring leaves columns outside the selected `(c,d)`-set
unchanged. -/
lemma recolor_two_colors_of_not_mem_pair
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)} {j : Fin n}
    (hj : j ∉ color_pair_columns κ c d) :
    recolor_two_colors κ c d red j = κ j := by
  have hjimage : j ∉ red.image (color_pair_embedding κ c d) := by
    intro hj'
    rcases Finset.mem_image.1 hj' with ⟨x, hx, hxj⟩
    subst hxj
    exact hj <| by
      exact Finset.orderEmbOfFin_mem (color_pair_columns κ c d) rfl x
  simp [recolor_two_colors, hjimage, hj]

/-- Helper for Exercise 4.10: replacing a bad pair of colors by an equitable bicoloring on their
selected-column submatrix strictly lowers the square-sum potential. -/
lemma recolor_two_colors_decreases_potential
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d))
      red blue)
    (iwit : Fin m)
    (hwit : 1 < Int.natAbs (column_color_sum A κ c iwit - column_color_sum A κ d iwit)) :
    coloring_potential A (recolor_two_colors κ c d red) < coloring_potential A κ := by
  -- TODO: prove the bichromatic-exchange inequality row by row, using preservation of the
  -- `(c,d)` total row sum on the selected submatrix and the identity
  -- `2 * (x^2 + y^2) = (x - y)^2 + (x + y)^2`, with strict improvement on `iwit`.
  sorry

/-- Exercise 4.10: every totally unimodular integer matrix admits an equitable `k`-coloring for
every positive integer `k`; when `k = 1`, the pairwise condition is vacuous. -/
theorem exists_equitable_k_coloring_of_is_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : A.IsTotallyUnimodular)
    (hk : 0 < k) :
    ∃ κ : Fin n → Fin k, equitable_k_coloring A κ := by
  classical
  let baseColor : Fin k := ⟨0, hk⟩
  have hcolorings_nonempty : (Finset.univ : Finset (Fin n → Fin k)).Nonempty := by
    refine ⟨fun _ ↦ baseColor, by simp⟩
  obtain ⟨κmin, -, hκmin_min⟩ :=
    (Finset.univ : Finset (Fin n → Fin k)).exists_min_image
      (coloring_potential A) hcolorings_nonempty
  refine ⟨κmin, ?_⟩
  intro c d hcd i
  by_contra hbad
  have hwit :
      1 < Int.natAbs (column_color_sum A κmin c i - column_color_sum A κmin d i) := by
    omega
  obtain ⟨red, blue, hredblue⟩ :=
    exists_equitable_bicoloring_on_column_set A hA
      (color_pair_columns κmin c d)
  have hredblue' :
      is_equitable_bicoloring
        (A.submatrix id (color_pair_embedding κmin c d))
        red blue := by
    simpa [color_pair_embedding] using hredblue
  let κ' := recolor_two_colors κmin c d red
  have hlt : coloring_potential A κ' < coloring_potential A κmin := by
    -- Route correction: the main minimizer skeleton is now in place, and the only remaining
    -- substantive step is the planned bichromatic-exchange decrease lemma.
    simpa [κ'] using recolor_two_colors_decreases_potential
      A κmin c d red blue hredblue' i hwit
  have hmin_le : coloring_potential A κmin ≤ coloring_potential A κ' :=
    hκmin_min κ' (by simp)
  exact (not_lt_of_ge hmin_le) hlt

end Exercise410
