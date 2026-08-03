import Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_definition_4_8_1_extra_1
import Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_proposition_4_33

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section Theorem434

variable {n : ℕ}

/-- A list of indices is admissible for the mixing inequalities when it is nonempty, strictly
increasing, and has strictly increasing positive fractional parts. -/
def IsMixingIndexSequence (b : Fin n → ℚ) : List (Fin n) → Prop
  | [] => False
  | i :: is =>
      0 < mixingFractionalPart b i ∧
        (i :: is).IsChain (· < ·) ∧
        (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k)

/-- The coefficient sum appearing in mixing inequality (4.29): the coefficient of each selected
coordinate is the increment of the corresponding fractional part over the previous one, starting
from `0`. -/
private def mixingInequalityTypeOneRawSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * x i.succ + mixingInequalityTypeOneRawSumAux b x fi is

/-- Helper for Theorem 4.34: the floor contribution subtracted from the selected coordinates in the
shifted version of mixing inequality `(4.29)`. -/
private def mixingInequalityFloorSumAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (⌊b i⌋ : ℝ) + mixingInequalityFloorSumAux b fi is

/-- The coefficient sum appearing in mixing inequality (4.29): the selected successor coordinates
are measured after subtracting their floor parts, following the shifted-coordinate source
convention. -/
private def mixingInequalityTypeOneSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (x i.succ - (⌊b i⌋ : ℝ)) + mixingInequalityTypeOneSumAux b x fi is

/-- The left-hand-side increment sum for mixing inequality (4.29). -/
def mixingInequalityTypeOneSum
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : ℝ :=
  mixingInequalityTypeOneSumAux b x 0 s

/-- Helper for Theorem 4.34: the accumulated floor contribution in the shifted-coordinate mixing
inequalities. -/
private def mixingInequalityFloorSum
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  mixingInequalityFloorSumAux b 0 s

/-- Mixing inequality (4.29) associated with an admissible index sequence. -/
def mixingInequalityTypeOne
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s.reverse with
  | [] => True
  | last :: _ =>
      mixingFractionalPart b last ≤ x 0 + mixingInequalityTypeOneSum b s x

/-- Mixing inequality (4.30) associated with an admissible index sequence. Its first selected
coordinate receives the additional coefficient `1 - f_{i_m}`. -/
def mixingInequalityTypeTwo
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      mixingFractionalPart b last ≤
        x 0 + mixingInequalityTypeOneSum b s x +
          (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))
  | _, _ => True

/-- The selected-coordinate coefficient contribution in the linear form realizing mixing
inequality `(4.29)`. -/
private def mixingInequalityTypeOneCoeffAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → Fin (n + 1) → ℝ
  | _, [] => fun _ ↦ 0
  | prev, i :: is =>
      fun j ↦
        (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
          mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j

/-- Bridge/view: the coefficient vector whose linear inequality is exactly mixing inequality
`(4.29)`. -/
def mixingInequalityTypeOneCoeff
    (b : Fin n → ℚ) (s : List (Fin n)) : Fin (n + 1) → ℝ :=
  fun j ↦ (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j

/-- The common right-hand side of the linear forms realizing mixing inequalities `(4.29)` and
`(4.30)` splits after the shift repair, because the floor contributions now depend on the selected
coordinates. -/
def mixingInequalityTypeOneRhs
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  match s.reverse with
  | [] => 0
  | last :: _ => -mixingFractionalPart b last - mixingInequalityFloorSum b s

/-- The right-hand side of the linear form realizing shifted mixing inequality `(4.30)`. -/
def mixingInequalityTypeTwoRhs
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      -mixingFractionalPart b last - mixingInequalityFloorSum b s -
        (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ)
  | _, _ => 0

/-- Helper for Theorem 4.34: a single-coordinate coefficient vector evaluates to the expected
scalar multiple of that coordinate. -/
private lemma single_coordinate_dotProduct
    {m : ℕ} (j : Fin m) (c : ℝ) (x : Fin m → ℝ) :
    (fun k : Fin m ↦ if k = j then c else 0) ⬝ᵥ x = c * x j := by
  -- Collapse the finite dot product to its unique nonzero coordinate.
  rw [dotProduct, Fintype.sum_eq_single j]
  · simp
  · intro k hk
    simp [hk]

/-- Helper for Theorem 4.34: the recursive coefficient vector for `(4.29)` evaluates to the
negative of the recursive increment sum. -/
private lemma mixingInequalityTypeOneRawSumAux_eq_shifted_add_floor
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneRawSumAux b x prev s =
        mixingInequalityTypeOneSumAux b x prev s + mixingInequalityFloorSumAux b prev s
  | prev, [] => by
      -- The empty sequence has no shifted or floor contribution.
      simp [mixingInequalityTypeOneRawSumAux, mixingInequalityTypeOneSumAux,
        mixingInequalityFloorSumAux]
  | prev, i :: is => by
      -- Split the raw coordinate into its shifted part plus the floor that was removed.
      rw [mixingInequalityTypeOneRawSumAux, mixingInequalityTypeOneSumAux,
        mixingInequalityFloorSumAux, mixingInequalityTypeOneRawSumAux_eq_shifted_add_floor]
      ring

/-- Helper for Theorem 4.34: the recursive coefficient vector for `(4.29)` evaluates to the
negative of the unshifted recursive increment sum. -/
private lemma mixingInequalityTypeOneCoeffAux_dotProduct
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneCoeffAux b prev s ⬝ᵥ x =
        -mixingInequalityTypeOneRawSumAux b x prev s
  | prev, [] => by
      -- The empty sequence contributes no coefficients and no sum.
      simp [mixingInequalityTypeOneCoeffAux, mixingInequalityTypeOneRawSumAux, dotProduct]
  | prev, i :: is => by
      -- Split off the new selected coordinate and reuse the recursive evaluation on the tail.
      rw [mixingInequalityTypeOneCoeffAux, mixingInequalityTypeOneRawSumAux]
      -- View the recursive coefficient vector as a sum of the new singleton coefficient and the
      -- tail coefficients, then evaluate each summand separately.
      have hadd :
          (fun j : Fin (n + 1) ↦
              (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
                mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x := by
        change
          (((fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x)
        exact
          add_dotProduct
            (fun j : Fin (n + 1) ↦
              if j = i.succ then -(mixingFractionalPart b i - prev) else 0)
            (mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is)
            x
      rw [hadd, single_coordinate_dotProduct, mixingInequalityTypeOneCoeffAux_dotProduct]
      ring

/-- Helper for Theorem 4.34: the coefficient vector for `(4.29)` evaluates to the negative of its
unshifted left-hand-side linear form before the floor-shift constants are moved to the right-hand
side. -/
private lemma mixingInequalityTypeOneCoeff_dotProduct
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x =
      -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 s) := by
  -- Separate the zeroth-coordinate coefficient from the recursive tail contribution.
  change
    (fun j : Fin (n + 1) ↦
        (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j) ⬝ᵥ x =
      -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 s)
  -- Split the dot product into the `x 0` term and the recursive tail term.
  have hadd :
      (fun j : Fin (n + 1) ↦
          (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          mixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x := by
    change
      (((fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) +
          mixingInequalityTypeOneCoeffAux b 0 s) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          mixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x)
    exact
      add_dotProduct
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0)
        (mixingInequalityTypeOneCoeffAux b 0 s)
        x
  rw [hadd, single_coordinate_dotProduct, mixingInequalityTypeOneCoeffAux_dotProduct]
  ring

/-- For an admissible mixing index sequence, the linear inequality with coefficient vector
`mixingInequalityTypeOneCoeff b s` is exactly `(4.29)`. -/
theorem mixingInequalityTypeOneCoeff_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeOneRhs b s ↔
      mixingInequalityTypeOne b s x := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Reduce the vector inequality to the shifted scalar textbook inequality.
          rw [mixingInequalityTypeOneCoeff_dotProduct]
          have hsum :
              mixingInequalityTypeOneRawSumAux b x 0 (first :: tail) =
                mixingInequalityTypeOneSum b (first :: tail) x +
                  mixingInequalityFloorSum b (first :: tail) := by
            simpa [mixingInequalityTypeOneSum, mixingInequalityFloorSum] using
              mixingInequalityTypeOneRawSumAux_eq_shifted_add_floor b x 0 (first :: tail)
          have hlin :
              -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 (first :: tail)) ≤
                  mixingInequalityTypeOneRhs b (first :: tail) ↔
                mixingFractionalPart b last ≤
                  x 0 + mixingInequalityTypeOneSum b (first :: tail) x := by
            have hrhs :
                mixingInequalityTypeOneRhs b (first :: tail) =
                  -mixingFractionalPart b last - mixingInequalityFloorSum b (first :: tail) := by
              simp [mixingInequalityTypeOneRhs, hrev]
            constructor
            · intro h
              rw [hrhs] at h
              linarith [h, hsum]
            · intro h
              rw [hrhs]
              linarith [h, hsum]
          simpa [mixingInequalityTypeOne, mixingInequalityTypeOneRhs, hrev, hsum] using hlin

/-- Bridge/view: the coefficient vector whose linear inequality is exactly mixing inequality
`(4.30)`. -/
def mixingInequalityTypeTwoCoeff
    (b : Fin n → ℚ) (s : List (Fin n)) : Fin (n + 1) → ℝ :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      fun j ↦
        mixingInequalityTypeOneCoeff b s j +
          (if j = first.succ then -(1 - mixingFractionalPart b last) else 0)
  | _, _ => mixingInequalityTypeOneCoeff b s

/-- Helper for Theorem 4.34: once the first and last selected indices are fixed, the coefficient
vector for `(4.30)` evaluates to the negative of its left-hand-side linear form. -/
private lemma mixingInequalityTypeTwoCoeff_dotProduct_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ x =
      -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 (first :: tail) +
        (1 - mixingFractionalPart b last) * x first.succ) := by
  -- The extra first-coordinate coefficient contributes exactly the additional term in `(4.30)`.
  simp only [mixingInequalityTypeTwoCoeff, hrev]
  -- Split the repaired coefficient vector into the type-one part and the extra first-coordinate
  -- correction.
  have hadd :
      (fun j : Fin (n + 1) ↦
          mixingInequalityTypeOneCoeff b (first :: tail) j +
            (if j = first.succ then -(1 - mixingFractionalPart b last) else 0)) ⬝ᵥ x =
        mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ x +
          (fun j : Fin (n + 1) ↦
            if j = first.succ then -(1 - mixingFractionalPart b last) else 0) ⬝ᵥ x := by
    change
      ((mixingInequalityTypeOneCoeff b (first :: tail) +
            (fun j : Fin (n + 1) ↦
              if j = first.succ then -(1 - mixingFractionalPart b last) else 0)) ⬝ᵥ x =
        mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ x +
          (fun j : Fin (n + 1) ↦
            if j = first.succ then -(1 - mixingFractionalPart b last) else 0) ⬝ᵥ x)
    exact
      add_dotProduct
        (mixingInequalityTypeOneCoeff b (first :: tail))
        (fun j : Fin (n + 1) ↦
          if j = first.succ then -(1 - mixingFractionalPart b last) else 0)
        x
  rw [hadd, mixingInequalityTypeOneCoeff_dotProduct, single_coordinate_dotProduct]
  ring

/-- For an admissible mixing index sequence, the linear inequality with coefficient vector
`mixingInequalityTypeTwoCoeff b s` is exactly `(4.30)`. -/
theorem mixingInequalityTypeTwoCoeff_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeTwoRhs b s ↔
      mixingInequalityTypeTwo b s x := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Reduce the vector inequality to the shifted scalar textbook inequality with the extra
          -- first-coordinate correction.
          rw [mixingInequalityTypeTwoCoeff_dotProduct_of_reverse b first last tail revTail hrev]
          have hsum :
              mixingInequalityTypeOneRawSumAux b x 0 (first :: tail) =
                mixingInequalityTypeOneSum b (first :: tail) x +
                  mixingInequalityFloorSum b (first :: tail) := by
            simpa [mixingInequalityTypeOneSum, mixingInequalityFloorSum] using
              mixingInequalityTypeOneRawSumAux_eq_shifted_add_floor b x 0 (first :: tail)
          have hlin :
              -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 (first :: tail) +
                    (1 - mixingFractionalPart b last) * x first.succ) ≤
                  mixingInequalityTypeTwoRhs b (first :: tail) ↔
                mixingFractionalPart b last ≤
                  x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                    (1 - mixingFractionalPart b last) *
                      (x first.succ - (⌊b first⌋ : ℝ)) := by
            have hrhs :
                mixingInequalityTypeTwoRhs b (first :: tail) =
                  -mixingFractionalPart b last - mixingInequalityFloorSum b (first :: tail) -
                    (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ) := by
              simp [mixingInequalityTypeTwoRhs, hrev]
            constructor
            · intro h
              rw [hrhs] at h
              linarith [h, hsum]
            · intro h
              rw [hrhs]
              linarith [h, hsum]
          simpa [mixingInequalityTypeTwo, mixingInequalityTypeTwoRhs, hrev, hsum] using hlin

-- Semantic recall note: no competing mathlib owner was found, so this file keeps the source
-- description of `P^mix` directly.
/-- An auxiliary region cut out by `x₀ ≥ 0`, the degenerate zero-fractional-part singleton
relaxation inequalities, and all mixing inequalities `(4.29)` and `(4.30)` indexed by admissible
sequences. -/
def mixingInequalitiesRegion
    (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧
      (∀ i : Fin n, mixingFractionalPart b i = 0 → (b i : ℝ) ≤ x 0 + x i.succ) ∧
      ∀ s : List (Fin n), IsMixingIndexSequence b s →
        mixingInequalityTypeOne b s x ∧ mixingInequalityTypeTwo b s x}

/-- The source-facing region cut out by `x₀ ≥ 0` and the mixing inequalities `(4.29)` and
`(4.30)` for admissible positive-fraction index sequences. -/
def positiveFractionMixingInequalitiesRegion
    (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧
      ∀ s : List (Fin n), IsMixingIndexSequence b s →
        mixingInequalityTypeOne b s x ∧ mixingInequalityTypeTwo b s x}

/-- Helper for Theorem 4.34: the ceiling base point used throughout the ambient-space recession
argument. -/
private def mixingCeilingWitness (b : Fin n → ℚ) : Fin (n + 1) → ℝ :=
  fun i ↦ Fin.cases 0 (fun t : Fin n ↦ (⌈b t⌉ : ℝ)) i

/-- Helper for Theorem 4.34: every mixing fractional part is nonnegative. -/
private lemma mixingFractionalPart_nonneg
    (b : Fin n → ℚ) (i : Fin n) :
    0 ≤ mixingFractionalPart b i := by
  -- The source fractional parts are real `Int.fract` values.
  simpa [mixingFractionalPart_eq_fract] using Int.fract_nonneg ((b i : ℚ) : ℝ)

/-- Helper for Theorem 4.34: every member of an admissible sequence has positive fractional part. -/
private lemma mixingFractionalPart_pos_of_mem_isMixingIndexSequence
    (b : Fin n → ℚ) :
    ∀ {s : List (Fin n)}, IsMixingIndexSequence b s →
      ∀ {i : Fin n}, i ∈ s → 0 < mixingFractionalPart b i
  | [], hs, i, hi => False.elim hs
  | i0 :: is, hs, i, hi => by
      -- The head is positive by definition, and the fractional-part chain propagates that
      -- positivity to every later member.
      rcases hs with ⟨hi0_pos, -, hfracChain⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hi0_pos
      · exact lt_trans hi0_pos (hfracChain.rel_cons hi)
 

/-- Helper for Theorem 4.34: at the ceiling witness, every selected positive-fraction coordinate
contributes exactly `1` after subtracting its floor part. -/
private lemma mixingCeilingWitness_succ_sub_floor_eq_one_of_pos
    (b : Fin n → ℚ) {i : Fin n}
    (hi_pos : 0 < mixingFractionalPart b i) :
    mixingCeilingWitness b i.succ - (⌊b i⌋ : ℝ) = 1 := by
  -- A positive fractional part means `bᵢ` is nonintegral, so its ceiling is `⌊bᵢ⌋ + 1`.
  change ((⌈b i⌉ : ℝ) - (⌊b i⌋ : ℝ) = 1)
  have hnot_int : b i ∉ Set.range (fun z : ℤ ↦ (z : ℚ)) := by
    intro hmem
    rcases hmem with ⟨z, hz⟩
    have hz' : ((b i : ℚ) : ℝ) = (z : ℝ) := by
      simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) hz.symm
    have : mixingFractionalPart b i = 0 := by
      rw [mixingFractionalPart_eq_fract, hz']
      simp
    exact (ne_of_gt hi_pos) this
  have hceil_eq : ⌈b i⌉ = ⌊b i⌋ + 1 := by
    exact (Int.ceil_eq_floor_add_one_iff_notMem (b i)).2 hnot_int
  have hceil_eq_cast : (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
    exact_mod_cast hceil_eq
  linarith

/-- Helper for Theorem 4.34: evaluating the shifted type-one sum at the ceiling witness telescopes
to the last fractional part. -/
private lemma mixingInequalityTypeOneSumAux_mixingCeilingWitness
    (b : Fin n → ℚ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      (∀ i ∈ s, 0 < mixingFractionalPart b i) →
      mixingInequalityTypeOneSumAux b (mixingCeilingWitness b) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - prev
  | _, [], _ => by
      -- The empty sequence contributes no shifted terms.
      simp [mixingInequalityTypeOneSumAux]
  | prev, [i], hs => by
      -- A singleton admissible sequence contributes one unit after the floor shift.
      have hi_pos : 0 < mixingFractionalPart b i := hs i (by simp)
      rw [mixingInequalityTypeOneSumAux,
        mixingCeilingWitness_succ_sub_floor_eq_one_of_pos b hi_pos]
      simp [mixingInequalityTypeOneSumAux]
  | prev, i :: j :: is, hs => by
      -- The shifted ceiling witness turns every selected coordinate contribution into `1`, so the
      -- increment sum telescopes along the tail.
      have hi_pos : 0 < mixingFractionalPart b i := hs i (by simp)
      have htail :
          ∀ k ∈ j :: is, 0 < mixingFractionalPart b k := by
        intro k hk
        exact hs k (by simp [hk])
      rw [mixingInequalityTypeOneSumAux,
        mixingCeilingWitness_succ_sub_floor_eq_one_of_pos b hi_pos]
      simp only [mul_one]
      rw [mixingInequalityTypeOneSumAux_mixingCeilingWitness b (mixingFractionalPart b i) (j :: is)
        htail]
      cases hrev : (j :: is).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          simp [List.reverse_cons, hrev]

/-- Helper for Theorem 4.34: the ceiling base point already satisfies every defining inequality of
the auxiliary stronger region. -/
private lemma mixingCeilingWitness_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    mixingCeilingWitness b ∈ mixingInequalitiesRegion b := by
  -- The ceiling witness satisfies the degenerate zero-fraction constraints and makes every
  -- positive-fraction mixing inequality hold by the telescoping computation above.
  refine ⟨by simp [mixingCeilingWitness], ?_, ?_⟩
  · intro i hi_zero
    have hceil : ((b i : ℚ) : ℝ) ≤ (⌈b i⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil (b i)
    simpa [mixingCeilingWitness] using hceil
  · intro s hs
    cases s with
    | nil =>
        cases hs
    | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      have hs' : IsMixingIndexSequence b (first :: tail) :=
        ⟨hfirst_pos, hindexChain, hfracChain⟩
      have hspos :
          ∀ i ∈ first :: tail, 0 < mixingFractionalPart b i := by
        intro i hi
        exact mixingFractionalPart_pos_of_mem_isMixingIndexSequence b hs' hi
      have hsum :
          mixingInequalityTypeOneSum b (first :: tail) (mixingCeilingWitness b) =
            match (first :: tail).reverse with
            | [] => 0
            | last :: _ => mixingFractionalPart b last := by
        simpa [mixingInequalityTypeOneSum] using
          mixingInequalityTypeOneSumAux_mixingCeilingWitness b 0 (first :: tail) hspos
      constructor
      · -- Route correction: prove the type-one inequality directly from the telescoping sum.
        cases hrev : (first :: tail).reverse with
        | nil =>
            simp at hrev
        | cons last revTail =>
            rw [mixingInequalityTypeOne]
            simp [hrev, hsum, mixingCeilingWitness]
      · -- The type-two inequality adds the nonnegative correction `(1 - f_last) * 1`.
        cases hrev : (first :: tail).reverse with
        | nil =>
            simp at hrev
        | cons last revTail =>
            have hfirst_shift :
                mixingCeilingWitness b first.succ - (⌊b first⌋ : ℝ) = 1 :=
              mixingCeilingWitness_succ_sub_floor_eq_one_of_pos b hfirst_pos
            have hlast_lt : mixingFractionalPart b last < 1 := by
              simpa [mixingFractionalPart_eq_fract] using Int.fract_lt_one ((b last : ℚ) : ℝ)
            have hzero : mixingCeilingWitness b 0 = 0 := by
              simp [mixingCeilingWitness]
            have hsum' :
                mixingInequalityTypeOneSum b (first :: tail) (mixingCeilingWitness b) =
                  mixingFractionalPart b last := by
              simpa [hrev] using hsum
            have hgoal :
                mixingFractionalPart b last ≤
                  mixingCeilingWitness b 0 +
                    mixingInequalityTypeOneSum b (first :: tail) (mixingCeilingWitness b) +
                      (1 - mixingFractionalPart b last) *
                        (mixingCeilingWitness b first.succ - (⌊b first⌋ : ℝ)) := by
              rw [hzero, hsum', hfirst_shift]
              nlinarith [hlast_lt]
            simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for Theorem 4.34: every point of the auxiliary stronger region lies in the underlying
Exercise 3.29 relaxation. -/
private lemma mixingInequalitiesRegion_subset_exercisePolyhedron
    (b : Fin n → ℚ) :
    mixingInequalitiesRegion b ⊆ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) := by
  -- Each relaxation inequality is either the explicit zero-fraction clause or the singleton
  -- type-two mixing inequality.
  intro x hx
  rcases hx with ⟨hx0, hzero, hmix⟩
  rw [mem_exercise_3_29_polyhedron_iff]
  refine ⟨hx0, ?_⟩
  intro i
  by_cases hfi : mixingFractionalPart b i = 0
  · exact hzero i hfi
  · have hfi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne' (mixingFractionalPart_nonneg b i) hfi
    have hsingleton : IsMixingIndexSequence b [i] := by
      refine ⟨hfi_pos, ?_, ?_⟩ <;> simp
    have htypeTwo : mixingInequalityTypeTwo b [i] x := (hmix [i] hsingleton).2
    have hineq' :
        mixingFractionalPart b i ≤ x i.succ + (-((⌊b i⌋ : ℝ)) + x 0) := by
      -- On a singleton sequence, the type-two inequality collapses to a shifted one-variable
      -- bound.
      simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using htypeTwo
    have hineq :
        mixingFractionalPart b i + (⌊b i⌋ : ℝ) ≤ x 0 + x i.succ := by
      linarith
    have hb_eq :
        (b i : ℝ) = mixingFractionalPart b i + (⌊b i⌋ : ℝ) := by
      calc
        (b i : ℝ) = Int.fract ((b i : ℚ) : ℝ) + (⌊((b i : ℚ) : ℝ)⌋ : ℝ) := by
          linarith [Int.floor_add_fract ((b i : ℚ) : ℝ)]
        _ = mixingFractionalPart b i + (⌊b i⌋ : ℝ) := by
          have hfloor : ⌊((b i : ℚ) : ℝ)⌋ = ⌊b i⌋ :=
            (Rat.floor_cast (b i) : ⌊((b i : ℚ) : ℝ)⌋ = ⌊b i⌋)
          rw [mixingFractionalPart_eq_fract, hfloor]
    linarith

/-- Helper for Theorem 4.34: every point of `P^mix` satisfies the underlying continuous
relaxation `x₀ ≥ 0` and `bᵢ ≤ x₀ + xᵢ`. -/
private lemma mixingHull_subset_exercisePolyhedron
    (b : Fin n → ℚ) :
    mixingHull b ⊆ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) := by
  -- It is enough to check the defining relaxation on the generators and then use convexity.
  refine convexHull_min ?_ ?_
  · intro x hx
    rw [mem_mixingSet_iff] at hx
    rw [mem_exercise_3_29_polyhedron_iff]
    exact ⟨hx.1, hx.2.2⟩
  · intro x hx y hy a b' ha hb hab
    -- The relaxation inequalities are affine, so they are preserved by convex combinations.
    rw [mem_exercise_3_29_polyhedron_iff] at hx hy ⊢
    constructor
    · have hx0 :
          0 ≤ a * x 0 := mul_nonneg ha hx.1
      have hy0 :
          0 ≤ b' * y 0 := mul_nonneg hb hy.1
      have hsum0 :
          0 ≤ a * x 0 + b' * y 0 := add_nonneg hx0 hy0
      have hcoord0 :
          (a • x + b' • y) 0 = a * x 0 + b' * y 0 := by
        simp [Pi.add_apply, Pi.smul_apply]
      rw [hcoord0]
      exact hsum0
    · intro t
      have hineq :
          (b t : ℝ) ≤ (a • x + b' • y) 0 + (a • x + b' • y) t.succ := by
        calc
          (b t : ℝ) = (a + b') * (b t : ℝ) := by
            rw [hab, one_mul]
          _ = a * (b t : ℝ) + b' * (b t : ℝ) := by
            ring
          _ ≤ a * (x 0 + x t.succ) + b' * (y 0 + y t.succ) := by
            gcongr
            · exact hx.2 t
            · exact hy.2 t
          _ = (a • x + b' • y) 0 + (a • x + b' • y) t.succ := by
            simp [Pi.add_apply, Pi.smul_apply, mul_add, add_assoc, add_left_comm, add_comm]
      exact hineq

/-- Helper for Theorem 4.34: the auxiliary stronger region is convex, because each defining clause
is an affine halfspace condition. -/
private lemma mixingInequalitiesRegion_convex
    (b : Fin n → ℚ) :
    Convex ℝ (mixingInequalitiesRegion b) := by
  -- Each defining inequality is affine, so convex combinations preserve the region.
  intro x hx y hy a c ha hc hac
  rcases hx with ⟨hx0, hxzero, hxmix⟩
  rcases hy with ⟨hy0, hyzero, hymix⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The zeroth coordinate stays nonnegative under convex combinations.
    have hcoord0 : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [hcoord0]
    exact add_nonneg (mul_nonneg ha hx0) (mul_nonneg hc hy0)
  · -- The zero-fraction covering inequalities are affine as well.
    intro i hi_zero
    calc
      (b i : ℝ) = (a + c) * (b i : ℝ) := by rw [hac, one_mul]
      _ = a * (b i : ℝ) + c * (b i : ℝ) := by ring
      _ ≤ a * (x 0 + x i.succ) + c * (y 0 + y i.succ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hxzero i hi_zero) ha)
          (mul_le_mul_of_nonneg_left (hyzero i hi_zero) hc)
      _ = (a • x + c • y) 0 + (a • x + c • y) i.succ := by
        simp [Pi.add_apply, Pi.smul_apply, mul_add, add_assoc, add_left_comm, add_comm]
  · -- Rewrite the source inequalities to linear forms and preserve them by convexity.
    intro s hs
    constructor
    · have hxlin :
          mixingInequalityTypeOneCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeOneRhs b s :=
        (mixingInequalityTypeOneCoeff_iff b s hs x).2 (hxmix s hs).1
      have hylin :
          mixingInequalityTypeOneCoeff b s ⬝ᵥ y ≤ mixingInequalityTypeOneRhs b s :=
        (mixingInequalityTypeOneCoeff_iff b s hs y).2 (hymix s hs).1
      have hweighted :
          a * (mixingInequalityTypeOneCoeff b s ⬝ᵥ x) +
              c * (mixingInequalityTypeOneCoeff b s ⬝ᵥ y) ≤
            a * mixingInequalityTypeOneRhs b s + c * mixingInequalityTypeOneRhs b s :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxlin ha)
          (mul_le_mul_of_nonneg_left hylin hc)
      have hrhs :
          a * mixingInequalityTypeOneRhs b s + c * mixingInequalityTypeOneRhs b s =
            mixingInequalityTypeOneRhs b s := by
        calc
          a * mixingInequalityTypeOneRhs b s + c * mixingInequalityTypeOneRhs b s =
              (a + c) * mixingInequalityTypeOneRhs b s := by ring
          _ = mixingInequalityTypeOneRhs b s := by rw [hac, one_mul]
      have hlin :
          mixingInequalityTypeOneCoeff b s ⬝ᵥ (a • x + c • y) ≤
            mixingInequalityTypeOneRhs b s := by
        calc
          mixingInequalityTypeOneCoeff b s ⬝ᵥ (a • x + c • y) =
              a * (mixingInequalityTypeOneCoeff b s ⬝ᵥ x) +
                c * (mixingInequalityTypeOneCoeff b s ⬝ᵥ y) := by
            rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
            simp [smul_eq_mul]
          _ ≤ a * mixingInequalityTypeOneRhs b s + c * mixingInequalityTypeOneRhs b s :=
            hweighted
          _ = mixingInequalityTypeOneRhs b s := hrhs
      exact (mixingInequalityTypeOneCoeff_iff b s hs (a • x + c • y)).1 hlin
    · have hxlin :
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeTwoRhs b s :=
        (mixingInequalityTypeTwoCoeff_iff b s hs x).2 (hxmix s hs).2
      have hylin :
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ y ≤ mixingInequalityTypeTwoRhs b s :=
        (mixingInequalityTypeTwoCoeff_iff b s hs y).2 (hymix s hs).2
      have hweighted :
          a * (mixingInequalityTypeTwoCoeff b s ⬝ᵥ x) +
              c * (mixingInequalityTypeTwoCoeff b s ⬝ᵥ y) ≤
            a * mixingInequalityTypeTwoRhs b s + c * mixingInequalityTypeTwoRhs b s :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxlin ha)
          (mul_le_mul_of_nonneg_left hylin hc)
      have hrhs :
          a * mixingInequalityTypeTwoRhs b s + c * mixingInequalityTypeTwoRhs b s =
            mixingInequalityTypeTwoRhs b s := by
        calc
          a * mixingInequalityTypeTwoRhs b s + c * mixingInequalityTypeTwoRhs b s =
              (a + c) * mixingInequalityTypeTwoRhs b s := by ring
          _ = mixingInequalityTypeTwoRhs b s := by rw [hac, one_mul]
      have hlin :
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ (a • x + c • y) ≤
            mixingInequalityTypeTwoRhs b s := by
        calc
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ (a • x + c • y) =
              a * (mixingInequalityTypeTwoCoeff b s ⬝ᵥ x) +
                c * (mixingInequalityTypeTwoCoeff b s ⬝ᵥ y) := by
            rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
            simp [smul_eq_mul]
          _ ≤ a * mixingInequalityTypeTwoRhs b s + c * mixingInequalityTypeTwoRhs b s :=
            hweighted
          _ = mixingInequalityTypeTwoRhs b s := hrhs
      exact (mixingInequalityTypeTwoCoeff_iff b s hs (a • x + c • y)).1 hlin

/-- Helper for Theorem 4.34: on points with integral tail coordinates, the source-facing mixing
inequalities already recover the original mixing-set inequalities. -/
private lemma mixingInequalitiesRegion_mem_mixingSet_of_integerTail
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    (htail : ∀ i : Fin n, x i.succ ∈ Set.range (fun z : ℤ ↦ (z : ℝ))) :
    x ∈ mixingSet b := by
  -- The region already lies in the continuous relaxation; the extra hypothesis supplies the
  -- missing tail integrality needed for `mixingSet`.
  have hxrel : x ∈ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) :=
    mixingInequalitiesRegion_subset_exercisePolyhedron b hx
  rw [mem_exercise_3_29_polyhedron_iff] at hxrel
  rw [mem_mixingSet_iff_forall]
  exact ⟨hx.1, htail, hxrel.2⟩

/-- Helper for Theorem 4.34: along a strictly increasing list of fractional parts, every later
fractional part dominates the head fractional part. -/
private lemma mixingFractionalPart_le_of_mem_chain
    (b : Fin n → ℚ) {i : Fin n} {is : List (Fin n)}
    (hchain : (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    {j : Fin n} (hj : j ∈ is) :
    mixingFractionalPart b i ≤ mixingFractionalPart b j := by
  -- The fractional-part chain already gives the strict head-to-tail comparison.
  exact le_of_lt (hchain.rel_cons hj)

/-- Helper for Theorem 4.34: every successor coordinate of the auxiliary coefficient vector for
`(4.29)` is nonpositive once the recursive fractional-part increments are nonnegative. -/
private lemma mixingInequalityTypeOneCoeffAux_succ_nonpos
    (b : Fin n → ℚ) (i0 : Fin n) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, prev ≤ mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      mixingInequalityTypeOneCoeffAux b prev s i0.succ ≤ 0 := by
  intro prev s
  induction s generalizing prev with
  | nil =>
      intro hmono hchain
      -- The empty recursive coefficient vector vanishes identically.
      simp [mixingInequalityTypeOneCoeffAux]
  | cons i is ih =>
      intro hmono hchain
      -- Split off the current increment and control the tail recursively with the new base level.
      rw [mixingInequalityTypeOneCoeffAux]
      have hhead_nonneg : 0 ≤ mixingFractionalPart b i - prev :=
        sub_nonneg.mpr (hmono i (by simp))
      have hhead_nonpos :
          (if i0.succ = i.succ then -(mixingFractionalPart b i - prev) else 0 : ℝ) ≤ 0 := by
        by_cases hEq : i0.succ = i.succ
        · have hneg : -(mixingFractionalPart b i - prev) ≤ 0 :=
            neg_nonpos.mpr hhead_nonneg
          simpa [hEq] using hneg
        · simp [hEq]
      have htail_mono :
          ∀ j ∈ is, mixingFractionalPart b i ≤ mixingFractionalPart b j := by
        intro j hj
        exact le_of_lt (hchain.rel_cons hj)
      have htail_nonpos :
          mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is i0.succ ≤ 0 :=
        ih htail_mono hchain.tail
      linarith

/-- Helper for Theorem 4.34: every successor coordinate of the type-one mixing coefficient vector
`mixingInequalityTypeOneCoeff b s` is nonpositive on an admissible sequence. -/
private lemma mixingInequalityTypeOneCoeff_succ_nonpos
    (b : Fin n → ℚ) {s : List (Fin n)} (hs : IsMixingIndexSequence b s) (i0 : Fin n) :
    mixingInequalityTypeOneCoeff b s i0.succ ≤ 0 := by
  -- The head coefficient `-1` disappears at successor coordinates, so only the recursive tail
  -- coefficients remain.
  cases s with
  | nil =>
      cases hs
  | cons i is =>
      rcases hs with ⟨hi_pos, hindexChain, hfracChain⟩
      have hmono : ∀ j ∈ i :: is, (0 : ℝ) ≤ mixingFractionalPart b j := by
        intro j hj
        exact mixingFractionalPart_nonneg b j
      simpa [mixingInequalityTypeOneCoeff] using
        mixingInequalityTypeOneCoeffAux_succ_nonpos b i0 hmono hfracChain

/-- Helper for Theorem 4.34: every successor coordinate of the type-two mixing coefficient vector
`mixingInequalityTypeTwoCoeff b s` is nonpositive on an admissible sequence. -/
private lemma mixingInequalityTypeTwoCoeff_succ_nonpos
    (b : Fin n → ℚ) {s : List (Fin n)} (hs : IsMixingIndexSequence b s) (i0 : Fin n) :
    mixingInequalityTypeTwoCoeff b s i0.succ ≤ 0 := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      have hs' : IsMixingIndexSequence b (first :: tail) :=
        ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- The type-two coefficient vector is the type-one vector plus one extra nonpositive
          -- first-coordinate correction.
          have htypeOne :
              mixingInequalityTypeOneCoeff b (first :: tail) i0.succ ≤ 0 :=
            mixingInequalityTypeOneCoeff_succ_nonpos b hs' i0
          have hlast_lt_one : mixingFractionalPart b last < 1 := by
            simpa [mixingFractionalPart_eq_fract] using Int.fract_lt_one ((b last : ℚ) : ℝ)
          have hextra_nonpos :
              (if i0.succ = first.succ then
                  -(1 - mixingFractionalPart b last)
                else 0 : ℝ) ≤ 0 := by
            by_cases hEq : i0.succ = first.succ
            · have hnonneg : 0 ≤ 1 - mixingFractionalPart b last := by
                linarith
              have hneg : -(1 - mixingFractionalPart b last) ≤ 0 :=
                neg_nonpos.mpr hnonneg
              simpa [hEq] using hneg
            · simp [hEq]
          have hsum_nonpos :
              mixingInequalityTypeOneCoeff b (first :: tail) i0.succ +
                  (if i0.succ = first.succ then
                      -(1 - mixingFractionalPart b last)
                    else 0 : ℝ) ≤
                0 :=
            add_nonpos htypeOne hextra_nonpos
          simpa [mixingInequalityTypeTwoCoeff, hrev] using hsum_nonpos

/-- Helper for Theorem 4.34: a successor Exercise 3.29 ray pairs with a coefficient vector by
reading off the matching successor coordinate. -/
private lemma dotProduct_exercise_3_29_ray_succ
    (c : Fin (n + 1) → ℝ) (i0 : Fin n) :
    c ⬝ᵥ exercise_3_29_ray i0.succ = c i0.succ := by
  -- A successor ray is the single-coordinate vector at `i0.succ`.
  have hray :
      exercise_3_29_ray i0.succ =
        fun k : Fin (n + 1) ↦ if k = i0.succ then (1 : ℝ) else 0 := by
    funext k
    have hsucc_ne_zero : ¬ (Fin.succ i0 : Fin (n + 1)) = 0 := by
      simp
    simp [exercise_3_29_ray, hsucc_ne_zero]
  rw [dotProduct_comm, hray]
  simpa using single_coordinate_dotProduct i0.succ 1 c

/-- Helper for Theorem 4.34: translating by the head ray `r⁰` subtracts the telescoping last
fractional part from the shifted type-one sum. -/
private lemma mixingInequalityTypeOneSumAux_translate_headRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (a : ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneSumAux b
          (x + a • exercise_3_29_ray (0 : Fin (n + 1))) prev s =
        mixingInequalityTypeOneSumAux b x prev s +
          match s.reverse with
          | [] => 0
          | last :: _ => a * (prev - mixingFractionalPart b last) := by
  intro prev s
  induction s generalizing prev with
  | nil =>
      -- The empty selected set contributes no shifted sum.
      simp [mixingInequalityTypeOneSumAux]
  | cons i is ih =>
      -- Each selected successor coordinate drops by `a`, and the recursive tail telescopes.
      have hcoord :
          (x + a • exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ) =
            (x i.succ - (⌊b i⌋ : ℝ)) - a := by
        have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
          simp
        calc
          (x + a • exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ)
            = (x i.succ + a * (-1 : ℝ)) - (⌊b i⌋ : ℝ) := by
                simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
          _ = (x i.succ - (⌊b i⌋ : ℝ)) - a := by
                ring
      rw [mixingInequalityTypeOneSumAux, hcoord, ih]
      cases hrev : is.reverse with
      | nil =>
          simp [mixingInequalityTypeOneSumAux, List.reverse_cons, hrev]
          ring
      | cons last revTail =>
          rw [mixingInequalityTypeOneSumAux]
          simp [List.reverse_cons, hrev]
          ring

/-- Helper for Theorem 4.34: translating a region point by the head ray preserves every
source-facing mixing inequality. -/
private lemma mixingInequalitiesRegion_translate_headRay
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) {a : ℝ}
    (ha : 0 ≤ a) :
    x + a • exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingInequalitiesRegion b := by
  rcases hx with ⟨hx0, hzero, hmix⟩
  rcases exercise_3_29_ray_zero_head_coordinate_effect x a with ⟨hhead, -⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The head ray increases the zeroth coordinate by `a`.
    rw [hhead]
    linarith
  · intro i hi_zero
    -- Every zero-fraction covering inequality is unchanged because `r⁰` preserves `x₀ + xᵢ`.
    have hi_cover := hzero i hi_zero
    rcases exercise_3_29_ray_zero_mixed_coordinate_effect x a i with ⟨hmixed, -⟩
    rw [hmixed]
    exact hi_cover
  · intro s hs
    rcases hmix s hs with ⟨htypeOne, htypeTwo⟩
    cases s with
    | nil =>
        cases hs
    | cons first tail =>
        cases hrev : (first :: tail).reverse with
        | nil =>
            simp at hrev
        | cons last revTail =>
            have hlast_lt_one : mixingFractionalPart b last < 1 := by
              simpa [mixingFractionalPart_eq_fract] using Int.fract_lt_one ((b last : ℚ) : ℝ)
            have hsum :
                mixingInequalityTypeOneSum b (first :: tail)
                    (x + a • exercise_3_29_ray (0 : Fin (n + 1))) =
                  mixingInequalityTypeOneSum b (first :: tail) x +
                    a * (0 - mixingFractionalPart b last) := by
              simpa [mixingInequalityTypeOneSum, hrev] using
                mixingInequalityTypeOneSumAux_translate_headRay b x a 0 (first :: tail)
            have hfirst_shift :
                (x + a • exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ) =
                  x first.succ - (⌊b first⌋ : ℝ) - a := by
              have hsucc_ne_zero : ¬ (first.succ : Fin (n + 1)) = 0 := by
                simp
              calc
                (x + a • exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ)
                  = (x first.succ + a * (-1 : ℝ)) - (⌊b first⌋ : ℝ) := by
                      simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
                _ = x first.succ - (⌊b first⌋ : ℝ) - a := by
                      ring
            constructor
            · -- The type-one right-hand side gains the nonnegative amount `a * (1 - f_last)`.
              have horig :
                  mixingFractionalPart b last ≤
                    x 0 + mixingInequalityTypeOneSum b (first :: tail) x := by
                simpa [mixingInequalityTypeOne, hrev] using htypeOne
              have hgain_nonneg : 0 ≤ a * (1 - mixingFractionalPart b last) := by
                have hfactor_nonneg : 0 ≤ 1 - mixingFractionalPart b last := by
                  linarith
                exact mul_nonneg ha hfactor_nonneg
              have hgoal :
                  mixingFractionalPart b last ≤
                    (x + a • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
                      mixingInequalityTypeOneSum b (first :: tail)
                        (x + a • exercise_3_29_ray (0 : Fin (n + 1))) := by
                rw [hhead, hsum]
                have hrew :
                    x 0 + a + (mixingInequalityTypeOneSum b (first :: tail) x +
                        a * (0 - mixingFractionalPart b last)) =
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                        a * (1 - mixingFractionalPart b last) := by
                  ring
                rw [hrew]
                linarith
              simpa [mixingInequalityTypeOne, hrev] using hgoal
            · -- The type-two right-hand side is exactly invariant under the head translation.
              have horig :
                  mixingFractionalPart b last ≤
                    x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                      (1 - mixingFractionalPart b last) *
                        (x first.succ - (⌊b first⌋ : ℝ)) := by
                simpa [mixingInequalityTypeTwo, hrev] using htypeTwo
              have hgoal :
                  mixingFractionalPart b last ≤
                    (x + a • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
                      mixingInequalityTypeOneSum b (first :: tail)
                        (x + a • exercise_3_29_ray (0 : Fin (n + 1))) +
                        (1 - mixingFractionalPart b last) *
                          ((x + a • exercise_3_29_ray (0 : Fin (n + 1))) first.succ -
                            (⌊b first⌋ : ℝ)) := by
                rw [hhead, hsum, hfirst_shift]
                linarith
              simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for Theorem 4.34: translating a region point by a successor ray preserves every
source-facing mixing inequality. -/
private lemma mixingInequalitiesRegion_translate_succRay
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) (i0 : Fin n) {a : ℝ}
    (ha : 0 ≤ a) :
    x + a • exercise_3_29_ray (Fin.succ i0) ∈ mixingInequalitiesRegion b := by
  rcases hx with ⟨hx0, hzero, hmix⟩
  refine ⟨?_, ?_, ?_⟩
  · -- A successor ray leaves the head coordinate unchanged.
    rcases exercise_3_29_ray_succ_head_coordinate_effect x a i0 with ⟨hhead, -⟩
    simpa [hhead] using hx0
  · intro i hi_zero
    -- The unique support inequality becomes easier; every off-support inequality is unchanged.
    by_cases hi : i = i0
    · subst i
      have hi_cover := hzero i0 hi_zero
      rcases exercise_3_29_ray_succ_support_coordinate_effect x a i0 with ⟨hmixed, -⟩
      rw [hmixed]
      linarith
    · have hi_cover := hzero i hi_zero
      rcases exercise_3_29_ray_succ_offsupport_coordinate_effect x a hi with ⟨hmixed, -⟩
      rw [hmixed]
      exact hi_cover
  · intro s hs
    rcases hmix s hs with ⟨htypeOne, htypeTwo⟩
    constructor
    · -- Route correction: preserve `(4.29)` in coefficient normal form instead of the stalled
      -- source-level recursive successor-shift induction.
      have hxlin :
          mixingInequalityTypeOneCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeOneRhs b s :=
        (mixingInequalityTypeOneCoeff_iff b s hs x).2 htypeOne
      have hterm :
          a * mixingInequalityTypeOneCoeff b s i0.succ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha (mixingInequalityTypeOneCoeff_succ_nonpos b hs i0)
      have hlin :
          mixingInequalityTypeOneCoeff b s ⬝ᵥ (x + a • exercise_3_29_ray i0.succ) ≤
            mixingInequalityTypeOneRhs b s := by
        calc
          mixingInequalityTypeOneCoeff b s ⬝ᵥ (x + a • exercise_3_29_ray i0.succ) =
              mixingInequalityTypeOneCoeff b s ⬝ᵥ x +
                a * mixingInequalityTypeOneCoeff b s i0.succ := by
                rw [dotProduct_add, dotProduct_smul, dotProduct_exercise_3_29_ray_succ]
                simp [smul_eq_mul]
          _ ≤ mixingInequalityTypeOneCoeff b s ⬝ᵥ x := by
                linarith
          _ ≤ mixingInequalityTypeOneRhs b s := hxlin
      exact (mixingInequalityTypeOneCoeff_iff b s hs
        (x + a • exercise_3_29_ray i0.succ)).1 hlin
    · -- The same coefficient-sign route preserves `(4.30)`.
      have hxlin :
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeTwoRhs b s :=
        (mixingInequalityTypeTwoCoeff_iff b s hs x).2 htypeTwo
      have hterm :
          a * mixingInequalityTypeTwoCoeff b s i0.succ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha (mixingInequalityTypeTwoCoeff_succ_nonpos b hs i0)
      have hlin :
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ (x + a • exercise_3_29_ray i0.succ) ≤
            mixingInequalityTypeTwoRhs b s := by
        calc
          mixingInequalityTypeTwoCoeff b s ⬝ᵥ (x + a • exercise_3_29_ray i0.succ) =
              mixingInequalityTypeTwoCoeff b s ⬝ᵥ x +
                a * mixingInequalityTypeTwoCoeff b s i0.succ := by
                rw [dotProduct_add, dotProduct_smul, dotProduct_exercise_3_29_ray_succ]
                simp [smul_eq_mul]
          _ ≤ mixingInequalityTypeTwoCoeff b s ⬝ᵥ x := by
                linarith
          _ ≤ mixingInequalityTypeTwoRhs b s := hxlin
      exact (mixingInequalityTypeTwoCoeff_iff b s hs
        (x + a • exercise_3_29_ray i0.succ)).1 hlin

/-- Helper for Theorem 4.34: every distinguished Exercise 3.29 ray preserves the auxiliary
stronger mixing-inequality region, so it lies in that region's recession cone. -/
private lemma exerciseRay_mem_recessionCone_mixingInequalitiesRegion
    (b : Fin n → ℚ) (s : Fin (n + 1)) :
    exercise_3_29_ray s ∈ recessionCone (mixingInequalitiesRegion b) := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  -- Dispatch the ray index by its `Fin.cases` decomposition.
  cases s using Fin.cases with
  | zero =>
      simpa using mixingInequalitiesRegion_translate_headRay b hx ha
  | succ i0 =>
      simpa using mixingInequalitiesRegion_translate_succRay b hx i0 ha

/-- Helper for Theorem 4.34: every recession direction of the underlying Exercise 3.29 relaxation
is already a recession direction of the mixing-inequality region, because that cone is generated by
the distinguished rays `r⁰, r¹, …, rⁿ`. -/
private lemma exercisePolyhedron_recessionCone_subset_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) ⊆
      recessionCone (mixingInequalitiesRegion b) := by
  intro r hr
  have hrProps :
      0 ≤ r 0 ∧ ∀ t : Fin n, 0 ≤ r 0 + r t.succ := by
    exact exercise_3_29_mem_recessionCone_iff.mp hr
  -- Reassemble the canonical Exercise 3.29 ray decomposition inside the region recession cone.
  change r ∈ recessionPointedCone ℝ (mixingInequalitiesRegion b)
  have hray_eq :
      r = r 0 • exercise_3_29_ray (0 : Fin (n + 1)) +
        ∑ t : Fin n, (r 0 + r t.succ) • exercise_3_29_ray t.succ :=
    exercise_3_29_recession_direction_eq_ray_combination
  rw [hray_eq]
  have hhead :
      r 0 • exercise_3_29_ray (0 : Fin (n + 1)) ∈
        recessionPointedCone ℝ (mixingInequalitiesRegion b) :=
    PointedCone.smul_mem _ hrProps.1
      (exerciseRay_mem_recessionCone_mixingInequalitiesRegion b 0)
  have htail :
      (∑ t : Fin n, (r 0 + r t.succ) • exercise_3_29_ray t.succ) ∈
        recessionPointedCone ℝ (mixingInequalitiesRegion b) := by
    exact Submodule.sum_mem _ fun t _ ↦
      PointedCone.smul_mem _ (hrProps.2 t)
        (exerciseRay_mem_recessionCone_mixingInequalitiesRegion b t.succ)
  exact add_mem hhead htail

/-- Helper for Theorem 4.34: for a mixing-set point with `x₀ < 1`, every shifted successor
coordinate dominates the `0/1` threshold dictated by whether the fractional part is already below
`x₀`. -/
private lemma mixingSet_shiftedCoordinate_lower_bound
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) (hx0_lt_one : x 0 < 1) (i : Fin n) :
    (if mixingFractionalPart b i ≤ x 0 then (0 : ℝ) else 1) ≤
      x i.succ - (⌊b i⌋ : ℝ) := by
  rw [mem_mixingSet_iff_forall] at hx
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  rcases htail i with ⟨m, hm⟩
  have hceil_le : ⌈(b i : ℝ) - x 0⌉ ≤ m := by
    apply Int.ceil_le.mpr
    have hcov : (b i : ℝ) - x 0 ≤ x i.succ := by
      linarith [hcover i]
    simpa [hm] using hcov
  have hbranch :
      (⌈(b i : ℝ) - x 0⌉ : ℝ) =
        if mixingFractionalPart b i ≤ x 0 then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) :=
    ceil_sub_eq_floor_or_ceil_by_fract hx0_nonneg hx0_lt_one i
  by_cases hle : mixingFractionalPart b i ≤ x 0
  · -- In the low-fraction branch the covering inequality already forces `xᵢ ≥ ⌊bᵢ⌋`.
    have hfloor_le : (⌊b i⌋ : ℝ) ≤ m := by
      calc
        (⌊b i⌋ : ℝ) = (⌈(b i : ℝ) - x 0⌉ : ℝ) := by
          rw [hbranch, if_pos hle]
        _ ≤ m := by
          exact_mod_cast hceil_le
    rw [if_pos hle]
    simpa [hm] using sub_nonneg.mpr hfloor_le
  · -- In the high-fraction branch the least admissible integer is the ceiling, namely
    -- `⌊bᵢ⌋ + 1`.
    have hceil_le' : (⌈b i⌉ : ℝ) ≤ m := by
      calc
        (⌈b i⌉ : ℝ) = (⌈(b i : ℝ) - x 0⌉ : ℝ) := by
          rw [hbranch, if_neg hle]
        _ ≤ m := by
          exact_mod_cast hceil_le
    have hfrac_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_lt hx0_nonneg (lt_of_not_ge hle)
    have hceil_eq_floor_add_one :
        (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
      have hone :
          mixingCeilingWitness b i.succ - (⌊b i⌋ : ℝ) = 1 :=
        mixingCeilingWitness_succ_sub_floor_eq_one_of_pos b hfrac_pos
      simpa [mixingCeilingWitness] using (by linarith [hone] :
        (mixingCeilingWitness b i.succ : ℝ) = (⌊b i⌋ : ℝ) + 1)
    rw [if_neg hle]
    have htarget : 1 ≤ m - (⌊b i⌋ : ℝ) := by
      linarith [hceil_le', hceil_eq_floor_add_one]
    simpa [hm] using htarget

/-- Helper for Theorem 4.34: if every shifted selected coordinate dominates its `0/1` threshold,
then the type-one mixing sum already dominates the deficit between the last fractional part and
the current head level. -/
private lemma mixingInequalityTypeOneSumAux_ge_last_sub_max
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ i ∈ s, prev ≤ mixingFractionalPart b i) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      (∀ i ∈ s,
        (if mixingFractionalPart b i ≤ t then (0 : ℝ) else 1) ≤
          x i.succ - (⌊b i⌋ : ℝ)) →
      mixingInequalityTypeOneSumAux b x prev s ≥
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - max prev t := by
  intro prev s
  induction s generalizing prev with
  | nil =>
      intro hmono hchain hlower
      -- The empty sum matches the empty right-hand side.
      simp [mixingInequalityTypeOneSumAux]
  | cons i is ih =>
      intro hmono hchain hlower
      cases is with
      | nil =>
          -- On a singleton sequence, the first shifted coordinate pays the whole deficit.
          by_cases hle : mixingFractionalPart b i ≤ t
          · have hprev_le_t : prev ≤ t := le_trans (hmono i (by simp)) hle
            have hshift_nonneg : 0 ≤ x i.succ - (⌊b i⌋ : ℝ) := by
              have hcoord := hlower i (by simp)
              rw [if_pos hle] at hcoord
              simpa using hcoord
            have hcoeff_nonneg : 0 ≤ mixingFractionalPart b i - prev :=
              sub_nonneg.mpr (hmono i (by simp))
            have hterm_nonneg :
                0 ≤
                  (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) :=
              mul_nonneg hcoeff_nonneg hshift_nonneg
            have hgoal :
                mixingFractionalPart b i ≤
                  (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) + t := by
              linarith
            simpa [mixingInequalityTypeOneSumAux, max_eq_right hprev_le_t] using hgoal
          · have hcoeff_nonneg : 0 ≤ mixingFractionalPart b i - prev :=
              sub_nonneg.mpr (hmono i (by simp))
            have hshift_ge_one : 1 ≤ x i.succ - (⌊b i⌋ : ℝ) := by
              have hcoord := hlower i (by simp)
              rw [if_neg hle] at hcoord
              simpa using hcoord
            have hterm_ge :
                mixingFractionalPart b i - prev ≤
                  (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) := by
              have hmul :
                  (mixingFractionalPart b i - prev) * 1 ≤
                    (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) :=
                mul_le_mul_of_nonneg_left hshift_ge_one hcoeff_nonneg
              simpa using hmul
            have hgap_le :
                mixingFractionalPart b i - max prev t ≤
                  mixingFractionalPart b i - prev := by
              linarith [le_max_left prev t]
            have hgoal :
                mixingFractionalPart b i ≤
                  (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) +
                    max prev t := by
              linarith
            simpa [mixingInequalityTypeOneSumAux] using hgoal
      | cons j js =>
          -- The head term only has to bridge the gap between the two `max` levels; the tail
          -- induction controls the last fractional part.
          have htail_mono :
              ∀ k ∈ j :: js, mixingFractionalPart b i ≤ mixingFractionalPart b k := by
            intro k hk
            exact mixingFractionalPart_le_of_mem_chain b hchain hk
          have htail_lower :
              ∀ k ∈ j :: js,
                (if mixingFractionalPart b k ≤ t then (0 : ℝ) else 1) ≤
                  x k.succ - (⌊b k⌋ : ℝ) := by
            intro k hk
            exact hlower k (by simp [hk])
          have htail :
              mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i) (j :: js) ≥
                match (j :: js).reverse with
                | [] => 0
                | last :: _ => mixingFractionalPart b last - max (mixingFractionalPart b i) t :=
            ih htail_mono (List.isChain_cons.mp hchain).2 htail_lower
          have hbridge :
              max (mixingFractionalPart b i) t - max prev t ≤
                (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) := by
            by_cases hle : mixingFractionalPart b i ≤ t
            · have hprev_le_t : prev ≤ t := le_trans (hmono i (by simp)) hle
              have hshift_nonneg : 0 ≤ x i.succ - (⌊b i⌋ : ℝ) := by
                have hcoord := hlower i (by simp)
                rw [if_pos hle] at hcoord
                simpa using hcoord
              have hcoeff_nonneg : 0 ≤ mixingFractionalPart b i - prev :=
                sub_nonneg.mpr (hmono i (by simp))
              have hterm_nonneg :
                  0 ≤
                    (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) :=
                mul_nonneg hcoeff_nonneg hshift_nonneg
              have hcalc :
                  max (mixingFractionalPart b i) t - max prev t =
                    (0 : ℝ) := by
                rw [max_eq_right hle, max_eq_right hprev_le_t]
                ring
              rw [hcalc]
              exact hterm_nonneg
            · have hcoeff_nonneg : 0 ≤ mixingFractionalPart b i - prev :=
                sub_nonneg.mpr (hmono i (by simp))
              have hshift_ge_one : 1 ≤ x i.succ - (⌊b i⌋ : ℝ) := by
                have hcoord := hlower i (by simp)
                rw [if_neg hle] at hcoord
                simpa using hcoord
              have hterm_ge :
                  mixingFractionalPart b i - prev ≤
                    (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) := by
                have hmul :
                    (mixingFractionalPart b i - prev) * 1 ≤
                      (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) :=
                  mul_le_mul_of_nonneg_left hshift_ge_one hcoeff_nonneg
                simpa using hmul
              have hgap_le :
                  mixingFractionalPart b i - max prev t ≤
                    mixingFractionalPart b i - prev := by
                linarith [le_max_left prev t]
              have hmax_eq : max (mixingFractionalPart b i) t = mixingFractionalPart b i :=
                max_eq_left (le_of_lt (lt_of_not_ge hle))
              rw [hmax_eq]
              exact le_trans hgap_le hterm_ge
          rw [mixingInequalityTypeOneSumAux]
          cases hrev : (j :: js).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              simp [List.reverse_cons, hrev] at htail ⊢
              have hbridge' :
                  max (mixingFractionalPart b i) t ≤
                    (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) +
                      max prev t := by
                linarith
              have hsum :
                  mixingFractionalPart b last ≤
                    mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i) (j :: js) +
                      (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) +
                        max prev t := by
                calc
                  mixingFractionalPart b last ≤
                      mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i) (j :: js) +
                        max (mixingFractionalPart b i) t := htail
                  _ ≤ mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i) (j :: js) +
                        ((mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) +
                          max prev t) := by
                          simpa [add_assoc, add_left_comm, add_comm] using
                            add_le_add_left hbridge'
                              (mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i)
                                (j :: js))
                  _ = mixingInequalityTypeOneSumAux b x (mixingFractionalPart b i) (j :: js) +
                        (mixingFractionalPart b i - prev) * (x i.succ - (⌊b i⌋ : ℝ)) +
                          max prev t := by
                          ring
              simpa [mixingInequalityTypeOneSumAux, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Theorem 4.34: every generator of `P^mix` satisfies the source-facing mixing
inequalities, so the entire mixed-integer set lies in the claimed region. -/
private lemma mixingSet_subset_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    mixingSet b ⊆ mixingInequalitiesRegion b := by
  intro x hx
  rw [mem_mixingSet_iff_forall] at hx
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  let m : ℤ := ⌊x 0⌋
  let y : Fin (n + 1) → ℝ := x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))
  have hm_nonneg_int : 0 ≤ m := Int.floor_nonneg.mpr hx0_nonneg
  have hm_nonneg : 0 ≤ (m : ℝ) := by
    exact_mod_cast hm_nonneg_int
  have hy_mem_mixingSet : y ∈ mixingSet b := by
    -- Normalize the head coordinate into `[0, 1)` by subtracting `⌊x₀⌋ r⁰`; the mixed covering
    -- inequalities stay unchanged and the integral tail shifts by a common integer amount.
    rw [mem_mixingSet_iff_forall]
    refine ⟨?_, ?_, ?_⟩
    · rcases exercise_3_29_ray_zero_head_coordinate_effect x (m : ℝ) with ⟨-, hhead⟩
      rw [show y 0 = x 0 - (m : ℝ) by simpa [y] using hhead]
      exact sub_nonneg.mpr (Int.floor_le (x 0))
    · intro i
      rcases htail i with ⟨z, hz⟩
      refine ⟨z + m, ?_⟩
      have hcoord :
          y i.succ = x i.succ + (m : ℝ) := by
        have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
          simp
        calc
          y i.succ = x i.succ - ((m : ℝ) * (-1 : ℝ)) := by
            simp [y, Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
          _ = x i.succ + (m : ℝ) := by
            ring
      rw [hcoord, ← hz]
      norm_num
    · intro i
      rcases exercise_3_29_ray_zero_mixed_coordinate_effect x (m : ℝ) i with ⟨-, hmixed⟩
      rw [show y 0 + y i.succ = x 0 + x i.succ by simpa [y] using hmixed]
      exact hcover i
  have hy_mem_mixingSet_forall :
      0 ≤ y 0 ∧
        (∀ t : Fin n, y t.succ ∈ Set.range (fun z : ℤ ↦ (z : ℝ))) ∧
        ∀ t : Fin n, (b t : ℝ) ≤ y 0 + y t.succ :=
    (mem_mixingSet_iff_forall).mp hy_mem_mixingSet
  have hy0_nonneg : 0 ≤ y 0 := hy_mem_mixingSet_forall.1
  have hy0_lt_one : y 0 < 1 := by
    rcases exercise_3_29_ray_zero_head_coordinate_effect x (m : ℝ) with ⟨-, hhead⟩
    rw [show y 0 = x 0 - (m : ℝ) by simpa [y] using hhead]
    have hfract_eq : x 0 - (m : ℝ) = Int.fract (x 0) := by
      have hfloor : ((⌊x 0⌋ : ℤ) : ℝ) + Int.fract (x 0) = x 0 := Int.floor_add_fract (x 0)
      simpa [m] using sub_eq_iff_eq_add'.2 hfloor
    rw [hfract_eq]
    exact Int.fract_lt_one (x 0)
  have hy_region : y ∈ mixingInequalitiesRegion b := by
    refine ⟨hy0_nonneg, ?_, ?_⟩
    · intro i hi_zero
      exact hy_mem_mixingSet_forall.2.2 i
    · intro s hs
      cases s with
      | nil =>
          cases hs
      | cons first tail =>
          rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
          have hlower :
              ∀ i ∈ first :: tail,
                (if mixingFractionalPart b i ≤ y 0 then (0 : ℝ) else 1) ≤
                  y i.succ - (⌊b i⌋ : ℝ) := by
            intro i hi
            exact mixingSet_shiftedCoordinate_lower_bound b hy_mem_mixingSet hy0_lt_one i
          have hmono :
              ∀ i ∈ first :: tail, (0 : ℝ) ≤ mixingFractionalPart b i := by
            intro i hi
            exact mixingFractionalPart_nonneg b i
          have hsum_ge :
              mixingInequalityTypeOneSumAux b y 0 (first :: tail) ≥
                match (first :: tail).reverse with
                | [] => 0
                | last :: _ => mixingFractionalPart b last - max (0 : ℝ) (y 0) :=
            mixingInequalityTypeOneSumAux_ge_last_sub_max b y (y 0)
              hmono hfracChain hlower
          cases hrev : (first :: tail).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              have hmax_eq : max (0 : ℝ) (y 0) = y 0 := max_eq_right hy0_nonneg
              have htypeOne_core :
                  mixingFractionalPart b last ≤
                    y 0 + mixingInequalityTypeOneSum b (first :: tail) y := by
                have hsum_ge' :
                    mixingFractionalPart b last - y 0 ≤
                      mixingInequalityTypeOneSum b (first :: tail) y := by
                  simpa [mixingInequalityTypeOneSum, hrev, hmax_eq] using hsum_ge
                linarith
              have hfirst_shift_nonneg :
                  0 ≤ y first.succ - (⌊b first⌋ : ℝ) := by
                by_cases hfirst_le : mixingFractionalPart b first ≤ y 0
                · have hbound := hlower first (by simp)
                  rw [if_pos hfirst_le] at hbound
                  simpa using hbound
                · have hbound := hlower first (by simp)
                  rw [if_neg hfirst_le] at hbound
                  linarith
              have hlast_lt_one : mixingFractionalPart b last < 1 := by
                simpa [mixingFractionalPart_eq_fract] using Int.fract_lt_one ((b last : ℚ) : ℝ)
              constructor
              · simpa [mixingInequalityTypeOne, hrev] using htypeOne_core
              · have hextra_nonneg :
                    0 ≤
                      (1 - mixingFractionalPart b last) *
                        (y first.succ - (⌊b first⌋ : ℝ)) := by
                  exact mul_nonneg (by linarith) hfirst_shift_nonneg
                have htypeTwo_core :
                    mixingFractionalPart b last ≤
                      y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                        (1 - mixingFractionalPart b last) *
                          (y first.succ - (⌊b first⌋ : ℝ)) := by
                  linarith
                simpa [mixingInequalityTypeTwo, hrev] using htypeTwo_core
  -- Translate the normalized slice back to the original point by `⌊x₀⌋ r⁰`.
  have hx_eq : x = y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) := by
    ext i
    simp [y]
  rw [hx_eq]
  exact mixingInequalitiesRegion_translate_headRay b hy_region hm_nonneg

/-- Helper for Theorem 4.34: the canonical mixed-integer point at head level `c` uses the least
integral successor coordinates allowed by the covering inequalities. -/
private def mixingSliceWitness
    (b : Fin n → ℚ) (c : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases c (fun i : Fin n ↦ (⌈(b i : ℝ) - c⌉ : ℝ))

/-- Helper for Theorem 4.34: every slice witness `mixingSliceWitness b c` with `0 ≤ c < 1` already
lies in `mixingSet b`. -/
private lemma mixingSliceWitness_mem_mixingSet
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingSet b := by
  -- The slice witness uses integer ceiling coordinates and therefore satisfies the defining
  -- covering inequalities coordinatewise.
  rw [mem_mixingSet_iff]
  refine ⟨hc_nonneg, ?_, ?_⟩
  · rw [mem_integerVectors_iff_forall]
    intro i
    refine ⟨⌈(b i : ℝ) - c⌉, ?_⟩
    simp [mixingSliceWitness]
  · intro i
    have hceil : (b i : ℝ) - c ≤ (⌈(b i : ℝ) - c⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil ((b i : ℝ) - c)
    have hcover : (b i : ℝ) ≤ c + (⌈(b i : ℝ) - c⌉ : ℝ) := by
      linarith
    simpa [mixingSliceWitness, add_comm] using hcover

/-- Helper for Theorem 4.34: every slice witness already gives a hull base point because it is one
of the mixed-integer generators. -/
private lemma mixingSliceWitness_mem_mixingHull
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingHull b := by
  -- Promote the explicit slice witness from the generating set to the convex hull.
  simpa [mixingHull] using
    (subset_convexHull ℝ (mixingSet b)
      (mixingSliceWitness_mem_mixingSet b hc_nonneg hc_lt_one))

/-- Helper for Theorem 4.34: the explicit normalized-slice base candidate is the convex
combination of two slice witnesses. -/
private def mixingSliceChord
    (b : Fin n → ℚ) (dLo dHi alpha beta : ℝ) : Fin (n + 1) → ℝ :=
  alpha • mixingSliceWitness b dLo + beta • mixingSliceWitness b dHi

/-- Helper for Theorem 4.34: a convex combination of two slice witnesses stays inside `mixingHull
b`. -/
private lemma mixingSliceChord_mem_mixingHull
    (b : Fin n → ℚ) {dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hweights : alpha + beta = 1) :
    mixingSliceChord b dLo dHi alpha beta ∈ mixingHull b := by
  -- Keep the main reverse-inclusion route at the hull level before doing any coordinate algebra.
  have hdLo_mem : mixingSliceWitness b dLo ∈ mixingHull b :=
    mixingSliceWitness_mem_mixingHull b hdLo_nonneg hdLo_lt_one
  have hdHi_mem : mixingSliceWitness b dHi ∈ mixingHull b :=
    mixingSliceWitness_mem_mixingHull b hdHi_nonneg hdHi_lt_one
  simpa [mixingSliceChord, mixingHull] using
    (convex_convexHull ℝ (mixingSet b) hdLo_mem hdHi_mem halpha hbeta hweights)

/-- Helper for Theorem 4.34: the zeroth coordinate of the slice chord is the corresponding affine
combination of the two endpoint head levels. -/
private lemma mixingSliceChord_apply_zero
    (b : Fin n → ℚ) (dLo dHi alpha beta : ℝ) :
    mixingSliceChord b dLo dHi alpha beta 0 = alpha * dLo + beta * dHi := by
  -- Evaluate both endpoint witnesses at coordinate `0`.
  simp [mixingSliceChord, mixingSliceWitness, Pi.smul_apply, Pi.add_apply]

/-- Helper for Theorem 4.34: a positive mixing fractional part forces `⌈bᵢ⌉ = ⌊bᵢ⌋ + 1`. -/
private lemma ceil_eq_floor_add_one_of_mixingFractionalPart_pos
    (b : Fin n → ℚ) {i : Fin n}
    (hi_pos : 0 < mixingFractionalPart b i) :
    (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
  -- Reuse the earlier ceiling-witness computation to expose the floor/ceiling gap.
  have hone :
      mixingCeilingWitness b i.succ - (⌊b i⌋ : ℝ) = 1 :=
    mixingCeilingWitness_succ_sub_floor_eq_one_of_pos b hi_pos
  have hgap : (⌈b i⌉ : ℝ) - (⌊b i⌋ : ℝ) = 1 := by
    simpa [mixingCeilingWitness] using hone
  linarith

/-- Helper for Theorem 4.34: each successor coordinate of the slice chord is the affine
combination of the endpoint floor/ceiling threshold values. -/
private lemma mixingSliceChord_apply_succ_by_fract
    (b : Fin n → ℚ) {dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (i : Fin n) :
    mixingSliceChord b dLo dHi alpha beta i.succ =
      alpha * (if mixingFractionalPart b i ≤ dLo then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ)) +
        beta * (if mixingFractionalPart b i ≤ dHi then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ)) := by
  -- Rewrite the endpoint ceilings through the breakpoint test from Proposition 4.33.
  simp [mixingSliceChord, mixingSliceWitness, Pi.smul_apply, Pi.add_apply,
    ceil_sub_eq_floor_or_ceil_by_fract hdLo_nonneg hdLo_lt_one i,
    ceil_sub_eq_floor_or_ceil_by_fract hdHi_nonneg hdHi_lt_one i]

/-- Helper for Theorem 4.34: if the fractional part is already below the left breakpoint, then the
slice chord uses the floor value at that successor coordinate. -/
private lemma mixingSliceChord_apply_succ_of_frac_le_left
    (b : Fin n → ℚ) {dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (hdLo_le_hi : dLo ≤ dHi) (hweights : alpha + beta = 1)
    (i : Fin n) (hfi_le_lo : mixingFractionalPart b i ≤ dLo) :
    mixingSliceChord b dLo dHi alpha beta i.succ = (⌊b i⌋ : ℝ) := by
  -- Both endpoint witnesses pick the floor branch, so the convex combination collapses.
  have hfi_le_hi : mixingFractionalPart b i ≤ dHi := le_trans hfi_le_lo hdLo_le_hi
  rw [mixingSliceChord_apply_succ_by_fract b hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one i]
  rw [if_pos hfi_le_lo, if_pos hfi_le_hi]
  calc
    alpha * (⌊b i⌋ : ℝ) + beta * (⌊b i⌋ : ℝ) = (alpha + beta) * (⌊b i⌋ : ℝ) := by
      ring
    _ = (⌊b i⌋ : ℝ) := by
      rw [hweights, one_mul]

/-- Helper for Theorem 4.34: if the fractional part lies strictly between the two breakpoints, the
slice chord gives the affine middle value `⌊bᵢ⌋ + λ`. -/
private lemma mixingSliceChord_apply_succ_of_left_lt_frac_le_right
    (b : Fin n → ℚ) {dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (hweights : alpha + beta = 1)
    (i : Fin n)
    (hdLo_lt_fi : dLo < mixingFractionalPart b i)
    (hfi_le_hi : mixingFractionalPart b i ≤ dHi) :
    mixingSliceChord b dLo dHi alpha beta i.succ = (⌊b i⌋ : ℝ) + alpha := by
  -- The left endpoint sees the ceiling and the right endpoint sees the floor.
  have hfi_pos : 0 < mixingFractionalPart b i := lt_of_le_of_lt hdLo_nonneg hdLo_lt_fi
  have hceil_eq :
      (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 :=
    ceil_eq_floor_add_one_of_mixingFractionalPart_pos b hfi_pos
  rw [mixingSliceChord_apply_succ_by_fract b hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one i]
  rw [if_neg (not_le.mpr hdLo_lt_fi), if_pos hfi_le_hi, hceil_eq]
  calc
    alpha * ((⌊b i⌋ : ℝ) + 1) + beta * (⌊b i⌋ : ℝ)
      = (alpha + beta) * (⌊b i⌋ : ℝ) + alpha := by
          ring
    _ = (⌊b i⌋ : ℝ) + alpha := by
          rw [hweights]
          ring

/-- Helper for Theorem 4.34: if the fractional part is above the right breakpoint, then the slice
chord uses the ceiling value at that successor coordinate. -/
private lemma mixingSliceChord_apply_succ_of_right_lt_frac
    (b : Fin n → ℚ) {dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (hdLo_le_hi : dLo ≤ dHi) (hweights : alpha + beta = 1)
    (i : Fin n) (hdHi_lt_fi : dHi < mixingFractionalPart b i) :
    mixingSliceChord b dLo dHi alpha beta i.succ = (⌈b i⌉ : ℝ) := by
  -- Both endpoint witnesses now take the ceiling branch, so only the total weight matters.
  have hnot_le_hi : ¬ mixingFractionalPart b i ≤ dHi := not_le.mpr hdHi_lt_fi
  have hnot_le_lo : ¬ mixingFractionalPart b i ≤ dLo := by
    intro hfi_le_lo
    exact hnot_le_hi (le_trans hfi_le_lo hdLo_le_hi)
  rw [mixingSliceChord_apply_succ_by_fract b hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one i]
  rw [if_neg hnot_le_lo, if_neg hnot_le_hi]
  calc
    alpha * (⌈b i⌉ : ℝ) + beta * (⌈b i⌉ : ℝ) = (alpha + beta) * (⌈b i⌉ : ℝ) := by
      ring
    _ = (⌈b i⌉ : ℝ) := by
      rw [hweights, one_mul]

/-- Helper for Theorem 4.34: adding the head ray `r⁰` to a mixed-set point preserves the
mixed-integer constraints. -/
private lemma mixingSet_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingSet b := by
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The head coordinate increases by one.
    have hhead : (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
      simp [exercise_3_29_ray_apply]
    rw [hhead]
    linarith
  · -- Every tail coordinate decreases by one and stays integral.
    rw [mem_integerVectors_iff_forall] at htail ⊢
    intro t
    rcases htail t with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    simp [exercise_3_29_ray_apply, hm, sub_eq_add_neg]
  · -- The mixed covering sums are unchanged by the head ray.
    intro t
    have ht := hcover t
    have hmixed :
        (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 +
            (x + exercise_3_29_ray (0 : Fin (n + 1))) t.succ =
          x 0 + x t.succ := by
      simp [exercise_3_29_ray_apply, sub_eq_add_neg]
      ring
    rw [hmixed]
    exact ht

/-- Helper for Theorem 4.34: if a convex-hull point can be translated by one copy of a ray while
staying in the hull, then that unit translation extends from generators to the whole hull. -/
private lemma mixingHull_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
  -- Push the generator-level head translation through the convex hull via the convex target
  -- set `{y | y + r⁰ ∈ mixingHull b}`.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray (0 : Fin (n + 1))
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    exact subset_convexHull ℝ (mixingSet b) (mixingSet_add_headRay_mem b hy)
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
          = a * y j + c * z j + (a + c) * r j := by
              ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for Theorem 4.34: the same unit-translation argument works for every successor ray
`rⁱ`, because Proposition 4.33 already supplies generator-level preservation. -/
private lemma mixingHull_add_successorRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ} (i : Fin n)
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray i.succ ∈ mixingHull b := by
  -- The successor-ray translation uses the same convex-hull transport, now with the generator
  -- preservation imported from Proposition 4.33.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray i.succ
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    exact subset_convexHull ℝ (mixingSet b) (mixingSet_add_successor_ray_mem hy i)
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
          = a * y j + c * z j + (a + c) * r j := by
              ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for Theorem 4.34: every distinguished Exercise 3.29 ray already lies in the recession
cone of `mixingHull b`, because unit translations preserve the hull and convexity fills in the
fractional part of the step size. -/
private lemma exerciseRay_mem_recessionCone_mixingHull
    (b : Fin n → ℚ) (s : Fin (n + 1)) :
    exercise_3_29_ray s ∈ recessionCone (mixingHull b) := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray s
  have hstep : ∀ {y : Fin (n + 1) → ℝ}, y ∈ mixingHull b → y + r ∈ mixingHull b := by
    intro y hy
    cases s using Fin.cases with
    | zero =>
        simpa [r] using mixingHull_add_headRay_mem b hy
    | succ i =>
        simpa [r] using mixingHull_add_successorRay_mem b i hy
  have hnatTranslate : ∀ k : ℕ, x + (k : ℝ) • r ∈ mixingHull b := by
    intro k
    induction k with
    | zero =>
        simpa [r] using hx
    | succ k ih =>
        have hnext : (x + (k : ℝ) • r) + r ∈ mixingHull b := hstep ih
        have hrewrite :
            (x + (k : ℝ) • r) + r = x + ((Nat.succ k : ℕ) : ℝ) • r := by
          ext i
          simp [Pi.add_apply, Pi.smul_apply, Nat.cast_succ]
          ring
        rw [hrewrite] at hnext
        exact hnext
  let m : ℤ := ⌊a⌋
  have hm_nonneg_int : 0 ≤ m := Int.floor_nonneg.mpr ha
  have hm_cast :
      ((Int.toNat m : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm_nonneg_int
  have hfloorTranslate : x + (m : ℝ) • r ∈ mixingHull b := by
    have hnat : x + ((Int.toNat m : ℕ) : ℝ) • r ∈ mixingHull b := hnatTranslate (Int.toNat m)
    rw [hm_cast] at hnat
    exact hnat
  have hnextTranslate : x + ((m : ℝ) + 1) • r ∈ mixingHull b := by
    have hnext : (x + (m : ℝ) • r) + r ∈ mixingHull b := hstep hfloorTranslate
    have hrewrite :
        (x + (m : ℝ) • r) + r = x + ((m : ℝ) + 1) • r := by
      ext i
      simp [Pi.add_apply, Pi.smul_apply]
      ring
    rw [hrewrite] at hnext
    exact hnext
  have hfract_nonneg : 0 ≤ Int.fract a := Int.fract_nonneg a
  have hone_sub_nonneg : 0 ≤ 1 - Int.fract a := by
    linarith [Int.fract_lt_one a]
  have hconv :
      x + ((m : ℝ) + Int.fract a) • r ∈ mixingHull b := by
    have hcomb :
        (1 - Int.fract a) • (x + (m : ℝ) • r) +
            Int.fract a • (x + ((m : ℝ) + 1) • r) =
          x + ((m : ℝ) + Int.fract a) • r := by
      ext i
      simp [Pi.add_apply, Pi.smul_apply]
      ring
    rw [← hcomb]
    simpa [mixingHull] using
      (convex_convexHull ℝ (mixingSet b))
        hfloorTranslate hnextTranslate hone_sub_nonneg hfract_nonneg
        (by ring)
  have hdecomp : (m : ℝ) + Int.fract a = a := by
    simpa [m] using (Int.floor_add_fract a)
  rw [← hdecomp]
  exact hconv

/-- Helper for Theorem 4.34: every recession direction of the underlying Exercise 3.29 relaxation
is already a recession direction of `mixingHull b`, because that cone is generated by the
distinguished rays `r⁰, r¹, …, rⁿ`. -/
private lemma exercisePolyhedron_recessionCone_subset_mixingHull
    (b : Fin n → ℚ) :
    recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) ⊆
      recessionCone (mixingHull b) := by
  intro r hr
  have hrProps :
      0 ≤ r 0 ∧ ∀ t : Fin n, 0 ≤ r 0 + r t.succ := by
    exact exercise_3_29_mem_recessionCone_iff.mp hr
  -- Reassemble the canonical Exercise 3.29 ray decomposition inside the hull recession cone.
  change r ∈ recessionPointedCone ℝ (mixingHull b)
  have hray_eq :
      r = r 0 • exercise_3_29_ray (0 : Fin (n + 1)) +
        ∑ t : Fin n, (r 0 + r t.succ) • exercise_3_29_ray t.succ :=
    exercise_3_29_recession_direction_eq_ray_combination
  rw [hray_eq]
  have hhead :
      r 0 • exercise_3_29_ray (0 : Fin (n + 1)) ∈
        recessionPointedCone ℝ (mixingHull b) :=
    PointedCone.smul_mem _ hrProps.1
      (exerciseRay_mem_recessionCone_mixingHull b 0)
  have htail :
      (∑ t : Fin n, (r 0 + r t.succ) • exercise_3_29_ray t.succ) ∈
        recessionPointedCone ℝ (mixingHull b) := by
    exact Submodule.sum_mem _ fun t _ ↦
      PointedCone.smul_mem _ (hrProps.2 t)
        (exerciseRay_mem_recessionCone_mixingHull b t.succ)
  exact add_mem hhead htail

/-- Helper for Theorem 4.34: once a base point already lies in `mixingHull b`, any Exercise 3.29
recession direction can be added without leaving the hull. -/
private lemma mixingHull_add_exercise_recession_mem
    (b : Fin n → ℚ) {x r : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b)
    (hr : r ∈ recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)))) {a : ℝ}
    (ha : 0 ≤ a) :
    x + a • r ∈ mixingHull b := by
  -- Transport the Exercise 3.29 recession direction to the hull and apply it at the chosen base
  -- point.
  have hrHull : r ∈ recessionCone (mixingHull b) :=
    exercisePolyhedron_recessionCone_subset_mixingHull b hr
  exact (mem_recessionCone_iff.mp hrHull) hx a ha

/-- Helper for Theorem 4.34: translating a slice witness at breakpoint level `d` up to head level
`c` along `r⁰` stays inside `mixingHull b` and exposes the expected shifted step profile on the
successor coordinates. -/
private lemma translatedSliceBase_spec
    (b : Fin n → ℚ) {c d : ℝ}
    (hd_nonneg : 0 ≤ d) (hd_lt_one : d < 1) (hd_le_c : d ≤ c) :
    let z : Fin (n + 1) → ℝ := mixingSliceWitness b d + (c - d) • exercise_3_29_ray 0
    z ∈ mixingHull b ∧ z 0 = c ∧
      ∀ i : Fin n,
        z i.succ - (⌊b i⌋ : ℝ) =
          if mixingFractionalPart b i ≤ d then d - c else 1 + d - c := by
  let a : ℝ := c - d
  let z : Fin (n + 1) → ℝ := mixingSliceWitness b d + a • exercise_3_29_ray 0
  have ha_nonneg : 0 ≤ a := by
    -- The head translation amount is exactly the nonnegative gap from `d` up to `c`.
    simpa [a] using sub_nonneg.mpr hd_le_c
  have hz_mem : z ∈ mixingHull b := by
    -- Start from the slice witness at level `d` and translate it forward along the head ray.
    have hslice_mem : mixingSliceWitness b d ∈ mixingHull b :=
      mixingSliceWitness_mem_mixingHull b hd_nonneg hd_lt_one
    have hray_mem :
        exercise_3_29_ray (0 : Fin (n + 1)) ∈
          recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) :=
      exercise_3_29_ray_mem_recessionCone (fun i ↦ (b i : ℝ)) 0
    simpa [z, a] using
      mixingHull_add_exercise_recession_mem b hslice_mem hray_mem ha_nonneg
  refine ⟨hz_mem, ?_, ?_⟩
  · -- The zeroth coordinate increases from `d` to `c`.
    calc
      z 0 = mixingSliceWitness b d 0 + a * exercise_3_29_ray (0 : Fin (n + 1)) 0 := by
        simp [z, Pi.add_apply, Pi.smul_apply]
      _ = d + a := by
        simp [mixingSliceWitness, exercise_3_29_ray_apply]
      _ = c := by
        simp [a]
  · intro i
    -- Rewrite the slice witness through the floor/ceiling breakpoint test, then subtract the head
    -- translation `a`.
    have hwitness :
        mixingSliceWitness b d i.succ =
          if mixingFractionalPart b i ≤ d then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) := by
      simp [mixingSliceWitness, ceil_sub_eq_floor_or_ceil_by_fract hd_nonneg hd_lt_one i]
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    by_cases hfi : mixingFractionalPart b i ≤ d
    · -- On the floor branch, the shifted coordinate is exactly `-a = d - c`.
      calc
        z i.succ - (⌊b i⌋ : ℝ)
            = (mixingSliceWitness b d i.succ + a * exercise_3_29_ray (0 : Fin (n + 1)) i.succ) -
                (⌊b i⌋ : ℝ) := by
                  simp [z, Pi.add_apply, Pi.smul_apply]
        _ = ((⌊b i⌋ : ℝ) + a * (-1 : ℝ)) - (⌊b i⌋ : ℝ) := by
              rw [hwitness, if_pos hfi]
              simp [exercise_3_29_ray, hsucc_ne_zero]
        _ = d - c := by
              ring
        _ = if mixingFractionalPart b i ≤ d then d - c else 1 + d - c := by
              rw [if_pos hfi]
    · -- On the ceiling branch, the shifted coordinate is `1 - a = 1 + d - c`.
      have hfi_pos : 0 < mixingFractionalPart b i := by
        exact lt_of_le_of_lt hd_nonneg (lt_of_not_ge hfi)
      have hceil_eq :
          (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 :=
        ceil_eq_floor_add_one_of_mixingFractionalPart_pos b hfi_pos
      calc
        z i.succ - (⌊b i⌋ : ℝ)
            = (mixingSliceWitness b d i.succ + a * exercise_3_29_ray (0 : Fin (n + 1)) i.succ) -
                (⌊b i⌋ : ℝ) := by
                  simp [z, Pi.add_apply, Pi.smul_apply]
        _ = ((⌈b i⌉ : ℝ) + a * (-1 : ℝ)) - (⌊b i⌋ : ℝ) := by
              rw [hwitness, if_neg hfi]
              simp [exercise_3_29_ray, hsucc_ne_zero]
        _ = 1 + d - c := by
              rw [hceil_eq]
              ring
        _ = if mixingFractionalPart b i ≤ d then d - c else 1 + d - c := by
              rw [if_neg hfi]

/-- Helper for Theorem 4.34: among the extended fractional values bounded by `c`, one can choose
an index attaining the largest such value; if some value is strictly above `c`, one can also
choose an index attaining the smallest such upper value. -/
private lemma selectPlateauAwareSliceWindow
    (b : Fin n → ℚ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ tLo : Fin (n + 1),
      extendedMixingFractionalPart b tLo ≤ c ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s ≤ c →
          extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tLo) ∧
      ((∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c) ∨
        ∃ tHi : Fin (n + 1),
          c < extendedMixingFractionalPart b tHi ∧
            ∀ s : Fin (n + 1),
              c < extendedMixingFractionalPart b s →
                extendedMixingFractionalPart b tHi ≤ extendedMixingFractionalPart b s) := by
  let lowerSet : Set (Fin (n + 1)) := {t | extendedMixingFractionalPart b t ≤ c}
  have hLower_nonempty : lowerSet.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [lowerSet] using hc_nonneg
  obtain ⟨tLo, htLo, hmax⟩ :=
    Set.exists_max_image lowerSet (extendedMixingFractionalPart b) lowerSet.toFinite
      hLower_nonempty
  refine ⟨tLo, htLo, ?_, ?_⟩
  · intro s hs
    exact hmax s hs
  · by_cases hplateau : ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c
    · exact Or.inl hplateau
    · have hUpper_nonempty : {t : Fin (n + 1) | c < extendedMixingFractionalPart b t}.Nonempty := by
        by_contra hEmpty
        apply hplateau
        intro s
        by_contra hs
        exact hEmpty ⟨s, lt_of_not_ge hs⟩
      obtain ⟨tHi, htHi, hmin⟩ :=
        Set.exists_min_image {t : Fin (n + 1) | c < extendedMixingFractionalPart b t}
          (extendedMixingFractionalPart b)
          {t : Fin (n + 1) | c < extendedMixingFractionalPart b t}.toFinite
          hUpper_nonempty
      exact Or.inr ⟨tHi, htHi, fun s hs ↦ hmin s hs⟩

/-- Helper for Theorem 4.34: a strict plateau-aware selector leaves no extended fractional value
strictly between its lower and upper endpoints. -/
private lemma no_extendedMixingFractionalPart_between_selector_window
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)}
    (hlo : extendedMixingFractionalPart b tLo ≤ c)
    (hmax : ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s ≤ c →
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tLo)
    (hhi : c < extendedMixingFractionalPart b tHi)
    (hmin : ∀ s : Fin (n + 1),
      c < extendedMixingFractionalPart b s →
        extendedMixingFractionalPart b tHi ≤ extendedMixingFractionalPart b s) :
    ¬ ∃ s : Fin (n + 1),
      extendedMixingFractionalPart b tLo < extendedMixingFractionalPart b s ∧
        extendedMixingFractionalPart b s < extendedMixingFractionalPart b tHi := by
  intro hbetween
  rcases hbetween with ⟨s, hs_lo, hs_hi⟩
  -- Route correction: split at `c` instead of trying to compare raw selector witnesses directly.
  by_cases hs_le_c : extendedMixingFractionalPart b s ≤ c
  · exact (not_lt_of_ge (hmax s hs_le_c)) hs_lo
  · have hc_lt_s : c < extendedMixingFractionalPart b s := lt_of_not_ge hs_le_c
    exact (not_lt_of_ge (hmin s hc_lt_s)) hs_hi

/-- Helper for Theorem 4.34: in a strict selector window, any successor fractional part above the
lower endpoint and at most the upper endpoint must equal the upper endpoint. -/
private lemma mixingFractionalPart_eq_selector_upper_of_between
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)} {i : Fin n}
    (hlo : extendedMixingFractionalPart b tLo ≤ c)
    (hmax : ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s ≤ c →
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tLo)
    (hhi : c < extendedMixingFractionalPart b tHi)
    (hmin : ∀ s : Fin (n + 1),
      c < extendedMixingFractionalPart b s →
        extendedMixingFractionalPart b tHi ≤ extendedMixingFractionalPart b s)
    (hlo_lt_fi : extendedMixingFractionalPart b tLo < mixingFractionalPart b i)
    (hfi_le_hi : mixingFractionalPart b i ≤ extendedMixingFractionalPart b tHi) :
    mixingFractionalPart b i = extendedMixingFractionalPart b tHi := by
  -- The no-gap selector window collapses the old middle branch to the upper endpoint.
  have hno_gap :
      ¬ ∃ s : Fin (n + 1),
        extendedMixingFractionalPart b tLo < extendedMixingFractionalPart b s ∧
          extendedMixingFractionalPart b s < extendedMixingFractionalPart b tHi :=
    no_extendedMixingFractionalPart_between_selector_window b hlo hmax hhi hmin
  rcases lt_or_eq_of_le hfi_le_hi with hfi_lt_hi | hfi_eq_hi
  · exfalso
    exact hno_gap ⟨i.succ, hlo_lt_fi, by simpa using hfi_lt_hi⟩
  · simpa using hfi_eq_hi

/-- Helper for Theorem 4.34: in the top-plateau branch, translating the top slice witness along
`exercise_3_29_ray 0` produces a hull base point with head coordinate `c` and floor-shifted tail
coordinates. -/
private lemma topPlateauSliceBase_spec
    (b : Fin n → ℚ) {c : ℝ} {tLo : Fin (n + 1)}
    (hlo : extendedMixingFractionalPart b tLo ≤ c)
    (hmax : ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s ≤ c →
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tLo)
    (hplateau : ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c) :
    let dTop := extendedMixingFractionalPart b tLo
    let a := c - dTop
    let z := mixingSliceWitness b dTop + a • exercise_3_29_ray (0 : Fin (n + 1))
    z ∈ mixingHull b ∧ z 0 = c ∧
      ∀ i : Fin n, z i.succ = (⌊b i⌋ : ℝ) - a := by
  let dTop : ℝ := extendedMixingFractionalPart b tLo
  let a : ℝ := c - dTop
  let z : Fin (n + 1) → ℝ := mixingSliceWitness b dTop + a • exercise_3_29_ray (0 : Fin (n + 1))
  have hdTop_nonneg : 0 ≤ dTop := by
    have hdTop_nonneg' : 0 ≤ extendedMixingFractionalPart b tLo :=
      extendedMixingFractionalPart_nonneg tLo
    simpa [dTop] using hdTop_nonneg'
  have hdTop_lt_one : dTop < 1 := by
    have hdTop_lt_one' : extendedMixingFractionalPart b tLo < 1 :=
      extendedMixingFractionalPart_lt_one tLo
    simpa [dTop] using hdTop_lt_one'
  have hz_spec := translatedSliceBase_spec b hdTop_nonneg hdTop_lt_one hlo
  refine ⟨hz_spec.1, hz_spec.2.1, ?_⟩
  intro i
  -- In the top-plateau branch every successor fractional value lies on the floor side of the
  -- translated slice profile.
  have hfi_le_dTop : mixingFractionalPart b i ≤ dTop := by
    have hi_le_c : extendedMixingFractionalPart b i.succ ≤ c := hplateau i.succ
    simpa [dTop] using hmax i.succ hi_le_c
  have hshift :
      z i.succ - (⌊b i⌋ : ℝ) =
        if mixingFractionalPart b i ≤ dTop then dTop - c else 1 + dTop - c := by
    simpa [z, dTop] using hz_spec.2.2 i
  rw [if_pos hfi_le_dTop] at hshift
  linarith [hshift]

/-- Helper for Theorem 4.34: once a strict-window scalar profile is available, the corresponding
slice chord is a hull base point with the required head coordinate and coordinatewise tail
domination. -/
private lemma strictWindowChord_sameHeadHullBasepoint_of_profile
    (b : Fin n → ℚ) {y : Fin (n + 1) → ℝ} {c dLo dHi alpha beta : ℝ}
    (hdLo_nonneg : 0 ≤ dLo) (hdLo_lt_one : dLo < 1)
    (hdHi_nonneg : 0 ≤ dHi) (hdHi_lt_one : dHi < 1)
    (hdLo_le_hi : dLo ≤ dHi) (hdLo_lt_hi : dLo < dHi)
    (halpha_nonneg : 0 ≤ alpha) (hbeta_nonneg : 0 ≤ beta)
    (hweights : alpha + beta = 1)
    (hhead : alpha * dLo + beta * dHi = c)
    (hprofile_left : ∀ i : Fin n,
      mixingFractionalPart b i ≤ dLo → 0 ≤ y i.succ - (⌊b i⌋ : ℝ))
    (hprofile_mid : ∀ i : Fin n,
      dLo < mixingFractionalPart b i →
        mixingFractionalPart b i ≤ dHi →
          alpha ≤ y i.succ - (⌊b i⌋ : ℝ))
    (hprofile_right : ∀ i : Fin n,
      dHi < mixingFractionalPart b i → 1 ≤ y i.succ - (⌊b i⌋ : ℝ)) :
    ∃ yBase : Fin (n + 1) → ℝ,
      yBase ∈ mixingHull b ∧
        yBase 0 = c ∧
        ∀ i : Fin n, yBase i.succ ≤ y i.succ := by
  refine ⟨mixingSliceChord b dLo dHi alpha beta, ?_, ?_, ?_⟩
  · -- The endpoint slice witnesses already lie in the hull, so their convex combination does too.
    exact
      mixingSliceChord_mem_mixingHull b
        hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one
        halpha_nonneg hbeta_nonneg hweights
  · -- The head coordinate is the affine interpolation value chosen to equal `c`.
    rw [mixingSliceChord_apply_zero, hhead]
  · intro i
    -- Split by the fractional-part location relative to the strict window.
    by_cases hleft : mixingFractionalPart b i ≤ dLo
    · rw [mixingSliceChord_apply_succ_of_frac_le_left b
        hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one hdLo_le_hi hweights i hleft]
      linarith [hprofile_left i hleft]
    · have hdLo_lt_fi : dLo < mixingFractionalPart b i := lt_of_not_ge hleft
      by_cases hmid : mixingFractionalPart b i ≤ dHi
      · rw [mixingSliceChord_apply_succ_of_left_lt_frac_le_right b
          hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one hweights i hdLo_lt_fi hmid]
        linarith [hprofile_mid i hdLo_lt_fi hmid]
      · have hdHi_lt_fi : dHi < mixingFractionalPart b i := lt_of_not_ge hmid
        rw [mixingSliceChord_apply_succ_of_right_lt_frac b
          hdLo_nonneg hdLo_lt_one hdHi_nonneg hdHi_lt_one hdLo_le_hi hweights i hdHi_lt_fi]
        have hfi_pos : 0 < mixingFractionalPart b i := by
          exact lt_of_le_of_lt hdLo_nonneg (lt_trans hdLo_lt_hi hdHi_lt_fi)
        have hceil_eq :
            (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
          exact
            ceil_eq_floor_add_one_of_mixingFractionalPart_pos b
              hfi_pos
        linarith [hprofile_right i hdHi_lt_fi, hceil_eq]

/-- Helper for Theorem 4.34: once the plateau offset bound is available, the translated top slice
witness is already a same-head hull base point dominated by `y`. -/
private lemma topPlateauSameHeadHullBasepoint_of_offset
    (b : Fin n → ℚ) {y : Fin (n + 1) → ℝ} {c : ℝ} {tLo : Fin (n + 1)}
    (hlo : extendedMixingFractionalPart b tLo ≤ c)
    (hmax : ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s ≤ c →
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tLo)
    (hplateau : ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c)
    (hoffset : ∀ i : Fin n,
      extendedMixingFractionalPart b tLo - c ≤ y i.succ - (⌊b i⌋ : ℝ)) :
    ∃ yBase : Fin (n + 1) → ℝ,
      yBase ∈ mixingHull b ∧
        yBase 0 = c ∧
        ∀ i : Fin n, yBase i.succ ≤ y i.succ := by
  let dTop : ℝ := extendedMixingFractionalPart b tLo
  let a : ℝ := c - dTop
  let z : Fin (n + 1) → ℝ := mixingSliceWitness b dTop + a • exercise_3_29_ray (0 : Fin (n + 1))
  have hz_spec := topPlateauSliceBase_spec b hlo hmax hplateau
  refine ⟨z, hz_spec.1, hz_spec.2.1, ?_⟩
  intro i
  -- Rewrite the explicit top-plateau tail coordinate and compare it with the assumed offset
  -- lower bound on `y`.
  have hz_tail : z i.succ = (⌊b i⌋ : ℝ) - a := hz_spec.2.2 i
  have hbound := hoffset i
  have ha_eq : dTop - c = -a := by
    simp [a, dTop]
  rw [hz_tail]
  linarith [hbound, ha_eq]

/-- Helper for Theorem 4.34: if two points have the same head coordinate and one dominates the
other coordinatewise on the tail, then their difference is an Exercise 3.29 recession direction. -/
private lemma sub_mem_exercisePolyhedron_recessionCone_of_same_head_tail_le
    (b : Fin n → ℚ) {y yBase : Fin (n + 1) → ℝ}
    (hhead : yBase 0 = y 0)
    (htail : ∀ i : Fin n, yBase i.succ ≤ y i.succ) :
    y - yBase ∈ recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) := by
  rw [exercise_3_29_mem_recessionCone_iff]
  constructor
  · -- Matching head coordinates force the recession vector to have zeroth entry `0`.
    simp [Pi.sub_apply, hhead]
  · intro i
    -- The tail domination hypothesis is exactly the mixed-coordinate nonnegativity condition.
    have hdiff_nonneg : 0 ≤ y i.succ - yBase i.succ := sub_nonneg.mpr (htail i)
    simpa [Pi.sub_apply, hhead] using hdiff_nonneg

/-- Helper for Theorem 4.34: once the normalized slice dominates a hull base point with the same
head coordinate, the original point lies in `mixingHull b` after reattaching the head-ray and the
remaining Exercise 3.29 recession slack. -/
private lemma mem_mixingHull_of_normalized_basepoint
    (b : Fin n → ℚ) {x y yBase : Fin (n + 1) → ℝ} {m : ℤ}
    (hx_eq : x = y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)))
    (hm_nonneg : 0 ≤ (m : ℝ))
    (hyBase_mem : yBase ∈ mixingHull b)
    (hhead : yBase 0 = y 0)
    (htail : ∀ i : Fin n, yBase i.succ ≤ y i.succ) :
    x ∈ mixingHull b := by
  let r : Fin (n + 1) → ℝ := y - yBase
  have hr_mem :
      r ∈ recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) :=
    sub_mem_exercisePolyhedron_recessionCone_of_same_head_tail_le b hhead htail
  have hbase_shift :
      yBase + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
    -- First restore the integral head-ray multiple to the hull base point.
    have hray_mem :
        exercise_3_29_ray (0 : Fin (n + 1)) ∈
          recessionCone (exercise_3_29_polyhedron (fun i ↦ (b i : ℝ))) :=
      exercise_3_29_ray_mem_recessionCone (fun i ↦ (b i : ℝ)) 0
    exact mixingHull_add_exercise_recession_mem b hyBase_mem hray_mem hm_nonneg
  have hsum :
      x = (yBase + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))) + r := by
    -- The remaining difference is exactly the normalized slack `y - yBase`.
    ext i
    simp [hx_eq, r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hsum]
  simpa [one_smul, r] using
    mixingHull_add_exercise_recession_mem b hbase_shift hr_mem zero_le_one

/-- Helper for Theorem 4.34: the normalized slice obtained by subtracting `⌊x₀⌋ r⁰` from a region
point still belongs to the ambient Exercise 3.29 relaxation. -/
private lemma normalizedSlice_mem_exercisePolyhedron_of_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) {x y : Fin (n + 1) → ℝ} {m : ℤ}
    (hx : x ∈ mixingInequalitiesRegion b)
    (hm : m = ⌊x 0⌋)
    (hy : y = x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))) :
    y ∈ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) := by
  have hxrel : x ∈ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) :=
    mixingInequalitiesRegion_subset_exercisePolyhedron b hx
  rw [mem_exercise_3_29_polyhedron_iff] at hxrel ⊢
  refine ⟨?_, ?_⟩
  · -- The normalized head coordinate is the fractional part `x₀ - ⌊x₀⌋`.
    rw [hy, hm]
    simpa [exercise_3_29_ray_apply] using sub_nonneg.mpr (Int.floor_le (x 0))
  · intro i
    -- The mixed covering sum is invariant under the head-ray normalization.
    have hmixed :
        y 0 + y i.succ = x 0 + x i.succ := by
      rw [hy]
      simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray_apply]
    rw [hmixed]
    exact hxrel.2 i

/-- Helper for Theorem 4.34: translating the singleton type-two inequality from `x` to the
normalized slice `y` yields the basic lower bound `fᵢ - c ≤ yᵢ - ⌊bᵢ⌋`. -/
private lemma translatedSingletonShift_ge_fractionalGap_of_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) {x y : Fin (n + 1) → ℝ} {m : ℤ} {c : ℝ} {i : Fin n}
    (hx : x ∈ mixingInequalitiesRegion b)
    (hy : y = x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)))
    (hy0 : y 0 = c)
    (hi_pos : 0 < mixingFractionalPart b i) :
    mixingFractionalPart b i - c ≤ y i.succ - (⌊b i⌋ : ℝ) := by
  have hs : IsMixingIndexSequence b [i] := by
    refine ⟨hi_pos, ?_, ?_⟩ <;> simp
  have htypeTwo : mixingInequalityTypeTwo b [i] x := (hx.2.2 [i] hs).2
  have hineq :
      mixingFractionalPart b i ≤ x 0 + (x i.succ - (⌊b i⌋ : ℝ)) := by
    -- On a singleton sequence, the type-two inequality collapses to the shifted one-coordinate
    -- covering bound.
    simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using htypeTwo
  have hx0 : x 0 = c + (m : ℝ) := by
    -- The head coordinate splits into the normalized head level `c` and the removed integer part.
    have hy0' : y 0 = x 0 - (m : ℝ) := by
      rw [hy]
      simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray_apply]
    rw [hy0] at hy0'
    linarith
  have hxi :
      x i.succ = y i.succ - (m : ℝ) := by
    -- Every successor coordinate loses exactly the same head-ray amount under normalization.
    rw [hy]
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
  rw [hx0, hxi] at hineq
  linarith

/-- Helper for Theorem 4.34: translating the two-term type-two inequality from `x` to the
normalized slice `y` preserves its exact affine form on the shifted successor coordinates. -/
private lemma translatedTypeTwoPairInequality_of_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) {x y : Fin (n + 1) → ℝ} {m : ℤ} {c : ℝ} {i j : Fin n}
    (hx : x ∈ mixingInequalitiesRegion b)
    (hy : y = x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)))
    (hy0 : y 0 = c)
    (hs : IsMixingIndexSequence b [i, j]) :
    mixingFractionalPart b j ≤
      c +
        (1 - mixingFractionalPart b j + mixingFractionalPart b i) *
          (y i.succ - (⌊b i⌋ : ℝ)) +
        (mixingFractionalPart b j - mixingFractionalPart b i) *
          (y j.succ - (⌊b j⌋ : ℝ)) := by
  have htypeTwo : mixingInequalityTypeTwo b [i, j] x := (hx.2.2 [i, j] hs).2
  have hineq :
      mixingFractionalPart b j ≤
        x 0 +
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) +
            (mixingFractionalPart b j - mixingFractionalPart b i) *
              (x j.succ - (⌊b j⌋ : ℝ)) +
            (1 - mixingFractionalPart b j) * (x i.succ - (⌊b i⌋ : ℝ)) := by
    -- Expand `(4.30)` on the two-term sequence `[i, j]` before translating to `y`.
    simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using htypeTwo
  have hx0 : x 0 = c + (m : ℝ) := by
    -- The zeroth coordinate splits into the normalized head level `c` and the removed integer
    -- head-ray amount.
    have hy0' : y 0 = x 0 - (m : ℝ) := by
      rw [hy]
      simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray_apply]
    rw [hy0] at hy0'
    linarith
  have hxi :
      x i.succ = y i.succ - (m : ℝ) := by
    -- Every successor coordinate decreases by the same integer amount under the normalization.
    rw [hy]
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
  have hxj :
      x j.succ = y j.succ - (m : ℝ) := by
    -- The same normalization formula applies to the second selected coordinate.
    rw [hy]
    have hsucc_ne_zero : ¬ (j.succ : Fin (n + 1)) = 0 := by
      simp
    simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero]
  rw [hx0, hxi, hxj] at hineq
  ring_nf at hineq ⊢
  exact hineq

/-- Helper for Theorem 4.34: once lower-envelope coefficients are available, the translated slice
bases can be assembled inside `mixingHull b` by convexity, and the resulting tail profile is the
corresponding weighted average of the translated step profiles. -/
private lemma translatedSliceEnvelope_spec
    {ι : Type*} [Fintype ι]
    (b : Fin n → ℚ) {c : ℝ} (d : ι → ℝ) (w : ι → ℝ)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hd_lt_one : ∀ t, d t < 1)
    (hd_le_c : ∀ t, d t ≤ c)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_sum : ∑ t, w t = 1) :
    let z : ι → Fin (n + 1) → ℝ :=
      fun t ↦ mixingSliceWitness b (d t) + (c - d t) • exercise_3_29_ray 0
    let yBase : Fin (n + 1) → ℝ := ∑ t, w t • z t
    yBase ∈ mixingHull b ∧
      yBase 0 = c ∧
      ∀ i : Fin n,
        yBase i.succ - (⌊b i⌋ : ℝ) =
          ∑ t, w t *
            (if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c) := by
  let z : ι → Fin (n + 1) → ℝ :=
    fun t ↦ mixingSliceWitness b (d t) + (c - d t) • exercise_3_29_ray 0
  let yBase : Fin (n + 1) → ℝ := ∑ t, w t • z t
  have hz_mem : ∀ t, z t ∈ mixingHull b := by
    intro t
    -- Each translated slice base already lies in the hull.
    simpa [z] using
      (translatedSliceBase_spec b (hd_nonneg t) (hd_lt_one t) (hd_le_c t)).1
  have hz_zero : ∀ t, z t 0 = c := by
    intro t
    -- The translation aligns every slice base to the common head level `c`.
    simpa [z] using
      (translatedSliceBase_spec b (hd_nonneg t) (hd_lt_one t) (hd_le_c t)).2.1
  have hz_shift :
      ∀ t (i : Fin n),
        z t i.succ - (⌊b i⌋ : ℝ) =
          if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c := by
    intro t i
    -- The translated slice API already gives the exact shifted successor-coordinate profile.
    simpa [z] using
      (translatedSliceBase_spec b (hd_nonneg t) (hd_lt_one t) (hd_le_c t)).2.2 i
  have hyBase_mem : yBase ∈ mixingHull b := by
    -- Assemble the translated slice bases by a finite convex combination.
    have hconv : Convex ℝ (mixingHull b) := by
      simpa [mixingHull] using convex_convexHull ℝ (mixingSet b)
    have hyBase_mem' : (∑ t ∈ Finset.univ, w t • z t) ∈ mixingHull b := by
      exact hconv.sum_mem
        (fun t _ ↦ hw_nonneg t)
        (by simpa using hw_sum)
        (fun t _ ↦ hz_mem t)
    simpa [yBase] using hyBase_mem'
  refine ⟨hyBase_mem, ?_, ?_⟩
  · -- Evaluate the convex combination at the head coordinate.
    calc
      yBase 0 = ∑ t, w t * c := by
        simp [yBase, hz_zero, Pi.smul_apply]
      _ = (∑ t, w t) * c := by
        rw [Finset.sum_mul]
      _ = c := by
        simp [hw_sum]
  · intro i
    -- Rewrite the shifted tail coordinate as the weighted sum of the translated slice profiles.
    have hweighted_sub :
        (∑ t, w t * z t i.succ) - (∑ t, w t) * (⌊b i⌋ : ℝ) =
          ∑ t, w t * (z t i.succ - (⌊b i⌋ : ℝ)) := by
      calc
        (∑ t, w t * z t i.succ) - (∑ t, w t) * (⌊b i⌋ : ℝ)
            = (∑ t, w t * z t i.succ) - ∑ t, w t * (⌊b i⌋ : ℝ) := by
                rw [Finset.sum_mul]
        _ = ∑ t, (w t * z t i.succ - w t * (⌊b i⌋ : ℝ)) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ t, w t * (z t i.succ - (⌊b i⌋ : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              ring
    calc
      yBase i.succ - (⌊b i⌋ : ℝ)
          = (∑ t, w t * z t i.succ) - (∑ t, w t) * (⌊b i⌋ : ℝ) := by
              simp [yBase, Pi.smul_apply, hw_sum]
      _ = ∑ t, w t * (z t i.succ - (⌊b i⌋ : ℝ)) := hweighted_sub
      _ = ∑ t, w t *
            (if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [hz_shift t i]

/-- Helper for Theorem 4.34: the translated-envelope successor profile splits into its common
moment term `∑ w_t d_t - c` plus the cumulative weight strictly below the tested fractional
value. -/
private lemma translatedEnvelopeShift_eq_moment_plus_massBelow
    {ι : Type*} [Fintype ι]
    (b : Fin n → ℚ) {c : ℝ} (d : ι → ℝ) (w : ι → ℝ)
    (hw_sum : ∑ t, w t = 1) (i : Fin n) :
    (∑ t, w t *
        (if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c)) =
      ((∑ t, w t * d t) - c) +
        ∑ t, if d t < mixingFractionalPart b i then w t else 0 := by
  -- Rewrite each translated step profile as `(d_t - c)` plus the indicator of `d_t < f_i`.
  have hterm :
      ∀ t,
        w t * (if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c) =
          (w t * d t - w t * c) +
            (if d t < mixingFractionalPart b i then w t else 0) := by
    intro t
    by_cases hle : mixingFractionalPart b i ≤ d t
    · -- On and above the tested breakpoint, only the common moment term survives.
      have hnot_lt : ¬ d t < mixingFractionalPart b i := not_lt.mpr hle
      rw [if_pos hle, if_neg hnot_lt]
      ring
    · -- Below the tested breakpoint, the translated step picks up one extra unit of mass.
      have hlt : d t < mixingFractionalPart b i := lt_of_not_ge hle
      rw [if_neg hle, if_pos hlt]
      ring
  calc
    (∑ t, w t *
        (if mixingFractionalPart b i ≤ d t then d t - c else 1 + d t - c)) =
        ∑ t, ((w t * d t - w t * c) +
          (if d t < mixingFractionalPart b i then w t else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [hterm t]
    _ = (∑ t, (w t * d t - w t * c)) +
          ∑ t, if d t < mixingFractionalPart b i then w t else 0 := by
            rw [Finset.sum_add_distrib]
    _ = ((∑ t, w t * d t) - (∑ t, w t) * c) +
          ∑ t, if d t < mixingFractionalPart b i then w t else 0 := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ((∑ t, w t * d t) - c) +
          ∑ t, if d t < mixingFractionalPart b i then w t else 0 := by
            rw [hw_sum]
            ring

/-- Helper for Theorem 4.34: every realized positive fractional value admits a representative
whose shifted successor coordinate is minimal inside that fractional class. -/
private lemma exists_minimizingFractionalRepresentative
    (b : Fin n → ℚ) (y : Fin (n + 1) → ℝ) {d : ℝ}
    (hd : d ∈ Set.range (mixingFractionalPart b)) :
    ∃ i : Fin n,
      mixingFractionalPart b i = d ∧
        ∀ j : Fin n, mixingFractionalPart b j = d →
          y i.succ - (⌊b i⌋ : ℝ) ≤ y j.succ - (⌊b j⌋ : ℝ) := by
  classical
  let fiber : Set (Fin n) := {i | mixingFractionalPart b i = d}
  have hfiber_nonempty : fiber.Nonempty := by
    rcases hd with ⟨i, rfl⟩
    exact ⟨i, by simp [fiber]⟩
  obtain ⟨i, hi_fiber, hi_min⟩ :=
    Set.exists_min_image fiber
      (fun j : Fin n ↦ y j.succ - (⌊b j⌋ : ℝ))
      fiber.toFinite hfiber_nonempty
  refine ⟨i, ?_, ?_⟩
  · -- Unpack the minimizing witness back into the original fractional-class equation.
    simpa [fiber] using hi_fiber
  · intro j hj
    -- The chosen representative minimizes the shifted successor coordinate on its whole fiber.
    exact hi_min j (by simpa [fiber] using hj)

/-- Helper for Theorem 4.34: a lower bound proved at the minimizing representative of a fractional
class automatically transfers to every point in the same class. -/
private lemma lower_bound_of_minimizingFractionalRepresentative
    (b : Fin n → ℚ) (y : Fin (n + 1) → ℝ) {ρ : ℝ} {rep i : Fin n}
    (hfrac : mixingFractionalPart b i = mixingFractionalPart b rep)
    (hmin : ∀ j : Fin n, mixingFractionalPart b j = mixingFractionalPart b rep →
      y rep.succ - (⌊b rep⌋ : ℝ) ≤ y j.succ - (⌊b j⌋ : ℝ))
    (hrep : ρ ≤ y rep.succ - (⌊b rep⌋ : ℝ)) :
    ρ ≤ y i.succ - (⌊b i⌋ : ℝ) := by
  -- Apply the minimizing property at the target index and then chain the inequalities.
  have hclass :
      y rep.succ - (⌊b rep⌋ : ℝ) ≤ y i.succ - (⌊b i⌋ : ℝ) :=
    hmin i hfrac
  linarith

/-- Helper for Theorem 4.34: once the remaining translated strict-window and plateau scalar
profiles are available, the normalized slice admits a same-head hull base point dominated on the
tail. -/
private lemma normalizedSliceSameHeadHullBasepoint
    (b : Fin n → ℚ) {x y : Fin (n + 1) → ℝ} {m : ℤ} {c : ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    (hm : m = ⌊x 0⌋)
    (hy : y = x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)))
    (hy0 : y 0 = c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1) :
    ∃ yBase : Fin (n + 1) → ℝ,
      yBase ∈ mixingHull b ∧
        yBase 0 = y 0 ∧
        ∀ i : Fin n, yBase i.succ ≤ y i.succ := by
  -- Route correction: isolate the remaining reverse-inclusion branch split here instead of
  -- keeping it inline in the theorem body.
  have hselector := selectPlateauAwareSliceWindow b hc_nonneg
  have hy_relax :
      y ∈ exercise_3_29_polyhedron (fun i ↦ (b i : ℝ)) :=
    normalizedSlice_mem_exercisePolyhedron_of_mem_mixingInequalitiesRegion b hx hm hy
  -- The translated singleton and pair lemmas above now provide the scalar inputs already proved:
  -- `translatedSingletonShift_ge_fractionalGap_of_mem_mixingInequalitiesRegion` gives the
  -- one-point lower bounds, and
  -- `translatedTypeTwoPairInequality_of_mem_mixingInequalitiesRegion` gives the exact translated
  -- two-term type-two inequality. The previous nonnegativity target for the left strict-window
  -- profile was too strong: a point can satisfy the region inequalities while still having
  -- `y i.succ - ⌊b i⌋ < 0` on the left side of the selector window.
  -- The convex-combination assembly is now packaged by `translatedSliceEnvelope_spec`, and
  -- `translatedEnvelopeShift_eq_moment_plus_massBelow` plus the minimizing-representative lemmas
  -- above already handle the final normalization and same-fraction transfer steps. The only
  -- remaining gap is to extract lower-envelope coefficients from `y` that make that explicit
  -- translated step profile stay below the shifted tail coordinates of `y`.
  rcases hselector with ⟨tLo, hlo, hmax, hbranch⟩
  cases hbranch with
  | inl hplateau =>
      let dTop : ℝ := extendedMixingFractionalPart b tLo
      have hdTop_nonneg : 0 ≤ dTop := by
        -- The plateau branch still starts from the maximal lower breakpoint.
        simpa [dTop] using extendedMixingFractionalPart_nonneg tLo
      have hdTop_lt_one : dTop < 1 := by
        -- Every extended fractional value stays strictly below `1`.
        simpa [dTop] using extendedMixingFractionalPart_lt_one tLo
      -- TODO: the remaining plateau step is to derive the uniform offset bound
      -- `dTop - c ≤ y i.succ - ⌊b i⌋` for every `i`, then close with
      -- `topPlateauSameHeadHullBasepoint_of_offset`. The current blocker is structural:
      -- the translated singleton lemma controls each class separately, but the available
      -- translated pair lemma only applies to order-compatible admissible pairs `[i, j]`.
      -- To make the plateau argument go through in the unsorted case, we need an
      -- order-aware extraction lemma that converts the region inequalities into a bound
      -- from the maximal breakpoint `dTop` to an arbitrary tail index without assuming a
      -- globally monotone fractional-part order.
      let _ := hy_relax
      let _ := hmax
      let _ := hplateau
      let _ := hdTop_nonneg
      let _ := hdTop_lt_one
      sorry
  | inr hstrict =>
      rcases hstrict with ⟨tHi, hhi, hmin⟩
      let dLo : ℝ := extendedMixingFractionalPart b tLo
      let dHi : ℝ := extendedMixingFractionalPart b tHi
      have hdLo_nonneg : 0 ≤ dLo := by
        -- The lower selector still comes from the extended fractional-value set.
        simpa [dLo] using extendedMixingFractionalPart_nonneg tLo
      have hdHi_nonneg : 0 ≤ dHi := by
        -- The upper selector is another extended fractional value.
        simpa [dHi] using extendedMixingFractionalPart_nonneg tHi
      have hdLo_lt_hi : dLo < dHi := by
        -- The strict branch separates the lower and upper selector values across `c`.
        have hdLo_le_c : dLo ≤ c := by
          simpa [dLo] using hlo
        have hc_lt_dHi : c < dHi := by
          simpa [dHi] using hhi
        exact lt_of_le_of_lt hdLo_le_c hc_lt_dHi
      have hdHi_lt_one : dHi < 1 := by
        -- The upper selector is still a genuine fractional value.
        simpa [dHi] using extendedMixingFractionalPart_lt_one tHi
      -- TODO: the strict branch should now build the lower-envelope coefficients behind
      -- `translatedSliceEnvelope_spec`. The concrete blocker is again order-sensitive:
      -- the plan needs translated two-term inequalities between breakpoint classes, but
      -- `translatedTypeTwoPairInequality_of_mem_mixingInequalitiesRegion` requires an
      -- admissible index pair `[i, j]` with `i < j` and `f_i < f_j`. The selector data
      -- only gives breakpoint values `dLo < dHi`, not an order-compatible pair realizing
      -- them, so the missing step is an order-aware chain/representative extraction lemma.
      let _ := hy_relax
      let _ := hmax
      let _ := hmin
      let _ := hdLo_nonneg
      let _ := hdHi_nonneg
      let _ := hdLo_lt_hi
      let _ := hdHi_lt_one
      sorry

/-- Theorem 4.34. `P^mix` is described by the inequality `x₀ ≥ 0`, the degenerate zero-fraction
singleton covering inequalities, and the mixing inequalities `(4.29)` and `(4.30)` for all
sequences `1 ≤ i₁ < ⋯ < i_m ≤ n` such that `0 < f_{i₁} < ⋯ < f_{i_m}`. -/
theorem mixingHull_eq_mixing_inequalities_region
    (b : Fin n → ℚ) :
    mixingHull b = mixingInequalitiesRegion b := by
  ext x
  constructor
  · -- The hull inclusion is the easy convexity direction: every generator satisfies the region
    -- inequalities, and the region is convex.
    intro hx
    exact
      (convexHull_min
        (mixingSet_subset_mixingInequalitiesRegion b)
        (mixingInequalitiesRegion_convex b)) hx
  · intro hx
    let m : ℤ := ⌊x 0⌋
    let y : Fin (n + 1) → ℝ := x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))
    have hm : m = ⌊x 0⌋ := rfl
    have hy : y = x - (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) := rfl
    have hy0_nonneg : 0 ≤ y 0 := by
      -- Normalizing by the head ray leaves the fractional part of `x₀`.
      rw [hy, hm]
      simpa [exercise_3_29_ray_apply] using sub_nonneg.mpr (Int.floor_le (x 0))
    have hy0_lt_one : y 0 < 1 := by
      -- The normalized head coordinate is strictly below `1` because it is again the fractional
      -- part of `x₀`.
      have hfrac_lt : x 0 - (⌊x 0⌋ : ℝ) < 1 := by
        linarith [Int.lt_floor_add_one (x 0)]
      rw [hy, hm]
      simpa [exercise_3_29_ray_apply] using hfrac_lt
    obtain ⟨yBase, hyBase_mem, hhead, htail⟩ :=
      normalizedSliceSameHeadHullBasepoint b hx hm hy rfl hy0_nonneg hy0_lt_one
    have hm_nonneg_int : 0 ≤ m := by
      rw [hm]
      exact Int.floor_nonneg.mpr hx.1
    have hm_nonneg : 0 ≤ (m : ℝ) := by
      exact_mod_cast hm_nonneg_int
    have hx_eq :
        x = y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) := by
      -- Reattach the removed integral head-ray multiple.
      rw [hy]
      ext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    exact mem_mixingHull_of_normalized_basepoint b hx_eq hm_nonneg hyBase_mem hhead htail

end Theorem434
