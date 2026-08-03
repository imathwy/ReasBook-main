import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_17

open scoped BigOperators Matrix

-- This exercise reuses the Chapter 5 owner `mixed_integer_feasible_set` for pure-integer
-- feasibility of `A x ≤ b`; deleting one row is kept as the direct source-facing omission of that
-- single inequality rather than as a parallel wrapper predicate.

section Exercise615

variable {m n : ℕ}

/-- Helper for Exercise 6.15: an integer vector is deleted-feasible for row `i` when it satisfies
every inequality except possibly the `i`th one. -/
abbrev deletedFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  ∀ j : Fin m, j ≠ i → (A *ᵥ fun k ↦ (x k : ℚ)) j ≤ b j

/-- Helper for Exercise 6.15: the parity signature of an integral vector is its coordinatewise
reduction modulo `2`. -/
abbrev paritySignature
    (x : Fin n → ℤ) : Fin n → ZMod 2 :=
  fun k ↦ (x k : ZMod 2)

/-- Helper for Exercise 6.15: the finite set of parity signatures realized by deleted-feasible
witnesses for row `i`. -/
noncomputable def deletedFeasibleParitySet
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Finset (Fin n → ZMod 2) :=
  letI : DecidablePred
      (fun p : Fin n → ZMod 2 ↦
        ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p) :=
    Classical.decPred _
  Finset.univ.filter
    (fun p ↦ ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p)

/-- Helper for Exercise 6.15: membership in the parity-signature set is exactly realization by a
deleted-feasible witness. -/
lemma mem_deletedFeasibleParitySet_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    {p : Fin n → ZMod 2} :
    p ∈ deletedFeasibleParitySet A b i ↔
      ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p := by
  classical
  -- Unfold the filtered finite parity universe once and read off the realizing witness.
  simp [deletedFeasibleParitySet]

/-- Helper for Exercise 6.15: every deleted row has at least one realized parity signature. -/
lemma deletedFeasibleParitySet_nonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (i : Fin m) :
    (deletedFeasibleParitySet A b i).Nonempty := by
  rcases hdeleted i with ⟨x, hx⟩
  -- Record the parity signature of an existing deleted-feasible witness.
  refine ⟨paritySignature x, ?_⟩
  exact (mem_deletedFeasibleParitySet_iff A b i).2 ⟨x, hx, rfl⟩

/-- Helper for Exercise 6.15: any integral point satisfying all rows except `i` must strictly
violate the omitted row, because otherwise its real cast would be a point of
`mixed_integer_feasible_set`. -/
lemma deletedIntegralPointStrictlyViolatesOmittedRow
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i : Fin m}
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  -- If the omitted row also held, the real cast of `x` would satisfy every inequality and every
  -- coordinate integrality constraint.
  by_contra hnot
  apply hinfeasible
  refine ⟨fun k ↦ (x k : ℝ), ?_⟩
  rw [mem_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst hji
      have hnotR : (((A *ᵥ fun k ↦ (x k : ℚ)) j : ℚ) : ℝ) ≤ (b j : ℝ) := by
        exact_mod_cast not_lt.mp hnot
      simpa [Matrix.mulVec, dotProduct] using hnotR
    · have hxR : (((A *ᵥ fun k ↦ (x k : ℚ)) j : ℚ) : ℝ) ≤ (b j : ℝ) := by
        exact_mod_cast hx j hji
      simpa [Matrix.mulVec, dotProduct] using hxR
  · intro j hj
    exact ⟨x j, rfl⟩

/-- Helper for Exercise 6.15: coordinatewise parity equality forces each coordinate sum
`x k + y k` to be even. -/
lemma sameParitySumEven
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ k : Fin n, Even (x k + y k) := by
  intro k
  -- Reduce evenness to a `ZMod 2` vanishing statement where subtraction and addition agree.
  rw [← ZMod.intCast_eq_zero_iff_even]
  calc
    ((x k + y k : ℤ) : ZMod 2) = ((x k : ZMod 2) + (y k : ZMod 2)) := by
      simp
    _ = ((x k : ZMod 2) - (y k : ZMod 2)) := by
      rw [sub_eq_add_neg]
      simp
    _ = ((x k - y k : ℤ) : ZMod 2) := by
      simp
    _ = 0 := by
      rw [Int.cast_sub, hparity k, sub_self]

/-- Helper for Exercise 6.15: the integral midpoint of two vectors with the same parity signature
has rational coordinates equal to the arithmetic midpoint of the endpoint casts. -/
lemma sameParityMidpointEqAverage
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ k : Fin n,
      (((x k + y k) / 2 : ℤ) : ℚ) = (((x k : ℚ) + (y k : ℚ)) / 2) := by
  intro k
  -- First record that the midpoint numerator is divisible by `2`.
  have hsumEven : Even (x k + y k) := sameParitySumEven x y hparity k
  rw [even_iff_two_dvd] at hsumEven
  have htwoQ : ((2 : ℤ) : ℚ) ≠ 0 := by
    norm_num
  -- Then move integer division across the rational cast using that divisibility witness.
  calc
    (((x k + y k) / 2 : ℤ) : ℚ) = ((x k + y k : ℤ) : ℚ) / 2 := by
      exact Int.cast_div hsumEven htwoQ
    _ = (((x k : ℚ) + (y k : ℚ)) / 2) := by
      simp

/-- Helper for Exercise 6.15: the integral midpoint attached to a same-parity pair of integer
vectors. -/
def sameParityMidpoint
    (x y : Fin n → ℤ) : Fin n → ℤ :=
  fun k ↦ (x k + y k) / 2

/-- Helper for Exercise 6.15: every row value at a same-parity midpoint is the arithmetic average
of the row values at the endpoints. -/
lemma sameParityMidpointRowEqAverage
    (A : Matrix (Fin m) (Fin n) ℚ)
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ i : Fin m,
      (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i =
        (((A *ᵥ fun k ↦ (x k : ℚ)) i) + ((A *ᵥ fun k ↦ (y k : ℚ)) i)) / 2 := by
  intro i
  -- Rewrite the midpoint coordinates first, then move the average through the finite row sum.
  calc
    (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i
        = ∑ k : Fin n, A i k * (sameParityMidpoint x y k : ℚ) := by
            simp [Matrix.mulVec, dotProduct]
    _ = ∑ k : Fin n, A i k * ((((x k : ℚ) + (y k : ℚ)) / 2)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [sameParityMidpoint, sameParityMidpointEqAverage x y hparity k]
    _ = ∑ k : Fin n, (A i k * (x k : ℚ) + A i k * (y k : ℚ)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (∑ k : Fin n, (A i k * (x k : ℚ) + A i k * (y k : ℚ))) / 2 := by
          rw [← Finset.sum_div]
    _ = ((∑ k : Fin n, A i k * (x k : ℚ)) + ∑ k : Fin n, A i k * (y k : ℚ)) / 2 := by
          rw [Finset.sum_add_distrib]
    _ = (((A *ᵥ fun k ↦ (x k : ℚ)) i) + ((A *ᵥ fun k ↦ (y k : ℚ)) i)) / 2 := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 6.15: a same-parity midpoint of two deleted-feasible witnesses satisfies
every row omitted by neither endpoint. -/
lemma sameParityMidpointSatisfiesNonendpointRows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {i j r : Fin m}
    (hri : r ≠ i)
    (hrj : r ≠ j)
    (x y : Fin n → ℤ)
    (hx : deletedFeasible A b i x)
    (hy : deletedFeasible A b j y)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r ≤ b r := by
  -- Both endpoints satisfy row `r`, so the midpoint satisfies it by the row-average identity.
  have hxRow : (A *ᵥ fun k ↦ (x k : ℚ)) r ≤ b r := hx r hri
  have hyRow : (A *ᵥ fun k ↦ (y k : ℚ)) r ≤ b r := hy r hrj
  rw [sameParityMidpointRowEqAverage A x y hparity r]
  linarith

/-- Helper for Exercise 6.15: if two deleted-feasible witnesses have the same parity signature,
their integral midpoint must violate at least one omitted row, otherwise it would solve the full
system integrally. -/
lemma sameParityMidpointViolatesAnEndpoint
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i j : Fin m}
    (hij : i ≠ j)
    (x y : Fin n → ℤ)
    (hx : deletedFeasible A b i x)
    (hy : deletedFeasible A b j y)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i ∨
      b j < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) j := by
  -- If both omitted rows also held at the midpoint, the midpoint would be an integral point of the
  -- full system.
  by_contra hmid
  push Not at hmid
  apply hinfeasible
  refine ⟨fun k ↦ (sameParityMidpoint x y k : ℝ), ?_⟩
  rw [mem_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hri : r = i
    · subst hri
      have hrow : (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
        exact_mod_cast hmid.1
      simpa [Matrix.mulVec, dotProduct] using hrow
    · by_cases hrj : r = j
      · subst hrj
        have hrow : (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
          exact_mod_cast hmid.2
        simpa [Matrix.mulVec, dotProduct] using hrow
      · have hrowMid :
          (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r ≤ b r :=
            sameParityMidpointSatisfiesNonendpointRows A b hri hrj x y hx hy hparity
        have hrow :
            (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
          exact_mod_cast hrowMid
        simpa [Matrix.mulVec, dotProduct] using hrow
  · intro r hr
    exact ⟨sameParityMidpoint x y r, rfl⟩

/-- Helper for Exercise 6.15: the augmented rational row `(A i, b i)` whose common denominator
clears the `i`th inequality. -/
def rowAugmentedData
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Fin (n + 1) → ℚ :=
  Fin.append (A i) (fun _ ↦ b i)

/-- Helper for Exercise 6.15: the common denominator attached to the augmented row
`(A i, b i)`. -/
def rowCommonDenominator
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : ℕ :=
  rational_vector_common_denominator (rowAugmentedData A b i)

/-- Helper for Exercise 6.15: the integral coefficient vector obtained by clearing denominators in
the `i`th row. -/
def rowScaledCoeff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Fin n → ℤ :=
  fun j ↦ common_denominator_scaled_vector (rowAugmentedData A b i) (Fin.castAdd 1 j)

/-- Helper for Exercise 6.15: the integral right-hand side obtained by clearing denominators in
the `i`th inequality. -/
def rowScaledRhs
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : ℤ :=
  common_denominator_scaled_vector (rowAugmentedData A b i) (Fin.natAdd n 0)

/-- Helper for Exercise 6.15: the denominator-cleared slack of row `i` at the integral vector
`x`. Positive slack means strict violation of the `i`th inequality. -/
def rowScaledSlack
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : ℤ :=
  ∑ j : Fin n, rowScaledCoeff A b i j * x j - rowScaledRhs A b i

/-- Helper for Exercise 6.15: the nonnegative part of the cleared `i`th slack. This is the
discrete row-violation objective used in the parity-counting argument. -/
def rowViolationNat
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : ℕ :=
  Int.toNat (rowScaledSlack A b i x)

/-- Helper for Exercise 6.15: a prefix competitor for row `i` satisfies every earlier inequality
and strictly violates the `i`th one. -/
def prefixCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  (∀ r : Fin m, r < i → (A *ᵥ fun k ↦ (x k : ℚ)) r ≤ b r) ∧
    b i < (A *ᵥ fun k ↦ (x k : ℚ)) i

/-- Helper for Exercise 6.15: the augmented row common denominator is always nonzero. -/
lemma rowCommonDenominator_ne_zero
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) :
    rowCommonDenominator A b i ≠ 0 := by
  -- This is the rowwise specialization of the common-denominator nonvanishing fact.
  simpa [rowCommonDenominator, rowAugmentedData] using
    rationalVectorCommonDenominator_ne_zero (v := rowAugmentedData A b i)

/-- Helper for Exercise 6.15: the cleared row slack is exactly the common denominator times the
rational slack `(A x)_i - b_i`. -/
lemma rowScaledSlack_cast_eq
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    (((rowScaledSlack A b i x : ℤ) : ℚ)) =
      (rowCommonDenominator A b i : ℚ) *
        (((A *ᵥ fun k ↦ (x k : ℚ)) i) - b i) := by
  -- Clear denominators once on the augmented row, then collect the scaled row slack.
  have hcoeff :
      ∀ j : Fin n, ((rowScaledCoeff A b i j : ℤ) : ℚ) =
        (rowCommonDenominator A b i : ℚ) * A i j := by
    intro j
    have hscaled :=
      congrFun (common_denominator_scaled_vector_eq_smul (v := rowAugmentedData A b i))
        (Fin.castAdd 1 j)
    simpa [rowScaledCoeff, rowCommonDenominator, rowAugmentedData] using hscaled
  have hrhs : ((rowScaledRhs A b i : ℤ) : ℚ) =
      (rowCommonDenominator A b i : ℚ) * b i := by
    have hscaled :=
      congrFun (common_denominator_scaled_vector_eq_smul (v := rowAugmentedData A b i))
        (Fin.natAdd n 0)
    simpa [rowScaledRhs, rowCommonDenominator, rowAugmentedData] using hscaled
  calc
    (((rowScaledSlack A b i x : ℤ) : ℚ))
        = (∑ j : Fin n, ((rowScaledCoeff A b i j : ℤ) : ℚ) * (x j : ℚ)) -
            ((rowScaledRhs A b i : ℤ) : ℚ) := by
              simp [rowScaledSlack]
    _ = (∑ j : Fin n, ((rowCommonDenominator A b i : ℚ) * A i j) * (x j : ℚ)) -
          ((rowScaledRhs A b i : ℤ) : ℚ) := by
            refine congrArg (fun t : ℚ ↦ t - ((rowScaledRhs A b i : ℤ) : ℚ)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hcoeff j]
    _ = (∑ j : Fin n, ((rowCommonDenominator A b i : ℚ) * A i j) * (x j : ℚ)) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            rw [hrhs]
    _ = (∑ j : Fin n, (rowCommonDenominator A b i : ℚ) * (A i j * (x j : ℚ))) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            refine congrArg (fun t : ℚ ↦ t - ((rowCommonDenominator A b i : ℚ) * b i)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = (rowCommonDenominator A b i : ℚ) * (∑ j : Fin n, A i j * (x j : ℚ)) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            rw [Finset.mul_sum]
    _ = (rowCommonDenominator A b i : ℚ) *
          ((∑ j : Fin n, A i j * (x j : ℚ)) - b i) := by
            ring
    _ = (rowCommonDenominator A b i : ℚ) *
          (((A *ᵥ fun k ↦ (x k : ℚ)) i) - b i) := by
            simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 6.15: positive denominator-cleared slack is equivalent to strict
violation of the original rational row inequality. -/
lemma rowScaledSlack_pos_iff_rowViolation
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    0 < rowScaledSlack A b i x ↔ b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  have hden_pos : 0 < (rowCommonDenominator A b i : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (rowCommonDenominator_ne_zero A b i)
  constructor
  · intro hslack
    have hslackQ : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
      exact_mod_cast hslack
    rw [rowScaledSlack_cast_eq A b i x] at hslackQ
    have hdiff : (0 : ℚ) < ((A *ᵥ fun k ↦ (x k : ℚ)) i - b i) := by
      nlinarith
    linarith
  · intro hviol
    have hdiff : (0 : ℚ) < ((A *ᵥ fun k ↦ (x k : ℚ)) i - b i) := by
      linarith
    have hslackQ : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
      rw [rowScaledSlack_cast_eq A b i x]
      nlinarith
    exact_mod_cast hslackQ

/-- Helper for Exercise 6.15: the natural row-violation objective is positive exactly at strict
violations of the original rational row inequality. -/
lemma rowViolationNat_pos_iff_rowViolation
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    0 < rowViolationNat A b i x ↔ b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  constructor
  · intro hpos
    have hslackPos : 0 < rowScaledSlack A b i x := by
      by_contra hnot
      have hnonpos : rowScaledSlack A b i x ≤ 0 := le_of_not_gt hnot
      have hzero : rowViolationNat A b i x = 0 := by
        simp [rowViolationNat, Int.toNat_of_nonpos hnonpos]
      omega
    exact (rowScaledSlack_pos_iff_rowViolation A b i x).1 hslackPos
  · intro hviol
    have hslackPos : 0 < rowScaledSlack A b i x :=
      (rowScaledSlack_pos_iff_rowViolation A b i x).2 hviol
    have hcast : (0 : ℤ) < ((rowViolationNat A b i x : ℕ) : ℤ) := by
      -- Once the cleared slack is positive, the `toNat` coercion is definitionally stable.
      unfold rowViolationNat
      simpa [Int.toNat_of_nonneg hslackPos.le] using hslackPos
    exact_mod_cast hcast

/-- Helper for Exercise 6.15: the natural row-violation objective vanishes exactly on points that
satisfy the corresponding rational row inequality. -/
lemma rowViolationNat_eq_zero_iff_rowSatisfied
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    rowViolationNat A b i x = 0 ↔ (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i := by
  constructor
  · intro hzero
    by_contra hviol
    have hviol' : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := lt_of_not_ge hviol
    have hpos : 0 < rowViolationNat A b i x :=
      (rowViolationNat_pos_iff_rowViolation A b i x).2 hviol'
    omega
  · intro hsatisfied
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hviol : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i :=
      (rowViolationNat_pos_iff_rowViolation A b i x).1 hpos
    linarith

/-- Helper for Exercise 6.15: a satisfied row has nonpositive denominator-cleared slack. -/
lemma rowScaledSlack_nonpos_of_rowSatisfied
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ)
    (hsatisfied : (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i) :
    rowScaledSlack A b i x ≤ 0 := by
  -- Positive cleared slack would contradict the assumed row satisfaction.
  by_contra hnot
  have hpos : 0 < rowScaledSlack A b i x := lt_of_not_ge hnot
  have hviol : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i :=
    (rowScaledSlack_pos_iff_rowViolation A b i x).1 hpos
  linarith

/-- Helper for Exercise 6.15: denominator-cleared row slack commutes with the same-parity
midpoint operation by taking arithmetic averages. -/
lemma sameParityMidpointRowScaledSlack_eq_average
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    (((rowScaledSlack A b i (sameParityMidpoint x y) : ℤ) : ℚ)) =
      ((((rowScaledSlack A b i x : ℤ) : ℚ)) + (((rowScaledSlack A b i y : ℤ) : ℚ))) / 2 := by
  -- Rewrite every cleared slack as the common denominator times a rational row slack, then use
  -- the midpoint row-average formula.
  rw [rowScaledSlack_cast_eq, rowScaledSlack_cast_eq, rowScaledSlack_cast_eq]
  rw [sameParityMidpointRowEqAverage A x y hparity i]
  ring

/-- Helper for Exercise 6.15: if the left endpoint strictly violates row `i`, the right endpoint
satisfies it, and the same-parity midpoint still violates row `i`, then the midpoint has strictly
smaller natural row violation on row `i`. -/
lemma sameParityMidpointRowViolation_lt_of_leftViolation_rightSatisfaction
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hleft : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i)
    (hright : (A *ᵥ fun k ↦ (y k : ℚ)) i ≤ b i)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2))
    (hmid : b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i) :
    rowViolationNat A b i (sameParityMidpoint x y) < rowViolationNat A b i x := by
  -- Transport the midpoint row identity to cleared slacks, then compare the positive integer
  -- slacks through their rational casts before returning to `ℕ`.
  have hxSlackPos : 0 < rowScaledSlack A b i x :=
    (rowScaledSlack_pos_iff_rowViolation A b i x).2 hleft
  have hySlackNonpos : rowScaledSlack A b i y ≤ 0 :=
    rowScaledSlack_nonpos_of_rowSatisfied A b i y hright
  have hmidSlackPos : 0 < rowScaledSlack A b i (sameParityMidpoint x y) :=
    (rowScaledSlack_pos_iff_rowViolation A b i (sameParityMidpoint x y)).2 hmid
  have hxSlackQPos : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
    exact_mod_cast hxSlackPos
  have hySlackQNonpos : (((rowScaledSlack A b i y : ℤ) : ℚ)) ≤ 0 := by
    exact_mod_cast hySlackNonpos
  have hmidAverage :=
    sameParityMidpointRowScaledSlack_eq_average A b i x y hparity
  have hmidSlackQLt : (((rowScaledSlack A b i (sameParityMidpoint x y) : ℤ) : ℚ)) <
      (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
    rw [hmidAverage]
    linarith
  have hmidSlackLt : rowScaledSlack A b i (sameParityMidpoint x y) < rowScaledSlack A b i x := by
    exact_mod_cast hmidSlackQLt
  have hmidCast :
      (((rowViolationNat A b i (sameParityMidpoint x y) : ℕ) : ℤ)) =
        rowScaledSlack A b i (sameParityMidpoint x y) := by
    -- Positive midpoint slack keeps the `toNat` cast transparent.
    unfold rowViolationNat
    simp [Int.toNat_of_nonneg hmidSlackPos.le]
  have hxCast : (((rowViolationNat A b i x : ℕ) : ℤ)) = rowScaledSlack A b i x := by
    -- The left endpoint also has positive slack, so its `toNat` cast is transparent as well.
    unfold rowViolationNat
    simp [Int.toNat_of_nonneg hxSlackPos.le]
  have hnatCastLt :
      (((rowViolationNat A b i (sameParityMidpoint x y) : ℕ) : ℤ)) <
        (((rowViolationNat A b i x : ℕ) : ℤ)) := by
    simpa [hmidCast, hxCast] using hmidSlackLt
  exact_mod_cast hnatCastLt

/-- Helper for Exercise 6.15: every deleted-feasible witness is automatically a prefix competitor
for its omitted row. -/
lemma deletedFeasible_isPrefixCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i : Fin m}
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    prefixCompetitor A b i x := by
  -- Deleted-feasibility gives all earlier rows, and infeasibility supplies the strict `i`th
  -- violation.
  refine ⟨?_, deletedIntegralPointStrictlyViolatesOmittedRow A b hinfeasible hx⟩
  intro r hri
  exact hx r (ne_of_lt hri)

/-- Helper for Exercise 6.15: with a fixed exempt row `k`, a witness for row `i` is admissible
when it satisfies every row except possibly `i` and `k`. -/
abbrev exemptRowFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  ∀ r : Fin m, r ≠ i → r ≠ k → (A *ᵥ fun j ↦ (x j : ℚ)) r ≤ b r

/-- Helper for Exercise 6.15: a fixed-exempt-row competitor is an admissible witness that still
strictly violates its owned row. -/
abbrev exemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  exemptRowFeasible A b k i x ∧ b i < (A *ᵥ fun j ↦ (x j : ℚ)) i

/-- Helper for Exercise 6.15: every deleted-feasible witness is automatically admissible in every
fixed-exempt-row universe. -/
lemma deletedFeasible_toExemptRowFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    exemptRowFeasible A b k i x := by
  intro r hri _
  -- Forgetting one additional exempt row only weakens the deleted-feasibility requirements.
  exact hx r hri

/-- Helper for Exercise 6.15: every deleted-feasible witness is a fixed-exempt-row competitor for
its own row because infeasibility forces the omitted row to be strictly violated. -/
lemma deletedFeasible_toExemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (k i : Fin m)
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    exemptRowCompetitor A b k i x := by
  refine ⟨deletedFeasible_toExemptRowFeasible A b k i hx, ?_⟩
  -- The owned row stays strictly violated for every deleted-feasible witness.
  exact deletedIntegralPointStrictlyViolatesOmittedRow A b hinfeasible hx

/-- Helper for Exercise 6.15: each deleted row already has a witness in every fixed-exempt-row
universe. -/
lemma existsExemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (k i : Fin m) :
    ∃ x : Fin n → ℤ, exemptRowCompetitor A b k i x := by
  rcases hdeleted i with ⟨x, hx⟩
  -- Reuse the deleted-feasible witness inside the weaker fixed-exempt-row admissible family.
  exact ⟨x, deletedFeasible_toExemptRowCompetitor A b hinfeasible k i hx⟩

/-- Helper for Exercise 6.15: in a fixed-exempt-row universe, the midpoint of two same-parity
witnesses satisfies every row omitted by neither endpoint and by the exempt row. -/
lemma sameParityMidpointSatisfiesExemptRows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {k i j r : Fin m}
    (hri : r ≠ i)
    (hrj : r ≠ j)
    (hrk : r ≠ k)
    (x y : Fin n → ℤ)
    (hx : exemptRowFeasible A b k i x)
    (hy : exemptRowFeasible A b k j y)
    (hparity : ∀ t : Fin n, (x t : ZMod 2) = (y t : ZMod 2)) :
    (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r ≤ b r := by
  have hxRow : (A *ᵥ fun t ↦ (x t : ℚ)) r ≤ b r := hx r hri hrk
  have hyRow : (A *ᵥ fun t ↦ (y t : ℚ)) r ≤ b r := hy r hrj hrk
  -- The fixed exempt row stays outside the averaging step, so the original midpoint argument
  -- still proves every genuinely nonendpoint row.
  rw [sameParityMidpointRowEqAverage A x y hparity r]
  linarith

/-- Helper for Exercise 6.15: Hall's theorem chooses pairwise distinct deleted-feasible parity
signatures, one for each row. -/
lemma existsInjectiveDeletedFeasibleParityChoice
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion (deletedFeasibleParitySet A b)).card) :
    ∃ σ : Fin m → (Fin n → ZMod 2),
      Function.Injective σ ∧ ∀ i : Fin m, σ i ∈ deletedFeasibleParitySet A b i := by
  classical
  -- Apply Hall directly to the row-indexed family of realized parity-signature sets.
  simpa using
    (Finset.all_card_le_biUnion_card_iff_exists_injective (deletedFeasibleParitySet A b)).1 hHall

/-- Helper for Exercise 6.15: an injective parity choice can be lifted back to actual
deleted-feasible integral witnesses. -/
lemma existsInjectiveDeletedFeasibleWitnessFamily
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion (deletedFeasibleParitySet A b)).card) :
    ∃ w : Fin m → (Fin n → ℤ),
      (∀ i : Fin m, deletedFeasible A b i (w i)) ∧
        Function.Injective (fun i : Fin m ↦ paritySignature (w i)) := by
  classical
  rcases existsInjectiveDeletedFeasibleParityChoice A b hHall with ⟨σ, hσinj, hσmem⟩
  have hwitness :
      ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = σ i := by
    intro i
    exact (mem_deletedFeasibleParitySet_iff A b i).1 (hσmem i)
  choose w hwDeleted hwParity using hwitness
  refine ⟨w, hwDeleted, ?_⟩
  intro i j hij
  -- Rewriting the chosen witness parities through the Hall-selected family restores injectivity.
  apply hσinj
  calc
    σ i = paritySignature (w i) := (hwParity i).symm
    _ = paritySignature (w j) := hij
    _ = σ j := hwParity j

/-- Exercise 6.15. Let `A ∈ ℚ^(m × n)` and `b ∈ ℚ^m` be such that the system `A x ≤ b` has no
integral solution, but deleting any one of the `m` inequalities yields a system with an integral
solution. Then `m ≤ 2^n`. -/
theorem minimal_integral_infeasible_rational_system_row_bound
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hminimal :
      ∀ i : Fin m,
        ∃ x : Fin n → ℤ,
          ∀ j : Fin m, j ≠ i → (A *ᵥ fun k ↦ (x k : ℚ)) j ≤ b j) :
    m ≤ 2 ^ n := by
  classical
  -- Route correction: the previous route tried to prove a global Hall statement for
  -- `deletedFeasibleParitySet A b`, but that statement is false already for the one-dimensional
  -- system `x ≤ 0`, `x ≥ 2`, where both deleted-feasible parity sets are `{0 mod 2}`. The next
  -- route must instead work with a stronger witness package than plain deleted-feasibility.
  have hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x := by
    intro i
    rcases hminimal i with ⟨x, hx⟩
    -- Repackage the row-deletion witness in the source-facing owner `deletedFeasible`.
    exact ⟨x, hx⟩
  -- TODO: replace the false global Hall step by a corrected fixed-exempt-row or equivalent
  -- witness-selection lemma, then finish with the existing finite-parity counting argument.
  sorry

end Exercise615
