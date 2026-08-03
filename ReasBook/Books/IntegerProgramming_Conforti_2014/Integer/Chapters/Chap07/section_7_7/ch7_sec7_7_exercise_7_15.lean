import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch`, so this file follows the local Chapter 7 mixed-integer / facet API
-- precedent already used for flow-cover statements.

section Exercise715

variable {n : ℕ}

/-- The source index block `{1, …, k}` on `Fin n`, encoded using the zero-based condition
`j.1 < k`. -/
def exercise_7_15_head_indices (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j.1 < k

/-- Membership in `exercise_7_15_head_indices k` means that the zero-based index lies strictly
before `k`, i.e. it belongs to the source block `{1, …, k}`. -/
theorem mem_exercise_7_15_head_indices_iff
    (k : ℕ) (j : Fin n) :
    j ∈ exercise_7_15_head_indices k ↔ j.1 < k := by
  -- This is just membership in a filtered copy of `Finset.univ`.
  simp [exercise_7_15_head_indices]

/-- The source index block `{k + 1, …, n}` on `Fin n`, encoded using the zero-based condition
`k ≤ j.1`. -/
def exercise_7_15_tail_indices (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ k ≤ j.1

/-- Membership in `exercise_7_15_tail_indices k` means that the zero-based index is at least
`k`, i.e. it belongs to the source block `{k + 1, …, n}`. -/
theorem mem_exercise_7_15_tail_indices_iff
    (k : ℕ) (j : Fin n) :
    j ∈ exercise_7_15_tail_indices k ↔ k ≤ j.1 := by
  -- This is the same filtered-universal membership computation for the tail block.
  simp [exercise_7_15_tail_indices]

/-- The source complement `\bar L = {k + 1, …, n} \setminus L` used in Exercise 7.15. -/
def exercise_7_15_tail_complement (k : ℕ) (L : Finset (Fin n)) : Finset (Fin n) :=
  exercise_7_15_tail_indices k \ L

/-- Membership in `exercise_7_15_tail_complement k L` means belonging to the source tail block
while not belonging to `L`. -/
theorem mem_exercise_7_15_tail_complement_iff
    (k : ℕ) (L : Finset (Fin n)) (j : Fin n) :
    j ∈ exercise_7_15_tail_complement k L ↔
      k ≤ j.1 ∧ j ∉ L := by
  -- The source complement is a finset difference of the tail block by `L`.
  simp [exercise_7_15_tail_complement, mem_exercise_7_15_tail_indices_iff]

/-- The mixed integer set `T` from Exercise 7.15, where the source blocks `1, …, k` and
`k + 1, …, n` are encoded on `Fin n` as `j.1 < k` and `k ≤ j.1`. -/
def exercise_7_15_mixed_integer_set
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
      (∀ j, 0 ≤ p.2 j) ∧
        ((Finset.sum (exercise_7_15_head_indices k) fun j ↦ p.2 j) -
            (Finset.sum (exercise_7_15_tail_indices k) fun j ↦ p.2 j)) ≤
          b ∧
          ∀ j, p.2 j ≤ a j * p.1 j}

/-- Membership in `exercise_7_15_mixed_integer_set k b a` is exactly the binary,
nonnegativity, signed-balance, and upper-bound system from Exercise 7.15. -/
theorem mem_exercise_7_15_mixed_integer_set_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise_7_15_mixed_integer_set k b a ↔
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
        (∀ j, 0 ≤ p.2 j) ∧
          ((Finset.sum (exercise_7_15_head_indices k) fun j ↦ p.2 j) -
              (Finset.sum (exercise_7_15_tail_indices k) fun j ↦ p.2 j)) ≤
            b ∧
            ∀ j, p.2 j ≤ a j * p.1 j := by
  -- Membership is definitionally the conjunction of the four source constraints.
  rfl

/-- The left-hand side of the Exercise 7.15 lifted inequality evaluated at a point `(x, y)`. -/
def exercise_7_15_lifted_flow_cover_value
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ((Finset.sum C fun j ↦ p.2 j) -
    (Finset.sum (exercise_7_15_tail_complement k L) fun j ↦ p.2 j)) +
      (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) -
        (Finset.sum L fun j ↦ lam * p.1 j)

/-- `exercise_7_15_lifted_flow_cover_value k a C L λ p` expands to the source inequality left-hand
side `∑_{j ∈ C} y_j - ∑_{j ∈ \bar L} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j) - ∑_{j ∈ L} λ x_j`.
-/
theorem exercise_7_15_lifted_flow_cover_value_eq
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise_7_15_lifted_flow_cover_value k a C L lam p =
      ((Finset.sum C fun j ↦ p.2 j) -
        (Finset.sum (exercise_7_15_tail_complement k L) fun j ↦ p.2 j)) +
          (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) -
            (Finset.sum L fun j ↦ lam * p.1 j) := by
  -- The left-hand side is introduced precisely by this definition.
  rfl

/-- Helper for Exercise 7.15: inserting one tail index into `L` replaces the corresponding
`-y_i` contribution by `-λ x_i`, so the lifted value changes by `y_i - λ x_i`. -/
theorem exercise_7_15_value_insert_tail
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    {i : Fin n}
    (hiL : i ∉ L)
    (htail : k ≤ i.1) :
    exercise_7_15_lifted_flow_cover_value k a C (insert i L) lam p =
      exercise_7_15_lifted_flow_cover_value k a C L lam p + p.2 i - lam * p.1 i := by
  have hsplit_tail :
      Finset.sum (exercise_7_15_tail_indices k \ L) (fun j ↦ p.2 j) =
        p.2 i + Finset.sum (exercise_7_15_tail_indices k \ insert i L) (fun j ↦ p.2 j) := by
    -- The old tail complement is the new one plus the single index `i`.
    have hset :
        exercise_7_15_tail_indices k \ L =
          insert i (exercise_7_15_tail_indices k \ insert i L) := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [exercise_7_15_tail_indices, hiL, htail]
      · simp [exercise_7_15_tail_indices, hji]
    rw [hset]
    rw [Finset.sum_insert]
    · simp
    · simp [exercise_7_15_tail_indices]
  have hsplit_L :
      Finset.sum (insert i L) (fun j ↦ lam * p.1 j) =
        lam * p.1 i + Finset.sum L (fun j ↦ lam * p.1 j) := by
    -- The lifted `L`-term gains exactly the new coefficient at `i`.
    rw [Finset.sum_insert hiL]
  -- After splitting the two affected sums, the identity is a polynomial rearrangement.
  rw [exercise_7_15_lifted_flow_cover_value, exercise_7_15_lifted_flow_cover_value,
    exercise_7_15_tail_complement, exercise_7_15_tail_complement, hsplit_tail, hsplit_L]
  ring

/-- The equality face of `conv(T)` cut out by the Exercise 7.15 lifted inequality. -/
def exercise_7_15_lifted_flow_cover_face
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) ∧
      exercise_7_15_lifted_flow_cover_value k a C L lam p = b}

/-- Membership in `exercise_7_15_lifted_flow_cover_face k b a C L λ` means belonging to `conv(T)`
and meeting the Exercise 7.15 lifted inequality at equality. -/
theorem mem_exercise_7_15_lifted_flow_cover_face_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise_7_15_lifted_flow_cover_face k b a C L lam ↔
      p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) ∧
        exercise_7_15_lifted_flow_cover_value k a C L lam p = b := by
  -- The face owner is defined as this equality slice inside `conv(T)`.
  rfl

/-- Exercise 7.15. Let
`T = {(x,y) ∈ {0,1}^n × ℝ^n_+ | ∑_{j=1}^k y_j - ∑_{j=k+1}^n y_j ≤ b, y_j ≤ a_j x_j for all j}`
with `b > 0` and `a_j > 0` for all `j`. Let `C ⊆ {1, …, k}` be a flow cover, let
`λ = flow_cover_excess a b C = ∑_{j ∈ C} a_j - b`, and let
`L ⊆ {k + 1, …, n}` with `\bar L = {k + 1, …, n} \setminus L`. If `max_{j ∈ C} a_j > λ` and
`a_j > λ` for all `j ∈ L`, then the inequality
`∑_{j ∈ C} y_j - ∑_{j ∈ \bar L} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j) - ∑_{j ∈ L} λ x_j ≤ b`
is valid for `conv(T)` and its equality face is a facet of `conv(T)`. The source hypothesis
`max_{j ∈ C} a_j > λ` is recorded directly by asking for some `j ∈ C` with `a_j > λ`. -/
theorem exercise_7_15_lifted_flow_cover_inequality_defines_facet
    (k : ℕ)
    (b : ℝ) (a : Fin n → ℝ)
    (C L : Finset (Fin n))
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hC : IsFlowCover a b C)
    (hmax : ∃ j ∈ C, flow_cover_excess a b C < a j)
    (hLsub : ∀ ⦃j : Fin n⦄, j ∈ L → k ≤ j.1)
    (hLgt : ∀ ⦃j : Fin n⦄, j ∈ L → flow_cover_excess a b C < a j) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) →
          exercise_7_15_lifted_flow_cover_value k a C L (flow_cover_excess a b C) p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise_7_15_mixed_integer_set k b a))
        (exercise_7_15_lifted_flow_cover_face k b a C L (flow_cover_excess a b C)) := by
  -- Route correction: the easy definitional API is now in place, but the actual source-faithful
  -- sequential-lifting argument still needs the base facet construction and the tail-lift step.
  -- TODO: prove the `L = ∅` base facet, then lift one tail index at a time using
  -- `exercise_7_15_value_insert_tail` and a tight exchange-point construction.
  sorry

end Exercise715
