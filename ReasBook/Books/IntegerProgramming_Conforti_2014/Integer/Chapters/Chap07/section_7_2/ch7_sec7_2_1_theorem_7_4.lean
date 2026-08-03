import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2
import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_1_remark_7_5

open scoped BigOperators

section Theorem74

variable {n : ℕ}

/-- The prefix cover `{1, ..., t}` from Theorem 7.4, represented on `Fin n` by the indices
`< t`. -/
def theorem_7_4_cover
    (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i < t

/-- Membership in `theorem_7_4_cover t` means that the index lies among the first `t`
positions. -/
@[simp] theorem theorem_7_4_cover_mem_iff
    {t : ℕ}
    {j : Fin n} :
    j ∈ theorem_7_4_cover t ↔ j < t := by
  simp [theorem_7_4_cover]

/-- The ordered cover weights `a₁, ..., a_t` from Theorem 7.4, reindexed as a function on
`Fin t`. -/
def theorem_7_4_cover_weight
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Fin t → ℕ :=
  fun i ↦ weights (i.castLE ht)

/-- Evaluating `theorem_7_4_cover_weight weights ht` at `i` recovers the corresponding cover
weight from the first `t` indices. -/
@[simp] theorem theorem_7_4_cover_weight_apply
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n)
    (i : Fin t) :
    theorem_7_4_cover_weight weights ht i = weights (i.castLE ht) :=
  rfl

/-- `theorem_7_4_cover_weights_descending weights ht` records the assumption
`a₁ ≥ a₂ ≥ ··· ≥ a_t` from Theorem 7.4 on the ordered cover indices. -/
def theorem_7_4_cover_weights_descending
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Prop :=
  Antitone (theorem_7_4_cover_weight weights ht)

/-- Expanding `theorem_7_4_cover_weights_descending weights ht` recovers that the ordered cover
weights are antitone. -/
theorem theorem_7_4_cover_weights_descending_iff
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) :
    theorem_7_4_cover_weights_descending weights ht ↔
      Antitone (theorem_7_4_cover_weight weights ht) :=
  Iff.rfl

/-- The partial sums `μ_h = ∑_{ℓ=1}^h a_ℓ` from Theorem 7.4, extended to all natural indices by
summing the first `h` ordered cover weights among the first `t` positions. -/
def theorem_7_4_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) : ℕ → ℕ :=
  fun h ↦
    (Finset.range h).sum fun ℓ ↦
      if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0

/-- The initial partial sum from Theorem 7.4 is `μ₀ = 0`. -/
theorem theorem_7_4_mu_zero
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_mu weights t ht 0 = 0 := by
  -- The initial partial sum is the empty sum over `range 0`.
  simp [theorem_7_4_mu]

/-- For `h < t`, the next partial sum from Theorem 7.4 satisfies `μ_{h+1} = μ_h + a_{h+1}` in
zero-based `Fin` indexing. -/
theorem theorem_7_4_mu_succ_of_lt
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (h : ℕ)
    (hh : h < t) :
    theorem_7_4_mu weights t ht (h + 1) =
      theorem_7_4_mu weights t ht h + theorem_7_4_cover_weight weights ht ⟨h, hh⟩ := by
  -- Split the next partial sum at the new index `h`.
  rw [theorem_7_4_mu, theorem_7_4_mu, Finset.sum_range_succ]
  -- The new summand is exactly the `h`th cover weight because `h < t`.
  simp [theorem_7_4_cover_weight, hh]

/-- The cover excess `λ = μ_t - b` from Theorem 7.4. -/
def theorem_7_4_cover_excess
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) : ℕ :=
  theorem_7_4_mu weights t ht t - capacity

/-- Expanding `theorem_7_4_cover_excess weights capacity t ht` recovers the formula
`λ = μ_t - b` from Theorem 7.4. -/
theorem theorem_7_4_cover_excess_eq
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_cover_excess weights capacity t ht =
      theorem_7_4_mu weights t ht t - capacity :=
  rfl

/-- Helper for Theorem 7.4: the prefix cover `{i | i < t}` is exactly the image of `Fin t` in
`Fin n` under `Fin.castLE ht`. -/
theorem theorem_7_4_cover_eq_castLEImage
    (t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_cover (n := n) t =
      (Finset.univ : Finset (Fin t)).map
        ⟨fun i ↦ i.castLE ht, by
          intro a b hab
          exact Fin.ext (congrArg (fun x : Fin n ↦ x.1) hab)
        ⟩ := by
  ext j
  constructor
  · intro hj
    rw [Finset.mem_map]
    refine ⟨⟨j, theorem_7_4_cover_mem_iff.mp hj⟩, by simp, ?_⟩
    simp
  · intro hj
    rw [Finset.mem_map] at hj
    rcases hj with ⟨i, -, hij⟩
    subst hij
    simp [theorem_7_4_cover]

/-- Helper for Theorem 7.4: summing the weights over the prefix cover gives the partial sum
`μ_t`. -/
theorem theorem_7_4_cover_sum_eq_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    (theorem_7_4_cover t).sum weights = theorem_7_4_mu weights t ht t := by
  let g : ℕ → ℕ := fun ℓ ↦
    if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0
  -- Reindex the prefix cover by the canonical embedding `Fin t ↪ Fin n`.
  rw [theorem_7_4_cover_eq_castLEImage (n := n) t ht]
  rw [Finset.sum_map]
  calc
    ∑ x : Fin t, weights (x.castLE ht)
      = ∑ x : Fin t, g x := by
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [g]
          have hxcast : x.castLE ht = ⟨↑x, Nat.lt_of_lt_of_le x.isLt ht⟩ := by
            exact Fin.ext rfl
          rw [hxcast]
          simp [x.isLt]
    _ = ∑ ℓ ∈ Finset.range t, g ℓ := by
          simpa using (Fin.sum_univ_eq_sum_range g t)
    _ = theorem_7_4_mu weights t ht t := by
          simp [g, theorem_7_4_mu]

/-- Helper for Theorem 7.4: evaluating `μ_s` inside a larger prefix problem agrees with
evaluating the same prefix sum in the shorter prefix problem. -/
theorem theorem_7_4_mu_prefix_eq
    (weights : Fin n → ℕ)
    {s t : ℕ}
    (hsn : s ≤ n)
    (htn : t ≤ n)
    (hst : s ≤ t) :
    theorem_7_4_mu weights s hsn s = theorem_7_4_mu weights t htn s := by
  -- Every summand in `range s` lies below both cutoffs `s` and `t`.
  unfold theorem_7_4_mu
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hlt_s : ℓ < s := Finset.mem_range.mp hℓ
  have hlt_t : ℓ < t := Nat.lt_of_lt_of_le hlt_s hst
  simp [hlt_s, hlt_t]

/-- Helper for Theorem 7.4: minimality of the prefix cover implies `λ ≤ a_r` for every cover
index `r < t`. -/
theorem theorem_7_4_coverExcess_le_coverWeight
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (r : Fin t) :
    theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_cover_weight weights ht r := by
  have hrmem : r.castLE ht ∈ theorem_7_4_cover t := by
    simp [theorem_7_4_cover, r.isLt]
  have herase := hC.erase_sum_le (r.castLE ht) hrmem
  have hsum : (theorem_7_4_cover t).sum weights = theorem_7_4_mu weights t ht t :=
    theorem_7_4_cover_sum_eq_mu weights t ht
  -- Delete the cover item `r` and compare the remaining weight with the capacity.
  have hsum_le : (theorem_7_4_cover t).sum weights ≤ capacity + weights (r.castLE ht) := by
    have haux := Nat.add_le_add_right herase (weights (r.castLE ht))
    simpa [← (theorem_7_4_cover t).sum_erase_add weights hrmem,
      add_comm, add_left_comm, add_assoc] using haux
  have hmu_le : theorem_7_4_mu weights t ht t ≤ capacity + weights (r.castLE ht) := by
    simpa [hsum] using hsum_le
  have htarget : theorem_7_4_mu weights t ht t - capacity ≤ weights (r.castLE ht) := by
    omega
  simpa [theorem_7_4_cover_excess, theorem_7_4_cover_weight] using htarget

/-- The closed interval from Theorem 7.4 (1) is
`μ_h ≤ a_j ≤ μ_{h+1} - λ` for an index `j ∉ C`. -/
def theorem_7_4_exact_interval_condition
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) : Prop :=
  theorem_7_4_mu weights t ht h ≤ weights j ∧
    weights j ≤ theorem_7_4_mu weights t ht (h + 1) -
      theorem_7_4_cover_excess weights capacity t ht

/-- Expanding `theorem_7_4_exact_interval_condition weights capacity t ht j h` recovers the
closed interval condition `μ_h ≤ a_j ≤ μ_{h+1} - λ` from Theorem 7.4 (1). -/
theorem theorem_7_4_exact_interval_condition_iff
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) :
    theorem_7_4_exact_interval_condition weights capacity t ht j h ↔
      theorem_7_4_mu weights t ht h ≤ weights j ∧
        weights j ≤ theorem_7_4_mu weights t ht (h + 1) -
          theorem_7_4_cover_excess weights capacity t ht :=
  Iff.rfl

/-- The boundary interval from Theorem 7.4 is the open interval
`μ_{h+1} - λ < a_j < μ_{h+1}` for an index `j ∉ C`. -/
def theorem_7_4_boundary_interval_condition
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) : Prop :=
  theorem_7_4_mu weights t ht (h + 1) -
      theorem_7_4_cover_excess weights capacity t ht <
    weights j ∧
    weights j < theorem_7_4_mu weights t ht (h + 1)

/-- Expanding `theorem_7_4_boundary_interval_condition weights capacity t ht j h` recovers the
open interval condition `μ_{h+1} - λ < a_j < μ_{h+1}` from Theorem 7.4. -/
theorem theorem_7_4_boundary_interval_condition_iff
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) :
    theorem_7_4_boundary_interval_condition weights capacity t ht j h ↔
    theorem_7_4_mu weights t ht (h + 1) -
          theorem_7_4_cover_excess weights capacity t ht <
        weights j ∧
        weights j < theorem_7_4_mu weights t ht (h + 1) :=
  Iff.rfl

/-- The facet-defining liftings of the prefix minimal cover from Theorem 7.4, expressed as valid
liftings of the cover inequality whose lifted face is a facet of the knapsack polytope. -/
abbrev theorem_7_4_facet_defining_liftings
    (weights : Fin n → ℕ)
    (capacity t : ℕ) :
    Set (Fin n → ℝ) :=
  facet_defining_liftings_of_minimal_cover_inequality
    weights
    capacity
    (theorem_7_4_cover t)

/-- Helper for Theorem 7.4: a shorter prefix cover is contained in a longer one. -/
theorem theorem_7_4_cover_subset
    {s t : ℕ}
    (hst : s ≤ t) :
    theorem_7_4_cover (n := n) s ⊆ theorem_7_4_cover t := by
  -- Membership is just the corresponding strict inequality on indices.
  intro i hi
  exact theorem_7_4_cover_mem_iff.mpr
    (Nat.lt_of_lt_of_le (theorem_7_4_cover_mem_iff.mp hi) hst)

/-- Helper for Theorem 7.4: the prefix cover `{i | i < t}` has exactly `t` elements when
`t ≤ n`. -/
theorem theorem_7_4_cover_card
    (t : ℕ)
    (ht : t ≤ n) :
    (theorem_7_4_cover (n := n) t).card = t := by
  -- Reindex the prefix cover by `Fin t`.
  rw [theorem_7_4_cover_eq_castLEImage (n := n) t ht]
  simp

/-- Helper for Theorem 7.4: filtering the prefix cover by `s ≤ i` removes the shorter prefix
`theorem_7_4_cover s`. -/
theorem theorem_7_4_cover_filter_ge_eq_sdiff
    (t s : ℕ) :
    (theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) =
      theorem_7_4_cover t \ theorem_7_4_cover s := by
  -- On the prefix cover, `s ≤ i` is equivalent to `i ∉ theorem_7_4_cover s`.
  ext i
  simp [theorem_7_4_cover_mem_iff]

/-- Helper for Theorem 7.4: the weights on the suffix `{i ∈ C | s ≤ i}` sum to `μ_t - μ_s`. -/
theorem theorem_7_4_cover_suffix_sum_eq
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).sum weights =
      theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s := by
  have hs : s ≤ n := Nat.le_trans hst ht
  -- Rewrite the suffix as the difference between the long and short prefix covers.
  rw [theorem_7_4_cover_filter_ge_eq_sdiff]
  have hsum :
      (theorem_7_4_cover t \ theorem_7_4_cover s).sum weights +
          (theorem_7_4_cover s).sum weights =
        (theorem_7_4_cover t).sum weights := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff (theorem_7_4_cover_subset (n := n) hst) (f := weights))
  have hmu_prefix_eq :
      theorem_7_4_mu weights s hs s = theorem_7_4_mu weights t ht s := by
    -- The first `s` partial sums are independent of the larger ambient prefix length `t`.
    exact theorem_7_4_mu_prefix_eq weights hs ht hst
  -- Compare the two prefix sums using the canonical `μ`-normalization.
  rw [theorem_7_4_cover_sum_eq_mu weights t ht, theorem_7_4_cover_sum_eq_mu weights s hs] at hsum
  rw [hmu_prefix_eq] at hsum
  omega

/-- Helper for Theorem 7.4: the suffix `{i ∈ C | s ≤ i}` contains exactly the last `t - s`
cover indices. -/
theorem theorem_7_4_cover_suffix_card_eq
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).card = t - s := by
  have hs : s ≤ n := Nat.le_trans hst ht
  -- Rewrite the suffix as a set difference of the two prefix covers.
  rw [theorem_7_4_cover_filter_ge_eq_sdiff]
  -- The cardinals of the prefix covers are already known explicitly.
  rw [Finset.card_sdiff_of_subset (theorem_7_4_cover_subset (n := n) hst)]
  rw [theorem_7_4_cover_card (n := n) t ht, theorem_7_4_cover_card (n := n) s hs]

/-- Helper for Theorem 7.4: the explicit source witness is supported on the off-cover index `j`
and the cover suffix `{i ∈ C | s ≤ i}`. -/
private def theorem_7_4_suffixWitnessSupport
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Finset (Fin n) :=
  insert j ((theorem_7_4_cover t).filter fun i : Fin n ↦ s ≤ (i : ℕ))

/-- Helper for Theorem 7.4: the source suffix witness is the binary indicator of the support
`{j} ∪ {i ∈ C | s ≤ i}`. -/
private def theorem_7_4_suffixWitness
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Fin n → ℝ :=
  fun i ↦ if i ∈ theorem_7_4_suffixWitnessSupport t j s then 1 else 0

/-- Helper for Theorem 7.4: an off-cover index never belongs to the chosen cover suffix. -/
private theorem theorem_7_4_not_mem_cover_suffix
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ) :
    j ∉ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) := by
  -- The suffix is contained in the cover, so an off-cover index cannot lie in it.
  intro hjSuffix
  exact hj ((Finset.mem_filter.mp hjSuffix).1)

/-- Helper for Theorem 7.4: the indicator witness is the sum of the cover indicator on the suffix
and the singleton vector at the off-cover index. -/
private theorem theorem_7_4_suffixWitness_eq
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ) :
    theorem_7_4_suffixWitness t j s =
      cover_indicator ((theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))) +
        Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst i
    have hjsuffix :
        j ∉ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) :=
      theorem_7_4_not_mem_cover_suffix (j := j) hj s
    simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hjsuffix]
  · by_cases hi :
      i ∈ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
    · simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hi, hij]
    · simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hi, hij]

/-- Helper for Theorem 7.4: the witness weight is the off-cover weight plus the chosen suffix
weight. -/
private theorem theorem_7_4_suffixWitnessWeight
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    ∑ i, (weights i : ℝ) * theorem_7_4_suffixWitness t j s i =
      (weights j : ℝ) +
        (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) := by
  let suffix :=
    (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum :
      suffix.sum weights =
        theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s := by
    simpa [suffix] using theorem_7_4_cover_suffix_sum_eq weights t ht s hst
  -- Rewrite the witness as the sum of the suffix indicator and the singleton at `j`.
  calc
    ∑ i, (weights i : ℝ) * theorem_7_4_suffixWitness t j s i
      = (fun i ↦ (weights i : ℝ)) ⬝ᵥ theorem_7_4_suffixWitness t j s := by
          simp [dotProduct]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [theorem_7_4_suffixWitness_eq (j := j) hj s]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ cover_indicator suffix +
          (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = suffix.sum (fun i ↦ (weights i : ℝ)) + weights j := by
          rw [dotProduct_comm, coverIndicator_dot_eq_sum]
          simp
    _ = (((suffix.sum weights : ℕ) : ℝ)) + weights j := by
          rw [Nat.cast_sum]
    _ = (weights j : ℝ) + (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) := by
          rw [hsuffix_sum]
          ring

/-- Helper for Theorem 7.4: any coefficient vector that equals `1` on the cover evaluates on the
suffix witness as `α j + (t - s)`. -/
private theorem theorem_7_4_suffixWitnessCoeff
    (t : ℕ)
    (ht : t ≤ n)
    {α : Fin n → ℝ}
    (hαcover : ∀ i ∈ theorem_7_4_cover t, α i = 1)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    α ⬝ᵥ theorem_7_4_suffixWitness t j s = α j + (t - s : ℝ) := by
  let suffix :=
    (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum_one :
      suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hαcover i ((Finset.mem_filter.mp hi).1)
  calc
    α ⬝ᵥ theorem_7_4_suffixWitness t j s
      = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [theorem_7_4_suffixWitness_eq (j := j) hj s]
    _ = α ⬝ᵥ cover_indicator suffix + α ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = cover_indicator suffix ⬝ᵥ α + α j := by
          rw [dotProduct_comm]
          simp
    _ = suffix.sum α + α j := by
          rw [coverIndicator_dot_eq_sum]
    _ = (suffix.card : ℝ) + α j := by
          rw [hsuffix_sum_one]
          simp
    _ = α j + (t - s : ℝ) := by
          rw [theorem_7_4_cover_suffix_card_eq (n := n) t ht s hst, Nat.cast_sub hst]
          ring

/-- Helper for Theorem 7.4: the suffix witness is feasible whenever its normalized total weight
fits within the residual capacity. -/
private theorem theorem_7_4_suffixWitnessFeasible
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t)
    (hfeasible :
      (weights j : ℝ) +
        (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) ≤ capacity) :
    theorem_7_4_suffixWitness t j s ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- The witness is an indicator, so every coordinate is either `0` or `1`.
    intro i
    by_cases hi : i ∈ theorem_7_4_suffixWitnessSupport t j s
    · right
      simp [theorem_7_4_suffixWitness, hi]
    · left
      simp [theorem_7_4_suffixWitness, hi]
  · -- Rewrite the witness weight through the normalized suffix sum and apply the residual bound.
    rw [theorem_7_4_suffixWitnessWeight (weights := weights) (t := t) (ht := ht) (j := j) hj s hst]
    exact hfeasible

/-- Helper for Theorem 7.4: if the off-cover weight lies below `μ_s - λ`, then the suffix
starting at `s` together with the off-cover item fits within the knapsack capacity. -/
theorem theorem_7_4_suffixResidualLeCapacity
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    {s : ℕ}
    (hst : s ≤ t)
    (hμs :
      theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht s)
    (hupper :
      weights j ≤ theorem_7_4_mu weights t ht s -
        theorem_7_4_cover_excess weights capacity t ht) :
    weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s) ≤ capacity := by
  have hmu_t_ge_capacity : capacity ≤ theorem_7_4_mu weights t ht t := by
    have hcover : IsKnapsackCover weights capacity (theorem_7_4_cover t) := inferInstance
    have hcover_lt :
        capacity < (theorem_7_4_cover t).sum weights :=
      (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hcover
    rw [theorem_7_4_cover_sum_eq_mu weights t ht] at hcover_lt
    exact Nat.le_of_lt hcover_lt
  have hupper' :
      weights j + theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht s :=
    (Nat.le_sub_iff_add_le hμs).mp hupper
  have hs_le_n : s ≤ n := Nat.le_trans hst ht
  have hmu_prefix_le :
      theorem_7_4_mu weights t ht s ≤ theorem_7_4_mu weights t ht t := by
    have hprefix_sum_le :
        (theorem_7_4_cover (n := n) s).sum weights ≤
          (theorem_7_4_cover (n := n) t).sum weights :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (theorem_7_4_cover_subset (n := n) hst)
        (by
          intro i hi hino
          exact Nat.zero_le _)
    have hprefix_sum_eq :
        (theorem_7_4_cover (n := n) s).sum weights =
          theorem_7_4_mu weights t ht s := by
      calc
        (theorem_7_4_cover (n := n) s).sum weights
            = theorem_7_4_mu weights s hs_le_n s := by
                rw [theorem_7_4_cover_sum_eq_mu]
        _ = theorem_7_4_mu weights t ht s := by
              rw [theorem_7_4_mu_prefix_eq weights hs_le_n ht hst]
    have hcover_sum_eq :
        (theorem_7_4_cover (n := n) t).sum weights =
          theorem_7_4_mu weights t ht t := by
      rw [theorem_7_4_cover_sum_eq_mu]
    rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
    exact hprefix_sum_le
  -- Rewrite the residual-capacity inequality into the target suffix form once.
  have hupper'' :
      weights j + (theorem_7_4_mu weights t ht t - capacity) ≤ theorem_7_4_mu weights t ht s := by
    simpa [theorem_7_4_cover_excess] using hupper'
  omega

/-- Helper for Theorem 7.4: the exact interval hypothesis already forces the upper bound
`α j ≤ h` from validity. -/
theorem theorem_7_4_exact_interval_upper_bound
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {α : Fin n → ℝ}
    (hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_exact_interval_condition weights capacity t ht j h) :
    α j ≤ h := by
  have hαcover :
      ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  -- Move validity from the convex hull owner back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact is_valid_inequality_convexHull_iff.mp hαvalid_poly
  have hs : h + 1 ≤ t := Nat.succ_le_of_lt hh
  have hlam_le_mu :
      theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht (h + 1) := by
    -- Minimality bounds the cover excess by every cover weight, hence by the next partial sum.
    rw [theorem_7_4_mu_succ_of_lt weights t ht h hh]
    have hlam_le_weight :
        theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_cover_weight weights ht ⟨h, hh⟩ :=
      theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h, hh⟩
    omega
  have hfeasible_nat :
      weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 1)) ≤
        capacity :=
    theorem_7_4_suffixResidualLeCapacity
      weights capacity t ht hC hs hlam_le_mu hinterval.2
  have hfeasible :
      (weights j : ℝ) +
          (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 1) : ℕ) : ℝ)) ≤
        capacity := by
    exact_mod_cast hfeasible_nat
  have hx_mem :
      theorem_7_4_suffixWitness t j (h + 1) ∈
        zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) :=
    theorem_7_4_suffixWitnessFeasible weights capacity t ht hj (h + 1) hs hfeasible
  have hx_valid := hαvalid_set hx_mem
  have hcoeff := theorem_7_4_suffixWitnessCoeff t ht hαcover hj (h + 1) hs
  have hcover_rhs :
      cover_inequality_rhs (theorem_7_4_cover (n := n) t) = (t : ℝ) - 1 := by
    rw [cover_inequality_rhs_eq, theorem_7_4_cover_card (n := n) t ht]
  have hsucc_real :
      ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by
    norm_num
  -- Evaluate the witness and compare it with the cover right-hand side.
  rw [hcoeff, hcover_rhs] at hx_valid
  linarith [hsucc_real]

/-- Helper for Theorem 7.4: the boundary interval hypothesis still gives the upper bound
`α j ≤ h + 1` from validity. -/
theorem theorem_7_4_boundary_interval_upper_bound
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {α : Fin n → ℝ}
    (hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    α j ≤ h + 1 := by
  have hαcover :
      ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  -- Move validity from the convex hull owner back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact is_valid_inequality_convexHull_iff.mp hαvalid_poly
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hh) with hs | hs
  · have hs' : h + 2 ≤ t := Nat.succ_le_of_lt hs
    have hlam_le_mu :
        theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht (h + 2) := by
      -- In the strict case, the next cover weight still dominates the cover excess.
      rw [theorem_7_4_mu_succ_of_lt weights t ht (h + 1) hs]
      have hlam_le_weight :
          theorem_7_4_cover_excess weights capacity t ht ≤
            theorem_7_4_cover_weight weights ht ⟨h + 1, hs⟩ :=
        theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h + 1, hs⟩
      omega
    have hupper :
        weights j ≤ theorem_7_4_mu weights t ht (h + 2) -
          theorem_7_4_cover_excess weights capacity t ht := by
      have hmu_gap :
          theorem_7_4_mu weights t ht (h + 1) ≤
            theorem_7_4_mu weights t ht (h + 2) -
              theorem_7_4_cover_excess weights capacity t ht := by
        rw [theorem_7_4_mu_succ_of_lt weights t ht (h + 1) hs]
        have hlam_le_weight :
            theorem_7_4_cover_excess weights capacity t ht ≤
              theorem_7_4_cover_weight weights ht ⟨h + 1, hs⟩ :=
          theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h + 1, hs⟩
        omega
      have hweights_le_mu : weights j ≤ theorem_7_4_mu weights t ht (h + 1) :=
        Nat.le_of_lt hinterval.2
      exact le_trans hweights_le_mu hmu_gap
    have hfeasible_nat :
        weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 2)) ≤
          capacity :=
      theorem_7_4_suffixResidualLeCapacity
        weights capacity t ht hC hs' hlam_le_mu hupper
    have hfeasible :
        (weights j : ℝ) +
            (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 2) : ℕ) : ℝ)) ≤
          capacity := by
      exact_mod_cast hfeasible_nat
    have hx_mem :
        theorem_7_4_suffixWitness t j (h + 2) ∈
          zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) :=
      theorem_7_4_suffixWitnessFeasible weights capacity t ht hj (h + 2) hs' hfeasible
    have hx_valid := hαvalid_set hx_mem
    have hcoeff := theorem_7_4_suffixWitnessCoeff t ht hαcover hj (h + 2) hs'
    have hcover_rhs :
        cover_inequality_rhs (theorem_7_4_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, theorem_7_4_cover_card (n := n) t ht]
    have hsucc_real :
        ((h + 2 : ℕ) : ℝ) = (h : ℝ) + 2 := by
      norm_num
    -- The shifted suffix witness leaves room for at most the coefficient `h + 1`.
    rw [hcoeff, hcover_rhs] at hx_valid
    linarith [hsucc_real]
  · have hmu_t_ge_capacity : capacity ≤ theorem_7_4_mu weights t ht t := by
      have hcover : IsKnapsackCover weights capacity (theorem_7_4_cover t) := inferInstance
      have hcover_lt :
          capacity < (theorem_7_4_cover t).sum weights :=
        (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hcover
      rw [theorem_7_4_cover_sum_eq_mu weights t ht] at hcover_lt
      exact Nat.le_of_lt hcover_lt
    have hcapacity_eq :
        theorem_7_4_mu weights t ht (h + 1) -
            theorem_7_4_cover_excess weights capacity t ht =
          capacity := by
      have hs' : h + 1 = t := by
        simpa using hs
      rw [hs', theorem_7_4_cover_excess]
      omega
    have hcapacity_lt : capacity < weights j := by
      simpa [hcapacity_eq] using hinterval.1
    -- Route correction: the terminal boundary case is impossible because the open interval becomes
    -- `capacity < weights j < μ_t`, contradicting the standing item bound `weights j ≤ capacity`.
    exact (False.elim <| not_lt_of_ge (hweights_le j) hcapacity_lt)

/-- Helper for Theorem 7.4: every coordinate of a `0,1` knapsack polytope point lies in the unit
interval. -/
private theorem theorem_7_4_polytopeCoordBounds
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    {x : Fin n → ℝ}
    (hx :
      x ∈ zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
    (j : Fin n) :
    0 ≤ x j ∧ x j ≤ 1 := by
  have hlower_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (-Pi.single j (1 : ℝ))
        0 := by
    -- On binary points, the lower bound is just `-x_j ≤ 0`.
    intro y hy
    rcases (mem_zero_one_knapsack_set_iff.mp hy).1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hupper_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- On binary points, the upper bound is exactly `x_j ≤ 1`.
    intro y hy
    rcases (mem_zero_one_knapsack_set_iff.mp hy).1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hlower_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (-Pi.single j (1 : ℝ))
        0 := by
    -- Validity passes from the binary set to its convex hull owner.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hlower_set
  have hupper_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- Validity passes from the binary set to its convex hull owner.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hupper_set
  refine ⟨?_, ?_⟩
  · -- Evaluate the lower-bound inequality at `x`.
    have hxlower := hlower_poly hx
    simpa [dotProduct, Pi.single_apply] using hxlower
  · -- Evaluate the upper-bound inequality at `x`.
    have hxupper := hupper_poly hx
    simpa [dotProduct, Pi.single_apply] using hxupper

/-- Helper for Theorem 7.4: increasing an off-cover coefficient only changes the lifted cover
coefficient vector by a singleton at that coordinate. -/
private theorem theorem_7_4_updatedLiftedCoeff_eq
    {t : ℕ}
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (σ : ℝ) :
    lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ) =
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α +
        Pi.single j (σ - α j) := by
  -- Route correction: keep the comparison on the original owner and isolate the coefficient
  -- update as a single-coordinate perturbation.
  funext i
  by_cases hij : i = j
  · subst i
    simp [lifted_cover_inequality_coeff, hj]
  · by_cases hi : i ∈ theorem_7_4_cover t
    · simp [lifted_cover_inequality_coeff, hi, hij]
    · simp [lifted_cover_inequality_coeff, hi, hij, Function.update]

/-- Helper for Theorem 7.4: if a strictly larger off-cover coefficient is still valid, every point
on the old lifted-cover face has zero in that coordinate. -/
private theorem theorem_7_4_faceCoordinateZero_of_strict_update
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {σ : ℝ}
    (hασ : α j < σ)
    (hvalidσ :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ))
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t))) :
    ∀ ⦃x : Fin n → ℝ⦄,
      x ∈ lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α →
        x j = 0 := by
  intro x hx
  rcases (mem_face_set_iff.mp (by simpa [lifted_cover_face] using hx)) with ⟨hxP, hxEq⟩
  have hxUpdated : (lifted_cover_inequality_coeff
      (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x ≤
        cover_inequality_rhs (theorem_7_4_cover t) :=
    hvalidσ hxP
  have hxNonneg : 0 ≤ x j :=
    (theorem_7_4_polytopeCoordBounds weights capacity hxP j).1
  have hxUpdatedEq :
      (lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          (σ - α j) * x j := by
    -- Expand the singleton perturbation and evaluate its dot product.
    rw [theorem_7_4_updatedLiftedCoeff_eq (t := t) (α := α) (j := j) hj σ, add_dotProduct]
    simp [dotProduct, Pi.single_apply]
  have hdiffPos : 0 < σ - α j := sub_pos.mpr hασ
  rw [hxUpdatedEq, hxEq] at hxUpdated
  rcases lt_or_eq_of_le hxNonneg with hxPos | hxZero
  · -- A positive `x_j` would make the stricter valid inequality exceed the old face value.
    have hprodPos : 0 < (σ - α j) * x j := mul_pos hdiffPos hxPos
    linarith
  · exact hxZero.symm

/-- Helper for Theorem 7.4: once the stricter updated inequality is valid, the old lifted-cover
face sits inside the updated face. -/
private theorem theorem_7_4_faceSubset_of_strict_update
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {σ : ℝ}
    (hασ : α j < σ)
    (hvalidσ :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ))
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t))) :
    lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α ⊆
      lifted_cover_face
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        (theorem_7_4_cover t)
        (Function.update α j σ) := by
  intro x hx
  rcases (mem_face_set_iff.mp (by simpa [lifted_cover_face] using hx)) with ⟨hxP, hxEq⟩
  have hxj0 :
      x j = 0 :=
    theorem_7_4_faceCoordinateZero_of_strict_update
      weights capacity t hj hασ hvalidσ hx
  have hxUpdatedEq :
      (lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          (σ - α j) * x j := by
    -- The singleton perturbation vanishes because `x_j = 0` on the old face.
    rw [theorem_7_4_updatedLiftedCoeff_eq (t := t) (α := α) (j := j) hj σ, add_dotProduct]
    simp [dotProduct, Pi.single_apply]
  -- Reuse the old face equality after deleting the zero pivot contribution.
  refine (mem_face_set_iff.mpr ?_)
  refine ⟨hxP, ?_⟩
  rw [hxUpdatedEq, hxEq, hxj0]
  ring

/-- Theorem 7.4 (1). Let
`K := {x ∈ {0,1}^n | ∑ j, a_j x_j ≤ b}`, assume `b ≥ a_j > 0` for all `j`, let
`C = {1, ..., t}` be a minimal cover with ordered cover weights `a₁ ≥ a₂ ≥ ··· ≥ a_t`, and let
`∑_{j ∈ C} x_j + ∑_{j ∉ C} α_j x_j ≤ |C| - 1` be a facet-defining lifting of the cover
inequality. If `μ_h ≤ a_j ≤ μ_{h+1} - λ` for some `j ∉ C` and `h < t`, then `α_j = h`. -/
theorem theorem_7_4_forces_exact_lifting_coefficient
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {α : Fin n → ℝ}
    (hαfacet : α ∈ theorem_7_4_facet_defining_liftings weights capacity t)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_exact_interval_condition weights capacity t ht j h) :
    α j = h :=
  by
  have hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t) :=
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hαfacet).1
  have hupper : α j ≤ h := by
    -- The exact interval already supplies the source upper bound.
    exact theorem_7_4_exact_interval_upper_bound weights capacity t ht hC hαvalid hj hh hinterval
  -- TODO: use Proposition 7.2 after swapping `j` to the last coordinate to prove the reverse
  -- inequality `h ≤ α j`, then combine it with the upper bound above.
  sorry

/-- Theorem 7.4 (2). Under the same hypotheses as Theorem 7.4, if
`μ_{h+1} - λ < a_j < μ_{h+1}` for some `j ∉ C` and `h < t`, then the lifting coefficient lies in
the interval `h ≤ α_j ≤ h + 1`. -/
theorem theorem_7_4_bounds_lifting_coefficient_on_boundary_interval
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {α : Fin n → ℝ}
    (hαfacet : α ∈ theorem_7_4_facet_defining_liftings weights capacity t)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    (h : ℝ) ≤ α j ∧ α j ≤ h + 1 :=
  by
  have hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t) :=
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hαfacet).1
  have hupper : α j ≤ h + 1 := by
    -- The shifted suffix witness gives the source upper bound on the boundary interval.
    exact
      theorem_7_4_boundary_interval_upper_bound
        weights capacity t ht hweights_le hC hαvalid hj hh hinterval
  -- TODO: obtain the lower bound `(h : ℝ) ≤ α j` from the bar-`x` witness built out of a
  -- maximizing slice point after the same swap-to-last-coordinate reduction as in part (1).
  sorry

/-- Theorem 7.4 (3). Under the same hypotheses as Theorem 7.4, if
`μ_{h+1} - λ < a_j < μ_{h+1}` for some `j ∉ C` and `h < t`, then there exists a facet-defining
lifting of the form `(7.5)` whose coefficient on `x_j` is `h + 1`. -/
theorem theorem_7_4_boundary_interval_realizes_upper_lifting_coefficient
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    ∃ α' : Fin n → ℝ,
      α' ∈ theorem_7_4_facet_defining_liftings weights capacity t ∧
        α' j = h + 1 :=
  by
  -- TODO: after transporting `j` to the last coordinate, lift that variable first and apply the
  -- Proposition 7.2 facet-preservation step; the boundary slice should force the new coefficient
  -- to be `h + 1`, and then the resulting facet can be transported back.
  sorry

end Theorem74
