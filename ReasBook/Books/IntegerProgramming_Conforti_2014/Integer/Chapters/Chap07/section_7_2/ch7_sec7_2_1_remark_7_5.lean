import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2

open scoped BigOperators Matrix

section Remark75

variable {n : ℕ}

/-- The prefix cover `{1, ..., t}` from the Theorem 7.4 setup, represented on `Fin n` by the
indices `< t`. -/
def remark_7_5_cover
    (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i < t

/-- Membership in `remark_7_5_cover t` means that the index lies among the first `t`
positions. -/
@[simp] theorem remark_7_5_cover_mem_iff
    {t : ℕ}
    {j : Fin n} :
    j ∈ remark_7_5_cover t ↔ j < t := by
  simp [remark_7_5_cover]

/-- The ordered cover weights `a₁, ..., a_t` from the Theorem 7.4 setup, reindexed as a function
on `Fin t`. -/
def remark_7_5_cover_weight
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Fin t → ℕ :=
  fun i ↦ weights (i.castLE ht)

/-- `remark_7_5_cover_weights_descending weights ht` records the ordering
`a₁ ≥ a₂ ≥ ··· ≥ a_t` from the Theorem 7.4 hypotheses. -/
def remark_7_5_cover_weights_descending
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Prop :=
  Antitone (remark_7_5_cover_weight weights ht)

/-- The partial sums `μ_h = ∑_{ℓ=1}^h a_ℓ` from the Theorem 7.4 setup, extended to all natural
indices by summing the first `h` ordered cover weights among the first `t` positions. -/
def remark_7_5_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) : ℕ → ℕ :=
  fun h ↦
    (Finset.range h).sum fun ℓ ↦
      if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0

/-- Helper for Remark 7.5: the prefix cover `{i | i < t}` is exactly the image of `Fin t` in
`Fin n` under `Fin.castLE ht`. -/
theorem remark_7_5_cover_eq_castLEImage
    (t : ℕ)
    (ht : t ≤ n) :
    remark_7_5_cover (n := n) t =
      (Finset.univ : Finset (Fin t)).map
        ⟨fun i ↦ i.castLE ht, by
          intro a b hab
          exact Fin.ext (congrArg (fun x : Fin n ↦ x.1) hab)
        ⟩ := by
  ext j
  constructor
  · intro hj
    rw [Finset.mem_map]
    refine ⟨⟨j, remark_7_5_cover_mem_iff.mp hj⟩, by simp, ?_⟩
    simp
  · intro hj
    rw [Finset.mem_map] at hj
    rcases hj with ⟨i, -, hij⟩
    subst hij
    simp [remark_7_5_cover]

/-- Helper for Remark 7.5: summing the weights over the prefix cover gives the partial sum
`μ_t`. -/
theorem remark_7_5_cover_sum_eq_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    (remark_7_5_cover t).sum weights = remark_7_5_mu weights t ht t := by
  let g : ℕ → ℕ := fun ℓ ↦
    if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0
  -- Reindex the prefix cover by the canonical embedding `Fin t ↪ Fin n`.
  rw [remark_7_5_cover_eq_castLEImage (n := n) t ht]
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
    _ = remark_7_5_mu weights t ht t := by
          simp [g, remark_7_5_mu]

/-- Helper for Remark 7.5: evaluating `μ_s` inside a larger Theorem 7.4 context agrees with
evaluating the same prefix sum in the shorter prefix problem. -/
theorem remark_7_5_mu_prefix_eq
    (weights : Fin n → ℕ)
    {s t : ℕ}
    (hsn : s ≤ n)
    (htn : t ≤ n)
    (hst : s ≤ t) :
    remark_7_5_mu weights s hsn s = remark_7_5_mu weights t htn s := by
  -- Every summand in `range s` lies below both cutoffs `s` and `t`.
  unfold remark_7_5_mu
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hℓs : ℓ < s := Finset.mem_range.mp hℓ
  have hℓt : ℓ < t := Nat.lt_of_lt_of_le hℓs hst
  simp [hℓs, hℓt]

/-- The cover excess `λ = μ_t - b` coming from the Theorem 7.4 setup. -/
def remark_7_5_cover_excess
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) : ℕ :=
  remark_7_5_mu weights t ht t - capacity

/-- `remark_7_5_theorem_7_4_context weights capacity C μ λ` packages the source-faithful
background from Theorem 7.4 that Remark 7.5 refers back to: `C` is the distinguished prefix
minimal cover, the cover weights are ordered, every item weight lies in `(0, capacity]`, `μ` is
the associated partial-sum sequence, and `λ` is the cover excess. -/
def remark_7_5_theorem_7_4_context
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (lam : ℕ) : Prop :=
  ∃ t, ∃ ht : t ≤ n,
    C = remark_7_5_cover t ∧
      remark_7_5_cover_weights_descending weights ht ∧
      (∀ j, 0 < weights j) ∧
      (∀ j, weights j ≤ capacity) ∧
      IsMinimalKnapsackCover weights capacity C ∧
      μ = remark_7_5_mu weights t ht ∧
      lam = remark_7_5_cover_excess weights capacity t ht

/-- The coefficient vector from Remark 7.5: it has value `1` on the cover `C` and value `h(j)` on
the complement `N \ C`. -/
abbrev remark_7_5_lifting_coeff
    (C : Finset (Fin n))
    (h : Fin n → ℕ) : Fin n → ℝ :=
  lifted_cover_inequality_coeff C fun j ↦ (h j : ℝ)

/-- Evaluating `remark_7_5_lifting_coeff C h` at `j` recovers the piecewise coefficient formula
from Remark 7.5. -/
theorem remark_7_5_lifting_coeff_apply
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    (j : Fin n) :
    remark_7_5_lifting_coeff C h j = if j ∈ C then 1 else (h j : ℝ) := by
  exact lifted_cover_inequality_coeff_apply C (fun k ↦ (h k : ℝ)) j

/-- On the cover `C`, the coefficient vector from Remark 7.5 has coefficient `1`. -/
@[simp] theorem remark_7_5_lifting_coeff_apply_of_mem
    {C : Finset (Fin n)}
    {h : Fin n → ℕ}
    {j : Fin n}
    (hj : j ∈ C) :
    remark_7_5_lifting_coeff C h j = 1 := by
  simp [remark_7_5_lifting_coeff, hj]

/-- Off the cover `C`, the coefficient vector from Remark 7.5 has coefficient `h(j)`. -/
@[simp] theorem remark_7_5_lifting_coeff_apply_of_not_mem
    {C : Finset (Fin n)}
    {h : Fin n → ℕ}
    {j : Fin n}
    (hj : j ∉ C) :
    remark_7_5_lifting_coeff C h j = (h j : ℝ) := by
  simp [remark_7_5_lifting_coeff, hj]

/-- Dotting the coefficient vector from Remark 7.5 with `x` gives the source formula
`∑_{j ∈ C} x_j + ∑_{j ∈ N \ C} h(j) x_j`. -/
theorem remark_7_5_lifting_coeff_dotProduct
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    (x : Fin n → ℝ) :
    remark_7_5_lifting_coeff C h ⬝ᵥ x =
      Finset.sum C (fun j ↦ x j) +
        Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) := by
  -- This is exactly the generic lifted-cover dot-product identity specialized to `α j = h j`.
  simpa [remark_7_5_lifting_coeff] using
    lifted_cover_inequality_coeff_dotProduct C (fun j ↦ (h j : ℝ)) x

/-- `remark_7_5_interval_indices weights C μ h` records the interval condition
`μ_{h(j)} ≤ a_j < μ_{h(j)+1}` for every index `j` outside the cover `C`. -/
def remark_7_5_interval_indices
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ) : Prop :=
  ∀ j, j ∉ C → μ (h j) ≤ weights j ∧ weights j < μ (h j + 1)

/-- Expanding `remark_7_5_interval_indices weights C μ h` recovers the interval-index condition
from Remark 7.5. -/
theorem remark_7_5_interval_indices_iff
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ) :
    remark_7_5_interval_indices weights C μ h ↔
      ∀ j, j ∉ C → μ (h j) ≤ weights j ∧ weights j < μ (h j + 1) :=
  Iff.rfl

/-- `remark_7_5_strong_upper_bound weights C μ h λ` records the strengthened hypothesis
`a_j ≤ μ_{h(j)+1} - λ` for every `j ∈ N \ C`. -/
def remark_7_5_strong_upper_bound
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ) : Prop :=
  ∀ j, j ∉ C → weights j ≤ μ (h j + 1) - lam

/-- Expanding `remark_7_5_strong_upper_bound weights C μ h λ` recovers the strengthened upper
bound hypothesis from Remark 7.5. -/
theorem remark_7_5_strong_upper_bound_iff
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ) :
    remark_7_5_strong_upper_bound weights C μ h lam ↔
      ∀ j, j ∉ C → weights j ≤ μ (h j + 1) - lam :=
  Iff.rfl

/-- Helper for Remark 7.5: a shorter prefix cover is contained in a longer one. -/
theorem remark_7_5_cover_subset
    {s t : ℕ}
    (hst : s ≤ t) :
    remark_7_5_cover (n := n) s ⊆ remark_7_5_cover t := by
  -- Membership is just the corresponding strict inequality on indices.
  intro i hi
  exact remark_7_5_cover_mem_iff.mpr
    (Nat.lt_of_lt_of_le (remark_7_5_cover_mem_iff.mp hi) hst)

/-- Helper for Remark 7.5: the prefix cover `{i | i < t}` has exactly `t` elements when
`t ≤ n`. -/
theorem remark_7_5_cover_card
    (t : ℕ)
    (ht : t ≤ n) :
    (remark_7_5_cover (n := n) t).card = t := by
  -- Reindex the prefix cover by `Fin t`.
  rw [remark_7_5_cover_eq_castLEImage (n := n) t ht]
  simp

/-- Helper for Remark 7.5: filtering the prefix cover by `s ≤ i` removes the shorter prefix
`remark_7_5_cover s`. -/
theorem remark_7_5_cover_filter_ge_eq_sdiff
    (t s : ℕ) :
    (remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) =
      remark_7_5_cover t \ remark_7_5_cover s := by
  -- On the prefix cover, `s ≤ i` is equivalent to `i ∉ remark_7_5_cover s`.
  ext i
  simp [remark_7_5_cover_mem_iff]

/-- Helper for Remark 7.5: the weights on the suffix `{i ∈ C | s ≤ i}` sum to `μ_t - μ_s`. -/
theorem remark_7_5_cover_suffix_sum_eq
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).sum weights =
      remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s := by
  -- Rewrite the suffix as a set difference and compare the two prefix sums.
  rw [remark_7_5_cover_filter_ge_eq_sdiff]
  have hsubset : remark_7_5_cover (n := n) s ⊆ remark_7_5_cover t :=
    remark_7_5_cover_subset (n := n) hst
  have hsdiff :
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
          (remark_7_5_cover s).sum weights =
        (remark_7_5_cover t).sum weights := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff hsubset (f := weights))
  have hs_sum :
      (remark_7_5_cover s).sum weights = remark_7_5_mu weights t ht s := by
    calc
      (remark_7_5_cover s).sum weights = remark_7_5_mu weights s (Nat.le_trans hst ht) s := by
        rw [remark_7_5_cover_sum_eq_mu]
      _ = remark_7_5_mu weights t ht s := by
        rw [remark_7_5_mu_prefix_eq weights (Nat.le_trans hst ht) ht hst]
  have hsdiff' :
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
          remark_7_5_mu weights t ht s =
        remark_7_5_mu weights t ht t := by
    calc
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights + remark_7_5_mu weights t ht s
          = (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
              (remark_7_5_cover s).sum weights := by rw [← hs_sum]
      _ = (remark_7_5_cover t).sum weights := hsdiff
      _ = remark_7_5_mu weights t ht t := by rw [remark_7_5_cover_sum_eq_mu]
  exact Nat.eq_sub_of_add_eq hsdiff'

/-- Helper for Remark 7.5: the suffix `{i ∈ C | s ≤ i}` has exactly `t - s` elements. -/
theorem remark_7_5_cover_suffix_card
    (t s : ℕ)
    (ht : t ≤ n)
    (hst : s ≤ t) :
    ((remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).card = t - s := by
  -- Rewrite the suffix as a difference of the two prefix covers and compare cardinalities.
  rw [remark_7_5_cover_filter_ge_eq_sdiff]
  rw [Finset.card_sdiff_of_subset (remark_7_5_cover_subset (n := n) hst)]
  rw [remark_7_5_cover_card (n := n) t ht, remark_7_5_cover_card (n := n) s (Nat.le_trans hst ht)]

/-- Helper for Remark 7.5: the explicit suffix witness is supported on the off-cover index `j`
and the cover suffix `{i ∈ C | s ≤ i}`. -/
private def remark_7_5_suffixWitnessSupport
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Finset (Fin n) :=
  insert j ((remark_7_5_cover t).filter fun i : Fin n ↦ s ≤ (i : ℕ))

/-- Helper for Remark 7.5: the canonical suffix witness is the binary indicator of the support
`{j} ∪ {i ∈ C | s ≤ i}` used in the interval and upper-bound arguments. -/
private def remark_7_5_suffixWitness
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Fin n → ℝ :=
  fun i ↦ if i ∈ remark_7_5_suffixWitnessSupport t j s then 1 else 0

/-- Helper for Remark 7.5: an off-cover index never belongs to the chosen cover suffix. -/
private theorem remark_7_5_not_mem_cover_suffix
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ) :
    j ∉ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) := by
  -- The suffix stays inside the cover, so an off-cover pivot cannot lie in it.
  intro hjSuffix
  exact hj ((Finset.mem_filter.mp hjSuffix).1)

/-- Helper for Remark 7.5: the suffix witness splits as the cover-suffix indicator plus the
singleton vector at the off-cover pivot. -/
private theorem remark_7_5_suffixWitness_eq
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ) :
    remark_7_5_suffixWitness t j s =
      cover_indicator ((remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))) +
        Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst i
    -- On the pivot coordinate, only the singleton term survives.
    have hjsuffix :
        j ∉ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) :=
      remark_7_5_not_mem_cover_suffix (j := j) hj s
    simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hjsuffix]
  · by_cases hi :
      i ∈ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
    · -- On the suffix, both descriptions are the same indicator value.
      simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hi, hij]
    · -- Away from the suffix and the pivot, both sides vanish.
      simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hi, hij]

/-- Helper for Remark 7.5: the suffix witness weight equals the pivot weight plus the chosen
cover-suffix weight `μ_t - μ_s`. -/
private theorem remark_7_5_suffixWitnessWeight
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    ∑ i, (weights i : ℝ) * remark_7_5_suffixWitness t j s i =
      (weights j : ℝ) +
        (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) := by
  let suffix :=
    (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum :
      suffix.sum weights =
        remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s := by
    simpa [suffix] using remark_7_5_cover_suffix_sum_eq weights t ht s hst
  -- Rewrite the witness through the suffix indicator plus the singleton pivot.
  calc
    ∑ i, (weights i : ℝ) * remark_7_5_suffixWitness t j s i
      = (fun i ↦ (weights i : ℝ)) ⬝ᵥ remark_7_5_suffixWitness t j s := by
          simp [dotProduct]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [remark_7_5_suffixWitness_eq (j := j) hj s]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ cover_indicator suffix +
          (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = suffix.sum (fun i ↦ (weights i : ℝ)) + weights j := by
          rw [dotProduct_comm, coverIndicator_dot_eq_sum]
          simp
    _ = (((suffix.sum weights : ℕ) : ℝ)) + weights j := by
          rw [Nat.cast_sum]
    _ = (weights j : ℝ) +
          (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) := by
          rw [hsuffix_sum]
          ring

/-- Helper for Remark 7.5: any coefficient vector that is `1` on the cover evaluates on the
suffix witness as the pivot coefficient plus the suffix cardinality `t - s`. -/
private theorem remark_7_5_suffixWitnessCoeff
    (t : ℕ)
    (ht : t ≤ n)
    {α : Fin n → ℝ}
    (hαcover : ∀ i ∈ remark_7_5_cover t, α i = 1)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    α ⬝ᵥ remark_7_5_suffixWitness t j s = α j + (t - s : ℝ) := by
  let suffix :=
    (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum_one :
      suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
    -- On the suffix, the lifting agrees with the base cover coefficient.
    apply Finset.sum_congr rfl
    intro i hi
    exact hαcover i ((Finset.mem_filter.mp hi).1)
  calc
    α ⬝ᵥ remark_7_5_suffixWitness t j s
      = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [remark_7_5_suffixWitness_eq (j := j) hj s]
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
          rw [remark_7_5_cover_suffix_card (n := n) t s ht hst, Nat.cast_sub hst]
          ring

/-- Helper for Remark 7.5: once the normalized residual-weight inequality is known, the suffix
witness is a feasible binary knapsack point. -/
private theorem remark_7_5_suffixWitnessFeasible
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t)
    (hfeasible :
      (weights j : ℝ) +
        (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) ≤ capacity) :
    remark_7_5_suffixWitness t j s ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- The witness is an indicator, so every coordinate is binary.
    intro i
    by_cases hi : i ∈ remark_7_5_suffixWitnessSupport t j s
    · right
      simp [remark_7_5_suffixWitness, hi]
    · left
      simp [remark_7_5_suffixWitness, hi]
  · -- The normalized weight formula reduces feasibility to the supplied residual bound.
    rw [remark_7_5_suffixWitnessWeight (weights := weights) (t := t) (ht := ht) (j := j) hj s hst]
    exact hfeasible

/-- The valid liftings of the minimal cover inequality attached to `C` are the coefficient vectors
that keep coefficient `1` on `C` and yield a valid inequality for the `0,1` knapsack polytope. -/
def valid_liftings_of_minimal_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {α |
    (∀ j ∈ C, α j = 1) ∧
      is_valid_inequality
        (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs C)}

/-- Membership in `valid_liftings_of_minimal_cover_inequality weights capacity C` means keeping
the cover coefficients equal to `1` and being valid for the knapsack polytope. -/
theorem mem_valid_liftings_of_minimal_cover_inequality_iff
    {weights : Fin n → ℕ}
    {capacity : ℕ}
    {C : Finset (Fin n)}
    {α : Fin n → ℝ} :
    α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ↔
      (∀ j ∈ C, α j = 1) ∧
        is_valid_inequality
          (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
          α
          (cover_inequality_rhs C) :=
  Iff.rfl

/-- The facet-defining liftings of the minimal cover inequality attached to `C` are the valid
liftings whose coefficient vector also belongs to the canonical cover-lifting facet owner. -/
def facet_defining_liftings_of_minimal_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {α |
    α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ∧
      α ∈ facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C}

/-- Membership in `facet_defining_liftings_of_minimal_cover_inequality weights capacity C` means
being a valid lifting and belonging to the canonical facet-defining cover-lifting owner. -/
theorem mem_facet_defining_liftings_of_minimal_cover_inequality_iff
    {weights : Fin n → ℕ}
    {capacity : ℕ}
    {C : Finset (Fin n)}
    {α : Fin n → ℝ} :
    α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C ↔
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ∧
        α ∈ facet_defining_liftings_of_cover_inequality
          (fun j ↦ (weights j : ℝ))
          (capacity : ℝ)
          C :=
  Iff.rfl

/-- Helper for Remark 7.5: every valid lifting already agrees with the remark coefficient vector
on the cover coordinates. -/
private theorem eqOnCoverOfMemValidLiftings
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    {α : Fin n → ℝ}
    (hα : α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∈ C) :
    α j = remark_7_5_lifting_coeff C h j := by
  have hcover : α j = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).1 j hj
  -- Both sides normalize to the base cover coefficient `1`.
  simpa [remark_7_5_lifting_coeff_apply_of_mem hj] using hcover

/-- Helper for Remark 7.5: the Theorem 7.4 context supplies the minimal-cover structure together
with the base cover validity and restricted-facet facts used by the sequential lifting route. -/
private theorem remark_7_5_baseFacetData
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam) :
    IsMinimalKnapsackCover weights capacity C ∧
      is_valid_inequality
        (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
        (cover_indicator C)
        (cover_inequality_rhs C) ∧
      facet_defining_inequality
        (cover_restricted_polytope weights capacity C)
        (cover_indicator C)
        (cover_inequality_rhs C) := by
  rcases hctx with ⟨_, _, _, _, _, hweights_le, hCmin, _, _⟩
  have hcover : IsKnapsackCover weights capacity C := inferInstance
  refine ⟨hCmin, ?_, ?_⟩
  · -- Every knapsack cover inequality is valid on the ambient knapsack polytope.
    exact coverInequality_validOnKnapsackPolytope weights capacity C hcover
  · -- Minimality upgrades the restricted cover face to the facet-defining owner.
    exact
      (cover_inequality_facet_defining_iff_minimal_cover
        weights capacity hweights_le C hcover).2 hCmin

/-- Helper for Remark 7.5: validity on the binary knapsack set transfers unchanged to its convex
hull, namely the public knapsack polytope owner. -/
private theorem remark_7_5_polytopeValid_of_setValid
    (a : Fin n → ℝ)
    (b : ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (hvalid : is_valid_inequality (zero_one_knapsack_set a b) α β) :
    is_valid_inequality (zero_one_knapsack_polytope a b) α β := by
  -- The polytope is defined as the convex hull of the binary feasible set.
  rw [zero_one_knapsack_polytope_eq_convexHull]
  exact (is_valid_inequality_convexHull_iff).2 hvalid

/-- Helper for Remark 7.5: under the strengthened upper bound, every valid lifting coefficient at
an off-cover index is bounded above by the prescribed interval index. -/
private theorem remark_7_5_coeff_le_of_mem_validLifting
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∉ C) :
    α j ≤ h j := by
  rcases hctx with ⟨t, ht, rfl, hdescending, hweights_pos, hweights_le, hCmin, rfl, rfl⟩
  have hα_cover :
      ∀ i ∈ remark_7_5_cover (n := n) t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (remark_7_5_cover (n := n) t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).2
  -- First move the valid inequality from the convex hull back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (remark_7_5_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact (is_valid_inequality_convexHull_iff.mp hαvalid_poly)
  by_cases hs : h j + 1 ≤ t
  · let suffix : Finset (Fin n) :=
      (remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ h j + 1 ≤ (i : ℕ))
    let x : Fin n → ℝ := cover_indicator suffix + Pi.single j (1 : ℝ)
    have hj_suffix : j ∉ suffix := by
      intro hj'
      exact hj ((Finset.mem_filter.mp hj').1)
    -- The suffix witness is binary and uses exactly the last `t - (h j + 1)` cover indices plus
    -- the off-cover variable `j`.
    have hx_mem : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
      rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        by_cases hij : i = j
        · subst hij
          right
          simp [x, cover_indicator, hj_suffix]
        · by_cases hi_suffix : i ∈ suffix
          · right
            simp [x, cover_indicator, hi_suffix, hij]
          · left
            simp [x, cover_indicator, hi_suffix, hij]
      · have hupperj : weights j ≤ remark_7_5_mu weights t ht (h j + 1) -
            remark_7_5_cover_excess weights capacity t ht :=
          hupper j hj
        have hsuffix_sum :
            suffix.sum weights =
              remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1) := by
          simpa [suffix] using
            remark_7_5_cover_suffix_sum_eq weights t ht (h j + 1) hs
        have hsuffix_le_capacity :
            suffix.sum weights ≤ capacity := by
          have ht_pos : 0 < t := Nat.lt_of_lt_of_le (Nat.succ_pos _) hs
          let r0 : Fin t := ⟨0, ht_pos⟩
          have hr0_mem : r0.castLE ht ∈ remark_7_5_cover (n := n) t := by
            simp [remark_7_5_cover]
          have hsuffix_subset :
              suffix ⊆ (remark_7_5_cover (n := n) t).erase (r0.castLE ht) := by
            intro i hi
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro hir0
              have hi_ge : h j + 1 ≤ (i : ℕ) := (Finset.mem_filter.mp hi).2
              have hir0_zero : (i : ℕ) = 0 := congrArg Fin.val hir0
              omega
            · exact (Finset.mem_filter.mp hi).1
          have hsuffix_le_erase :
              suffix.sum weights ≤ ((remark_7_5_cover (n := n) t).erase (r0.castLE ht)).sum weights :=
            Finset.sum_le_sum_of_subset_of_nonneg hsuffix_subset (by
              intro i hi hino
              exact Nat.zero_le _)
          exact le_trans hsuffix_le_erase (hCmin.erase_sum_le (r0.castLE ht) hr0_mem)
        have hweight_nat :
            weights j + suffix.sum weights ≤ capacity := by
          have hlam_le_mu :
              remark_7_5_mu weights t ht t - capacity ≤
                remark_7_5_mu weights t ht (h j + 1) := by
            rw [hsuffix_sum] at hsuffix_le_capacity
            omega
          have hupperj' :
              weights j ≤
                remark_7_5_mu weights t ht (h j + 1) -
                  (remark_7_5_mu weights t ht t - capacity) := by
            simpa [remark_7_5_cover_excess] using hupperj
          have hupperj_add :
              weights j + (remark_7_5_mu weights t ht t - capacity) ≤
                remark_7_5_mu weights t ht (h j + 1) :=
            (Nat.le_sub_iff_add_le hlam_le_mu).mp hupperj'
          have hmu_t_ge_capacity :
              capacity ≤ remark_7_5_mu weights t ht t := by
            have hcover : IsKnapsackCover weights capacity (remark_7_5_cover (n := n) t) :=
              inferInstance
            have hcover_lt :
                capacity < (remark_7_5_cover (n := n) t).sum weights :=
              (isKnapsackCover_iff weights capacity (remark_7_5_cover (n := n) t)).mp hcover
            rw [remark_7_5_cover_sum_eq_mu weights t ht] at hcover_lt
            exact Nat.le_of_lt hcover_lt
          have hupperj_total :
              weights j + remark_7_5_mu weights t ht t ≤
                remark_7_5_mu weights t ht (h j + 1) + capacity := by
            have hupperj_add_capacity := Nat.add_le_add_right hupperj_add capacity
            calc
              weights j + remark_7_5_mu weights t ht t
                  = weights j +
                      ((remark_7_5_mu weights t ht t - capacity) + capacity) := by
                        rw [Nat.sub_add_cancel hmu_t_ge_capacity]
              _ = (weights j + (remark_7_5_mu weights t ht t - capacity)) + capacity := by
                    omega
              _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_add_capacity
          have hmu_prefix_le :
              remark_7_5_mu weights t ht (h j + 1) ≤ remark_7_5_mu weights t ht t := by
            have hs_le_n : h j + 1 ≤ n := Nat.le_trans hs ht
            have hprefix_sum_le :
                (remark_7_5_cover (n := n) (h j + 1)).sum weights ≤
                  (remark_7_5_cover (n := n) t).sum weights :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (remark_7_5_cover_subset (n := n) hs)
                (by
                  intro i hi hino
                  exact Nat.zero_le _)
            have hprefix_sum_eq :
                (remark_7_5_cover (n := n) (h j + 1)).sum weights =
                  remark_7_5_mu weights t ht (h j + 1) := by
              calc
                (remark_7_5_cover (n := n) (h j + 1)).sum weights
                    = remark_7_5_mu weights (h j + 1) hs_le_n (h j + 1) := by
                        rw [remark_7_5_cover_sum_eq_mu]
                _ = remark_7_5_mu weights t ht (h j + 1) := by
                      rw [remark_7_5_mu_prefix_eq weights hs_le_n ht hs]
            have hcover_sum_eq :
                (remark_7_5_cover (n := n) t).sum weights =
                  remark_7_5_mu weights t ht t := by
              rw [remark_7_5_cover_sum_eq_mu]
            rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
            exact hprefix_sum_le
          have hmu_split :
              remark_7_5_mu weights t ht t =
                remark_7_5_mu weights t ht (h j + 1) + suffix.sum weights := by
            rw [hsuffix_sum]
            omega
          have hweight_nat' :
              weights j + suffix.sum weights ≤
                capacity := by
            have hcombined :
                weights j + suffix.sum weights +
                    remark_7_5_mu weights t ht (h j + 1) ≤
                  remark_7_5_mu weights t ht (h j + 1) + capacity := by
              calc
                weights j + suffix.sum weights +
                    remark_7_5_mu weights t ht (h j + 1)
                    = weights j + remark_7_5_mu weights t ht t := by
                        rw [hmu_split]
                        omega
                _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_total
            omega
          exact hweight_nat'
        -- The witness weight is the suffix sum plus the pivot weight.
        have hx_weight :
            ∑ i, (weights i : ℝ) * x i = (weights j + suffix.sum weights : ℝ) := by
          calc
            ∑ i, (weights i : ℝ) * x i
                = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
                    simp [dotProduct]
            _ = x ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by rw [dotProduct_comm]
            _ = (cover_indicator suffix + Pi.single j (1 : ℝ)) ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
                    simp [x]
            _ = cover_indicator suffix ⬝ᵥ (fun i ↦ (weights i : ℝ)) +
                  Pi.single j (1 : ℝ) ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
                    rw [add_dotProduct]
            _ = (suffix.sum fun i ↦ (weights i : ℝ)) + weights j := by
                    rw [coverIndicator_dot_eq_sum]
                    simp
            _ = (weights j + suffix.sum weights : ℝ) := by
                    rw [Nat.cast_sum]
                    norm_num [add_comm]
        rw [hx_weight]
        exact_mod_cast hweight_nat
    have hx_valid := hαvalid_set hx_mem
    have hsuffix_card :
        suffix.card = t - (h j + 1) := by
      simpa [suffix] using
        remark_7_5_cover_suffix_card (n := n) t (h j + 1) ht hs
    have hsuffix_dot :
        α ⬝ᵥ x = (suffix.card : ℝ) + α j := by
      have hsuffix_sum_one :
          suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hα_cover i ((Finset.mem_filter.mp hi).1)
      calc
        α ⬝ᵥ x
            = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
                simp [x]
        _ = α ⬝ᵥ cover_indicator suffix + α ⬝ᵥ Pi.single j (1 : ℝ) := by
                rw [dotProduct_add]
        _ = cover_indicator suffix ⬝ᵥ α + α j := by
                rw [dotProduct_comm]
                simp [dotProduct_comm]
        _ = suffix.sum α + α j := by
                rw [coverIndicator_dot_eq_sum]
        _ = (suffix.card : ℝ) + α j := by
                rw [hsuffix_sum_one]
                simp
    have hcover_rhs :
        cover_inequality_rhs (remark_7_5_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, remark_7_5_cover_card (n := n) t ht]
    have hsuffix_card_real :
        (suffix.card : ℝ) = (t : ℝ) - ((h j + 1 : ℕ) : ℝ) := by
      rw [hsuffix_card, Nat.cast_sub hs]
    -- The witness saturates the last `t - (h j + 1)` cover coefficients, so validity bounds `α j`
    -- by the remaining slack `h j`.
    rw [hsuffix_dot, hcover_rhs, hsuffix_card_real] at hx_valid
    norm_num at hx_valid
    linarith
  · have ht_le_hj : t ≤ h j := by
      omega
    let x : Fin n → ℝ := Pi.single j (1 : ℝ)
    -- If `h j` is already beyond the cover length, the singleton point at `j` gives the bound.
    have hx_mem : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
      rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        by_cases hij : i = j
        · right
          subst hij
          simp [x]
        · left
          simp [x, hij]
      · have hx_weight : ∑ i, (weights i : ℝ) * x i = weights j := by
          calc
            ∑ i, (weights i : ℝ) * x i = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
              simp [dotProduct]
            _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
              simp [x]
            _ = weights j := by
              simp
        rw [hx_weight]
        exact_mod_cast hweights_le j
    have hx_valid := hαvalid_set hx_mem
    have hcover_rhs :
        cover_inequality_rhs (remark_7_5_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, remark_7_5_cover_card (n := n) t ht]
    have ht_le_hj_real : (t : ℝ) ≤ h j := by
      exact_mod_cast ht_le_hj
    rw [hcover_rhs] at hx_valid
    simp [x] at hx_valid
    linarith

/-- Helper for Remark 7.5: isolating a pivot coordinate rewrites the knapsack weight sum as the
pivot contribution plus the sum over the remaining `succAbove` coordinates. -/
private theorem remark_7_5_weightedSum_insertNth
    (j : Fin (n + 1))
    (weights : Fin (n + 1) → ℕ)
    (xj : ℝ)
    (y : Fin n → ℝ) :
    ∑ i, (weights i : ℝ) * (@Fin.insertNth _ (fun _ ↦ ℝ) j xj y) i =
      (weights j : ℝ) * xj + ∑ i : Fin n, (weights (j.succAbove i) : ℝ) * y i := by
  -- Split the full sum into the pivot term and the remaining `succAbove` coordinates once.
  let z : Fin (n + 1) → ℝ := @Fin.insertNth _ (fun _ ↦ ℝ) j xj y
  simpa [z, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
    (Fin.sum_univ_succAbove
      (fun i : Fin (n + 1) ↦ (weights i : ℝ) * z i) j)

/-- Helper for Remark 7.5: after reindexing by a pivot `j`, binary knapsack membership is exactly
the binary conditions on the pivot and the `succAbove` coordinates together with the transported
capacity inequality. -/
private theorem remark_7_5_mem_zero_one_knapsack_set_insertNth_iff
    (j : Fin (n + 1))
    (weights : Fin (n + 1) → ℕ)
    (capacity : ℕ)
    (xj : ℝ)
    (y : Fin n → ℝ) :
    (@Fin.insertNth _ (fun _ ↦ ℝ) j xj y) ∈
        zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ↔
      (xj = 0 ∨ xj = 1) ∧
        (∀ i : Fin n, y i = 0 ∨ y i = 1) ∧
        (weights j : ℝ) * xj +
            ∑ i : Fin n, (weights (j.succAbove i) : ℝ) * y i ≤
          (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff, remark_7_5_weightedSum_insertNth]
  constructor
  · intro hx
    refine ⟨?_, ?_, hx.2⟩
    · simpa [Fin.insertNth_apply_same] using hx.1 j
    -- The non-pivot coordinates are exactly the `succAbove` coordinates of the inserted tuple.
    intro i
    simpa [Fin.insertNth_apply_succAbove] using hx.1 (j.succAbove i)
  · rintro ⟨hxj, hy, hweight⟩
    refine ⟨?_, hweight⟩
    -- Reassemble the full binary tuple from the pivot coordinate and the transported complement.
    exact (Fin.forall_iff_succAbove j).2
      ⟨by simpa [Fin.insertNth_apply_same] using hxj,
        fun i ↦ by simpa [Fin.insertNth_apply_succAbove] using hy i⟩

/-- Helper for Remark 7.5: every binary knapsack point already lies in the ambient zero-one owner
used by Proposition 7.2. -/
private theorem remark_7_5_zeroOneKnapsackSet_subset_zeroOnePointsUniv
    (weights : Fin n → ℕ)
    (capacity : ℕ) :
    zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ⊆
      zero_one_points (Nat.le_refl n) (Set.univ : Set (Fin n → ℝ)) := by
  intro x hx
  rw [mem_zero_one_points_iff]
  rw [mem_zero_one_knapsack_set_iff] at hx
  constructor
  · simp
  · simpa using hx.1

/-- Helper for Remark 7.5: once the ambient prefix has passed the cover length `t`, the next stage
coefficient vector is the previous-stage coefficient vector with the new last coefficient appended.
-/
private theorem remark_7_5_liftingCoeff_snoc
    {m t : ℕ}
    (ht : t ≤ m)
    (h : Fin (m + 1) → ℕ) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h =
      Fin.snoc
        (remark_7_5_lifting_coeff (remark_7_5_cover (n := m) t)
          (fun i : Fin m ↦ h i.castSucc))
        (h (Fin.last m)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
  · -- On the old coordinates, the cover-membership test is unchanged by `castSucc`.
    by_cases hj : j ∈ remark_7_5_cover (n := m) t
    · have hj' : j.castSucc ∈ remark_7_5_cover (n := m + 1) t := by
        exact remark_7_5_cover_mem_iff.mpr (by simpa using (remark_7_5_cover_mem_iff.mp hj))
      simp [remark_7_5_lifting_coeff, hj, hj']
    · have hj' : j.castSucc ∉ remark_7_5_cover (n := m + 1) t := by
        intro hj''
        exact hj (remark_7_5_cover_mem_iff.mpr (by simpa using (remark_7_5_cover_mem_iff.mp hj'')))
      simp [remark_7_5_lifting_coeff, hj, hj']
  · -- The new last coordinate is off the cover because `t ≤ m`.
    simp [remark_7_5_lifting_coeff, remark_7_5_cover, Nat.not_lt.mpr ht]

/-- Helper for Remark 7.5: validity on the previous prefix stage transfers directly to the zero
slice `x_last = 0` when the next variable is already the literal last coordinate. -/
private theorem remark_7_5_lastCoordinateZeroSliceValid
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (α : Fin m → ℝ)
    (β : ℝ)
    (hvalid :
      is_valid_inequality
        (zero_one_knapsack_set (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ))
        α
        β) :
    is_valid_inequality
      (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
        last_coordinate_eq_set m 0)
      (Fin.snoc α 0)
      β := by
  intro x hx
  rcases hx with ⟨hxS, hxlast⟩
  have hxlast0 : x (Fin.last m) = 0 := mem_last_coordinate_eq_set_iff.mp hxlast
  have hy_mem :
      (fun i : Fin m ↦ x i.castSucc) ∈
        zero_one_knapsack_set (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ) := by
    rw [mem_zero_one_knapsack_set_iff] at hxS ⊢
    constructor
    · intro i
      simpa using hxS.1 i.castSucc
    · -- The zero slice deletes the last-coordinate term from the knapsack weight sum.
      simpa [Fin.sum_univ_castSucc, hxlast0] using hxS.2
  have hy_valid := hvalid hy_mem
  -- The lifted coefficient vector restricts to the old stage because the last coordinate vanishes.
  calc
    Fin.snoc α 0 ⬝ᵥ x = partial_lifting_value α x + 0 * x (Fin.last m) := by
      rw [dotProduct_last_coordinate_lifting_coeffs]
    _ = α ⬝ᵥ (fun i : Fin m ↦ x i.castSucc) := by
      simp [partial_lifting_value, dotProduct, hxlast0]
    _ ≤ β := hy_valid

/-- Helper for Remark 7.5: the interval-index coefficients should yield a valid lifted cover
inequality on the binary knapsack set before passing to the polytope owner. -/
private theorem remark_7_5_setValidOfIntervalIndices
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    is_valid_inequality
      (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff C h)
      (cover_inequality_rhs C) := by
  -- Route correction: the old global lifting-profile route is stronger than Remark 7.5 needs.
  -- The raw binary-set transport is packaged by
  -- `remark_7_5_mem_zero_one_knapsack_set_insertNth_iff`, and the source witness arithmetic is now
  -- packaged by the `remark_7_5_suffixWitness*` lemmas above.
  -- TODO: either finish the direct prefix-validity induction from those witness bounds, or carry
  -- the zero slice and one-slice bounds through a single arbitrary-pivot-to-last-coordinate
  -- adapter before invoking Proposition 7.2.
  sorry

/-- Helper for Remark 7.5: the strengthened upper bound should upgrade the interval-index lifting
to the Chapter 7.1 facet-defining cover-lifting owner. -/
private theorem remark_7_5_coverFacetMembershipOfUpperBound
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C := by
  -- Route correction: the remaining work is local one-step lifting, not a global profile theorem.
  -- TODO: start from `remark_7_5_baseFacetData`, then sequentially lift the complement of `C`
  -- using Proposition 7.2 part (2); `remark_7_5_coeff_le_of_mem_validLifting` and the
  -- `remark_7_5_suffixWitness*` arithmetic now supply the witness/upper-bound side, so the
  -- missing work is only the transported exact-coefficient and face-growth step.
  sorry

/-- Helper for Remark 7.5: every facet-defining lifting should match the remark coefficients on
coordinates outside the cover. -/
private theorem remark_7_5_offCoverEqOfMemFacetDefining
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∉ C) :
    α j = (h j : ℝ) := by
  -- Route correction: uniqueness is coordinatewise once the exact next-coefficient step is known.
  -- TODO: combine the existing upper bound `α j ≤ h j` with either a last-coordinate exactness
  -- transport or the strict-update facet comparison once the canonical facet/witness package from
  -- the previous theorem is available.
  sorry

/-- Remark 7.5 (1). Let `K` be the `0,1` knapsack set with weights `weights` and capacity
`capacity`, and let `C` and the partial sums `μ` come from the Theorem 7.4 setup.
If `h(j)` is chosen for each `j ∉ C` so that `μ_{h(j)} ≤ a_j < μ_{h(j)+1}`, then the inequality
`∑_{j ∈ C} x_j + ∑_{j ∈ N \ C} h(j) x_j ≤ |C| - 1`
is a lifting of the minimal cover inequality associated with `C`. -/
theorem remark_7_5_lifted_cover_inequality_is_lifting
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    remark_7_5_lifting_coeff C h ∈
      valid_liftings_of_minimal_cover_inequality weights capacity C := by
  rw [mem_valid_liftings_of_minimal_cover_inequality_iff]
  constructor
  · intro j hj
    -- The displayed lifting keeps the cover coefficients fixed by construction.
    simpa using remark_7_5_lifting_coeff_apply_of_mem (C := C) (h := h) hj
  · -- First prove validity on the binary knapsack set, then pass to the convex-hull polytope.
    exact
      remark_7_5_polytopeValid_of_setValid
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C)
        (remark_7_5_setValidOfIntervalIndices
          weights capacity C μ h hctx hinterval)

/-- Companion bridge: Remark 7.5 (1) gives the canonical valid-inequality owner on the knapsack
polytope. -/
theorem remark_7_5_lifting_coeff_is_valid_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    is_valid_inequality
      (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff C h)
      (cover_inequality_rhs C) := by
  exact
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp
      (remark_7_5_lifted_cover_inequality_is_lifting
        weights capacity C μ h hctx hinterval)).2

/-- Remark 7.5 (2). If, in addition, `a_j ≤ μ_{h(j)+1} - λ` for every `j ∉ C`, then the lifted
inequality from Remark 7.5 is a facet-defining lifting of the minimal cover inequality attached
to the Theorem 7.4 cover `C`. -/
theorem remark_7_5_lifted_cover_inequality_is_facet_defining
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_minimal_cover_inequality weights capacity C := by
  rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
  constructor
  · -- The facet statement already contains the valid-lifting part as its first component.
    exact remark_7_5_lifted_cover_inequality_is_lifting weights capacity C μ h ⟨lam, hctx⟩ hinterval
  · -- The strengthened upper bound should upgrade the valid lifting to a facet-defining one.
    exact
      remark_7_5_coverFacetMembershipOfUpperBound
        weights capacity C μ h lam hctx hinterval hupper

/-- Companion bridge: Remark 7.5 (2) places the displayed coefficient vector in the canonical
cover-lifting facet owner. -/
theorem remark_7_5_lifting_coeff_mem_facet_defining_liftings_of_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C := by
  exact
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp
      (remark_7_5_lifted_cover_inequality_is_facet_defining
        weights capacity C μ h lam hctx hinterval hupper)).2

/-- Remark 7.5 (3). Under the strengthened upper bound
`a_j ≤ μ_{h(j)+1} - λ` for all `j ∉ C`, any facet-defining lifting of the minimal cover
inequality associated with `C` coincides with the coefficient vector from Remark 7.5. -/
theorem remark_7_5_eq_of_mem_facet_defining_liftings
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C) :
    α = remark_7_5_lifting_coeff C h := by
  ext j
  by_cases hj : j ∈ C
  · have hvalid :
        α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C :=
      (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).1
    -- On the cover, every valid lifting matches the Remark 7.5 coefficient vector.
    simpa using eqOnCoverOfMemValidLiftings weights capacity C h hvalid hj
  · -- Off the cover, the strengthened upper bound should force the exact Remark 7.5 coefficient.
    simpa [remark_7_5_lifting_coeff_apply_of_not_mem hj] using
      remark_7_5_offCoverEqOfMemFacetDefining
        weights capacity C μ h lam hctx hinterval hupper hα hj

end Remark75
