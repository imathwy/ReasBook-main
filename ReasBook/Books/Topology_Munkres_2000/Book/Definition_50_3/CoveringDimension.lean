module

public import Topology_Munkres_2000.Book.Definition_50_3

public section

open Set

universe u

/-- The open-cover characterization of `HasCoveringDimensionLE`. -/
theorem hasCoveringDimensionLE_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HasCoveringDimensionLE X n ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) →
        ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (n + 1) := by
  rfl

/-- The point-multiplicity characterization of `HasCoveringDimensionLE`. -/
theorem hasCoveringDimensionLE_iff_pointwise
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HasCoveringDimensionLE X n ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) →
        ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
            ∀ x : X, Set.encard {V ∈ ℬ | x ∈ V} ≤ (n + 1 : ℕ) := by
  simpa only [Set.hasOrderLE_iff] using hasCoveringDimensionLE_iff X n

namespace HasCoveringDimensionLE

/-- A covering-dimension bound remains valid after increasing the bound. -/
theorem mono {X : Type u} [TopologicalSpace X] {n m : ℕ}
    (h : HasCoveringDimensionLE X n) (hnm : n ≤ m) :
    HasCoveringDimensionLE X m := by
  -- Keep the same refining cover and enlarge only its order bound.
  intro 𝒜 h𝒜_open h𝒜_cover
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order⟩ := h 𝒜 h𝒜_open h𝒜_cover
  refine ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order.mono ?_⟩
  exact Nat.add_le_add_right hnm 1

end HasCoveringDimensionLE

/-- A space has covering dimension less than `0` exactly when it is empty. -/
theorem hasCoveringDimensionLT_zero_iff (X : Type u) [TopologicalSpace X] :
    HasCoveringDimensionLT X 0 ↔ IsEmpty X := by
  rfl

/-- Helper for Definition 50.3: a covering-dimension bound implies every larger strict bound. -/
lemma hasCoveringDimensionLT_of_bound {X : Type u} [TopologicalSpace X] {n k : ℕ}
    (h : HasCoveringDimensionLE X n) (hnk : n < k) :
    HasCoveringDimensionLT X k := by
  -- A positive strict bound is a predecessor-indexed non-strict bound.
  cases k with
  | zero => exact (Nat.not_lt_zero n hnk).elim
  | succ k =>
      exact h.mono (Nat.lt_succ_iff.mp hnk)

/-- Helper for Definition 50.3: an empty space satisfies every finite covering-dimension bound. -/
lemma hasCoveringDimensionLE_of_isEmpty {X : Type u} [TopologicalSpace X]
    (hX : IsEmpty X) (n : ℕ) : HasCoveringDimensionLE X n := by
  -- The empty collection is an open refinement and covers an empty space.
  intro 𝒜 _ _
  refine ⟨∅, ?_, ?_, ?_⟩
  · rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      intro B hB
      exact hB.elim
    · intro B hB
      exact hB.elim
  · ext x
    exact (hX.false x).elim
  · rw [Set.hasOrderLE_iff]
    intro x
    exact (hX.false x).elim

/-- The existence-of-a-bound characterization of finite covering dimension. -/
theorem finiteCoveringDimension_iff (X : Type u) [TopologicalSpace X] :
    FiniteCoveringDimension X ↔ ∃ n : ℕ, HasCoveringDimensionLE X n := by
  rfl

open scoped CoveringDimension

/-- The numerical covering dimension is at most `n` exactly when `n` is a
covering-dimension bound. -/
theorem coveringDimension_le_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    dim X ≤ (n : WithBot ℕ∞) ↔ HasCoveringDimensionLE X n := by
  constructor
  · intro hdim
    -- Discreteness turns the non-strict numerical bound into a strict successor bound.
    have hdim_succ : dim X < (n + 1 : ℕ) :=
      ENat.WithBot.lt_add_one_iff.mpr hdim
    rw [coveringDimension] at hdim_succ
    obtain ⟨d, hd_bounds, hd_succ⟩ := sInf_lt_iff.mp hdim_succ
    exact hd_bounds (n + 1) hd_succ
  · intro hbound
    -- The cast of `n` belongs to the defining set, so the infimum lies below it.
    rw [coveringDimension]
    apply sInf_le
    intro k hnk
    have hnk_nat : n < k := by
      exact_mod_cast hnk
    exact hasCoveringDimensionLT_of_bound hbound hnk_nat

/-- The covering dimension has value `-1` exactly for empty spaces. -/
theorem coveringDimension_eq_bot_iff (X : Type u) [TopologicalSpace X] :
    dim X = ⊥ ↔ IsEmpty X := by
  constructor
  · intro hdim
    -- A defining bound below zero must supply the strict zero-dimensional condition.
    have hdim_zero : dim X < (0 : WithBot ℕ∞) := by
      rw [hdim]
      exact WithBot.bot_lt_coe 0
    rw [coveringDimension] at hdim_zero
    obtain ⟨d, hd_bounds, hd_zero⟩ := sInf_lt_iff.mp hdim_zero
    exact hd_bounds 0 hd_zero
  · intro hX
    -- For an empty space, bottom itself satisfies every defining strict bound.
    apply le_antisymm
    · rw [coveringDimension]
      apply sInf_le
      intro n _
      cases n with
      | zero => exact hX
      | succ n => exact hasCoveringDimensionLE_of_isEmpty hX n
    · exact bot_le

/-- Finite covering dimension is equivalent to the numerical covering dimension
being different from `⊤`. -/
theorem finiteCoveringDimension_iff_coveringDimension_ne_top
    (X : Type u) [TopologicalSpace X] :
    FiniteCoveringDimension X ↔ dim X ≠ ⊤ := by
  constructor
  · rintro ⟨n, hn⟩ htop
    -- A finite numerical upper bound is incompatible with value `⊤`.
    have hdim : dim X ≤ (n : WithBot ℕ∞) :=
      (coveringDimension_le_iff X n).mpr hn
    rw [htop] at hdim
    have hn_top : (n : WithBot ℕ∞) = ⊤ := by
      simpa using hdim
    exact ENat.coe_ne_top n (WithBot.coe_eq_top.mp hn_top)
  · intro hdim
    -- If the value is not top, some natural number fails to lie below it.
    have hnot_all : ¬ ∀ n : ℕ, n ≤ dim X :=
      (ENat.WithBot.eq_top_iff_forall_ge.not).mp hdim
    push Not at hnot_all
    obtain ⟨n, hn⟩ := hnot_all
    refine ⟨n, (coveringDimension_le_iff X n).mp ?_⟩
    exact le_of_lt hn
