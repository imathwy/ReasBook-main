module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.WithTopology

public section

universe u

/-- Helper for Example 30.2: every discrete subspace of a second-countable space is countable. -/
theorem Set.countable_of_isDiscrete {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] {A : Set X} (hA : IsDiscrete A) : A.Countable :=
  (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hA

namespace UniformRealSequence

/-- Helper for Example 30.2: the uniform topology on real sequences is first-countable. -/
noncomputable instance instFirstCountableTopology :
    FirstCountableTopology UniformRealSequence := by
  -- Regard the unwrapped function space with the same named uniform topology and metric.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let unwrap : UniformRealSequence ≃ₜ (ℕ → ℝ) :=
    { WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ) with
      continuous_toFun := WithTopology.continuous_ofTopology (UniformMetric.topology ℕ)
      continuous_invFun := WithTopology.continuous_toTopology (UniformMetric.topology ℕ) }
  -- First countability pulls back along the inducing unwrapping map.
  exact unwrap.isInducing.firstCountableTopology

end UniformRealSequence

/-- The set of real sequences all of whose coordinates are either `0` or `1`. -/
def UniformRealSequence.zeroOneSequences : Set UniformRealSequence :=
  {x | ∀ n, WithTopology.ofTopology x n = 0 ∨ WithTopology.ofTopology x n = 1}

/-- Membership in `UniformRealSequence.zeroOneSequences` is coordinatewise. -/
@[simp] theorem UniformRealSequence.mem_zeroOneSequences (x : UniformRealSequence) :
    x ∈ zeroOneSequences ↔
      ∀ n, WithTopology.ofTopology x n = 0 ∨ WithTopology.ofTopology x n = 1 := Iff.rfl

namespace UniformRealSequence

/-- Helper for Example 30.2: the characteristic sequence of a set of natural numbers. -/
noncomputable def characteristicSequence (s : Set ℕ) : UniformRealSequence :=
  ofSequence (s.indicator fun _ : ℕ ↦ (1 : ℝ))

/-- Helper for Example 30.2: a characteristic sequence is `1` on its defining set. -/
theorem characteristicSequence_apply_of_mem {s : Set ℕ} {n : ℕ} (hn : n ∈ s) :
    WithTopology.ofTopology (characteristicSequence s) n = 1 := by
  -- Unwrap the named sequence and evaluate the indicator at a member.
  rw [characteristicSequence, ofSequence_eq_toTopology]
  exact Set.indicator_of_mem hn (fun _ : ℕ ↦ (1 : ℝ))

/-- Helper for Example 30.2: a characteristic sequence is `0` off its defining set. -/
theorem characteristicSequence_apply_of_notMem {s : Set ℕ} {n : ℕ} (hn : n ∉ s) :
    WithTopology.ofTopology (characteristicSequence s) n = 0 := by
  -- Unwrap the named sequence and evaluate the indicator away from the set.
  rw [characteristicSequence, ofSequence_eq_toTopology]
  exact Set.indicator_of_notMem hn (fun _ : ℕ ↦ (1 : ℝ))

/-- Helper for Example 30.2: every characteristic sequence is zero-one-valued. -/
theorem characteristicSequence_mem (s : Set ℕ) : characteristicSequence s ∈ zeroOneSequences := by
  -- Split according to whether the coordinate belongs to the defining set.
  intro n
  by_cases hn : n ∈ s
  · exact Or.inr (characteristicSequence_apply_of_mem hn)
  · exact Or.inl (characteristicSequence_apply_of_notMem hn)

/-- Helper for Example 30.2: a set of naturals determines a zero-one sequence. -/
noncomputable def zeroOneSequenceOfSet (s : Set ℕ) : zeroOneSequences :=
  ⟨characteristicSequence s, characteristicSequence_mem s⟩

/-- Helper for Example 30.2: coercing the bundled sequence recovers its characteristic sequence. -/
theorem coe_zeroOneSequenceOfSet (s : Set ℕ) :
    (zeroOneSequenceOfSet s : UniformRealSequence) = characteristicSequence s := by
  -- This is the value field of the bundled zero-one sequence.
  rfl

/-- Helper for Example 30.2: the power set of `ℕ` injects into the zero-one sequences. -/
theorem existsInjectiveSetNatZeroOneSequences :
    ∃ encode : Set ℕ → zeroOneSequences, Function.Injective encode := by
  -- Use the named characteristic-sequence construction.
  classical
  refine ⟨zeroOneSequenceOfSet, ?_⟩
  -- Equality of characteristic sequences detects membership at every coordinate.
  intro s t hst
  apply Set.ext
  intro n
  have hcoord := congrFun (congrArg WithTopology.ofTopology (congrArg Subtype.val hst)) n
  by_cases hns : n ∈ s
  · by_cases hnt : n ∈ t
    · exact iff_of_true hns hnt
    · rw [coe_zeroOneSequenceOfSet, coe_zeroOneSequenceOfSet,
        characteristicSequence_apply_of_mem hns,
        characteristicSequence_apply_of_notMem hnt] at hcoord
      norm_num at hcoord
  · by_cases hnt : n ∈ t
    · rw [coe_zeroOneSequenceOfSet, coe_zeroOneSequenceOfSet,
        characteristicSequence_apply_of_notMem hns,
        characteristicSequence_apply_of_mem hnt] at hcoord
      norm_num at hcoord
    · exact iff_of_false hns hnt

/-- Helper for Example 30.2: two distinct zero-one real values are distance one apart. -/
theorem dist_eq_one_of_mem_zeroOne {x y : ℝ} (hx : x = 0 ∨ x = 1)
    (hy : y = 0 ∨ y = 1) (hxy : x ≠ y) : dist x y = 1 := by
  -- Exhaust the two possible values at each endpoint.
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · norm_num
  · rcases hy with rfl | rfl
    · norm_num
    · exact (hxy rfl).elim

/-- Helper for Example 30.2: distinct zero-one sequences have uniform distance one. -/
theorem zeroOneSequences_dist_eq_one {x y : UniformRealSequence}
    (hx : x ∈ zeroOneSequences) (hy : y ∈ zeroOneSequences) (hxy : x ≠ y) :
    (UniformMetric.metricSpace ℕ).dist (WithTopology.ofTopology x)
      (WithTopology.ofTopology y) = 1 := by
  -- Distinct wrapped functions differ at some coordinate.
  have hcoord : ∃ n, WithTopology.ofTopology x n ≠ WithTopology.ofTopology y n := by
    by_contra h
    push Not at h
    apply hxy
    have hfun : WithTopology.ofTopology x = WithTopology.ofTopology y :=
      funext fun n ↦ h n
    exact congrArg (WithTopology.toTopology (UniformMetric.topology ℕ)) hfun
  obtain ⟨n, hn⟩ := hcoord
  -- The selected coordinate contributes exactly `1` to the supremum.
  have hnDist : dist (WithTopology.ofTopology x n) (WithTopology.ofTopology y n) = 1 :=
    dist_eq_one_of_mem_zeroOne (hx n) (hy n) hn
  rw [UniformMetric.dist_eq]
  apply le_antisymm
  · exact ciSup_le fun j ↦ min_le_right _ _
  · have hBound : BddAbove (Set.range fun j : ℕ ↦
        min (dist (WithTopology.ofTopology x j) (WithTopology.ofTopology y j)) 1) := by
      refine ⟨1, ?_⟩
      rintro z ⟨j, rfl⟩
      exact min_le_right _ _
    calc
      1 = min (dist (WithTopology.ofTopology x n) (WithTopology.ofTopology y n)) 1 := by
        rw [hnDist]
        norm_num
      _ ≤ ⨆ j, min (dist (WithTopology.ofTopology x j)
          (WithTopology.ofTopology y j)) 1 := le_ciSup hBound n

end UniformRealSequence

/-- Helper for Example 30.2: the set of zero-one-valued real sequences is uncountable. -/
theorem UniformRealSequence.zeroOneSequences_uncountable :
    ¬ zeroOneSequences.Countable := by
  -- A countability assumption would embed the zero-one sequences into `ℕ`.
  intro hCountable
  letI : Countable zeroOneSequences := hCountable.to_subtype
  obtain ⟨encode, hencode⟩ := Countable.exists_injective_nat zeroOneSequences
  obtain ⟨characteristic, hcharacteristic⟩ :=
    UniformRealSequence.existsInjectiveSetNatZeroOneSequences
  -- Composing with characteristic sequences contradicts Cantor's theorem.
  exact Function.cantor_injective (encode ∘ characteristic)
    (hencode.comp hcharacteristic)

/-- Helper for Example 30.2: the zero-one-valued sequences form a discrete subspace of the uniform
topology. -/
theorem UniformRealSequence.zeroOneSequences_isDiscrete :
    IsDiscrete zeroOneSequences := by
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  -- Pull back a radius-one ball from the defining metric on the raw function space.
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  let U : Set UniformRealSequence :=
    WithTopology.ofTopology ⁻¹' Metric.ball (WithTopology.ofTopology x) 1
  refine ⟨U, ?_, ?_⟩
  · exact Metric.isOpen_ball
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hyBall, hyZeroOne⟩
      change (UniformMetric.metricSpace ℕ).dist (WithTopology.ofTopology y)
        (WithTopology.ofTopology x) < 1 at hyBall
      have hyEq : y = x := by
        by_contra hyNe
        have hdist := UniformRealSequence.zeroOneSequences_dist_eq_one hyZeroOne hx hyNe
        exact (not_lt_of_ge (le_of_eq hdist.symm)) hyBall
      simp [hyEq]
    · intro hy
      have hyEq : y = x := by simpa using hy
      subst y
      constructor
      · change (UniformMetric.metricSpace ℕ).dist (WithTopology.ofTopology x)
          (WithTopology.ofTopology x) < 1
        rw [dist_self]
        exact zero_lt_one
      · exact hx

/-- Example 30.2. The uniform topology on real sequences is not second-countable. -/
theorem UniformRealSequence.notSecondCountable :
    ¬ SecondCountableTopology UniformRealSequence := by
  -- Second countability would force the discrete zero-one subspace to be countable.
  intro hSecondCountable
  letI : SecondCountableTopology UniformRealSequence := hSecondCountable
  exact UniformRealSequence.zeroOneSequences_uncountable
    (Set.countable_of_isDiscrete UniformRealSequence.zeroOneSequences_isDiscrete)

end
