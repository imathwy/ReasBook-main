module

public import Mathlib.SetTheory.Cardinal.Basic

public section

universe u

/-- Helper for Exercise 9.7: `A` has strictly greater cardinality than `B` exactly when
`B` injects into `A` but `A` does not inject into `B`. -/
theorem cardinalityLt_iff_injections (A B : Type u) :
    Cardinal.mk B < Cardinal.mk A ↔
      (∃ f : B → A, Function.Injective f) ∧ ¬ ∃ g : A → B, Function.Injective g := by
  rw [lt_iff_le_not_ge, Cardinal.le_def, Cardinal.le_def]
  constructor
  · rintro ⟨⟨f⟩, h⟩
    refine ⟨⟨f, f.injective⟩, ?_⟩
    rintro ⟨g, hg⟩
    exact h ⟨⟨g, hg⟩⟩
  · rintro ⟨⟨f, hf⟩, h⟩
    refine ⟨⟨⟨f, hf⟩⟩, ?_⟩
    rintro ⟨g⟩
    exact h ⟨g, g.injective⟩

/-- Helper for Exercise 9.7 (a): every uncountable type has strictly greater
cardinality than the positive integers. -/
theorem uncountable_cardinalityLt_pnat (A : Type u) [Uncountable A] :
    Cardinal.lift (Cardinal.mk (ℕ+)) < Cardinal.mk A := by
  simp only [Cardinal.mk_pnat, Cardinal.lift_aleph0]
  exact Cardinal.aleph0_lt_mk

/- Exercise 9.7 (b): Strict cardinal comparison is transitive. -/
#check lt_trans

/-- The explicit tower of infinite types used in Exercise 9.7, with stage `n`
corresponding to the textbook set `Aₙ₊₁`. -/
def iteratedPowerSet : ℕ → Type
  | 0 => (ℕ+)
  | n + 1 => Set (iteratedPowerSet n)

/-- Every stage of `iteratedPowerSet` is infinite. -/
instance iteratedPowerSet_infinite (n : ℕ) : Infinite (iteratedPowerSet n) := by
  -- Inductively, taking a powerset preserves infinitude.
  induction n with
  | zero =>
      rw [iteratedPowerSet]
      infer_instance
  | succ n ih =>
      rw [iteratedPowerSet]
      exact @Infinite.set (iteratedPowerSet n) ih

/-- Helper for Exercise 9.7 (c): each stage of `iteratedPowerSet` has strictly
smaller cardinality than its successor stage. -/
theorem iteratedPowerSet_lt_succ (n : ℕ) :
    Cardinal.mk (iteratedPowerSet n) < Cardinal.mk (iteratedPowerSet (n + 1)) := by
  -- The successor stage is the powerset of the current stage.
  rw [iteratedPowerSet, Cardinal.mk_set]
  exact Cardinal.cantor _

/-- An explicit common strict upper-bound carrier for all stages of
`iteratedPowerSet`. -/
def iteratedPowerSetBound : Type := Set (Σ n, iteratedPowerSet n)

/-- Helper for Exercise 9.7: each stage embeds into the dependent sum of all stages. -/
lemma iteratedPowerSet_mk_le_sigma (n : ℕ) :
    Cardinal.mk (iteratedPowerSet n) ≤ Cardinal.mk (Σ k, iteratedPowerSet k) := by
  -- Insert the stage as the fiber over its fixed index.
  refine Cardinal.mk_le_of_injective (f := fun x ↦ ⟨n, x⟩) ?_
  intro x y hxy
  cases hxy
  rfl

/-- Exercise 9.7 (d): Every stage of `iteratedPowerSet` has strictly smaller
cardinality than `iteratedPowerSetBound`. -/
theorem iteratedPowerSet_lt_bound (n : ℕ) :
    Cardinal.mk (iteratedPowerSet n) < Cardinal.mk iteratedPowerSetBound := by
  -- First enter the sum of all stages, then apply Cantor to its powerset.
  calc
    Cardinal.mk (iteratedPowerSet n) ≤ Cardinal.mk (Σ k, iteratedPowerSet k) :=
      iteratedPowerSet_mk_le_sigma n
    _ < Cardinal.mk iteratedPowerSetBound := by
      rw [iteratedPowerSetBound, Cardinal.mk_set]
      exact Cardinal.cantor _
