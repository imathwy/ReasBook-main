module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Lattice

public section

namespace Real

/-- A subset of `ℝ` is inductive when it contains `1` and is closed under adding `1`. -/
def IsInductive (A : Set ℝ) : Prop :=
  (1 : ℝ) ∈ A ∧ ∀ x ∈ A, x + 1 ∈ A

/-- A subset of `ℝ` is inductive exactly when it contains `1` and is closed under adding `1`. -/
theorem isInductive_iff (A : Set ℝ) :
    IsInductive A ↔ (1 : ℝ) ∈ A ∧ ∀ x ∈ A, x + 1 ∈ A := by
  rfl

/-- The collection of all inductive subsets of `ℝ`. -/
def inductiveSets : Set (Set ℝ) :=
  {A | IsInductive A}

/-- The positive integers regarded as the intersection of all inductive subsets of `ℝ`. -/
def positiveIntegers : Set ℝ :=
  ⋂₀ inductiveSets

/-- The positive integers, regarded as the intersection-defined subset of `ℝ`. -/
notation "ℤ₊" => positiveIntegers

/-- A set belongs to `Real.inductiveSets` exactly when it is inductive. -/
theorem mem_inductiveSets_iff (A : Set ℝ) :
    A ∈ inductiveSets ↔ IsInductive A := by
  rfl

/-- Membership in `ℤ₊` means membership in every inductive subset of `ℝ`. -/
theorem mem_positiveIntegers_iff (x : ℝ) :
    x ∈ ℤ₊ ↔ ∀ A : Set ℝ, IsInductive A → x ∈ A := by
  simp [positiveIntegers, inductiveSets]

/-- Helper for Definition 4.6: the real casts of positive naturals form an inductive set. -/
lemma isInductive_range_pnatCast :
    IsInductive (Set.range (fun n : ℕ+ ↦ (n : ℝ))) := by
  -- The cast of `1 : ℕ+` supplies the base point of the range.
  rw [isInductive_iff]
  constructor
  · refine ⟨1, ?_⟩
    simp
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    -- Adding one to a cast is the cast of the positive-natural successor.
    refine ⟨n + 1, ?_⟩
    simp

/-- Helper for Definition 4.6: every inductive subset of `ℝ` contains the cast of each
positive natural. -/
lemma pnatCast_mem_of_isInductive {A : Set ℝ} (hA : IsInductive A) (n : ℕ+) :
    (n : ℝ) ∈ A := by
  -- Positive-natural induction follows the base and successor clauses of inductivity.
  rw [isInductive_iff] at hA
  induction n using PNat.recOn with
  | one =>
      simpa using hA.1
  | succ n hn =>
      -- Normalize the successor cast after applying closure under adding one.
      simpa using hA.2 (n : ℝ) hn

end Real
