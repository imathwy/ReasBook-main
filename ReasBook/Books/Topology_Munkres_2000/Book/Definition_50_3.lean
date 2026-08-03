module

public import Topology_Munkres_2000.Book.Definition_39_4.Refinement
public import Topology_Munkres_2000.Book.Definition_50_1.Order
public import Mathlib.Data.ENat.Lattice

public section

open Set

universe u

/-
Definition 50.3. A space is finite dimensional when it has a finite covering-dimension
bound. Its covering dimension is the least such bound, with `⊥` representing the empty
space and `⊤` representing the absence of a finite bound.
-/

/-- Helper for Definition 50.3: a space has covering dimension at most `n` when every open
cover has an open refining cover of point multiplicity at most `n + 1`. -/
abbrev HasCoveringDimensionLE (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ 𝒜 : Set (Set X),
    (∀ U ∈ 𝒜, IsOpen U) →
    ⋃₀ 𝒜 = Set.univ →
    ∃ ℬ : Set (Set X),
      IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (n + 1)

/-- A space has covering dimension less than `0` exactly when it is empty, and has covering
dimension less than `n + 1` exactly when it has covering dimension at most `n`. -/
abbrev HasCoveringDimensionLT (X : Type u) [TopologicalSpace X] : ℕ → Prop
  | 0 => IsEmpty X
  | n + 1 => HasCoveringDimensionLE X n

/-- Helper for Definition 50.3: a space is finite dimensional when it has some finite
covering-dimension bound. -/
abbrev FiniteCoveringDimension (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, HasCoveringDimensionLE X n

/-- Definition 50.3. The covering dimension of a space, valued in `WithBot ℕ∞`, with
`⊥` for dimension `-1` and `⊤` when no finite covering-dimension bound exists. -/
noncomputable abbrev coveringDimension (X : Type u) [TopologicalSpace X] : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ n : ℕ, d < n → HasCoveringDimensionLT X n}

namespace CoveringDimension

/-- The source notation `dim X` for the covering dimension of `X`. -/
scoped notation "dim " X:arg => coveringDimension X

end CoveringDimension
