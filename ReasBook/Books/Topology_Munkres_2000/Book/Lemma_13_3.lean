module

public import Mathlib.Topology.Bases

public section

open Set

universe u

/-- Lemma 13.3: Given bases `ℬ` and `ℬ'` for topologies `𝒯` and `𝒯'` on `X`,
the topology `𝒯'` is finer than `𝒯` if and only if every `ℬ`-basis neighborhood
contains an `ℬ'`-basis neighborhood of the same point. -/
theorem TopologicalSpace.IsTopologicalBasis.topology_le_iff_refines {X : Type u}
    (𝒯 𝒯' : TopologicalSpace X) {ℬ ℬ' : Set (Set X)}
    (hℬ : 𝒯.IsTopologicalBasis ℬ) (hℬ' : 𝒯'.IsTopologicalBasis ℬ') :
    𝒯' ≤ 𝒯 ↔
      ∀ x B, B ∈ ℬ → x ∈ B → ∃ B', B' ∈ ℬ' ∧ x ∈ B' ∧ B' ⊆ B := by
  constructor
  · intro hle x B hB hx
    -- Transport the openness of `B` to the finer topology, then refine at `x`.
    have hBOpen : @IsOpen X 𝒯 B :=
      @TopologicalSpace.IsTopologicalBasis.isOpen X 𝒯 B ℬ hℬ hB
    have hBOpen' : @IsOpen X 𝒯' B := hle B hBOpen
    exact @TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open
      X 𝒯' ℬ' hℬ' x B hx hBOpen'
  · intro hrefine
    -- It suffices to refine every point of a `𝒯`-open set by an `ℬ'` element.
    rw [TopologicalSpace.le_def]
    intro U hUOpen
    rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X 𝒯' U ℬ' hℬ']
    intro x hx
    obtain ⟨B, hB, hxB, hBU⟩ :=
      @TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open
        X 𝒯 ℬ hℬ x U hx hUOpen
    obtain ⟨B', hB', hxB', hB'B⟩ := hrefine x B hB hxB
    exact ⟨B', hB', hxB', hB'B.trans hBU⟩
