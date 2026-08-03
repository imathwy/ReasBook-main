module

public import Topology_Munkres_2000.Book.Theorem_41_7

public section

universe u

open Function Set TopologicalSpace Topology

/-- Helper for Theorem 41.8: a locally finite family admits an open cover each
of whose members meets only finitely many sets in the family. -/
private lemma LocallyFinite.existsOpenCoverWithFiniteIntersections {ι : Type*}
    {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hs : LocallyFinite s) :
    ∃ U : X → Opens X, TopologicalSpace.IsOpenCover U ∧
      ∀ x, {i | (s i ∩ (U x : Set X)).Nonempty}.Finite := by
  classical
  -- Replace each witnessing neighborhood by its interior to obtain an open family.
  choose t htx htfinite using hs
  let U : X → Opens X := fun x ↦ ⟨interior (t x), isOpen_interior⟩
  refine ⟨U, ?_, ?_⟩
  · -- Every point lies in the open selected at that same point.
    apply TopologicalSpace.IsOpenCover.of_sets (v := fun x : X ↦ interior (t x))
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_iUnion]
    exact ⟨x, mem_of_mem_nhds (interior_mem_nhds.mpr (htx x))⟩
  · -- Shrinking the witness preserves finiteness of the intersecting indices.
    intro x
    exact (htfinite x).subset fun i hi ↦
      hi.mono (inter_subset_inter_right (s i) interior_subset)

/-- Helper for Theorem 41.8: finitely many positive constraints at each index
admit a positive weight below every applicable constraint. -/
private lemma existsPositiveWeightsLeOnFiniteSets {ι J : Type*} (A : J → Set ι)
    (hA : ∀ j, (A j).Finite) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ δ : J → ℝ, (∀ j, 0 < δ j) ∧ ∀ j i, i ∈ A j → δ j ≤ ε i := by
  classical
  -- At each index, use the finite infimum, with one as the empty-family fallback.
  have hchoice : ∀ j, ∃ d : ℝ, 0 < d ∧ ∀ i, i ∈ A j → d ≤ ε i := by
    intro j
    by_cases hj : (A j).Nonempty
    · have hAj : (hA j).toFinset.Nonempty :=
        (hA j).toFinset_nonempty.mpr hj
      refine ⟨(hA j).toFinset.inf' hAj ε, ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro i hi
        exact hε i
      · intro i hi
        exact Finset.inf'_le ε ((hA j).mem_toFinset.mpr hi)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro i hi
      exact False.elim (hj ⟨i, hi⟩)
  choose δ hδpos hδle using hchoice
  exact ⟨δ, hδpos, hδle⟩

namespace PartitionOfUnity

/-- Helper for Theorem 41.8: a partition of unity weighted by constants has a
continuous finsum. -/
private lemma continuousWeightedFinsum {J : Type*} {X : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity J X Set.univ) (δ : J → ℝ) :
    Continuous (fun x ↦ ∑ᶠ j, ρ j x • δ j) := by
  -- Constant weights satisfy the continuity requirement on every topological support.
  apply ρ.continuous_finsum_smul
  intro j x hx
  exact continuousAt_const

/-- Helper for Theorem 41.8: compatible positive weights on a partition of
unity produce an everywhere-positive continuous simultaneous minorant. -/
private lemma existsContinuousMapPosLeOnOfWeights {ι J : Type*} {X : Type*}
    [TopologicalSpace X] (ρ : PartitionOfUnity J X Set.univ) (s : ι → Set X)
    (ε : ι → ℝ) (δ : J → ℝ) (hδ : ∀ j, 0 < δ j)
    (hδle : ∀ j i, (s i ∩ tsupport (ρ j)).Nonempty → δ j ≤ ε i) :
    ∃ f : C(X, ℝ), (∀ x, 0 < f x) ∧ ∀ i, ∀ x ∈ s i, f x ≤ ε i := by
  let f : C(X, ℝ) :=
    ⟨fun x ↦ ∑ᶠ j, ρ j x • δ j, ρ.continuousWeightedFinsum δ⟩
  refine ⟨f, ?_, ?_⟩
  · -- One positive partition coefficient gives one positive weighted summand.
    intro x
    obtain ⟨j, hj⟩ := ρ.exists_pos (Set.mem_univ x)
    have hterm : 0 < ρ j x • δ j := by
      simpa only [smul_eq_mul] using mul_pos hj (hδ j)
    have hfinite : HasFiniteSupport (fun k ↦ ρ k x • δ k) :=
      (ρ.locallyFinite.point_finite x).subset fun k hk ↦
        support_smul_subset_left (fun l ↦ ρ l x) δ hk
    apply finsum_pos
    · intro k
      simpa only [smul_eq_mul] using mul_nonneg (ρ.nonneg k x) (hδ k).le
    · exact ⟨j, hterm⟩
    · exact hfinite
  · -- Compare each active weighted term with the prescribed bound, then sum.
    intro i x hx
    have weightedFinite (a : J → ℝ) : HasFiniteSupport (fun j ↦ ρ j x • a j) :=
      (ρ.locallyFinite.point_finite x).subset fun j hj ↦
        support_smul_subset_left (fun k ↦ ρ k x) a hj
    have hterm (j : J) : ρ j x • δ j ≤ ρ j x • ε i := by
      by_cases hj : ρ j x = 0
      · simp only [hj, zero_smul]
        exact le_rfl
      · have hxSupport : x ∈ support (ρ j) := hj
        have hxTopologicalSupport : x ∈ tsupport (ρ j) := subset_tsupport (ρ j) hxSupport
        exact smul_le_smul_of_nonneg_left
          (hδle j i ⟨x, hx, hxTopologicalSupport⟩) (ρ.nonneg j x)
    calc
      f x = ∑ᶠ j, ρ j x • δ j := rfl
      _ ≤ ∑ᶠ j, ρ j x • ε i :=
        finsum_le_finsum' (weightedFinite δ) (weightedFinite fun _ ↦ ε i) hterm
      _ = (∑ᶠ j, ρ j x) • ε i := (finsum_smul (fun j ↦ ρ j x) (ε i)).symm
      _ = ε i := by rw [ρ.sum_eq_one (Set.mem_univ x), one_smul]

end PartitionOfUnity

namespace LocallyFinite

/-- A positive bound on each member of a locally finite family admits an
everywhere-positive continuous simultaneous minorant. -/
theorem exists_continuousMap_pos_le {ι : Type*} {X : Type u} [TopologicalSpace X]
    [ParacompactSpace X] [T2Space X] {s : ι → Set X} (hs : LocallyFinite s)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ f : C(X, ℝ), (∀ x, 0 < f x) ∧ ∀ i, ∀ x ∈ s i, f x ≤ ε i := by
  classical
  -- Build the locally finite open cover and choose a subordinate partition of unity.
  obtain ⟨U, hU, hUfinite⟩ := hs.existsOpenCoverWithFiniteIntersections
  obtain ⟨ρ, hρ⟩ := hU.exists_partitionOfUnity
  -- Subordination transfers the finite-intersection property to each topological support.
  have hactive : ∀ a, {i | (s i ∩ tsupport (ρ a)).Nonempty}.Finite := by
    intro a
    exact (hUfinite a).subset fun i hi ↦
      hi.mono (inter_subset_inter_right (s i) (hρ a))
  -- Choose the finite-minimum weights and invoke the weighted-finsum interface.
  obtain ⟨δ, hδ, hδle⟩ :=
    existsPositiveWeightsLeOnFiniteSets
      (fun a ↦ {i | (s i ∩ tsupport (ρ a)).Nonempty}) hactive ε hε
  exact ρ.existsContinuousMapPosLeOnOfWeights s ε δ hδ hδle

end LocallyFinite
