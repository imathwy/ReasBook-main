module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Mathlib.Topology.Connected.Basic
import Topology_Munkres_2000.Book.Definition_23_1.Separation

public section

open scoped CoveringDimension

universe u

namespace ConnectedSpace

/-- Helper for Exercise 50.2: a family of order at most one is pairwise disjoint. -/
lemma orderOne_pairwiseDisjoint {X : Type u} {𝒰 : Set (Set X)}
    (horder : 𝒰.HasOrderLE 1) : 𝒰.PairwiseDisjoint id := by
  -- Two members meeting at a point must be the same member.
  intro U hU V hV hUV
  change Disjoint U V
  rw [Set.disjoint_left]
  intro z hzU hzV
  have hzorder := Set.hasOrderLE_iff.mp horder z
  have hunique := Set.encard_le_one_iff.mp hzorder
  have hUV_eq : U = V := hunique U V ⟨hU, hzU⟩ ⟨hV, hzV⟩
  exact hUV hUV_eq

/-- Helper for Exercise 50.2: each member of an open order-one cover is clopen. -/
lemma isClopen_of_mem_orderOneCover {X : Type u} [TopologicalSpace X]
    {𝒰 : Set (Set X)} (hopen : ∀ V ∈ 𝒰, IsOpen V)
    (hcover : ⋃₀ 𝒰 = Set.univ) (horder : 𝒰.HasOrderLE 1)
    {U : Set X} (hU : U ∈ 𝒰) : IsClopen U := by
  -- The complement of `U` is the union of all other cover members.
  have hcompl : Uᶜ = ⋃₀ (𝒰 \ {U}) := by
    ext z
    constructor
    · intro hz
      have hzuniv : z ∈ Set.univ := Set.mem_univ z
      rw [← hcover] at hzuniv
      obtain ⟨V, hV, hzV⟩ := hzuniv
      refine ⟨V, ⟨hV, ?_⟩, hzV⟩
      intro hVU
      exact hz (hVU ▸ hzV)
    · rintro ⟨V, ⟨hV, hVU⟩, hzV⟩
      intro hzU
      have hVU_ne : V ≠ U := by
        simpa only [Set.mem_singleton_iff] using hVU
      have hdisjoint := orderOne_pairwiseDisjoint horder hU hV hVU_ne.symm
      exact Set.disjoint_left.mp hdisjoint hzU hzV
  constructor
  · -- The displayed union is open, hence `U` is closed.
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_sUnion fun V hV ↦ hopen V hV.1
  · exact hopen U hU

/-- Helper for Exercise 50.2: a nontrivial `T1Space` of covering dimension zero
has a nonempty proper clopen subset. -/
lemma exists_nonempty_clopen_of_hasCoveringDimensionLE_zero
    {X : Type u} [TopologicalSpace X] [T1Space X] [Nontrivial X]
    (hdim : HasCoveringDimensionLE X 0) :
    ∃ U : Set X, IsClopen U ∧ U.Nonempty ∧ Uᶜ.Nonempty := by
  -- Refine the cover by complements of two distinct points.
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  let 𝒜 : Set (Set X) := {{x}ᶜ, {y}ᶜ}
  have h𝒜_open : ∀ U ∈ 𝒜, IsOpen U := by
    intro U hU
    rcases hU with hU | hU
    · rw [hU]
      exact isClosed_singleton.isOpen_compl
    · rw [Set.mem_singleton_iff.mp hU]
      exact isClosed_singleton.isOpen_compl
  have h𝒜_cover : ⋃₀ 𝒜 = Set.univ := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      by_cases hzx : z = x
      · refine ⟨{y}ᶜ, Set.mem_insert_iff.mpr (Or.inr rfl), ?_⟩
        simpa [hzx] using hxy
      · refine ⟨{x}ᶜ, Set.mem_insert_iff.mpr (Or.inl rfl), ?_⟩
        simpa using hzx
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order⟩ :=
    hdim 𝒜 h𝒜_open h𝒜_cover
  -- Choose the refining member through `x` and show that it omits `y`.
  have hx_cover : x ∈ ⋃₀ ℬ := by
    rw [hℬ_cover]
    exact Set.mem_univ x
  obtain ⟨U, hU, hxU⟩ := hx_cover
  have hyU : y ∉ U := by
    obtain ⟨A, hA, hUA⟩ := hℬ_refines.toIsRefinement.subset_of_mem hU
    rcases hA with hA | hA
    · have hx_not : x ∉ ({x}ᶜ : Set X) := by simp
      exact (hx_not (hA ▸ hUA hxU)).elim
    · have hUA_y : U ⊆ {y}ᶜ := by
        rwa [Set.mem_singleton_iff.mp hA] at hUA
      exact fun hy ↦ hUA_y hy rfl
  have hU_clopen := isClopen_of_mem_orderOneCover
    (fun V hV ↦ hℬ_refines.isOpen_of_mem hV) hℬ_cover hℬ_order hU
  -- The chosen points witness that the clopen set is nonempty and proper.
  exact ⟨U, hU_clopen, ⟨x, hxU⟩, ⟨y, hyU⟩⟩

/-- Exercise 50.2: Any connected `T1Space` with more than one point has covering
dimension at least `1`. -/
theorem one_le_coveringDimension {X : Type u} [TopologicalSpace X] [ConnectedSpace X]
    [T1Space X] [Nontrivial X] : 1 ≤ dim X := by
  -- It suffices to exclude the numerical zero-dimensional bound.
  have hpositive : (0 : WithBot ℕ∞) < dim X := by
    rw [← not_le]
    intro hdim
    have hzero : HasCoveringDimensionLE X 0 :=
      (coveringDimension_le_iff X 0).mp hdim
    obtain ⟨U, hU, hUne, hUcompl⟩ :=
      exists_nonempty_clopen_of_hasCoveringDimensionLE_zero hzero
    exact (preconnectedSpace_iff_no_separation X).mp inferInstance
      ⟨U, Uᶜ, hU.2, hU.1.isOpen_compl, disjoint_compl_right,
        hUne, hUcompl, Set.union_compl_self U⟩
  have hcast : ((0 : ℕ) : WithBot ℕ∞) + 1 = 1 := by
    have hzero : ((0 : ℕ) : WithBot ℕ∞) = 0 := rfl
    rw [hzero, zero_add]
  rw [← hcast]
  exact (ENat.WithBot.add_one_le_iff (n := 0) (m := dim X)).mpr hpositive

/-- A connected `T1Space` with more than one point is not zero-dimensional. -/
theorem not_hasCoveringDimensionLE_zero {X : Type u} [TopologicalSpace X]
    [ConnectedSpace X] [T1Space X] [Nontrivial X] :
    ¬HasCoveringDimensionLE X 0 := by
  -- A zero-dimensional bound would produce a forbidden separation.
  intro hdim
  obtain ⟨U, hU, hUne, hUcompl⟩ :=
    exists_nonempty_clopen_of_hasCoveringDimensionLE_zero hdim
  exact (preconnectedSpace_iff_no_separation X).mp inferInstance
    ⟨U, Uᶜ, hU.2, hU.1.isOpen_compl, disjoint_compl_right,
      hUne, hUcompl, Set.union_compl_self U⟩

end ConnectedSpace
