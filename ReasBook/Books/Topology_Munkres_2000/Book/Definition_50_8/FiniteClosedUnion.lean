module

public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Theorem_50_1.ClosedSubspace
public import Mathlib.Topology.Homeomorph.Lemmas

public section

open Set

universe u v

/-- Helper for Definition 50.8: covering-dimension bounds are preserved by homeomorphisms. -/
lemma HasCoveringDimensionLE.homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {n : ℕ} (h : HasCoveringDimensionLE X n) :
    HasCoveringDimensionLE Y n := by
  -- Pull an arbitrary cover back to the source and push the controlled refinement forward.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒜 h𝒜open h𝒜cover
  let 𝒜' : Set (Set X) := (fun U : Set Y ↦ e ⁻¹' U) '' 𝒜
  have h𝒜'open : ∀ U ∈ 𝒜', IsOpen U := by
    rintro U ⟨A, hA, rfl⟩
    exact (h𝒜open A hA).preimage e.continuous
  have h𝒜'cover : ⋃₀ 𝒜' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨A, hA, hxA⟩ := hx
    exact ⟨e ⁻¹' A, ⟨A, hA, rfl⟩, hxA⟩
  obtain ⟨ℬ, hℬrefines, hℬcover, hℬorder⟩ := h 𝒜' h𝒜'open h𝒜'cover
  let ℬ' : Set (Set Y) := (fun B : Set X ↦ e '' B) '' ℬ
  refine ⟨ℬ', ?_, ?_, ?_⟩
  · -- Images of the pulled-back parents give an open refinement of the original cover.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨B, hB, rfl⟩
      obtain ⟨A', hA', hBA⟩ := hℬrefines.subset_of_mem hB
      obtain ⟨A, hA, rfl⟩ := hA'
      refine ⟨A, hA, ?_⟩
      rintro y ⟨x, hxB, rfl⟩
      exact hBA hxB
    · rintro V ⟨B, hB, rfl⟩
      exact e.isOpen_image.mpr (hℬrefines.isOpen_of_mem hB)
  · -- Surjectivity of the homeomorphism transports the covering property.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ ℬ := hℬcover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨B, hB, hyB⟩ := hy
    exact ⟨e '' B, ⟨B, hB, rfl⟩, ⟨e.symm y, hyB, e.apply_symm_apply y⟩⟩
  · -- Containing members correspond bijectively, so point multiplicity is unchanged.
    intro y
    let S : Set (Set X) := {B ∈ ℬ | e.symm y ∈ B}
    have hmembers : {V ∈ ℬ' | y ∈ V} = (fun B : Set X ↦ e '' B) '' S := by
      ext V
      constructor
      · rintro ⟨⟨B, hB, rfl⟩, hyB⟩
        obtain ⟨x, hxB, hxy⟩ := hyB
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨B, ⟨hB, hx ▸ hxB⟩, rfl⟩
      · rintro ⟨B, ⟨hB, hyB⟩, rfl⟩
        exact ⟨⟨B, hB, rfl⟩, ⟨e.symm y, hyB, e.apply_symm_apply y⟩⟩
    rw [hmembers, e.injective.image_injective.encard_image]
    exact hℬorder (e.symm y)

/-- Helper for Definition 50.8: a finite closed cover inherits the common
covering-dimension bound. -/
lemma HasCoveringDimensionLE.finite_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ)
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE X n := by
  -- Convert the finite closed-union formula into numerical upper bounds.
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_closed Y hclosed hcover,
    Finset.sup_le_iff]
  intro i _
  exact (coveringDimension_le_iff (Y i) n).mpr (hdim i)

/-- Helper for Definition 50.8: a finite union of closed subspaces with a common
covering-dimension bound has that same bound. -/
lemma HasCoveringDimensionLE.finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE (⋃ i, Y i) n := by
  -- Cover the union subtype by closed preimage pieces and identify each piece once.
  let Z : Set X := ⋃ i, Y i
  let Zi : ι → Set Z := fun i ↦ Subtype.val ⁻¹' Y i
  apply HasCoveringDimensionLE.finite_iUnion_closed Zi
  · intro i
    exact (hclosed i).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro z
    rw [Set.mem_iUnion]
    have hz : z.1 ∈ ⋃ i, Y i := z.2
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact ⟨i, hzi⟩
  · intro i
    -- The original member and its preimage piece contain exactly the same ambient points.
    let hYZ : Y i ⊆ Z := fun _ hy ↦ Set.mem_iUnion.mpr ⟨i, hy⟩
    let inc : Y i → Z := Set.inclusion hYZ
    let f : Y i → Zi i := fun y ↦ ⟨inc y, y.2⟩
    have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hYZ
    have hf : Topology.IsEmbedding f := hinc.codRestrict _ fun y ↦ y.2
    have hfsurj : Function.Surjective f := by
      intro z
      refine ⟨⟨z.1.1, z.2⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)
    exact (hdim i).homeomorph (hf.toHomeomorphOfSurjective hfsurj)

/-- Helper for Definition 50.8: the strict covering-dimension bound is preserved by finite
unions of closed subspaces. -/
lemma hasCoveringDimensionLT_finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLT (Y i) n) :
    HasCoveringDimensionLT (⋃ i, Y i) n := by
  -- At zero every member is empty; at a successor use the non-strict union theorem.
  cases n with
  | zero =>
      apply (hasCoveringDimensionLT_zero_iff _).mpr
      constructor
      intro z
      have hz : z.1 ∈ ⋃ i, Y i := z.2
      rw [Set.mem_iUnion] at hz
      obtain ⟨i, hzi⟩ := hz
      exact ((hasCoveringDimensionLT_zero_iff _).mp (hdim i)).false ⟨z.1, hzi⟩
  | succ n =>
      exact HasCoveringDimensionLE.finiteUnionClosedSubtypes Y hclosed hdim

/-- Helper for Definition 50.8: a closed subspace of a space with a strict
covering-dimension bound inherits that bound. -/
lemma HasCoveringDimensionLT.closedSubset
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (h : HasCoveringDimensionLT Z n) (hYZ : Y ⊆ Z) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  -- Split off the empty-space case; successor bounds use the closed-subtype theorem.
  cases n with
  | zero =>
      apply (hasCoveringDimensionLT_zero_iff _).mpr
      constructor
      intro y
      exact ((hasCoveringDimensionLT_zero_iff _).mp h).false ⟨y.1, hYZ y.2⟩
  | succ n =>
      let P : Set Z := Subtype.val ⁻¹' Y
      have hPclosed : IsClosed P := hY.preimage continuous_subtype_val
      have hP : HasCoveringDimensionLE P n := h.closedSubtype hPclosed
      let hYZ' : Y ⊆ Z := hYZ
      let inc : Y → Z := Set.inclusion hYZ'
      let f : Y → P := fun y ↦ ⟨inc y, y.2⟩
      have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hYZ'
      have hf : Topology.IsEmbedding f := hinc.codRestrict _ fun y ↦ y.2
      have hfsurj : Function.Surjective f := by
        intro z
        refine ⟨⟨z.1.1, z.2⟩, ?_⟩
        exact Subtype.ext (Subtype.ext rfl)
      exact hP.homeomorph (hf.toHomeomorphOfSurjective hfsurj).symm
