module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Remark_50_2.BarycentricParity
public import Topology_Munkres_2000.Book.Remark_50_2.SimplexGrid
public import Topology_Munkres_2000.Book.Exercise_46_10.SigmaCompact
public import Topology_Munkres_2000.Book.Theorem_50_1.ClosedSubspace
public import Topology_Munkres_2000.Book.Theorem_50_6
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.SeparatedMap
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Ring.Nat

public section

universe u v

open Set
open scoped CoveringDimension

/-- Helper for Remark 50.2: covering-dimension bounds are invariant under homeomorphisms. -/
private lemma coveringDimensionBoundHomeomorph
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {n : ℕ} (h : HasCoveringDimensionLE X n) :
    HasCoveringDimensionLE Y n := by
  -- Pull a target cover to `X`, use the given bound there, and push the refinement forward.
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
  · -- Images of pulled-back parents form an open refinement of the original cover.
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
  · -- Surjectivity transports the covering property.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ ℬ := hℬcover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨B, hB, hyB⟩ := hy
    exact ⟨e '' B, ⟨B, hB, rfl⟩, ⟨e.symm y, hyB, e.apply_symm_apply y⟩⟩
  · -- Sets through `y` are indexed injectively by sets through `e.symm y`.
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

/-- Helper for Remark 50.2: a finite closed cover inherits a common
covering-dimension bound. -/
private lemma coveringDimensionBoundFiniteClosedCover
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ)
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE X n := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- Translate the finite-union formula to the common numerical upper bound.
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_closed Y hclosed hcover,
    Finset.sup_le_iff]
  intro i _
  exact (coveringDimension_le_iff (Y i) n).mpr (hdim i)

/-- Helper for Remark 50.2: a finite union of closed subspaces with a common
covering-dimension bound has the same bound. -/
private lemma coveringDimensionBoundFiniteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE (⋃ i, Y i) n := by
  -- Pull each closed member back to the union subtype, then use its canonical homeomorphism.
  let Z : Set X := ⋃ i, Y i
  let Zi : ι → Set Z := fun i ↦ Subtype.val ⁻¹' Y i
  apply coveringDimensionBoundFiniteClosedCover Zi
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
    let hYZ : Y i ⊆ Z := fun _ hy ↦ Set.mem_iUnion.mpr ⟨i, hy⟩
    let inc : Y i → Z := Set.inclusion hYZ
    let f : Y i → Zi i := fun y ↦ ⟨inc y, y.2⟩
    have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hYZ
    have hf : Topology.IsEmbedding f := hinc.codRestrict _ fun y ↦ y.2
    have hfsurj : Function.Surjective f := by
      intro z
      refine ⟨⟨z.1.1, z.2⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact Eq.refl z.1.1
    exact coveringDimensionBoundHomeomorph
      (hf.toHomeomorphOfSurjective hfsurj) (hdim i)

/-- Helper for Remark 50.2: a compact subset of a Euclidean-charted locally compact
Hausdorff space is a finite union of compact closed chart pieces. -/
private lemma existsFiniteCompactChartCover {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    ∃ (t : Finset M) (C : t → Set M), K = ⋃ i, C i ∧
      (∀ i, IsClosed (C i)) ∧ (∀ i, IsCompact (C i)) ∧
      ∀ i, C i ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source := by
  classical
  -- Reduce the chart-source cover of `K` to finitely many sources.
  have hchartOpen : ∀ x : M,
      IsOpen (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x
    exact (chartAt (EuclideanSpace ℝ (Fin m)) x).open_source
  have hchartCover :
      K ⊆ ⋃ x : M, (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin m)) x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin m)) x).source)
    hchartOpen hchartCover
  let U : t → Set M := fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source
  have hKU : K ⊆ ⋃ i, U i := by
    intro x hx
    have hxcover := ht hx
    simp only [Set.mem_iUnion] at hxcover ⊢
    obtain ⟨i, hi, hxi⟩ := hxcover
    exact ⟨⟨i, hi⟩, hxi⟩
  -- Shrink the finite open cover to compact closed subsets still inside their charts.
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact (chartAt (EuclideanSpace ℝ (Fin m)) i.1).open_source
  have hUpointFinite : ∀ x ∈ K, {i | x ∈ U i}.Finite := by
    intro _ _
    exact Set.toFinite _
  obtain ⟨V, hKV, hVclosed, hVsubset, hVcompact⟩ :=
    exists_subset_iUnion_compact_subset_t2space (u := U) hK hUopen hUpointFinite hKU
  let C : t → Set M := fun i ↦ K ∩ V i
  refine ⟨t, C, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hxK
      have hxV := hKV hxK
      rw [Set.mem_iUnion] at hxV ⊢
      obtain ⟨i, hxi⟩ := hxV
      exact ⟨i, hxK, hxi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact hxi.1
  · intro i
    exact hK.isClosed.inter (hVclosed i)
  · intro i
    exact (hVcompact i).inter_left hK.isClosed
  · intro i _ hxi
    exact hVsubset i hxi.2

/-- Helper for Remark 50.2: a compact set contained in one chart source has covering
dimension at most the dimension of the Euclidean model. -/
private lemma compactSubsetChartSourceHasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    (K : Set M) (hK : IsCompact K) (x : M)
    (hKsource : K ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) x).source) :
    HasCoveringDimensionLE K m := by
  -- Restrict the chart and transfer the Euclidean compact-subset bound back to `K`.
  have himageCompact :
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) :=
    hK.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin m)) x).continuousOn.mono hKsource)
  have himageIdentity :
      (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K =
        (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K := by
    rfl
  let restrictedChart :
      K ≃ₜ (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K :=
    (chartAt (EuclideanSpace ℝ (Fin m)) x).homeomorphOfImageSubsetSource
      hKsource himageIdentity
  have himageDimension :
      HasCoveringDimensionLE
        ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) m :=
    compactSubset_euclideanSpace_hasCoveringDimensionLE _ himageCompact
  exact coveringDimensionBoundHomeomorph restrictedChart.symm himageDimension

/-- Helper for Remark 50.2: every compact subset of a locally compact Hausdorff space
charted by `EuclideanSpace ℝ (Fin m)` has covering dimension at most `m`. -/
private lemma compactSubsetChartedSpaceHasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    HasCoveringDimensionLE K m := by
  -- Bound every member of the finite chart cover, then assemble the closed union.
  obtain ⟨t, C, hCunion, hCclosed, hCcompact, hCsource⟩ :=
    existsFiniteCompactChartCover (m := m) K hK
  have hCdimension : ∀ i, HasCoveringDimensionLE (C i) m := by
    intro i
    exact compactSubsetChartSourceHasCoveringDimensionLE
      (C i) (hCcompact i) i.1 (hCsource i)
  have hunionDimension :=
    coveringDimensionBoundFiniteUnionClosedSubtypes C hCclosed hCdimension
  rw [hCunion]
  exact hunionDimension

/-- Helper for Remark 50.2: a dimension-bounded compact subtype admits an ambient open
refinement with the same multiplicity bound at points of the compact set. -/
private lemma existsOpenRefinementWithOrderOnCompact {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (S : Set X) (hS_compact : IsCompact S)
    (hS_dim : HasCoveringDimensionLE S m) (ℬ : Set (Set X))
    (hℬ_open : ∀ B ∈ ℬ, IsOpen B) (hℬ_cover : ⋃₀ ℬ = Set.univ) :
    ∃ 𝒞 : Set (Set X), IsOpenRefinement 𝒞 ℬ ∧ ⋃₀ 𝒞 = Set.univ ∧
      ∀ x ∈ S, Set.encard {C ∈ 𝒞 | x ∈ C} ≤ (m + 1 : ℕ) := by
  classical
  let restrictedCover : Set (Set S) :=
    {U | ∃ B ∈ ℬ, U = Subtype.val ⁻¹' B}
  have hrestricted_open : ∀ U ∈ restrictedCover, IsOpen U := by
    rintro U ⟨B, hB, rfl⟩
    exact (hℬ_open B hB).preimage continuous_subtype_val
  have hrestricted_cover : ⋃₀ restrictedCover = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ ⋃₀ ℬ := by
      rw [hℬ_cover]
      exact Set.mem_univ x.1
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨Subtype.val ⁻¹' B, ⟨B, hB, rfl⟩, hxB⟩
  obtain ⟨𝒟, h𝒟_refines, h𝒟_cover, h𝒟_order⟩ :=
    hS_dim restrictedCover hrestricted_open hrestricted_cover
  rw [Set.hasOrderLE_iff] at h𝒟_order
  have h_parent_exists (D : 𝒟) :
      ∃ B ∈ ℬ, D.1 ⊆ Subtype.val ⁻¹' B := by
    obtain ⟨U, ⟨B, hB, rfl⟩, hDU⟩ := h𝒟_refines.subset_of_mem D.2
    exact ⟨B, hB, hDU⟩
  choose parent hparent_mem hD_parent using h_parent_exists
  have h_ambient_exists (D : 𝒟) :
      ∃ O : Set X, IsOpen O ∧ Subtype.val ⁻¹' O = D.1 := by
    exact isOpen_induced_iff.mp (h𝒟_refines.isOpen_of_mem D.2)
  choose ambient hambient_open hambient_preimage using h_ambient_exists
  let lift : 𝒟 → Set X := fun D ↦ ambient D ∩ parent D
  let outside : Set (Set X) := {C | ∃ B ∈ ℬ, C = B ∩ Sᶜ}
  let 𝒞 : Set (Set X) := Set.range lift ∪ outside
  refine ⟨𝒞, ?_, ?_, ?_⟩
  · -- Both lifted and exterior members are open subsets of members of `ℬ`.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      intro C hC
      rcases hC with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · exact ⟨parent D, hparent_mem D, fun _ hz ↦ hz.2⟩
      · exact ⟨B, hB, Set.inter_subset_left⟩
    · intro C hC
      rcases hC with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · exact (hambient_open D).inter (hℬ_open (parent D) (hparent_mem D))
      · exact (hℬ_open B hB).inter hS_compact.isClosed.isOpen_compl
  · -- Lifted members cover `S`, while exterior intersections cover its complement.
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxS : x ∈ S
    · have hxD : (⟨x, hxS⟩ : S) ∈ ⋃₀ 𝒟 := by
        rw [h𝒟_cover]
        exact Set.mem_univ _
      rw [Set.mem_sUnion] at hxD ⊢
      obtain ⟨D, hD, hxD⟩ := hxD
      let D' : 𝒟 := ⟨D, hD⟩
      refine ⟨lift D', Or.inl ⟨D', rfl⟩, ?_⟩
      constructor
      · exact (Set.ext_iff.mp (hambient_preimage D') ⟨x, hxS⟩).mpr hxD
      · exact hD_parent D' hxD
    · have hxB : x ∈ ⋃₀ ℬ := by
        rw [hℬ_cover]
        exact Set.mem_univ x
      rw [Set.mem_sUnion] at hxB ⊢
      obtain ⟨B, hB, hxB⟩ := hxB
      exact ⟨B ∩ Sᶜ, Or.inr ⟨B, hB, rfl⟩, ⟨hxB, hxS⟩⟩
  · -- At a point of `S`, exterior members disappear and lifted membership comes from `𝒟`.
    intro x hxS
    let source : Set 𝒟 := {D | (⟨x, hxS⟩ : S) ∈ D.1}
    have hmembers_subset : {C ∈ 𝒞 | x ∈ C} ⊆ lift '' source := by
      intro C hC
      rcases hC.1 with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · refine ⟨D, ?_, rfl⟩
        simpa only [source, Set.mem_setOf_eq] using
          (Set.ext_iff.mp (hambient_preimage D) ⟨x, hxS⟩).mp hC.2.1
      · exact (hC.2.2 hxS).elim
    have hsource_image : Subtype.val '' source =
        {D ∈ 𝒟 | (⟨x, hxS⟩ : S) ∈ D} := by
      ext D
      constructor
      · rintro ⟨D', hD', rfl⟩
        exact ⟨D'.2, hD'⟩
      · rintro ⟨hD, hxD⟩
        exact ⟨⟨D, hD⟩, hxD, rfl⟩
    calc
      Set.encard {C ∈ 𝒞 | x ∈ C} ≤ Set.encard (lift '' source) :=
        Set.encard_le_encard hmembers_subset
      _ ≤ Set.encard source := Set.encard_image_le lift source
      _ = Set.encard (Subtype.val '' source) :=
        (Subtype.val_injective.encard_image source).symm
      _ = Set.encard {D ∈ 𝒟 | (⟨x, hxS⟩ : S) ∈ D} := congrArg Set.encard hsource_image
      _ ≤ (m + 1 : ℕ) := h𝒟_order (⟨x, hxS⟩ : S)


/-- Helper for Remark 50.2: a shifted compact exhaustion supports an open refinement whose
members meeting one compact stage lie in the next stage. -/
private lemma existsControlledOpenRefinement {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (𝒜 : Set (Set X))
    (h𝒜_open : ∀ U ∈ 𝒜, IsOpen U) (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X), IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
      ∀ n B, B ∈ ℬ → (B ∩ K n).Nonempty → B ⊆ K (n + 1) := by
  classical
  -- Choose one member of the original cover through each point.
  have h_parent_exists (x : X) : ∃ U ∈ 𝒜, x ∈ U := by
    have hx : x ∈ ⋃₀ 𝒜 := by
      rw [h𝒜_cover]
      exact Set.mem_univ x
    simpa only [Set.mem_sUnion] using hx
  choose parent hparent_mem hx_parent using h_parent_exists
  let neighborhood : X → Set X := fun x ↦
    parent x ∩ interior (K (K.find x + 1)) ∩ (K (K.find x - 1))ᶜ
  refine ⟨Set.range neighborhood, ?_, ?_, ?_⟩
  · -- Each chosen neighborhood is open and remains inside its selected parent.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      rintro B ⟨x, rfl⟩
      exact ⟨parent x, hparent_mem x, fun _ hz ↦ hz.1.1⟩
    · rintro B ⟨x, rfl⟩
      exact ((h𝒜_open (parent x) (hparent_mem x)).inter isOpen_interior).inter
        (K.isCompact (K.find x - 1)).isClosed.isOpen_compl
  · -- Every point belongs to its own chosen neighborhood.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    refine ⟨neighborhood x, ⟨x, rfl⟩, ⟨⟨hx_parent x, ?_⟩, ?_⟩⟩
    · exact K.subset_interior_succ (K.find x) (K.mem_find x)
    · intro hx_lower
      have hfind_pos : 0 < K.find x := by
        by_contra h
        have hfind_zero : K.find x = 0 := Nat.eq_zero_of_not_pos h
        have : x ∈ (∅ : Set X) := by
          rw [← hK_zero, ← hfind_zero]
          exact K.mem_find x
        exact this
      have hfind_le_pred : K.find x ≤ K.find x - 1 :=
        K.mem_iff_find_le.mp hx_lower
      omega
  · -- Meeting `K n` forces the center rank below `n + 1`, hence controls the whole set.
    rintro n B ⟨x, rfl⟩ ⟨y, hyB, hyK⟩ z hz
    have hfind_pos : 0 < K.find x := by
      by_contra h
      have hfind_zero : K.find x = 0 := Nat.eq_zero_of_not_pos h
      have : x ∈ (∅ : Set X) := by
        rw [← hK_zero, ← hfind_zero]
        exact K.mem_find x
      exact this
    have hnot_le : ¬ n ≤ K.find x - 1 := by
      intro hn
      exact hyB.2 (K.subset hn hyK)
    have hfind_le : K.find x ≤ n := by omega
    exact K.subset (Nat.add_le_add_right hfind_le 1) (interior_subset hz.1.2)

/-- Helper for Remark 50.2: `CoverStage K m ℬ₀ n ℬ` records refinement, coverage, and
the order bound on the `n`th compact stage. -/
private def CoverStage {X : Type u} [TopologicalSpace X] (K : CompactExhaustion X) (m : ℕ)
    (ℬ₀ : Set (Set X)) (n : ℕ) (ℬ : Set (Set X)) : Prop :=
  IsOpenRefinement ℬ ℬ₀ ∧ ⋃₀ ℬ = Set.univ ∧
    ∀ x ∈ K n, Set.encard {B ∈ ℬ | x ∈ B} ≤ (m + 1 : ℕ)

/-- Helper for Remark 50.2: a member of a refining cover that meets the preceding compact
stage is contained in the current compact stage. -/
private lemma subset_compactStage_of_meets_previous {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (ℬ₀ ℬ : Set (Set X))
    (hℬ_refines : IsRefinement ℬ ℬ₀)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (n : ℕ) (B : Set X) (hB : B ∈ ℬ) (hB_meets : (B ∩ K (n - 1)).Nonempty) :
    B ⊆ K n := by
  -- Pass to an initial-cover parent and apply its support control.
  cases n with
  | zero =>
      obtain ⟨x, _, hxK⟩ := hB_meets
      rw [hK_zero] at hxK
      exact hxK.elim
  | succ n =>
      obtain ⟨B₀, hB₀, hBB₀⟩ := hℬ_refines.subset_of_mem hB
      have hB₀_meets : (B₀ ∩ K (Nat.succ n - 1)).Nonempty := by
        obtain ⟨x, hxB, hxK⟩ := hB_meets
        exact ⟨x, hBB₀ hxB, hxK⟩
      have hB₀_subset : B₀ ⊆ K ((Nat.succ n - 1) + 1) :=
        hℬ₀_control (Nat.succ n - 1) B₀ hB₀ hB₀_meets
      simpa using hBB₀.trans hB₀_subset

/-- Helper for Remark 50.2: membership of a set meeting a fixed compact core persists
forward through a core-stable sequence of covers. -/
private lemma coverMembership_persists {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (ℬ : ℕ → Set (Set X))
    (hstable : ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n))
    {q start : ℕ} {B : Set X} (hB_meets : (B ∩ K q).Nonempty)
    (hstart : q + 2 ≤ start) (hB_start : B ∈ ℬ start) :
    ∀ n ≥ start, B ∈ ℬ n := by
  -- At every later transition, `K q` lies in the stability core `K (n - 1)`.
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hB_start
  | succ n hn hBn =>
      have hq_pred : q ≤ n - 1 := by omega
      have hB_meets_pred : (B ∩ K (n - 1)).Nonempty := by
        obtain ⟨x, hxB, hxK⟩ := hB_meets
        exact ⟨x, hxB, K.subset hq_pred hxK⟩
      exact (hstable n B hB_meets_pred).2 hBn

/-- Helper for Remark 50.2: the sets belonging to every sufficiently late cover in a
sequence. -/
private def EventuallyStableCover {X : Type u} (ℬ : ℕ → Set (Set X)) : Set (Set X) :=
  {B | ∃ N, ∀ n ≥ N, B ∈ ℬ n}

/-- Helper for Remark 50.2: eventual membership in a core-stable sequence defines an open
refinement covering the space with the global stagewise order bound. -/
private lemma eventuallyStableCover_spec {m : ℕ} {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (ℬ₀ : Set (Set X)) (ℬ : ℕ → Set (Set X))
    (hstage : ∀ n, CoverStage K m ℬ₀ n (ℬ n))
    (hstable : ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n)) :
    IsOpenRefinement (EventuallyStableCover ℬ) ℬ₀ ∧
      ⋃₀ EventuallyStableCover ℬ = Set.univ ∧
      (EventuallyStableCover ℬ).HasOrderLE (m + 1) := by
  classical
  let eventual : Set (Set X) := EventuallyStableCover ℬ
  refine ⟨?_, ?_, ?_⟩
  · -- An eventual member belongs to one stage, so stage refinement supplies openness and a parent.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      intro B hB
      obtain ⟨N, hN⟩ := hB
      exact (hstage N).1.1.subset_of_mem (hN N le_rfl)
    · intro B hB
      obtain ⟨N, hN⟩ := hB
      exact (hstage N).1.isOpen_of_mem (hN N le_rfl)
  · -- Start two stages beyond a compact core containing the point, then persist forward.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨q, hxq⟩ := K.exists_mem x
    have hxcover : x ∈ ⋃₀ ℬ (q + 2) := by
      rw [(hstage (q + 2)).2.1]
      exact Set.mem_univ x
    rw [Set.mem_sUnion] at hxcover ⊢
    obtain ⟨B, hB_stage, hxB⟩ := hxcover
    have hB_meets : (B ∩ K q).Nonempty := ⟨x, hxB, hxq⟩
    refine ⟨B, ?_, hxB⟩
    exact ⟨q + 2, coverMembership_persists K ℬ hstable hB_meets le_rfl hB_stage⟩
  · -- Every eventual member through `x` already belongs to the fixed stage two beyond its core.
    rw [Set.hasOrderLE_iff]
    intro x
    obtain ⟨q, hxq⟩ := K.exists_mem x
    have hmembers_subset : {B ∈ eventual | x ∈ B} ⊆ {B ∈ ℬ (q + 2) | x ∈ B} := by
      intro B hB
      obtain ⟨N, hN⟩ := hB.1
      have hB_meets : (B ∩ K q).Nonempty := ⟨x, hB.2, hxq⟩
      by_cases hN_le : N ≤ q + 2
      · exact ⟨hN (q + 2) hN_le, hB.2⟩
      · have hstart : q + 2 ≤ N := by omega
        have hbackward : B ∈ ℬ (q + 2) := by
          refine Nat.decreasingInduction' (m := q + 2) (n := N) ?_ hstart (hN N le_rfl)
          intro k _ hk_lower hBk
          have hq_pred : q ≤ k - 1 := by omega
          have hB_meets_pred : (B ∩ K (k - 1)).Nonempty := by
            obtain ⟨y, hyB, hyK⟩ := hB_meets
            exact ⟨y, hyB, K.subset hq_pred hyK⟩
          exact (hstable k B hB_meets_pred).1 hBk
        exact ⟨hbackward, hB.2⟩
    exact (Set.encard_le_encard hmembers_subset).trans ((hstage (q + 2)).2.2 x
      (K.subset (by omega) hxq))

/-- Helper for Remark 50.2: retain a parent meeting the core, and otherwise replace it by
the union of its selected children. -/
private def coreReplacement {X : Type u} (core : Set X) (𝒞 : Set (Set X))
    (parent : Set X → Set X) (B : Set X) : Set X :=
  @ite (Set X) (B ∩ core).Nonempty (Classical.propDecidable _)
    B (⋃₀ {C ∈ 𝒞 | parent C = B})

/-- Helper for Remark 50.2: every core replacement is contained in its parent when each
selected child is contained in its parent. -/
private lemma coreReplacement_subset_parent {X : Type u} (core : Set X)
    (𝒞 : Set (Set X)) (parent : Set X → Set X)
    (hchild : ∀ C ∈ 𝒞, C ⊆ parent C) (B : Set X) :
    coreReplacement core 𝒞 parent B ⊆ B := by
  -- The retained branch is immediate; union membership supplies a child in the other branch.
  by_cases hB_core : (B ∩ core).Nonempty
  · simpa only [coreReplacement, if_pos hB_core] using (Set.Subset.rfl : B ⊆ B)
  · rw [coreReplacement, if_neg hB_core]
    intro x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨C, ⟨hC, hparent⟩, hxC⟩ := hx
    exact hparent ▸ hchild C hC hxC

/-- Helper for Remark 50.2: members through a point in an image-indexed replacement family
come from replacements of old members through that point. -/
private lemma coreReplacementMembers_subset_parentImage {X : Type u}
    (replacement : Set X → Set X) (ℬ : Set (Set X)) (x : X)
    (hsubset : ∀ B ∈ ℬ, replacement B ⊆ B) :
    {R ∈ replacement '' ℬ | x ∈ R} ⊆ replacement '' {B ∈ ℬ | x ∈ B} := by
  -- Unpack the replacement witness and transport point membership to its old parent.
  rintro R ⟨⟨B, hB, rfl⟩, hx⟩
  exact ⟨B, ⟨hB, hsubset B hB hx⟩, rfl⟩

/-- Helper for Remark 50.2: outside a controlled set, every replacement member through a
point is indexed by the parent of a child through that point. -/
private lemma coreReplacementMembersOutside_subset_childParentImage {X : Type u}
    (core controlled : Set X) (𝒞 ℬ : Set (Set X)) (parent : Set X → Set X) (x : X)
    (hcore_control : ∀ B ∈ ℬ, (B ∩ core).Nonempty → B ⊆ controlled)
    (hx_controlled : x ∉ controlled) :
    {R ∈ coreReplacement core 𝒞 parent '' ℬ | x ∈ R} ⊆
      coreReplacement core 𝒞 parent '' (parent '' {C ∈ 𝒞 | x ∈ C}) := by
  -- A retained parent would put `x` in the controlled set, so only the child-union branch remains.
  rintro R ⟨⟨B, hB, rfl⟩, hxR⟩
  have hB_core : ¬(B ∩ core).Nonempty := by
    intro hB_core
    have hxB : x ∈ B := by
      simpa only [coreReplacement, if_pos hB_core] using hxR
    exact hx_controlled (hcore_control B hB hB_core hxB)
  rw [coreReplacement, if_neg hB_core, Set.mem_sUnion] at hxR
  obtain ⟨C, ⟨hC, hparent⟩, hxC⟩ := hxR
  refine ⟨B, ?_, rfl⟩
  exact ⟨C, ⟨hC, hxC⟩, hparent⟩

/-- Helper for Remark 50.2: one cover stage can be refined while preserving exactly the
members meeting the preceding compact core. -/
private lemma existsCoreStableCoverStage {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (ℬ₀ ℬ : Set (Set X))
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (hstage : CoverStage K m ℬ₀ n ℬ)
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ' : Set (Set X), CoverStage K m ℬ₀ (n + 1) ℬ' ∧ IsRefinement ℬ' ℬ ∧
      ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ' ↔ B ∈ ℬ) := by
  classical
  -- Construction normalization: use raw-set images rather than a subtype-indexed range, so both
  -- multiplicity bounds reduce directly to image-cardinality inequalities.
  obtain ⟨𝒞, h𝒞_refines, h𝒞_cover, h𝒞_order⟩ :=
    existsOpenRefinementWithOrderOnCompact (K (n + 1)) (K.isCompact (n + 1))
      (h_dim (K (n + 1)) (K.isCompact (n + 1))) ℬ
      (fun _ hB ↦ hstage.1.isOpen_of_mem hB) hstage.2.1
  have hparent_exists (C : Set X) : ∃ B : Set X, C ∈ 𝒞 → B ∈ ℬ ∧ C ⊆ B := by
    by_cases hC : C ∈ 𝒞
    · obtain ⟨B, hB, hCB⟩ := h𝒞_refines.subset_of_mem hC
      exact ⟨B, fun _ ↦ ⟨hB, hCB⟩⟩
    · exact ⟨∅, fun hC' ↦ (hC hC').elim⟩
  choose parent hparent_spec using hparent_exists
  let core : Set X := K (n - 1)
  let replacement : Set X → Set X := coreReplacement core 𝒞 parent
  let ℬ' : Set (Set X) := replacement '' ℬ
  have hparent_mem (C : Set X) (hC : C ∈ 𝒞) : parent C ∈ ℬ :=
    (hparent_spec C hC).1
  have hchild_subset (C : Set X) (hC : C ∈ 𝒞) : C ⊆ parent C :=
    (hparent_spec C hC).2
  have hreplacement_subset (B : Set X) (hB : B ∈ ℬ) : replacement B ⊆ B := by
    exact coreReplacement_subset_parent core 𝒞 parent hchild_subset B
  have hcore_control (B : Set X) (hB : B ∈ ℬ)
      (hB_core : (B ∩ core).Nonempty) : B ⊆ K n := by
    exact subset_compactStage_of_meets_previous K hK_zero ℬ₀ ℬ hstage.1.1
      hℬ₀_control n B hB hB_core
  have hreplacement_open (B : Set X) (hB : B ∈ ℬ) : IsOpen (replacement B) := by
    -- Retained parents are already open; otherwise openness follows from the child union.
    by_cases hB_core : (B ∩ core).Nonempty
    · simpa only [replacement, coreReplacement, if_pos hB_core] using
        hstage.1.isOpen_of_mem hB
    · simp only [replacement, coreReplacement, if_neg hB_core]
      exact isOpen_sUnion fun C hC ↦ h𝒞_refines.isOpen_of_mem hC.1
  have hℬ'_refines : IsRefinement ℬ' ℬ := by
    rw [isRefinement_iff]
    rintro R ⟨B, hB, rfl⟩
    exact ⟨B, hB, hreplacement_subset B hB⟩
  have hℬ'_open : ∀ R ∈ ℬ', IsOpen R := by
    rintro R ⟨B, hB, rfl⟩
    exact hreplacement_open B hB
  have hℬ'_cover : ⋃₀ ℬ' = Set.univ := by
    -- A child through `x` either lies in its retained parent or in that parent's replacement union.
    apply Set.eq_univ_of_forall
    intro x
    have hx𝒞 : x ∈ ⋃₀ 𝒞 := by
      rw [h𝒞_cover]
      exact Set.mem_univ x
    rw [Set.mem_sUnion] at hx𝒞 ⊢
    obtain ⟨C, hC, hxC⟩ := hx𝒞
    refine ⟨replacement (parent C), ⟨parent C, hparent_mem C hC, rfl⟩, ?_⟩
    by_cases hparent_core : (parent C ∩ core).Nonempty
    · simp only [replacement, coreReplacement, if_pos hparent_core]
      exact hchild_subset C hC hxC
    · simp only [replacement, coreReplacement, if_neg hparent_core, Set.mem_sUnion]
      exact ⟨C, ⟨hC, rfl⟩, hxC⟩
  have hℬ'_order : ∀ x ∈ K (n + 1),
      Set.encard {R ∈ ℬ' | x ∈ R} ≤ (m + 1 : ℕ) := by
    intro x hx_stage
    by_cases hx_controlled : x ∈ K n
    · -- On the old stage, replacement membership maps to old-parent membership.
      have hmembers_subset : {R ∈ ℬ' | x ∈ R} ⊆
          replacement '' {B ∈ ℬ | x ∈ B} :=
        coreReplacementMembers_subset_parentImage replacement ℬ x hreplacement_subset
      calc
        Set.encard {R ∈ ℬ' | x ∈ R} ≤
            Set.encard (replacement '' {B ∈ ℬ | x ∈ B}) :=
          Set.encard_le_encard hmembers_subset
        _ ≤ Set.encard {B ∈ ℬ | x ∈ B} :=
          Set.encard_image_le replacement {B ∈ ℬ | x ∈ B}
        _ ≤ (m + 1 : ℕ) := hstage.2.2 x hx_controlled
    · -- Outside the old stage, every member is indexed by a child through `x` and its parent.
      have hmembers_subset : {R ∈ ℬ' | x ∈ R} ⊆
          replacement '' (parent '' {C ∈ 𝒞 | x ∈ C}) := by
        exact coreReplacementMembersOutside_subset_childParentImage core (K n) 𝒞 ℬ parent x
          hcore_control hx_controlled
      calc
        Set.encard {R ∈ ℬ' | x ∈ R} ≤
            Set.encard (replacement '' (parent '' {C ∈ 𝒞 | x ∈ C})) :=
          Set.encard_le_encard hmembers_subset
        _ ≤ Set.encard (parent '' {C ∈ 𝒞 | x ∈ C}) :=
          Set.encard_image_le replacement (parent '' {C ∈ 𝒞 | x ∈ C})
        _ ≤ Set.encard {C ∈ 𝒞 | x ∈ C} :=
          Set.encard_image_le parent {C ∈ 𝒞 | x ∈ C}
        _ ≤ (m + 1 : ℕ) := h𝒞_order x hx_stage
  refine ⟨ℬ', ?_, hℬ'_refines, ?_⟩
  · -- Assemble openness, refinement to the initial cover, coverage, and the stage order bound.
    refine ⟨?_, hℬ'_cover, hℬ'_order⟩
    rw [isOpenRefinement_iff]
    exact ⟨hℬ'_refines.trans hstage.1.1, hℬ'_open⟩
  · -- A core-meeting parent is retained, and containment forces every equal replacement witness
    -- to meet the core and hence to be retained as well.
    intro B hB_core
    constructor
    · rintro ⟨A, hA, hreplacement⟩
      have hBA : B ⊆ A := by
        intro x hxB
        exact hreplacement_subset A hA (hreplacement ▸ hxB)
      have hA_core : (A ∩ core).Nonempty := by
        obtain ⟨x, hxB, hxcore⟩ := hB_core
        exact ⟨x, hBA hxB, hxcore⟩
      have hreplacement_A : replacement A = A := by
        simp only [replacement, coreReplacement, if_pos hA_core]
      have hAB : A = B := hreplacement_A.symm.trans hreplacement
      exact hAB ▸ hA
    · intro hB
      refine ⟨B, hB, ?_⟩
      have hB_core' : (B ∩ core).Nonempty := by
        simpa only [core] using hB_core
      simp only [replacement, coreReplacement, if_pos hB_core']

/-- Helper for Remark 50.2: iterating the core-stable successor construction yields a sequence
of stagewise bounded covers with exact consecutive stability. -/
private lemma existsCoreStableCoverSequence {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (K : CompactExhaustion X) (hK_zero : K 0 = ∅)
    (ℬ₀ : Set (Set X)) (hℬ₀_open : ∀ B ∈ ℬ₀, IsOpen B) (hℬ₀_cover : ⋃₀ ℬ₀ = Set.univ)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ : ℕ → Set (Set X), ℬ 0 = ℬ₀ ∧ (∀ n, CoverStage K m ℬ₀ n (ℬ n)) ∧
      ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n) := by
  classical
  -- The initial order condition is vacuous because the zeroth compact stage is empty.
  have hinitial : CoverStage K m ℬ₀ 0 ℬ₀ := by
    refine ⟨?_, hℬ₀_cover, ?_⟩
    · rw [isOpenRefinement_iff]
      exact ⟨IsRefinement.refl ℬ₀, hℬ₀_open⟩
    · intro x hx
      rw [hK_zero] at hx
      exact hx.elim
  let StageData (n : ℕ) := {𝒞 : Set (Set X) // CoverStage K m ℬ₀ n 𝒞}
  let initial : StageData 0 := ⟨ℬ₀, hinitial⟩
  have hsuccessor (n : ℕ) (stage : StageData n) :
      ∃ next : StageData (n + 1), IsRefinement next.1 stage.1 ∧
        ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ next.1 ↔ B ∈ stage.1) := by
    obtain ⟨next, hnext, hrefines, hstable⟩ :=
      existsCoreStableCoverStage K hK_zero ℬ₀ stage.1 hℬ₀_control stage.2 h_dim
    exact ⟨⟨next, hnext⟩, hrefines, hstable⟩
  let next (n : ℕ) (stage : StageData n) : StageData (n + 1) :=
    Classical.choose (hsuccessor n stage)
  have hnext_stable (n : ℕ) (stage : StageData n) :
      ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ (next n stage).1 ↔ B ∈ stage.1) :=
    (Classical.choose_spec (hsuccessor n stage)).2
  let stages : (n : ℕ) → StageData n :=
    fun n ↦ Nat.rec initial (fun n stage ↦ next n stage) n
  refine ⟨fun n ↦ (stages n).1, ?_, ?_, ?_⟩
  · rfl
  · intro n
    exact (stages n).2
  · intro n B hB_meets
    exact hnext_stable n (stages n) B hB_meets

/-- Helper for Remark 50.2: a controlled cover can be recursively stabilized to a global
bounded-order refinement along a compact exhaustion. -/
private lemma existsGloballyBoundedRefinementOfControlledCover {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (K : CompactExhaustion X) (hK_zero : K 0 = ∅)
    (ℬ₀ : Set (Set X)) (hℬ₀_open : ∀ B ∈ ℬ₀, IsOpen B) (hℬ₀_cover : ⋃₀ ℬ₀ = Set.univ)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ : Set (Set X), IsOpenRefinement ℬ ℬ₀ ∧ ⋃₀ ℬ = Set.univ ∧
      ℬ.HasOrderLE (m + 1) := by
  -- Assemble the recursive stages, then pass to their eventually stable members.
  obtain ⟨stages, _, hstage, hstable⟩ :=
    existsCoreStableCoverSequence K hK_zero ℬ₀ hℬ₀_open hℬ₀_cover hℬ₀_control h_dim
  exact ⟨EventuallyStableCover stages, eventuallyStableCover_spec K ℬ₀ stages hstage hstable⟩


/-- Helper for Remark 50.2: a common covering-dimension bound on all compact subspaces of
a compactly exhaustible Hausdorff space globalizes to the whole space. -/
private lemma compactExhaustibleHasCoveringDimensionLE {m : ℕ} {X : Type u}
    [TopologicalSpace X] [CompactlyExhaustibleSpace X] [T2Space X]
    (hdim : ∀ K : Set X, IsCompact K → HasCoveringDimensionLE K m) :
    HasCoveringDimensionLE X m := by
  classical
  intro 𝒜 h𝒜open h𝒜cover
  -- Start with the canonical compact exhaustion shifted to have an empty initial stage.
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr
  have hKzero : K 0 = ∅ := rfl
  obtain ⟨ℬ₀, hℬ₀refines, hℬ₀cover, hℬ₀control⟩ :=
    existsControlledOpenRefinement K hKzero 𝒜 h𝒜open h𝒜cover
  have hℬ₀open : ∀ B ∈ ℬ₀, IsOpen B :=
    fun _ hB ↦ hℬ₀refines.isOpen_of_mem hB
  -- Stabilize the stagewise bounded refinements and compose refinement relations once.
  obtain ⟨ℬ, hℬrefines, hℬcover, hℬorder⟩ :=
    existsGloballyBoundedRefinementOfControlledCover K hKzero ℬ₀ hℬ₀open hℬ₀cover
      hℬ₀control hdim
  refine ⟨ℬ, ?_, hℬcover, hℬorder⟩
  rw [isOpenRefinement_iff] at hℬrefines hℬ₀refines ⊢
  exact ⟨hℬrefines.1.trans hℬ₀refines.1, hℬrefines.2⟩

/-- Helper for Remark 50.2: every chart contains a closed positive-radius Euclidean ball
whose inverse-chart image is closed in the ambient Hausdorff space. -/
private lemma existsClosedEuclideanBallChartPiece {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] (x : M) :
    ∃ (c : EuclideanSpace ℝ (Fin m)) (r : ℝ) (K : Set M), 0 < r ∧ IsClosed K ∧
      Nonempty ((Metric.closedBall c r : Set (EuclideanSpace ℝ (Fin m))) ≃ₜ K) := by
  -- Choose a smaller closed ball inside the open target of the chart at `x`.
  let chart := chartAt (EuclideanSpace ℝ (Fin m)) x
  have hxsource : x ∈ chart.source := mem_chart_source _ x
  have hxtarget : chart x ∈ chart.target := chart.map_source hxsource
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp chart.open_target (chart x) hxtarget
  let r : ℝ := ε / 2
  have hr : 0 < r := by
    exact half_pos hε
  have hrε : r < ε := by
    dsimp only [r]
    linarith
  have hclosedBallTarget : Metric.closedBall (chart x) r ⊆ chart.target := by
    intro y hy
    apply hball
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hrε)
  let K : Set M := chart.symm '' Metric.closedBall (chart x) r
  have hKidentity : chart.symm '' Metric.closedBall (chart x) r = K := rfl
  let chartEquiv :
      (Metric.closedBall (chart x) r : Set (EuclideanSpace ℝ (Fin m))) ≃ₜ K :=
    chart.symm.homeomorphOfImageSubsetSource hclosedBallTarget hKidentity
  have hKcompact : IsCompact K := by
    exact (isCompact_closedBall (chart x) r).image_of_continuousOn
      (chart.symm.continuousOn.mono hclosedBallTarget)
  -- Compactness in the Hausdorff manifold makes this chart piece closed.
  exact ⟨chart x, r, K, hr, hKcompact.isClosed, ⟨chartEquiv⟩⟩

/-- Helper for Remark 50.2: a fixed-point-free involution pairs the elements of a finite
set, so that set has even cardinality. -/
private lemma even_card_of_fixedPointFreeInvolution {P : Type*}
    (s : Finset P) (partner : P → P)
    (hpartner_mem : ∀ p ∈ s, partner p ∈ s)
    (hpartner_ne : ∀ p ∈ s, partner p ≠ p)
    (hpartner_involutive : ∀ p ∈ s, partner (partner p) = p) :
    Even s.card := by
  -- Sum the constant one in `ZMod 2`; each involutive pair contributes zero.
  have hsum : ∑ p ∈ s, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (s := s) (f := fun _ ↦ (1 : ZMod 2))
      (fun p _ ↦ partner p)
    · intro p hp
      exact CharP.cast_eq_zero (ZMod 2) 2
    · intro p hp _
      exact hpartner_ne p hp
    · intro p hp
      exact hpartner_mem p hp
    · intro p hp
      exact hpartner_involutive p hp
  -- The mod-two sum is the cast of the cardinality, which detects evenness.
  rw [← ZMod.natCast_eq_zero_iff_even]
  simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one] using hsum

/-- Helper for Remark 50.2: paired internal incidences and an odd boundary force an odd
number of cells whose incidence fibers are odd. -/
private lemma oddMarkedCells_of_pairedIncidences
    {C P : Type*} [DecidableEq C] [DecidableEq P]
    (cells : Finset C) (incidences boundary : Finset P) (cellOf : P → C)
    (marked : C → Prop) [DecidablePred marked]
    (hcellOf : ∀ p ∈ incidences, cellOf p ∈ cells)
    (hfiber : ∀ c ∈ cells,
      Odd ((incidences.filter fun p ↦ cellOf p = c).card) ↔ marked c)
    (hboundary : boundary ⊆ incidences)
    (partner : P → P)
    (hpartner_mem : ∀ p ∈ incidences \ boundary,
      partner p ∈ incidences \ boundary)
    (hpartner_ne : ∀ p ∈ incidences \ boundary, partner p ≠ p)
    (hpartner_involutive : ∀ p ∈ incidences \ boundary,
      partner (partner p) = p)
    (hboundary_odd : Odd boundary.card) :
    Odd ((cells.filter marked).card) := by
  -- Pairing cancels every internal incidence, leaving the total incidence count odd.
  have hinternal_even : Even (incidences \ boundary).card :=
    even_card_of_fixedPointFreeInvolution (incidences \ boundary) partner
      hpartner_mem hpartner_ne hpartner_involutive
  have hincidences_odd : Odd incidences.card := by
    rw [← Finset.card_sdiff_add_card_eq_card hboundary]
    exact hinternal_even.add_odd hboundary_odd
  -- Fiber the incidences by their owning cells and read parity cell by cell.
  rw [Finset.card_eq_sum_card_fiberwise hcellOf,
    Finset.odd_sum_iff_odd_card_odd] at hincidences_odd
  have hfilter :
      cells.filter (fun c ↦ Odd ((incidences.filter fun p ↦ cellOf p = c).card)) =
        cells.filter marked := by
    ext c
    constructor
    · intro hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, (hfiber c hc.1).mp hc.2⟩
    · intro hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, (hfiber c hc.1).mpr hc.2⟩
  rw [← hfilter]
  exact hincidences_odd

/-- Helper for Remark 50.2: realize all vertices of a positive-denominator simplex grid. -/
private noncomputable def simplexGridPoints (d q : ℕ) (hq : 0 < q) :
    Finset (stdSimplex ℝ (Fin (d + 1))) :=
  (Remark50_2.SimplexGrid.vertices d q).image (Remark50_2.SimplexGrid.toPoint hq)

/-- Helper for Remark 50.2: every abstract grid vertex belongs to the realized vertex set. -/
private lemma simplexGridPoint_mem (d : ℕ) {q : ℕ} (hq : 0 < q)
    (a : Remark50_2.SimplexGrid.Vertex d q) :
    Remark50_2.SimplexGrid.toPoint hq a ∈ simplexGridPoints d q hq := by
  -- Exhibit the abstract vertex itself as the preimage in the finite realization.
  exact Finset.mem_image.mpr
    ⟨a, Remark50_2.SimplexGrid.mem_vertices a, rfl⟩

/-- Helper for Remark 50.2: regard an abstract grid vertex as a vertex of the realized grid. -/
private noncomputable def asSimplexGridPoint (d : ℕ) {q : ℕ} (hq : 0 < q)
    (a : Remark50_2.SimplexGrid.Vertex d q) :
    {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ simplexGridPoints d q hq} :=
  ⟨Remark50_2.SimplexGrid.toPoint hq a, simplexGridPoint_mem d hq a⟩

/-- Helper for Remark 50.2: a realized target cell is the image of an abstract grid cell. -/
private noncomputable def realizedSimplexGridCell (d : ℕ) {q : ℕ} (hq : 0 < q)
    (cell : Finset (Remark50_2.SimplexGrid.Vertex d q)) :
    Finset {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ simplexGridPoints d q hq} :=
  cell.image (asSimplexGridPoint d hq)

/-- Helper for Remark 50.2: realize every candidate grid cell in the target vertex subtype. -/
private noncomputable def realizedSimplexGridCells (d : ℕ) {q : ℕ} (hq : 0 < q) :
    Finset (Finset {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ simplexGridPoints d q hq}) :=
  (Remark50_2.SimplexGrid.candidateCells d q).image (realizedSimplexGridCell d hq)

/-- Helper for Remark 50.2: an abstract candidate cell belongs to the realized cell family. -/
private lemma realizedSimplexGridCell_mem (d : ℕ) {q : ℕ} (hq : 0 < q)
    {cell : Finset (Remark50_2.SimplexGrid.Vertex d q)}
    (hcell : Remark50_2.SimplexGrid.IsCell cell) :
    realizedSimplexGridCell d hq cell ∈ realizedSimplexGridCells d hq := by
  -- Candidate-cell membership supplies the source witness for the finite image.
  apply Finset.mem_image.mpr
  exact ⟨cell, (Remark50_2.SimplexGrid.mem_candidateCells cell).mpr hcell, rfl⟩

/-- Helper for Remark 50.2: realized candidate cells inherit the abstract grid mesh bound. -/
private lemma realizedSimplexGridCells_mesh (d : ℕ) {q : ℕ} (hq : 0 < q)
    {ε : ℝ} (hmesh : 1 / (q : ℝ) < ε) :
    ∀ cell ∈ realizedSimplexGridCells d hq, ∀ x ∈ cell, ∀ y ∈ cell,
      dist (x.1 : stdSimplex ℝ (Fin (d + 1))) y.1 < ε := by
  -- Pull a target cell and its two vertices back through their finite-image witnesses.
  intro cell hcell x hx y hy
  obtain ⟨sourceCell, hsourceCell, rfl⟩ := Finset.mem_image.mp hcell
  have hsourceIsCell : Remark50_2.SimplexGrid.IsCell sourceCell :=
    (Remark50_2.SimplexGrid.mem_candidateCells sourceCell).mp hsourceCell
  obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hy
  subst x
  subst y
  exact (Remark50_2.SimplexGrid.cellDiameter_le_one_div hq hsourceIsCell ha hb).trans_lt
    hmesh

/-- Helper for Remark 50.2: a Sperner certificate on abstract candidate cells transports
to the realized finite mesh, without requiring a separate realization inverse. -/
private lemma existsRealizedSimplexGridMeshOfSperner
    (d q : ℕ) (hq : 0 < q) (ε : ℝ) (hmesh : 1 / (q : ℝ) < ε)
    (hsperner :
      ∀ label : Remark50_2.SimplexGrid.Vertex d q → Fin (d + 1),
        (∀ a, label a ∈ Function.support
          ((Remark50_2.SimplexGrid.toPoint hq a : stdSimplex ℝ (Fin (d + 1))) :
            Fin (d + 1) → ℝ)) →
        ∃ cell ∈ Remark50_2.SimplexGrid.candidateCells d q,
          ∀ i, ∃ a ∈ cell, label a = i) :
    ∃ V : Finset (stdSimplex ℝ (Fin (d + 1))),
      ∃ cells : Finset (Finset {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ V}),
        (∀ cell ∈ cells, ∀ x ∈ cell, ∀ y ∈ cell,
          dist (x.1 : stdSimplex ℝ (Fin (d + 1))) y.1 < ε) ∧
        ∀ label : {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ V} → Fin (d + 1),
          (∀ x, label x ∈ Function.support
            ((x.1 : stdSimplex ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ)) →
          ∃ cell ∈ cells, ∀ i, ∃ x ∈ cell, label x = i := by
  classical
  -- Fix the realized grid and its image-indexed candidate cells.
  refine ⟨simplexGridPoints d q hq, realizedSimplexGridCells d hq,
    realizedSimplexGridCells_mesh d hq hmesh, ?_⟩
  intro label hlabelSupport
  let abstractLabel : Remark50_2.SimplexGrid.Vertex d q → Fin (d + 1) :=
    fun a ↦ label (asSimplexGridPoint d hq a)
  have habstractSupport : ∀ a, abstractLabel a ∈ Function.support
      ((Remark50_2.SimplexGrid.toPoint hq a : stdSimplex ℝ (Fin (d + 1))) :
        Fin (d + 1) → ℝ) := by
    -- The subtype coercion of the realized vertex is precisely its grid realization.
    intro a
    exact hlabelSupport (asSimplexGridPoint d hq a)
  obtain ⟨cell, hcell, hfullyLabelled⟩ := hsperner abstractLabel habstractSupport
  refine ⟨realizedSimplexGridCell d hq cell,
    realizedSimplexGridCell_mem d hq
      ((Remark50_2.SimplexGrid.mem_candidateCells cell).mp hcell), ?_⟩
  intro i
  obtain ⟨a, ha, hlabel⟩ := hfullyLabelled i
  -- Map the labelled abstract witness into the corresponding realized cell.
  refine ⟨asSimplexGridPoint d hq a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  exact hlabel

/-- Helper for Remark 50.2: positive-dimensional candidate simplex-grid cells satisfy
the support-compatible Sperner conclusion. -/
private lemma simplexGridCandidateCells_hasSpernerProperty (d q : ℕ) (hq : 0 < q) :
    ∀ label : Remark50_2.SimplexGrid.Vertex (d + 1) q → Fin ((d + 1) + 1),
      (∀ a, label a ∈ Function.support
        ((Remark50_2.SimplexGrid.toPoint hq a :
          stdSimplex ℝ (Fin ((d + 1) + 1))) : Fin ((d + 1) + 1) → ℝ)) →
      ∃ cell ∈ Remark50_2.SimplexGrid.candidateCells (d + 1) q,
        ∀ i, ∃ a ∈ cell, label a = i :=
  -- Route correction: the grid-owner route is obsolete.  The imported
  -- `BarycentricParity.modTwoBoundary` proves internal cancellation and final-face
  -- reindexing without owners; the mesh consumer must now be replaced by barycentric flags.
  -- TODO: realize those flags as simplex barycenters, prove support-compatible label
  -- normalization and dimension induction, then replace this temporary grid interface.
  sorry

/-- Helper for Remark 50.2: the zero-dimensional simplex has the required one-cell
Sperner mesh at every positive scale. -/
private lemma existsStdSimplexSpernerMesh_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Finset (stdSimplex ℝ (Fin (0 + 1))),
      ∃ cells : Finset (Finset {x : stdSimplex ℝ (Fin (0 + 1)) // x ∈ V}),
        (∀ cell ∈ cells, ∀ x ∈ cell, ∀ y ∈ cell,
          dist (x.1 : stdSimplex ℝ (Fin (0 + 1))) y.1 < ε) ∧
        ∀ label : {x : stdSimplex ℝ (Fin (0 + 1)) // x ∈ V} → Fin (0 + 1),
          (∀ x, label x ∈ Function.support
            ((x.1 : stdSimplex ℝ (Fin (0 + 1))) : Fin (0 + 1) → ℝ)) →
          ∃ cell ∈ cells, ∀ i, ∃ x ∈ cell, label x = i := by
  classical
  let p : stdSimplex ℝ (Fin 1) :=
    ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  let V : Finset (stdSimplex ℝ (Fin 1)) := {p}
  let vertex : {x : stdSimplex ℝ (Fin 1) // x ∈ V} :=
    ⟨p, Finset.mem_singleton_self p⟩
  -- The unique vertex and its singleton cell give the complete mesh.
  refine ⟨V, {{vertex}}, ?_, ?_⟩
  · intro cell hcell x hx y hy
    have hcell_eq : cell = {vertex} := Finset.mem_singleton.mp hcell
    rw [hcell_eq] at hx hy
    have hx_eq : x = vertex := Finset.mem_singleton.mp hx
    have hy_eq : y = vertex := Finset.mem_singleton.mp hy
    rw [hx_eq, hy_eq, dist_self]
    exact hε
  · intro label _
    refine ⟨{vertex}, Finset.mem_singleton_self {vertex}, ?_⟩
    intro i
    -- Both the label and the requested index are the unique element of `Fin 1`.
    refine ⟨vertex, Finset.mem_singleton_self vertex, ?_⟩
    exact Fin.ext (by omega)

/-- Helper for Remark 50.2: every positive mesh scale admits a finite standard-simplex
triangulation with the support-compatible Sperner labelling property. -/
private lemma existsStdSimplexSpernerMesh (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Finset (stdSimplex ℝ (Fin (d + 1))),
      ∃ cells : Finset (Finset {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ V}),
        (∀ cell ∈ cells, ∀ x ∈ cell, ∀ y ∈ cell,
          dist (x.1 : stdSimplex ℝ (Fin (d + 1))) y.1 < ε) ∧
        ∀ label : {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ V} → Fin (d + 1),
          (∀ x, label x ∈ Function.support
            ((x.1 : stdSimplex ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ)) →
          ∃ cell ∈ cells, ∀ i, ∃ x ∈ cell, label x = i := by
  -- Split off the complete zero-dimensional certificate before the positive-dimensional parity
  -- argument.  The imported grid API already supplies realization, support, and mesh bounds.
  cases d with
  | zero =>
      exact existsStdSimplexSpernerMesh_zero ε hε
  | succ d =>
      -- Route correction: the former branch mixed metric realization with the unresolved parity
      -- theorem.  The realized-grid bridge above leaves only the abstract Sperner certificate.
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have hnpos : 0 < n + 1 := Nat.succ_pos n
      have hnmesh : 1 / ((n + 1 : ℕ) : ℝ) < ε := by
        simpa only [Nat.cast_add, Nat.cast_one] using hn
      exact existsRealizedSimplexGridMeshOfSperner (d + 1) (n + 1) hnpos ε hnmesh
        (simplexGridCandidateCells_hasSpernerProperty d (n + 1) hnpos)

/-- Helper for Remark 50.2: a face-compatible family on a standard simplex has arbitrarily
small fully labelled configurations. -/
private lemma stdSimplexKkmApproximation
    (d : ℕ) (C : Fin (d + 1) → Set (stdSimplex ℝ (Fin (d + 1))))
    (hface : ∀ J : Set (Fin (d + 1)),
      {x : stdSimplex ℝ (Fin (d + 1)) |
        Function.support (x : Fin (d + 1) → ℝ) ⊆ J} ⊆ ⋃ i ∈ J, C i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Fin (d + 1) → stdSimplex ℝ (Fin (d + 1)),
      (∀ i, p i ∈ C i) ∧ ∀ i j, dist (p i) (p j) < ε := by
  classical
  -- Obtain a finite mesh whose parity interface supplies fully labelled cells.
  obtain ⟨V, cells, hmesh, hsperner⟩ := existsStdSimplexSpernerMesh d ε hε
  have hlabel_exists (x : {x : stdSimplex ℝ (Fin (d + 1)) // x ∈ V}) :
      ∃ i, i ∈ Function.support
          ((x.1 : stdSimplex ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ) ∧ x.1 ∈ C i := by
    let J := Function.support
      ((x.1 : stdSimplex ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ)
    have hx : x.1 ∈ ⋃ i ∈ J, C i := by
      apply hface J
      exact Set.Subset.rfl
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    exact ⟨i, hx.1, hx.2⟩
  choose label hlabel_support hlabel_mem using hlabel_exists
  obtain ⟨cell, hcell, hfullyLabelled⟩ := hsperner label hlabel_support
  have hvertex_exists (i : Fin (d + 1)) : ∃ x, x ∈ cell ∧ label x = i :=
    hfullyLabelled i
  choose vertex hvertex_mem hvertex_label using hvertex_exists
  refine ⟨fun i ↦ (vertex i).1, ?_, ?_⟩
  · -- Each selected vertex belongs to the family member carrying its label.
    intro i
    have hi := hlabel_mem (vertex i)
    simpa only [hvertex_label i] using hi
  · -- All selected vertices lie in one cell, so the mesh estimate makes them uniformly close.
    intro i j
    exact hmesh cell hcell (vertex i) (hvertex_mem i) (vertex j) (hvertex_mem j)

/-- Helper for Remark 50.2: the approximate finite Sperner certificate implies the closed-set
KKM intersection theorem on a real standard simplex. -/
private lemma stdSimplexKkmIntersection
    (d : ℕ) (C : Fin (d + 1) → Set (stdSimplex ℝ (Fin (d + 1))))
    (hclosed : ∀ i, IsClosed (C i))
    (hface : ∀ J : Set (Fin (d + 1)),
      {x : stdSimplex ℝ (Fin (d + 1)) |
        Function.support (x : Fin (d + 1) → ℝ) ⊆ J} ⊆ ⋃ i ∈ J, C i) :
    ∃ x, ∀ i, x ∈ C i := by
  classical
  -- Choose successively finer approximate KKM configurations.
  have happ (k : ℕ) :
      ∃ p : Fin (d + 1) → stdSimplex ℝ (Fin (d + 1)),
        (∀ i, p i ∈ C i) ∧
          ∀ i j, dist (p i) (p j) < 1 / ((k : ℝ) + 1) := by
    apply stdSimplexKkmApproximation d C hface
    positivity
  choose p hp_mem hp_dist using happ
  -- Compactness supplies a limit for one label along a common subsequence.
  obtain ⟨x, φ, hφ, hlimit⟩ :=
    CompactSpace.tendsto_subseq (fun k ↦ p k (0 : Fin (d + 1)))
  refine ⟨x, ?_⟩
  intro i
  have hreciprocal : Filter.Tendsto
      (fun k : ℕ ↦ 1 / (((φ k : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hdist : Filter.Tendsto
      (fun k : ℕ ↦ dist (p (φ k) (0 : Fin (d + 1))) (p (φ k) i))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro k
      exact dist_nonneg
    · intro k
      exact (hp_dist (φ k) 0 i).le
    · exact hreciprocal
  have hi_limit : Filter.Tendsto (fun k : ℕ ↦ p (φ k) i) Filter.atTop (nhds x) := by
    exact hlimit.congr_dist hdist
  -- Closedness passes membership of each labelled sequence to the common limit.
  exact (hclosed i).mem_of_tendsto hi_limit (Filter.Eventually.of_forall fun k ↦ hp_mem (φ k) i)

/-- Helper for Remark 50.2: the real standard `(n + 1)`-simplex has no covering-dimension
bound `n`. -/
private lemma stdSimplexNotHasCoveringDimensionLEPred (n : ℕ) :
    ¬ HasCoveringDimensionLE (stdSimplex ℝ (Fin (n + 2))) n := by
  classical
  let S := stdSimplex ℝ (Fin (n + 2))
  let star : Fin (n + 2) → Set S := fun i ↦ {x | 0 < (x : Fin (n + 2) → ℝ) i}
  let 𝒜 : Set (Set S) := Set.range star
  have hstar_open : ∀ i, IsOpen (star i) := by
    intro i
    exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
  have h𝒜_open : ∀ U ∈ 𝒜, IsOpen U := by
    rintro U ⟨i, rfl⟩
    exact hstar_open i
  have h𝒜_cover : ⋃₀ 𝒜 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hcoordinate : ∃ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i ≠ 0 := by
      by_contra h
      push Not at h
      have hxsumzero : ∑ i, (x : Fin (n + 2) → ℝ) i = 0 := by
        simp only [h, Finset.sum_const_zero]
      exact zero_ne_one (hxsumzero.symm.trans x.2.2)
    obtain ⟨i, hi⟩ := hcoordinate
    rw [Set.mem_sUnion]
    refine ⟨star i, ⟨i, rfl⟩, ?_⟩
    exact lt_of_le_of_ne (x.2.1 i) (Ne.symm hi)
  intro hdim
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order⟩ := hdim 𝒜 h𝒜_open h𝒜_cover
  let I := {B : Set S // B ∈ ℬ}
  have hI_open : ∀ i : I, IsOpen (i.1 : Set S) := by
    intro i
    exact hℬ_refines.isOpen_of_mem i.2
  have hI_cover : Set.univ ⊆ ⋃ i : I, (i.1 : Set S) := by
    intro x _
    have hx : x ∈ ⋃₀ ℬ := hℬ_cover.symm ▸ Set.mem_univ x
    rw [Set.mem_sUnion] at hx
    obtain ⟨B, hB, hxB⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨B, hB⟩, hxB⟩
  -- Compactness reduces the refinement to finitely many subtype-indexed members.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : I ↦ (i.1 : Set S)) hI_open hI_cover
  let U : t → Set S := fun j ↦ (j.1.1 : Set S)
  have hU_cover : Set.univ ⊆ ⋃ j, U j := by
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨⟨i, hi⟩, hxi⟩
  have hU_open : ∀ j, IsOpen (U j) := by
    intro j
    exact hI_open j.1
  have hU_pointFinite : ∀ x ∈ (Set.univ : Set S), {j | x ∈ U j}.Finite := by
    intro _ _
    exact Set.toFinite _
  obtain ⟨D, hD_cover, hD_closed, hD_subset, _⟩ :=
    exists_subset_iUnion_compact_subset_t2space (u := U) isCompact_univ hU_open
      hU_pointFinite hU_cover
  have hparent_exists (j : t) : ∃ i : Fin (n + 2), U j ⊆ star i := by
    obtain ⟨A, ⟨i, hi⟩, hUA⟩ := hℬ_refines.subset_of_mem j.1.2
    exact ⟨i, hi ▸ hUA⟩
  choose parent hU_parent using hparent_exists
  let C : Fin (n + 2) → Set S := fun i ↦
    ⋃ j : {j : t // parent j = i}, D j.1
  have hC_closed : ∀ i, IsClosed (C i) := by
    intro i
    exact isClosed_iUnion_of_finite fun j ↦ hD_closed j.1
  have hface : ∀ J : Set (Fin (n + 2)),
      {x : S | Function.support (x : Fin (n + 2) → ℝ) ⊆ J} ⊆ ⋃ i ∈ J, C i := by
    intro J x hx_support
    have hxD : x ∈ ⋃ j, D j := hD_cover (Set.mem_univ x)
    rw [Set.mem_iUnion] at hxD
    obtain ⟨j, hxj⟩ := hxD
    have hxstar : x ∈ star (parent j) := hU_parent j (hD_subset j hxj)
    have hparent_support : parent j ∈ Function.support (x : Fin (n + 2) → ℝ) := by
      exact ne_of_gt hxstar
    have hparent_J : parent j ∈ J := hx_support hparent_support
    rw [Set.mem_iUnion]
    refine ⟨parent j, Set.mem_iUnion.mpr ⟨hparent_J, ?_⟩⟩
    exact Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, hxj⟩
  obtain ⟨x, hxC⟩ := stdSimplexKkmIntersection (n + 1) C hC_closed hface
  have hchosen_exists (i : Fin (n + 2)) :
      ∃ j : t, parent j = i ∧ x ∈ D j := by
    have hxi := hxC i
    rw [Set.mem_iUnion] at hxi
    obtain ⟨j, hxj⟩ := hxi
    exact ⟨j.1, j.2, hxj⟩
  choose chosen hchosen_parent hchosen_mem using hchosen_exists
  have hchosen_injective : Function.Injective chosen := by
    intro i k hik
    have hparent_eq := congrArg parent hik
    rw [hchosen_parent i, hchosen_parent k] at hparent_eq
    exact hparent_eq
  let selected : Fin (n + 2) → Set S := fun i ↦ (chosen i).1.1
  have hselected_injective : Function.Injective selected := by
    intro i k hik
    apply hchosen_injective
    apply Subtype.ext
    apply Subtype.ext
    exact hik
  have hselected_subset : Set.range selected ⊆ {B ∈ ℬ | x ∈ B} := by
    rintro B ⟨i, rfl⟩
    refine ⟨(chosen i).1.2, ?_⟩
    exact hD_subset (chosen i) (hchosen_mem i)
  have hcard : (n + 2 : ℕ∞) ≤ Set.encard {B ∈ ℬ | x ∈ B} := by
    calc
      (n + 2 : ℕ∞) ≤ Set.encard (Set.range selected) := by
        simpa using hselected_injective.encard_range
      _ ≤ Set.encard {B ∈ ℬ | x ∈ B} := Set.encard_le_encard hselected_subset
  have himpossible : (n + 2 : ℕ∞) ≤ (n + 1 : ℕ∞) :=
    hcard.trans (Set.hasOrderLE_iff.mp hℬ_order x)
  have himpossibleNat : n + 2 ≤ n + 1 := by
    exact_mod_cast himpossible
  omega

/-- Helper for Remark 50.2: a positive-radius Euclidean ball contains a closed copy of the
standard simplex of the same dimension. -/
private lemma existsClosedStandardSimplexInBall
    (n : ℕ) (c : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r) :
    ∃ K : Set (Metric.closedBall c r), IsClosed K ∧
      Nonempty (stdSimplex ℝ (Fin (n + 2)) ≃ₜ K) := by
  classical
  let S := stdSimplex ℝ (Fin (n + 2))
  let project : S → EuclideanSpace ℝ (Fin (n + 1)) := fun x ↦
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (fun i ↦ (x : Fin (n + 2) → ℝ) i.castSucc)
  have hproject_continuous : Continuous project := by
    exact (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
      (continuous_pi fun i ↦ (continuous_apply i.castSucc).comp continuous_subtype_val)
  have hproject_injective : Function.Injective project := by
    intro x y hxy
    have hcoordinates : ∀ i : Fin (n + 1),
        x.1 i.castSucc = y.1 i.castSucc := by
      intro i
      exact congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i) hxy
    have hsums : ∑ i : Fin (n + 1), x.1 i.castSucc =
        ∑ i : Fin (n + 1), y.1 i.castSucc := by
      exact Finset.sum_congr rfl fun i _ ↦ hcoordinates i
    have hlast : x.1 (Fin.last (n + 1)) = y.1 (Fin.last (n + 1)) := by
      have hxsum := x.2.2
      have hysum := y.2.2
      rw [Fin.sum_univ_castSucc] at hxsum hysum
      have hxlast : x.1 (Fin.last (n + 1)) =
          1 - ∑ i : Fin (n + 1), x.1 i.castSucc := by
        apply (eq_sub_iff_add_eq).2
        simpa only [add_comm] using hxsum
      have hylast : y.1 (Fin.last (n + 1)) =
          1 - ∑ i : Fin (n + 1), y.1 i.castSucc := by
        apply (eq_sub_iff_add_eq).2
        simpa only [add_comm] using hysum
      calc
        x.1 (Fin.last (n + 1)) = 1 - ∑ i : Fin (n + 1), x.1 i.castSucc := hxlast
        _ = 1 - ∑ i : Fin (n + 1), y.1 i.castSucc := by rw [hsums]
        _ = y.1 (Fin.last (n + 1)) := hylast.symm
    apply Subtype.ext
    funext i
    refine Fin.lastCases hlast (fun j ↦ ?_) i
    exact hcoordinates j
  obtain ⟨R, hR, hproject_bound⟩ :=
    (isCompact_range hproject_continuous).isBounded.subset_closedBall_lt 0 0
  let scale : ℝ := r / (2 * R)
  have hscale : 0 < scale := by
    exact div_pos hr (mul_pos two_pos hR)
  let affine : S → EuclideanSpace ℝ (Fin (n + 1)) := fun x ↦ c + scale • project x
  have haffine_continuous : Continuous affine := by
    fun_prop
  have haffine_injective : Function.Injective affine := by
    intro x y hxy
    have hscaled : scale • project x = scale • project y := add_left_cancel hxy
    exact hproject_injective (smul_right_injective _ hscale.ne' hscaled)
  have haffine_mem (x : S) : affine x ∈ Metric.closedBall c r := by
    have hproject_norm : ‖project x‖ ≤ R := by
      have hx := hproject_bound (Set.mem_range_self x)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hscale_nonneg : 0 ≤ scale := hscale.le
    calc
      dist (affine x) c = scale * ‖project x‖ := by
        simp only [affine, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hscale]
      _ ≤ scale * R := mul_le_mul_of_nonneg_left hproject_norm hscale_nonneg
      _ = r / 2 := by
        dsimp only [scale]
        rw [div_mul_eq_mul_div, mul_div_mul_right r 2 hR.ne']
      _ ≤ r := by linarith
  let embedded : S → Metric.closedBall c r := fun x ↦ ⟨affine x, haffine_mem x⟩
  have hembedded_continuous : Continuous embedded := by
    exact Continuous.subtype_mk haffine_continuous haffine_mem
  have hembedded_injective : Function.Injective embedded := by
    intro x y hxy
    exact haffine_injective (congrArg Subtype.val hxy)
  have hembedded : Topology.IsClosedEmbedding embedded :=
    hembedded_continuous.isClosedEmbedding hembedded_injective
  let K : Set (Metric.closedBall c r) := Set.range embedded
  refine ⟨K, ?_, ?_⟩
  · exact hembedded.isClosed_range
  · exact ⟨hembedded.toIsEmbedding.toHomeomorph⟩

/-- Helper for Remark 50.2: an `(n + 1)`-dimensional positive-radius closed Euclidean ball
does not have covering dimension at most `n`. -/
private lemma euclideanClosedBallNotHasCoveringDimensionLEPred
    (n : ℕ) (c : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r) :
    ¬ HasCoveringDimensionLE (Metric.closedBall c r) n := by
  -- Restrict a hypothetical bound to the closed simplex image and transport it back.
  intro hball
  obtain ⟨K, hKclosed, ⟨e⟩⟩ := existsClosedStandardSimplexInBall n c hr
  have hK : HasCoveringDimensionLE K n := hball.closedSubtype hKclosed
  have hsimp : HasCoveringDimensionLE (stdSimplex ℝ (Fin (n + 2))) n :=
    coveringDimensionBoundHomeomorph e.symm hK
  exact stdSimplexNotHasCoveringDimensionLEPred n hsimp

/-- Helper for Remark 50.2: the covering dimension of a nonempty topological `m`-manifold
is at least `m`. -/
private lemma topologicalManifoldCoveringDimension_ge {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] [Nonempty M] :
    (m : WithBot ℕ∞) ≤ dim M := by
  obtain ⟨x⟩ := ‹Nonempty M›
  cases m with
  | zero =>
      -- Nonemptiness rules out the sole value strictly below the finite value `0`.
      apply le_of_not_gt
      intro hdim
      have hbot : dim M = ⊥ := (WithBot.lt_zero_iff_eq_bot (dim M)).mp hdim
      have hempty : IsEmpty M := (coveringDimension_eq_bot_iff M).mp hbot
      exact hempty.false x
  | succ n =>
      -- A hypothetical predecessor bound restricts to a closed chart ball and contradicts
      -- the Euclidean ball obstruction.
      apply le_of_not_gt
      intro hdim
      have hdimPred : dim M ≤ (n : WithBot ℕ∞) :=
        ENat.WithBot.lt_add_one_iff.mp hdim
      have hMbound : HasCoveringDimensionLE M n :=
        (coveringDimension_le_iff M n).mp hdimPred
      obtain ⟨c, r, K, hr, hKclosed, ⟨e⟩⟩ :=
        existsClosedEuclideanBallChartPiece (m := n + 1) x
      have hKbound : HasCoveringDimensionLE K n := hMbound.closedSubtype hKclosed
      have hBallBound : HasCoveringDimensionLE (Metric.closedBall c r) n :=
        coveringDimensionBoundHomeomorph e.symm hKbound
      exact euclideanClosedBallNotHasCoveringDimensionLEPred n c hr hBallBound

/-- Helper for Remark 50.2: every topological `m`-manifold has covering dimension at most
`m`. -/
private lemma topologicalManifoldHasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] : HasCoveringDimensionLE M m := by
  -- Local instance justification (charted-space bridge): Euclidean charts canonically provide
  -- local compactness, but this instance is not synthesized from `ChartedSpace` automatically.
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  -- Apply the exhaustion theorem to the finite closed-chart decomposition of each compact set.
  apply compactExhaustibleHasCoveringDimensionLE
  intro K hK
  exact compactSubsetChartedSpaceHasCoveringDimensionLE K hK

/-- Remark 50.2. Every nonempty topological `m`-manifold has covering dimension
exactly `m`; the omitted proof requires algebraic topology. -/
theorem manifold_coveringDimension_eq {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] [Nonempty M] :
    dim M = (m : WithBot ℕ∞) := by
  -- Assemble the global upper bound and the closed-chart-ball lower bound.
  apply le_antisymm
  · exact (coveringDimension_le_iff M m).mpr topologicalManifoldHasCoveringDimensionLE
  · exact topologicalManifoldCoveringDimension_ge
