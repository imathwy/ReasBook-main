module

public import Topology_Munkres_2000.Book.Theorem_50_3
public import Topology_Munkres_2000.Book.Example_50_2
public import Topology_Munkres_2000.Book.Theorem_50_1.ClosedSubspace

public section

open scoped CoveringDimension

universe u v

/-- Helper for Example 50.4: a covering-dimension bound is preserved by a
homeomorphism. -/
private lemma hasCoveringDimensionLE_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  -- Pull an arbitrary target cover back to the source of the homeomorphism.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒰 h𝒰open h𝒰cover
  let 𝒰' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' 𝒰
  have h𝒰'open : ∀ U ∈ 𝒰', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (h𝒰open V hV).preimage e.continuous
  have h𝒰'cover : ⋃₀ 𝒰' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒰 := h𝒰cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
  obtain ⟨𝒱, h𝒱refines, h𝒱cover, h𝒱order⟩ := h 𝒰' h𝒰'open h𝒰'cover
  let 𝒱' : Set (Set B) := (fun U : Set A ↦ e '' U) '' 𝒱
  refine ⟨𝒱', ?_, ?_, ?_⟩
  · -- Push the controlled refinement forward into the original target cover.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨U, hU, rfl⟩
      obtain ⟨W, hW, hUW⟩ := h𝒱refines.subset_of_mem hU
      obtain ⟨Z, hZ, rfl⟩ := hW
      refine ⟨Z, hZ, ?_⟩
      rintro y ⟨x, hxU, rfl⟩
      exact hUW hxU
    · rintro V ⟨U, hU, rfl⟩
      exact e.isOpen_image.mpr (h𝒱refines.isOpen_of_mem hU)
  · -- Surjectivity transports the fact that the refinement covers the space.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ 𝒱 := h𝒱cover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨U, hU, hyU⟩ := hy
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
  · -- The members through a point correspond injectively under set image.
    intro y
    let incident : Set (Set A) := {U ∈ 𝒱 | e.symm y ∈ U}
    have hincident : {V ∈ 𝒱' | y ∈ V} = (fun U : Set A ↦ e '' U) '' incident := by
      ext V
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, hyU⟩
        obtain ⟨x, hxU, hxy⟩ := hyU
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨U, ⟨hU, hx ▸ hxU⟩, rfl⟩
      · rintro ⟨U, ⟨hU, hyU⟩, rfl⟩
        exact ⟨⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
    rw [hincident, e.injective.image_injective.encard_image]
    exact h𝒱order (e.symm y)

/-- Helper for Example 50.4: every nonempty open subset of one-dimensional
Euclidean space contains a compact copy of `unitInterval`. -/
private lemma existsUnitIntervalInOpenEuclideanOne
    {U : Set (EuclideanSpace ℝ (Fin 1))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 1)),
      IsCompact K ∧ K ⊆ U ∧ Nonempty (unitInterval ≃ₜ K) := by
  -- Transfer the open set to `ℝ` and choose a smaller nondegenerate closed interval.
  let e : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toHomeomorph
  have hpreimageOpen : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hpreimageNonempty : (e ⁻¹' U).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    have hyPreimage : e.symm y ∈ e ⁻¹' U := by
      simpa using hy
    exact ⟨e.symm y, hyPreimage⟩
  obtain ⟨a, b, hab, hIoo⟩ := hpreimageOpen.exists_Ioo_subset hpreimageNonempty
  let c : ℝ := (2 * a + b) / 3
  let d : ℝ := (a + 2 * b) / 3
  have hac : a < c := by
    dsimp [c]
    linarith
  have hcd : c < d := by
    dsimp [c, d]
    linarith
  have hdb : d < b := by
    dsimp [d]
    linarith
  let K : Set (EuclideanSpace ℝ (Fin 1)) := e '' Set.Icc c d
  have hKcompact : IsCompact K := by
    exact isCompact_Icc.image e.continuous
  have hKsubset : K ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    exact hIoo ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  let intervalEquiv : unitInterval ≃ₜ Set.Icc c d := (iccHomeoI c d hcd).symm
  let imageEquiv : Set.Icc c d ≃ₜ K := Homeomorph.image e (Set.Icc c d)
  -- Compose the interval normalization with the coordinate homeomorphism.
  exact ⟨K, hKcompact, hKsubset, ⟨intervalEquiv.trans imageEquiv⟩⟩

/-- Helper for Example 50.4: every nonempty Hausdorff space charted by the
one-dimensional Euclidean model contains a closed copy of `unitInterval`. -/
private lemma existsClosedUnitIntervalSubset (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) X]
    [T2Space X] [Nonempty X] :
    ∃ K : Set X, IsClosed K ∧ Nonempty (unitInterval ≃ₜ K) := by
  -- Choose one chart and place the compact Euclidean interval inside its target.
  obtain ⟨x⟩ := ‹Nonempty X›
  let chart := chartAt (EuclideanSpace ℝ (Fin 1)) x
  have hxsource : x ∈ chart.source := mem_chart_source _ x
  have htargetNonempty : chart.target.Nonempty := ⟨chart x, chart.map_source hxsource⟩
  obtain ⟨K, hKcompact, hKtarget, ⟨intervalEquiv⟩⟩ :=
    existsUnitIntervalInOpenEuclideanOne chart.open_target htargetNonempty
  let L : Set X := chart.symm '' K
  have hLeq : chart.symm '' K = L := rfl
  let chartEquiv : K ≃ₜ L :=
    chart.symm.homeomorphOfImageSubsetSource hKtarget hLeq
  have hLcompact : IsCompact L := by
    exact hKcompact.image_of_continuousOn
      (chart.symm.continuousOn.mono hKtarget)
  -- Compactness in the Hausdorff ambient space makes the pulled-back interval closed.
  exact ⟨L, hLcompact.isClosed, ⟨intervalEquiv.trans chartEquiv⟩⟩

/-- Example 50.4. Every nonempty compact `1`-manifold has covering dimension `1`. -/
theorem compactOneManifold_coveringDimension_eq (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [Nonempty X] :
    dim X = 1 := by
  -- Package the stated separation and countability hypotheses as the manifold instance.
  letI : TopologicalManifold 1 X := TopologicalManifold.of 1 inferInstance inferInstance
  apply le_antisymm
  · -- The compact-manifold theorem gives the global upper bound.
    exact (coveringDimension_le_iff X 1).mpr compactManifold_coveringDimension_le
  · -- A hypothetical smaller dimension restricts to a closed chart interval.
    apply le_of_not_gt
    intro hdim
    have hdimSucc : dim X < ((0 + 1 : ℕ) : WithBot ℕ∞) := by
      simpa using hdim
    have hdimZero : dim X ≤ (0 : WithBot ℕ∞) :=
      ENat.WithBot.lt_add_one_iff.mp hdimSucc
    have hbound : HasCoveringDimensionLE X 0 :=
      (coveringDimension_le_iff X 0).mp hdimZero
    obtain ⟨K, hKclosed, ⟨intervalEquiv⟩⟩ := existsClosedUnitIntervalSubset X
    have hKbound : HasCoveringDimensionLE K 0 := hbound.closedSubtype hKclosed
    have hIntervalBound : HasCoveringDimensionLE unitInterval 0 :=
      hasCoveringDimensionLE_homeomorph intervalEquiv.symm hKbound
    have hIntervalDimension : dim unitInterval ≤ (0 : WithBot ℕ∞) :=
      (coveringDimension_le_iff unitInterval 0).mpr hIntervalBound
    -- The known dimension of the unit interval contradicts this zero bound.
    rw [unitInterval_coveringDimension] at hIntervalDimension
    norm_num at hIntervalDimension
