module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

universe u v

/-- Helper for Theorem 9.0.1: extend a closed-subspace homotopy while keeping
the top time slice constant. -/
lemma existsNormalizedHomotopyExtension {X : Type u} [TopologicalSpace X]
    [NormalSpace (X × unitInterval)] {E : Type v} [TopologicalSpace E]
    [AddCommGroup E] [ContinuousAdd E] [ContinuousSub E] [TietzeExtension.{u, v} E]
    {A : Set X} (hA : IsClosed A) (F : C(unitInterval × A, E)) (y₀ : E)
    (hF₁ : ∀ a, F (1, a) = y₀) :
    ∃ G : C(X × unitInterval, E),
      (∀ t (a : A), G (a.1, t) = F (t, a)) ∧ ∀ x, G (x, 1) = y₀ := by
  -- Extend the swapped homotopy from the closed product `A × unitInterval`.
  let boundaryEmbedding : A × unitInterval → X × unitInterval :=
    Prod.map Subtype.val id
  have hBoundaryEmbedding : Topology.IsClosedEmbedding boundaryEmbedding :=
    hA.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  let swappedF : C(A × unitInterval, E) := F.comp ContinuousMap.prodSwap
  obtain ⟨G₀, hG₀⟩ := swappedF.exists_extension hBoundaryEmbedding
  -- Subtract the extended top slice so the normalization holds everywhere.
  have hTopContinuous : Continuous (fun p : X × unitInterval ↦ G₀ (p.1, 1)) :=
    (map_continuous G₀).comp (continuous_fst.prodMk continuous_const)
  have hGcontinuous : Continuous (fun p : X × unitInterval ↦ G₀ p - G₀ (p.1, 1) + y₀) :=
    ((map_continuous G₀).sub hTopContinuous).add continuous_const
  let G : C(X × unitInterval, E) :=
    ⟨fun p ↦ G₀ p - G₀ (p.1, 1) + y₀, hGcontinuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro t a
    have hG₀at : G₀ (a.1, t) = F (t, a) := by
      simpa [boundaryEmbedding, swappedF] using DFunLike.congr_fun hG₀ (a, t)
    have hG₀top : G₀ (a.1, 1) = F (1, a) := by
      simpa [boundaryEmbedding, swappedF] using DFunLike.congr_fun hG₀ (a, 1)
    simp only [G, ContinuousMap.coe_mk, hG₀at, hG₀top, hF₁, sub_add_cancel]
  · intro x
    simp only [G, ContinuousMap.coe_mk, sub_self, zero_add]

/-- Helper for Theorem 9.0.1: a neighborhood of `A × K` containing a compact
fiber contains a product neighborhood of that fiber. -/
lemma existsOpenTube {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {A : Set X} {K : Set T} (hK : IsCompact K) {U : Set (X × T)} (hU : IsOpen U)
    (hAK : A ×ˢ K ⊆ U) :
    ∃ W : Set X, IsOpen W ∧ A ⊆ W ∧ W ×ˢ K ⊆ U := by
  -- Apply the tube lemma pointwise and unite the resulting neighborhoods.
  choose W V hWopen hVopen hAW hKV hWV using fun a : A ↦
    generalized_tube_lemma (isCompact_singleton (x := a.1)) hK hU
      (fun p hp ↦ hAK ⟨hp.1 ▸ a.2, hp.2⟩)
  refine ⟨⋃ a : A, W a, isOpen_iUnion hWopen, ?_, ?_⟩
  · intro a ha
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hAW ⟨a, ha⟩ (Set.mem_singleton a)⟩
  · rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain ⟨a, hxa⟩ := mem_iUnion.1 hx
    exact hWV a ⟨hxa, hKV a ht⟩

/-- Helper for Theorem 9.0.1: normality of `X × unitInterval` descends to the
closed zero slice `X`. -/
lemma normalSpaceOfProdUnitInterval (X : Type u) [TopologicalSpace X]
    [NormalSpace (X × unitInterval)] : NormalSpace X := by
  -- Realize `X` as the closed zero slice of the normal product.
  let zeroSlice : X → X × unitInterval := fun x ↦ (x, 0)
  have hZeroSliceRange : Set.range zeroSlice = Set.univ ×ˢ ({0} : Set unitInterval) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Set.mem_univ x, Set.mem_singleton 0⟩
    · rintro ⟨-, hp⟩
      exact ⟨p.1, Prod.ext rfl (Set.mem_singleton_iff.1 hp).symm⟩
  have hZeroSliceIsEmbedding : Topology.IsEmbedding zeroSlice := by
    simpa [zeroSlice] using
      isEmbedding_prodMkLeft (X := X) (Y := unitInterval) (0 : unitInterval)
  have hZeroSliceEmbedding : Topology.IsClosedEmbedding zeroSlice := by
    refine ⟨hZeroSliceIsEmbedding, ?_⟩
    rw [hZeroSliceRange]
    exact (isClosed_univ : IsClosed (Set.univ : Set X)).prod
      (isClosed_singleton : IsClosed ({0} : Set unitInterval))
  exact hZeroSliceEmbedding.normalSpace

/-- Helper for Theorem 9.0.1: separate disjoint closed sets in a normal space
by a continuous map to `unitInterval`. -/
lemma existsUnitIntervalSeparator {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ φ : C(X, unitInterval), EqOn φ 0 s ∧ EqOn φ 1 t := by
  -- Cod-restrict the real-valued Urysohn function to its certified interval range.
  obtain ⟨φ, hφs, hφt, hφrange⟩ :=
    exists_continuous_zero_one_of_isClosed hs ht hst
  have hφIcontinuous : Continuous (fun x ↦ (⟨φ x, hφrange x⟩ : unitInterval)) := by
    fun_prop
  let φI : C(X, unitInterval) := ⟨fun x ↦ ⟨φ x, hφrange x⟩, hφIcontinuous⟩
  refine ⟨φI, ?_, ?_⟩
  · intro x hx
    apply Subtype.ext
    exact hφs hx
  · intro x hx
    apply Subtype.ext
    exact hφt hx

/-- Helper for Theorem 9.0.1: a selector equal to one outside a safe tube keeps
the selected map and its interpolation inside the open target. -/
lemma selectedTimesMemOpenTarget {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {Y : Set E} {W : Set X} (G : C(X × unitInterval, E)) (φ : C(X, unitInterval))
    (hGW : ∀ x ∈ W, ∀ t, G (x, t) ∈ Y) (hGtop : ∀ x, G (x, 1) ∈ Y)
    (hφ : EqOn φ 1 Wᶜ) :
    (∀ x, G (x, φ x) ∈ Y) ∧
      ∀ t x, G (x, Icc.convexComb (φ x) 1 t) ∈ Y := by
  -- Inside the tube every time is safe; outside it the selector is the top time.
  constructor
  · intro x
    by_cases hx : x ∈ W
    · exact hGW x hx (φ x)
    · simpa [hφ hx] using hGtop x
  · intro t x
    by_cases hx : x ∈ W
    · exact hGW x hx (Icc.convexComb (φ x) 1 t)
    · simpa [hφ hx] using hGtop x

/-- Helper for Theorem 9.0.1: a nullhomotopic map from a closed subspace into
an open Euclidean subset extends to a nullhomotopic ambient map. -/
theorem existsNullhomotopicExtensionIntoOpenEuclidean
    {X : Type u} [TopologicalSpace X] [NormalSpace (X × unitInterval)]
    {n : ℕ} {Y : Set (EuclideanSpace ℝ (Fin n))} (hY : IsOpen Y)
    {A : Set X} (hA : IsClosed A) (f : C(A, Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(X, Y), g.restrict A = f ∧ g.Nullhomotopic := by
  -- View the given nullhomotopy in ambient Euclidean space and extend it.
  obtain ⟨y₀, ⟨F⟩⟩ := hf
  let inclusion : C(Y, EuclideanSpace ℝ (Fin n)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let ambientF : C(unitInterval × A, EuclideanSpace ℝ (Fin n)) :=
    inclusion.comp F.toContinuousMap
  have hAmbientFtop : ∀ a, ambientF (1, a) = y₀ := by
    intro a
    simp [ambientF, inclusion]
  obtain ⟨G, hGA, hGtop⟩ :=
    existsNormalizedHomotopyExtension hA ambientF y₀ hAmbientFtop
  -- Find a product tube on which every homotopy time remains in the target.
  let U : Set (X × unitInterval) := G ⁻¹' Y
  have hUopen : IsOpen U := hY.preimage (map_continuous G)
  have hAU : A ×ˢ (Set.univ : Set unitInterval) ⊆ U := by
    rintro ⟨a, t⟩ ⟨ha, -⟩
    change G (a, t) ∈ Y
    have hGApoint : G (a, t) = ambientF (t, ⟨a, ha⟩) := by
      simpa using hGA t ⟨a, ha⟩
    rw [hGApoint]
    exact (F (t, ⟨a, ha⟩)).2
  obtain ⟨W, hWopen, hAW, hWU⟩ := existsOpenTube isCompact_univ hUopen hAU
  -- Separate the closed source from the unsafe complement by a time selector.
  letI : NormalSpace X := normalSpaceOfProdUnitInterval X
  have hDisjoint : Disjoint A Wᶜ := Set.disjoint_left.2 fun a ha hnotW ↦ hnotW (hAW ha)
  obtain ⟨φ, hφA, hφW⟩ :=
    existsUnitIntervalSeparator hA hWopen.isClosed_compl hDisjoint
  have hGW : ∀ x ∈ W, ∀ t, G (x, t) ∈ Y := by
    intro x hx t
    exact hWU ⟨hx, Set.mem_univ t⟩
  have hGtopY : ∀ x, G (x, 1) ∈ Y := by
    intro x
    rw [hGtop x]
    exact y₀.2
  obtain ⟨hSelected, hHomotopySelected⟩ :=
    selectedTimesMemOpenTarget G φ hGW hGtopY hφW
  -- Cod-restrict the selected map and verify the extension equation.
  let selectedMap : C(X, EuclideanSpace ℝ (Fin n)) :=
    G.comp ((ContinuousMap.id X).prodMk φ)
  have hgcontinuous : Continuous (fun x ↦ (⟨selectedMap x, hSelected x⟩ : Y)) := by
    fun_prop
  let g : C(X, Y) := ⟨fun x ↦ ⟨selectedMap x, hSelected x⟩, hgcontinuous⟩
  have hgA : g.restrict A = f := by
    apply ContinuousMap.ext
    intro a
    apply Subtype.ext
    simpa [g, selectedMap, hφA a.2, ambientF, inclusion] using hGA 0 a
  -- Interpolate the selected time to one to obtain the ambient nullhomotopy.
  have hHomotopyTimeContinuous :
      Continuous (fun p : unitInterval × X ↦ Icc.convexComb (φ p.2) 1 p.1) := by
    fun_prop
  let homotopyTime : C(unitInterval × X, unitInterval) :=
    ⟨fun p ↦ Icc.convexComb (φ p.2) 1 p.1, hHomotopyTimeContinuous⟩
  let ambientH : C(unitInterval × X, EuclideanSpace ℝ (Fin n)) :=
    G.comp (ContinuousMap.snd.prodMk homotopyTime)
  have hHcontinuous :
      Continuous (fun p ↦ (⟨ambientH p, hHomotopySelected p.1 p.2⟩ : Y)) := by
    fun_prop
  let H : C(unitInterval × X, Y) :=
    ⟨fun p ↦ ⟨ambientH p, hHomotopySelected p.1 p.2⟩, hHcontinuous⟩
  have hHzero : ∀ x, H (0, x) = g x := by
    intro x
    apply Subtype.ext
    simp [H, ambientH, homotopyTime, g, selectedMap]
  have hHone : ∀ x, H (1, x) = y₀ := by
    intro x
    apply Subtype.ext
    simp [H, ambientH, homotopyTime, hGtop]
  let nullhomotopy : ContinuousMap.Homotopy g (ContinuousMap.const X y₀) :=
    { H with
      map_zero_left := hHzero
      map_one_left := hHone }
  exact ⟨g, hgA, y₀, ⟨nullhomotopy⟩⟩

end
