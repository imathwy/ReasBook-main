module

public import Topology_Munkres_2000.Book.Lemma_62_1

public section

open Set

universe u v

/-- Helper for Exercise 62.3: a homotopy on a closed subspace extends to an ambient
homotopy whose top slice is a prescribed continuous map. -/
lemma exists_homotopyExtensionWithPrescribedTop {X : Type u} [TopologicalSpace X]
    [NormalSpace (X × unitInterval)] {E : Type v} [TopologicalSpace E]
    [AddCommGroup E] [ContinuousAdd E] [ContinuousSub E] [TietzeExtension.{u, v} E]
    {A : Set X} (hA : IsClosed A) (F : C(unitInterval × A, E)) (k : C(X, E))
    (hF₁ : ∀ a, F (1, a) = k a.1) :
    ∃ G : C(X × unitInterval, E),
      (∀ t (a : A), G (a.1, t) = F (t, a)) ∧ ∀ x, G (x, 1) = k x := by
  -- First extend the swapped cylinder map from the closed subspace `A × unitInterval`.
  let boundaryEmbedding : A × unitInterval → X × unitInterval :=
    Prod.map Subtype.val id
  have hBoundaryEmbedding : Topology.IsClosedEmbedding boundaryEmbedding :=
    hA.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  let swappedF : C(A × unitInterval, E) := F.comp ContinuousMap.prodSwap
  obtain ⟨G₀, hG₀⟩ := swappedF.exists_extension hBoundaryEmbedding
  -- Normalize the extension by its top slice and then add the prescribed map `k`.
  have hTopContinuous : Continuous (fun p : X × unitInterval ↦ G₀ (p.1, 1)) := by
    exact (map_continuous G₀).comp (continuous_fst.prodMk continuous_const)
  have hKContinuous : Continuous (fun p : X × unitInterval ↦ k p.1) := by
    exact (map_continuous k).comp continuous_fst
  have hGcontinuous :
      Continuous (fun p : X × unitInterval ↦ G₀ p - G₀ (p.1, 1) + k p.1) := by
    exact ((map_continuous G₀).sub hTopContinuous).add hKContinuous
  let G : C(X × unitInterval, E) :=
    ⟨fun p ↦ G₀ p - G₀ (p.1, 1) + k p.1, hGcontinuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro t a
    have hG₀at : G₀ (a.1, t) = F (t, a) := by
      simpa [boundaryEmbedding, swappedF] using DFunLike.congr_fun hG₀ (a, t)
    have hG₀top : G₀ (a.1, 1) = F (1, a) := by
      simpa [boundaryEmbedding, swappedF] using DFunLike.congr_fun hG₀ (a, 1)
    simp only [G, ContinuousMap.coe_mk, hG₀at, hG₀top, hF₁, sub_add_cancel]
  · intro x
    simp only [G, ContinuousMap.coe_mk, sub_self, zero_add]

/-- Exercise 62.3. If a continuous map from a closed subspace of `X` to an open
subspace of `EuclideanSpace ℝ (Fin n)` is homotopic to the restriction of a map
on `X`, then it extends to a map homotopic to that ambient map. -/
theorem existsHomotopicExtension {X : Type u} [TopologicalSpace X]
    [NormalSpace (X × unitInterval)] {n : ℕ} {Y : Set (EuclideanSpace ℝ (Fin n))}
    (hY : IsOpen Y) {A : Set X} (hA : IsClosed A) (f : C(A, Y)) (h : C(X, Y))
    (hf : f.Homotopic (h.restrict A)) :
    ∃ g : C(X, Y), g.restrict A = f ∧ g.Homotopic h := by
  -- View the given homotopy and the prescribed top map in the ambient Euclidean space.
  obtain ⟨F⟩ := hf
  let inclusion : C(Y, EuclideanSpace ℝ (Fin n)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let ambientF : C(unitInterval × A, EuclideanSpace ℝ (Fin n)) :=
    inclusion.comp F.toContinuousMap
  let ambientHMap : C(X, EuclideanSpace ℝ (Fin n)) := inclusion.comp h
  have hAmbientFtop : ∀ a, ambientF (1, a) = ambientHMap a.1 := by
    intro a
    simp [ambientF, ambientHMap, inclusion]
  obtain ⟨G, hGA, hGtop⟩ :=
    exists_homotopyExtensionWithPrescribedTop hA ambientF ambientHMap hAmbientFtop
  -- A tube around `A` consists entirely of points where every time slice remains in `Y`.
  let U : Set (X × unitInterval) := G ⁻¹' Y
  have hUopen : IsOpen U := hY.preimage (map_continuous G)
  have hAU : A ×ˢ (Set.univ : Set unitInterval) ⊆ U := by
    rintro ⟨a, t⟩ ⟨ha, -⟩
    change G (a, t) ∈ Y
    have hGApoint : G (a, t) = ambientF (t, ⟨a, ha⟩) := by
      simpa using hGA t ⟨a, ha⟩
    rw [hGApoint]
    exact (F (t, ⟨a, ha⟩)).2
  obtain ⟨W, hWopen, hAW, hWU⟩ :=
    exists_open_tube isCompact_univ hUopen hAU
  -- Choose time zero on `A` and time one outside the safe tube.
  letI : NormalSpace X := normalSpace_of_prod_unitInterval X
  have hDisjoint : Disjoint A Wᶜ := Set.disjoint_left.2 fun a ha hnotW ↦ hnotW (hAW ha)
  obtain ⟨φ, hφA, hφW⟩ :=
    exists_unitIntervalSeparator hA hWopen.isClosed_compl hDisjoint
  have hGW : ∀ x ∈ W, ∀ t, G (x, t) ∈ Y := by
    intro x hx t
    exact hWU ⟨hx, Set.mem_univ t⟩
  have hGtopY : ∀ x, G (x, 1) ∈ Y := by
    intro x
    rw [hGtop x]
    exact (h x).2
  obtain ⟨hSelected, hHomotopySelected⟩ :=
    selectedTimes_mem_openTarget G φ hGW hGtopY hφW
  -- Cod-restrict the selected time slice and identify its restriction with `f`.
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
  -- Move each selected time linearly to the prescribed top slice, which is `h`.
  have hHomotopyTimeContinuous :
      Continuous (fun p : unitInterval × X ↦ Icc.convexComb (φ p.2) 1 p.1) := by
    fun_prop
  let homotopyTime : C(unitInterval × X, unitInterval) :=
    ⟨fun p ↦ Icc.convexComb (φ p.2) 1 p.1, hHomotopyTimeContinuous⟩
  let ambientHomotopy : C(unitInterval × X, EuclideanSpace ℝ (Fin n)) :=
    G.comp (ContinuousMap.snd.prodMk homotopyTime)
  have hHomotopyContinuous :
      Continuous (fun p ↦ (⟨ambientHomotopy p, hHomotopySelected p.1 p.2⟩ : Y)) := by
    fun_prop
  let H : C(unitInterval × X, Y) :=
    ⟨fun p ↦ ⟨ambientHomotopy p, hHomotopySelected p.1 p.2⟩, hHomotopyContinuous⟩
  have hHzero : ∀ x, H (0, x) = g x := by
    intro x
    apply Subtype.ext
    simp [H, ambientHomotopy, homotopyTime, g, selectedMap]
  have hHone : ∀ x, H (1, x) = h x := by
    intro x
    apply Subtype.ext
    simp [H, ambientHomotopy, homotopyTime, hGtop, ambientHMap, inclusion]
  let homotopy : ContinuousMap.Homotopy g h :=
    { H with
      map_zero_left := hHzero
      map_one_left := hHone }
  exact ⟨g, hgA, ⟨homotopy⟩⟩

end
