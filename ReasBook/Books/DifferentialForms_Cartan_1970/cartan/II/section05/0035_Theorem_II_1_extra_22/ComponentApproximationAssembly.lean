import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackageBridges
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».BoundaryGeometry
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».RectangleIntegrals
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackages
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».SubtypeBoundaryBlocks
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ConnectedAmbientReduction
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ConnectedSetApproximationFinal
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».RootedBoundaryLoops

open MeasureTheory
open scoped BigOperators
open ConnectedSetApproximationSupport

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: in a connected open ambient set, the
two coordinate half-formulas follow directly from the rooted boundary loop, the rooted rectangle
stage family, and the rectangle exhaustion limits already provided by the lighter support files. -/
private theorem orientedBoundary_coordinateHalfFormulasInConnectedOpen
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior K, dPdy z) := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨z0, γ, hγ_piece, hγ_mem, hγ_intQ, hγ_intP, hBoundaryQ, hBoundaryP⟩ :=
      hΓ.existsRootedBoundaryLoopWithSameCoordinateHalfIntegralsConnectedOpen
        hKC hC_open hC_connected hP_cont hQ_cont
    have hz0C : z0 ∈ C := by
      -- The rooted boundary loop remains inside `C`, so its basepoint does too.
      exact hγ_mem ⟨0, by simp⟩
    rcases IsCompact.exists_finiteOrderedRectangleExhaustionOnInterior hΓ.isCompact with
      ⟨N, z, w, hOrdered, hRectSubset, hDisj, hVolume⟩
    rcases
        OrientedBoundaryApproximation.existsRootedRectangleStageLoopFamilyInConnectedOpen
          (C := C) (K := K) hz0C hC_open hC_connected hP_cont hQ_cont hKC hRectSubset with
      ⟨γStage, hγStage_piece, hγStage_mem, hγStage_intQ, hγStage_intP, hStageQ, hStageP⟩
    rcases
        orderedRectangleBoundaryStageLimits_onInterior
          (K := K) (C := C) hΓ.isCompact hKC hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx
          hOrdered hRectSubset hDisj hVolume with
      ⟨hStageContourQRects, hStageContourPRects⟩
    have hContourQInterior :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds (∫ ζ in interior K, dQdx ζ)) := by
      -- Rewriting the rooted stage contours back to rectangle-boundary sums recovers the known
      -- `dQdx` interior limit.
      refine Filter.Tendsto.congr' ?_ hStageContourQRects
      exact Filter.Eventually.of_forall fun n ↦ (hStageQ n).symm
    have hContourPInterior :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds (-∫ ζ in interior K, dPdy ζ)) := by
      -- The same stagewise rewrite yields the `dPdy` interior limit.
      refine Filter.Tendsto.congr' ?_ hStageContourPRects
      exact Filter.Eventually.of_forall fun n ↦ (hStageP n).symm
    -- The public comparison-data owner theorem now closes the connected-open case directly.
    exact
      IsOrientedBoundaryOf.totalBoundaryCoordinateHalfFormulas_ofComparisonData
        (ι := ι) (C := C) (K := K) (Γ := Γ)
        (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
        (_hΓ := hΓ) (_hKC := hKC) (_hC_open := hC_open) (_hC_connected := hC_connected)
        (_hP_cont := hP_cont) (_hQ_cont := hQ_cont)
        (_hdPdy_cont := hdPdy_cont) (_hdQdx_cont := hdQdx_cont)
        (_hP_dy := hP_dy) (_hQ_dx := hQ_dx)
        hz0C hγ_piece hγ_mem hγ_intQ hγ_intP hγStage_piece hγStage_mem hγStage_intQ
        hγStage_intP hOrdered hRectSubset hDisj hBoundaryQ hBoundaryP hStageQ hStageP
        hContourQInterior hContourPInterior hVolume
  · have hEmpty : IsEmpty ι := not_nonempty_iff.mp hι
    have hUnionEmpty : (⋃ i, Set.range (Γ i).toPath) = (∅ : Set ℂ) := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨i, _⟩
        exact False.elim (hEmpty.false i)
      · intro hz
        exact False.elim hz
    have hFrontier : frontier K = ∅ := by
      rw [← hΓ.iUnion_range_eq_frontier, hUnionEmpty]
    have hK_empty : K = ∅ := by
      rcases (frontier_eq_empty_iff : frontier K = ∅ ↔ K = ∅ ∨ K = Set.univ).1 hFrontier with
        hK_empty | hK_univ
      · exact hK_empty
      · exact False.elim (hΓ.isCompact.ne_univ hK_univ)
    -- With no boundary loops, the compact region is empty, so both contour sums and both
    -- interior integrals reduce to `0`.
    constructor <;> simp [hK_empty]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: route-correct the owner theorem to the
direct constant-contour approximation package `U`, `eQ`, `eP` that the interior half-formula
consumer actually uses. -/
theorem componentSetApproximations_toGlobalDirectSetApproximation
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hComp :
      ∀ {C : Set ℂ},
        C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0)) →
          ∃ UC : ℕ → Set ℂ,
            ∃ eQC : ℕ → ℝ,
              ∃ ePC : ℕ → ℝ,
                (∀ n, UC n ⊆ interior (K ∩ C)) ∧
                (∀ n, MeasurableSet (UC n)) ∧
                (∀ n,
                  (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                        (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
                      (∫ z in UC n, dQdx z) + eQC n) ∧
                    (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                        (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
                      -(∫ z in UC n, dPdy z) + ePC n)) ∧
                Filter.Tendsto
                  (fun n ↦ ∫ z in UC n, dQdx z)
                  Filter.atTop
                  (nhds (∫ z in interior (K ∩ C), dQdx z)) ∧
                Filter.Tendsto
                  (fun n ↦ ∫ z in UC n, dPdy z)
                  Filter.atTop
                  (nhds (∫ z in interior (K ∩ C), dPdy z)) ∧
                Filter.Tendsto eQC Filter.atTop (nhds 0) ∧
                Filter.Tendsto ePC Filter.atTop (nhds 0)) :
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n,
            ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior K, dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior K, dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  classical
  let components : Finset (Set ℂ) :=
    Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))
  have hBlockQ :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        components.sum
          (fun C =>
            (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) := by
    -- Group the global `Q dy` contour sum by the connected-component key before assembling the
    -- component approximation packages.
    simpa [components] using
      (sum_curveIntegral_eq_sum_component_blocks
        (Γ := Γ) (D := D) (ω := (((0 : ℂ → ℝ) dx + Q dy)))
          : (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) = _)
  have hBlockP :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        components.sum
          (fun C =>
            (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) := by
    -- The same block decomposition is reused for the horizontal half-form.
    simpa [components] using
      (sum_curveIntegral_eq_sum_component_blocks
        (Γ := Γ) (D := D) (ω := (P dx + (0 : ℂ → ℝ) dy))
          : (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) = _)
  have hInteriorDecomp :
      interior K = ⋃ C ∈ components, interior (K ∩ C) := by
    -- The support file already normalized the global interior as the finite union of the
    -- component interiors keyed by the boundary family.
    simpa [components] using
      (interior_eq_biUnion_boundaryComponents (Γ := Γ) hΓ hKD hD)
  have hRawComponentMem :
      ∀ {C : Set ℂ}, C ∈ components →
        C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0)) := by
    -- The chosen component finset is just a local abbreviation for the canonical image finset.
    intro C hC
    simpa [components] using hC
  let UC : ∀ {C : Set ℂ}, C ∈ components → ℕ → Set ℂ := fun {C} hC =>
    Classical.choose (hComp (hRawComponentMem hC))
  let eQC : ∀ {C : Set ℂ}, C ∈ components → ℕ → ℝ := fun {C} hC =>
    Classical.choose (Classical.choose_spec (hComp (hRawComponentMem hC)))
  let ePC : ∀ {C : Set ℂ}, C ∈ components → ℕ → ℝ := fun {C} hC =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hComp (hRawComponentMem hC))))
  have hUC_spec :
      ∀ {C : Set ℂ} (hC : C ∈ components),
        (∀ n, UC hC n ⊆ interior (K ∩ C)) ∧
          (∀ n, MeasurableSet (UC hC n)) ∧
          (∀ n,
            (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                  (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
                (∫ z in UC hC n, dQdx z) + eQC hC n) ∧
              (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                  (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
                -(∫ z in UC hC n, dPdy z) + ePC hC n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in UC hC n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior (K ∩ C), dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in UC hC n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior (K ∩ C), dPdy z)) ∧
          Filter.Tendsto (eQC hC) Filter.atTop (nhds 0) ∧
          Filter.Tendsto (ePC hC) Filter.atTop (nhds 0) := by
    intro C hC
    -- Unpack the three chosen witnesses back to the original specification for component `C`.
    exact
      Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec (hComp (hRawComponentMem hC))))
  have hUC_subset :
      ∀ {C : Set ℂ} (hC : C ∈ components), ∀ n, UC hC n ⊆ interior (K ∩ C) := by
    intro C hC
    exact (hUC_spec hC).1
  have hUC_meas :
      ∀ {C : Set ℂ} (hC : C ∈ components), ∀ n, MeasurableSet (UC hC n) := by
    intro C hC
    exact (hUC_spec hC).2.1
  have hUC_stage :
      ∀ {C : Set ℂ} (hC : C ∈ components), ∀ n,
        (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
            (∫ z in UC hC n, dQdx z) + eQC hC n) ∧
          (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
            -(∫ z in UC hC n, dPdy z) + ePC hC n) := by
    intro C hC
    exact (hUC_spec hC).2.2.1
  have hUC_tQ :
      ∀ {C : Set ℂ} (hC : C ∈ components),
        Filter.Tendsto
          (fun n ↦ ∫ z in UC hC n, dQdx z)
          Filter.atTop
          (nhds (∫ z in interior (K ∩ C), dQdx z)) := by
    intro C hC
    exact (hUC_spec hC).2.2.2.1
  have hUC_tP :
      ∀ {C : Set ℂ} (hC : C ∈ components),
        Filter.Tendsto
          (fun n ↦ ∫ z in UC hC n, dPdy z)
          Filter.atTop
          (nhds (∫ z in interior (K ∩ C), dPdy z)) := by
    intro C hC
    exact (hUC_spec hC).2.2.2.2.1
  have heQC :
      ∀ {C : Set ℂ} (hC : C ∈ components),
        Filter.Tendsto (eQC hC) Filter.atTop (nhds 0) := by
    intro C hC
    exact (hUC_spec hC).2.2.2.2.2.1
  have hePC :
      ∀ {C : Set ℂ} (hC : C ∈ components),
        Filter.Tendsto (ePC hC) Filter.atTop (nhds 0) := by
    intro C hC
    exact (hUC_spec hC).2.2.2.2.2.2
  let Ucomp : Set ℂ → ℕ → Set ℂ := fun C n =>
    if hC : C ∈ components then UC hC n else ∅
  let eQcomp : Set ℂ → ℕ → ℝ := fun C n =>
    if hC : C ∈ components then eQC hC n else 0
  let ePcomp : Set ℂ → ℕ → ℝ := fun C n =>
    if hC : C ∈ components then ePC hC n else 0
  let U : ℕ → Set ℂ := fun n => ⋃ C ∈ components, Ucomp C n
  let eQ : ℕ → ℝ := fun n => components.sum fun C => eQcomp C n
  let eP : ℕ → ℝ := fun n => components.sum fun C => ePcomp C n
  have hComponentSubsetDomain :
      ∀ {C : Set ℂ}, C ∈ components → C ⊆ D := by
    -- Every selected component key is a connected component of `D`.
    intro C hC
    simpa [components] using
      (boundaryComponent_subset_domain (Γ := Γ) hC)
  have hComponentsDisjoint :
      Set.Pairwise (components : Set (Set ℂ)) fun C₁ C₂ ↦ Disjoint C₁ C₂ := by
    intro C₁ hC₁ C₂ hC₂ hne
    -- Two distinct connected components of the same ambient domain are disjoint.
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_image.mp hC₁ with ⟨i₁, -, rfl⟩
    rcases Finset.mem_image.mp hC₂ with ⟨i₂, -, rfl⟩
    exact hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)
  have hInteriorDisjoint :
      Set.Pairwise (components : Set (Set ℂ)) fun C₁ C₂ ↦
        Disjoint (interior (K ∩ C₁)) (interior (K ∩ C₂)) := by
    intro C₁ hC₁ C₂ hC₂ hne
    -- Distinct component interiors are disjoint because they sit inside distinct connected
    -- components of `D`.
    exact
      (hComponentsDisjoint hC₁ hC₂ hne).mono
        (fun z hz ↦ (interior_subset hz).2)
        (fun z hz ↦ (interior_subset hz).2)
  have hIntegrableComponentQ :
      ∀ {C : Set ℂ}, C ∈ components → IntegrableOn dQdx (K ∩ C) := by
    intro C hC
    -- Continuity on the ambient domain and compactness of `K ∩ C` give the component integrals.
    exact
      (hdQdx_cont.mono fun z hz ↦ hComponentSubsetDomain hC hz.2).integrableOn_compact
        (compact_inter_boundaryComponent (Γ := Γ) hΓ hKD hD hC)
  have hIntegrableComponentP :
      ∀ {C : Set ℂ}, C ∈ components → IntegrableOn dPdy (K ∩ C) := by
    intro C hC
    -- The same compactness argument applies to `dPdy`.
    exact
      (hdPdy_cont.mono fun z hz ↦ hComponentSubsetDomain hC hz.2).integrableOn_compact
        (compact_inter_boundaryComponent (Γ := Γ) hΓ hKD hD hC)
  have hIntegrableInteriorQ :
      ∀ {C : Set ℂ}, C ∈ components → IntegrableOn dQdx (interior (K ∩ C)) := by
    intro C hC
    -- Restrict the compact component integral to its interior.
    exact (hIntegrableComponentQ hC).mono_set interior_subset
  have hIntegrableInteriorP :
      ∀ {C : Set ℂ}, C ∈ components → IntegrableOn dPdy (interior (K ∩ C)) := by
    intro C hC
    -- Restrict the same way for `dPdy`.
    exact (hIntegrableComponentP hC).mono_set interior_subset
  have hUcompDisjoint :
      ∀ n, Set.Pairwise (components : Set (Set ℂ)) fun C₁ C₂ ↦
        Disjoint (Ucomp C₁ n) (Ucomp C₂ n) := by
    intro n C₁ hC₁ C₂ hC₂ hne
    -- Each stage set stays inside the corresponding component interior, so distinct components
    -- remain disjoint after approximation.
    have hsub₁ : Ucomp C₁ n ⊆ interior (K ∩ C₁) := by
      intro z hz
      have hz' : z ∈ UC hC₁ n := by
        dsimp [Ucomp] at hz
        split_ifs at hz with h
        · have hh : h = hC₁ := Subsingleton.elim _ _
          subst hh
          simpa using hz
        · exact False.elim (h hC₁)
      exact hUC_subset hC₁ n hz'
    have hsub₂ : Ucomp C₂ n ⊆ interior (K ∩ C₂) := by
      intro z hz
      have hz' : z ∈ UC hC₂ n := by
        dsimp [Ucomp] at hz
        split_ifs at hz with h
        · have hh : h = hC₂ := Subsingleton.elim _ _
          subst hh
          simpa using hz
        · exact False.elim (h hC₂)
      exact hUC_subset hC₂ n hz'
    exact (hInteriorDisjoint hC₁ hC₂ hne).mono hsub₁ hsub₂
  have hIntegrableUcompQ :
      ∀ n {C : Set ℂ}, C ∈ components → IntegrableOn dQdx (Ucomp C n) := by
    intro n C hC
    -- The componentwise stage sets inherit integrability from the surrounding compact component.
    exact
      (hIntegrableInteriorQ hC).mono_set
        (by simpa [Ucomp, hC] using hUC_subset hC n)
  have hIntegrableUcompP :
      ∀ n {C : Set ℂ}, C ∈ components → IntegrableOn dPdy (Ucomp C n) := by
    intro n C hC
    -- The same restriction closes the `dPdy` integrability side condition.
    exact
      (hIntegrableInteriorP hC).mono_set
        (by simpa [Ucomp, hC] using hUC_subset hC n)
  have hIntegralUQ :
      ∀ n, ∫ z in U n, dQdx z = components.sum (fun C => ∫ z in Ucomp C n, dQdx z) := by
    intro n
    -- The global stage set is the finite disjoint union of the componentwise stage sets.
    simpa [U] using
      (MeasureTheory.integral_biUnion_finset (μ := volume) (t := components)
        (s := fun C ↦ Ucomp C n)
        (hs := fun C hC ↦ by simpa [Ucomp, hC] using hUC_meas hC n)
        (h's := hUcompDisjoint n)
        (hf := fun C hC ↦ hIntegrableUcompQ n hC))
  have hIntegralUP :
      ∀ n, ∫ z in U n, dPdy z = components.sum (fun C => ∫ z in Ucomp C n, dPdy z) := by
    intro n
    -- The same finite-union normalization works for the second derivative term.
    simpa [U] using
      (MeasureTheory.integral_biUnion_finset (μ := volume) (t := components)
        (s := fun C ↦ Ucomp C n)
        (hs := fun C hC ↦ by simpa [Ucomp, hC] using hUC_meas hC n)
        (h's := hUcompDisjoint n)
        (hf := fun C hC ↦ hIntegrableUcompP n hC))
  have hInteriorIntegralQ :
      ∫ z in interior K, dQdx z =
        components.sum (fun C => ∫ z in interior (K ∩ C), dQdx z) := by
    -- Once the interior has been decomposed by boundary components, its set integral splits into
    -- the finite sum of the component integrals.
    rw [hInteriorDecomp]
    simpa using
      (MeasureTheory.integral_biUnion_finset (μ := volume) (t := components)
        (s := fun C ↦ interior (K ∩ C))
        (hs := fun _ _ ↦ isOpen_interior.measurableSet)
        (h's := hInteriorDisjoint)
        (hf := fun C hC ↦ hIntegrableInteriorQ hC))
  have hInteriorIntegralP :
      ∫ z in interior K, dPdy z =
        components.sum (fun C => ∫ z in interior (K ∩ C), dPdy z) := by
    -- The horizontal derivative term splits over the same finite interior decomposition.
    rw [hInteriorDecomp]
    simpa using
      (MeasureTheory.integral_biUnion_finset (μ := volume) (t := components)
        (s := fun C ↦ interior (K ∩ C))
        (hs := fun _ _ ↦ isOpen_interior.measurableSet)
        (h's := hInteriorDisjoint)
        (hf := fun C hC ↦ hIntegrableInteriorP hC))
  have hSetQsum :
      Filter.Tendsto
        (fun n ↦ components.sum (fun C => ∫ z in Ucomp C n, dQdx z))
        Filter.atTop
        (nhds (components.sum (fun C => ∫ z in interior (K ∩ C), dQdx z))) := by
    -- Summing the already convergent component packages gives the global set-side limit.
    exact
      tendsto_finsetSum components
        (fun C hC ↦ by simpa [Ucomp, hC] using hUC_tQ hC)
  have hSetPsum :
      Filter.Tendsto
        (fun n ↦ components.sum (fun C => ∫ z in Ucomp C n, dPdy z))
        Filter.atTop
        (nhds (components.sum (fun C => ∫ z in interior (K ∩ C), dPdy z))) := by
    -- The same finite-sum limit argument works for the `dPdy` component packages.
    exact
      tendsto_finsetSum components
        (fun C hC ↦ by simpa [Ucomp, hC] using hUC_tP hC)
  have heQt :
      Filter.Tendsto eQ Filter.atTop (nhds 0) := by
    -- The global scalar error is the finite sum of the vanishing component errors.
    have hErrQsum :
        Filter.Tendsto
          (fun n ↦ components.sum (fun C => eQcomp C n))
          Filter.atTop
          (nhds (components.sum fun _ => (0 : ℝ))) := by
      exact
        tendsto_finsetSum components
          (fun C hC ↦ by simpa [eQcomp, hC] using heQC hC)
    simpa [eQ] using hErrQsum
  have hePt :
      Filter.Tendsto eP Filter.atTop (nhds 0) := by
    -- The second global scalar error is handled identically.
    have hErrPsum :
        Filter.Tendsto
          (fun n ↦ components.sum (fun C => ePcomp C n))
          Filter.atTop
          (nhds (components.sum fun _ => (0 : ℝ))) := by
      exact
        tendsto_finsetSum components
          (fun C hC ↦ by simpa [ePcomp, hC] using hePC hC)
    simpa [eP] using hErrPsum
  have hSetQ :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dQdx z)
        Filter.atTop
        (nhds (∫ z in interior K, dQdx z)) := by
    -- Rewrite the global set integral as the finite sum of the component set integrals, then use
    -- the already assembled finite-sum limit.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hIntegralUQ n).symm) ?_
    simpa [hInteriorIntegralQ] using hSetQsum
  have hSetP :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dPdy z)
        Filter.atTop
        (nhds (∫ z in interior K, dPdy z)) := by
    -- The same normalization closes the `dPdy` set-side limit.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hIntegralUP n).symm) ?_
    simpa [hInteriorIntegralP] using hSetPsum
  refine ⟨U, eQ, eP, ?_, hSetQ, hSetP, heQt, hePt⟩
  intro n
  constructor
  · -- Sum the component `Q dy` stage identities and normalize the disjoint union to the global
    -- stage set `U n`.
    calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
          components.sum
            (fun C =>
            ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z))) := hBlockQ
      _ = components.sum (fun C => (∫ z in Ucomp C n, dQdx z) + eQcomp C n) := by
        refine Finset.sum_congr rfl ?_
        intro C hC
        simpa [Ucomp, eQcomp, hC] using (hUC_stage hC n).1
      _ = components.sum (fun C => ∫ z in Ucomp C n, dQdx z) +
            components.sum (fun C => eQcomp C n) := by
        rw [Finset.sum_add_distrib]
      _ = (∫ z in U n, dQdx z) + eQ n := by
        simp [eQ, hIntegralUQ n]
  · -- Repeat the same finite-sum assembly for the horizontal half-form.
    calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
          components.sum
            (fun C =>
            ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z))) := hBlockP
      _ = components.sum (fun C => -(∫ z in Ucomp C n, dPdy z) + ePcomp C n) := by
        refine Finset.sum_congr rfl ?_
        intro C hC
        simpa [Ucomp, ePcomp, hC] using (hUC_stage hC n).2
      _ = components.sum (fun C => -(∫ z in Ucomp C n, dPdy z)) +
            components.sum (fun C => ePcomp C n) := by
        rw [Finset.sum_add_distrib]
      _ = -(components.sum (fun C => ∫ z in Ucomp C n, dPdy z)) +
            components.sum (fun C => ePcomp C n) := by
        simp
      _ = -(∫ z in U n, dPdy z) + eP n := by
        simp [eP, hIntegralUP n]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a single connected-component block of
the oriented boundary family should already admit the direct measurable approximation package on
`interior (K ∩ C)`. -/
private theorem subtypeBoundaryBlock_coordinateHalfFormulas_of_connectedOpenApproximation
    {ι : Type u} [Fintype ι] {C K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior K, dPdy z) := by
  -- The connected-open component case is now closed directly from the rooted-loop comparison
  -- package already available in the lighter support files.
  exact
    orientedBoundary_coordinateHalfFormulasInConnectedOpen
      (hΓ := hΓ) (hKC := hKC) hC_open hC_connected
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a single connected-component block of
the oriented boundary family should already admit the direct measurable approximation package on
`interior (K ∩ C)`. -/
theorem subtypeBoundaryBlock_directSetApproximationPackage
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n, U n ⊆ interior (K ∩ C)) ∧
          (∀ n, MeasurableSet (U n)) ∧
          (∀ n,
            (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                  (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                  (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior (K ∩ C), dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior (K ∩ C), dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  let Kc : Set ℂ := K ∩ C
  have hRestrict :=
    subtypeBoundaryBlock_restrictionData
      (Γ := Γ) (K := K) (D := D) hΓ hKD hD_open
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx hC
  rcases hRestrict with
    ⟨hΓC, hC_open, hC_connected, hKcC, hCD, hP_contC, hQ_contC, hdPdy_contC, hdQdx_contC,
      hP_dyC, hQ_dxC⟩
  have hHalfC :
      ((∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
          ∫ z in interior Kc, dQdx z) ∧
        ((∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
          -∫ z in interior Kc, dPdy z) := by
    -- Isolate the only place where the component assembly consumes the connected-open API.
    exact
      subtypeBoundaryBlock_coordinateHalfFormulas_of_connectedOpenApproximation
        (Γ := ΓC) (K := Kc) (C := C) hΓC hKcC hC_open hC_connected
        hP_contC hQ_contC hdPdy_contC hdQdx_contC hP_dyC hQ_dxC
  -- With the exact subtype-family half-formulas in hand, the rest is a formal packaging and
  -- reindexing step already isolated above.
  exact
    subtypeBoundaryBlock_directSetApproximationPackage_of_subtypeCoordinateHalfFormulas
      (Γ := Γ) (D := D) (Kc := Kc) (C := C) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      hHalfC.1 hHalfC.2

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: route-correct the owner theorem to the
direct constant-contour approximation package `U`, `eQ`, `eP` that the interior half-formula
consumer actually uses. -/
theorem existsDirectSetApproximationOnInterior
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n,
            ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior K, dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior K, dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  -- Route correction: the old proof tried to solve the global theorem before the missing
  -- componentwise direct package had been isolated. The global assembly is now closed separately,
  -- so this theorem only delegates to the one remaining connected-component owner.
  exact
    componentSetApproximations_toGlobalDirectSetApproximation
      (Γ := Γ) (K := K) (D := D) hΓ hKD hD hdPdy_cont hdQdx_cont
      (hComp := by
        intro C hC
        exact
          subtypeBoundaryBlock_directSetApproximationPackage
            (Γ := Γ) (K := K) (D := D) hΓ hKD hD
            hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx hC)
