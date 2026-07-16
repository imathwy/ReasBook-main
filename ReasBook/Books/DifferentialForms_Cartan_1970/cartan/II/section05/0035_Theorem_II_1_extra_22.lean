import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».SubtypeBoundaryBlocks
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ConnectedAmbientReduction
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ComponentApproximationAssembly

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators
open ConnectedSetApproximationSupport

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: each boundary loop is curve-integrable
against the horizontal and vertical coordinate half-forms used in the final Green-Riemann split. -/
private theorem boundaryPath_curveIntegrable_coordinateHalfForms
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {P Q : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D) (i : ι) :
    CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) (Γ i).toPath ∧
      CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (Γ i).toPath := by
  have hpathD : Set.range (Γ i).toPath ⊆ D :=
    rangeToPathSubsetDomainOfOrientedBoundary hΓ hKD i
  have hQ_form_cont : ContinuousOn (((0 : ℂ → ℝ) dx + Q dy)) D := by
    -- The vertical half-form inherits continuity from the coefficient `Q`.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := D) (P := (0 : ℂ → ℝ)) (Q := Q)
        continuousOn_const hQ_cont)
  have hP_form_cont : ContinuousOn (P dx + (0 : ℂ → ℝ) dy) D := by
    -- The horizontal half-form is handled symmetrically from the coefficient `P`.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := D) (P := P) (Q := (0 : ℂ → ℝ))
        hP_cont continuousOn_const)
  constructor
  · -- Continuity on `D` and piecewise differentiability of the boundary loop give curve
    -- integrability for the `Q dy` piece.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hQ_form_cont (hΓ.piecewiseDifferentiable i) hpathD
  · -- The same argument gives curve integrability for the `P dx` piece.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hP_form_cont (hΓ.piecewiseDifferentiable i) hpathD

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the contour integral of one boundary
loop splits into the sum of its horizontal and vertical coordinate-half integrals. -/
private theorem boundaryPath_curveIntegral_split_coordinateHalfForms
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {P Q : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D) (i : ι) :
    ∫ᶜ z in (Γ i).toPath, (P dx + Q dy) z =
      ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z +
        ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z := by
  have hInt :=
    boundaryPath_curveIntegrable_coordinateHalfForms
      (Γ := Γ) hΓ hKD hP_cont hQ_cont i
  have hform_split :
      (P dx + Q dy) = (P dx + (0 : ℂ → ℝ) dy) + (((0 : ℂ → ℝ) dx + Q dy)) := by
    -- The full planar form is the sum of its horizontal and vertical coordinate pieces.
    ext z v
    simp [Complex.planarDifferentialForm, add_comm]
  -- Once both coordinate halves are integrable, `curveIntegral_add` gives the split.
  rw [hform_split]
  simpa using
    (curveIntegral_add hInt.2 hInt.1 :
      curveIntegral ((P dx + (0 : ℂ → ℝ) dy) + (((0 : ℂ → ℝ) dx + Q dy)))
        ((Γ i).toPath) =
        ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z +
          ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: recombining the two coordinate-half
set integrals gives the textbook density `dQdx - dPdy`. -/
private theorem coordinateHalfSetIntegrals_eq_setIntegral_sub
    {K : Set ℂ} (hK_meas : MeasurableSet K)
    {dPdy dQdx : ℂ → ℝ}
    (hdPdy_int : IntegrableOn dPdy K) (hdQdx_int : IntegrableOn dQdx K) :
    (∫ z in K, -dPdy z) + ∫ z in K, dQdx z = ∫ z in K, (dQdx z - dPdy z) := by
  calc
    (∫ z in K, -dPdy z) + ∫ z in K, dQdx z = ∫ z in K, (-dPdy z) + dQdx z := by
      -- First package the two coordinate-half set integrals as the integral of their sum.
      symm
      exact integral_add (hdPdy_int.neg) hdQdx_int
    _ = ∫ z in K, (dQdx z - dPdy z) := by
      -- Then normalize the integrand back to the textbook order `dQdx - dPdy`.
      refine setIntegral_congr_fun hK_meas ?_
      intro z hz
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once a filtered component block
already carries a direct set-approximation package, the stage identities can be reindexed to the
canonical subtype family carrying that block key. -/
private theorem subtypeBoundaryBlockSubtypePackage_of_filteredApproximation
    {ι : Type u} [Fintype ι] {D Kc : Set ℂ} (Γ : ι → ClosedPath ℂ) {C : Set ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n, U n ⊆ interior Kc) ∧
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
              (nhds (∫ z in interior Kc, dQdx z)) ∧
            Filter.Tendsto
              (fun n ↦ ∫ z in U n, dPdy z)
              Filter.atTop
              (nhds (∫ z in interior Kc, dPdy z)) ∧
            Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
    let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
    let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n, U n ⊆ interior Kc) ∧
          (∀ n, MeasurableSet (U n)) ∧
          (∀ n,
            ((∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              ((∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior Kc, dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior Kc, dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  have hReindex :=
    subtypeBoundaryBlock_reindexContourSums
      (Γ := Γ) (D := D) (C := C) (P := P) (Q := Q)
  rcases hApprox with ⟨U, eQ, eP, hU_subset, hU_meas, hStage, hSetQ, hSetP, heQ, heP⟩
  refine ⟨U, eQ, eP, hU_subset, hU_meas, ?_, hSetQ, hSetP, heQ, heP⟩
  intro n
  constructor
  · -- Reindex the filtered `Q dy` contour identity to the canonical subtype family.
    exact hReindex.1.symm.trans (hStage n).1
  · -- The same subtype reindexing converts the `P dx` stage identity.
    exact hReindex.2.symm.trans (hStage n).2

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: in a connected open ambient set, the
two coordinate half-formulas should follow from a direct set-approximation package on the single
connected boundary block. -/
private theorem orientedBoundary_coordinateHalfFormulasInConnectedOpen
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
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
  -- Route correction: the same-item component assembly file already packages the connected-open
  -- geometry as a direct measurable approximation theorem, so this theorem should consume that
  -- owner instead of rebuilding the rooted comparison-data bridge locally.
  exact
    coordinateHalfFormulas_onInterior_of_directSetApproximationPackage
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      (hΓ.existsDirectSetApproximationInConnectedOpen
        hKC hC_open hC_connected hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: one connected boundary block already
contributes the exact coordinate-half integrals over its own interior piece `interior (K ∩ C)`.
-/
private theorem boundaryComponentBlock_coordinateHalfFormulas
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
        ∫ z in interior (K ∩ C), dQdx z) ∧
      (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
        -∫ z in interior (K ∩ C), dPdy z) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  let Kc : Set ℂ := K ∩ C
  have hιC : Nonempty ιC := by
    rcases Finset.mem_image.1 hC with ⟨i, -, hiC⟩
    exact ⟨⟨i, hiC⟩⟩
  have hRestrict :=
    subtypeBoundaryBlock_restrictionData
      (Γ := Γ) (K := K) (D := D) hΓ hKD hD
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx hC
  rcases hRestrict with
    ⟨hΓC, hC_open, hC_connected, hKcC, hCD, hP_contC, hQ_contC, hdPdy_contC, hdQdx_contC,
      hP_dyC, hQ_dxC⟩
  letI : Nonempty ιC := hιC
  have hHalfC :=
    orientedBoundary_coordinateHalfFormulasInConnectedOpen
      (Γ := ΓC) (C := C) (K := Kc) hΓC hKcC hC_open hC_connected
      hP_contC hQ_contC hdPdy_contC hdQdx_contC hP_dyC hQ_dxC
  constructor
  · calc
      ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
        ∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z := by
          simpa [ιC, ΓC] using
            (subtypeBoundaryBlock_reindexContourSums
              (Γ := Γ) (D := D) (C := C) (P := P) (Q := Q)).1
      _ = ∫ z in interior Kc, dQdx z := hHalfC.1
      _ = ∫ z in interior (K ∩ C), dQdx z := by rfl
  · calc
      ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
        ∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (P dx + (0 : ℂ → ℝ) dy) z := by
          simpa [ιC, ΓC] using
            (subtypeBoundaryBlock_reindexContourSums
              (Γ := Γ) (D := D) (C := C) (P := P) (Q := Q)).2
      _ = -∫ z in interior Kc, dPdy z := hHalfC.2
      _ = -∫ z in interior (K ∩ C), dPdy z := by rfl

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the interior of `K` splits as the
finite disjoint union of the component interiors `interior (K ∩ C)`, so continuous integrands can
be integrated componentwise. -/
private theorem boundaryComponentInteriorIntegral_sum
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {f : ℂ → ℝ} (hf_cont : ContinuousOn f D) :
    let components : Finset (Set ℂ) :=
      Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))
    ∫ z in interior K, f z =
      components.sum (fun C => ∫ z in interior (K ∩ C), f z) := by
  classical
  let components : Finset (Set ℂ) :=
    Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))
  have hInteriorDecomp :
      interior K = ⋃ C ∈ components, interior (K ∩ C) := by
    simpa [components] using
      (interior_eq_biUnion_boundaryComponents (Γ := Γ) hΓ hKD hD)
  have hComponentSubsetDomain :
      ∀ {C : Set ℂ}, C ∈ components → C ⊆ D := by
    intro C hC
    simpa [components] using (boundaryComponent_subset_domain (Γ := Γ) hC)
  have hComponentsDisjoint :
      Set.Pairwise (components : Set (Set ℂ)) fun C₁ C₂ ↦ Disjoint C₁ C₂ := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_image.mp hC₁ with ⟨i₁, -, rfl⟩
    rcases Finset.mem_image.mp hC₂ with ⟨i₂, -, rfl⟩
    exact hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)
  have hInteriorDisjoint :
      Set.Pairwise (components : Set (Set ℂ)) fun C₁ C₂ ↦
        Disjoint (interior (K ∩ C₁)) (interior (K ∩ C₂)) := by
    intro C₁ hC₁ C₂ hC₂ hne
    exact
      (hComponentsDisjoint hC₁ hC₂ hne).mono
        (fun z hz ↦ (interior_subset hz).2)
        (fun z hz ↦ (interior_subset hz).2)
  have hIntegrableInterior :
      ∀ {C : Set ℂ}, C ∈ components → IntegrableOn f (interior (K ∩ C)) := by
    intro C hC
    have hIntKC :
        IntegrableOn f (K ∩ C) := by
      exact
        (hf_cont.mono fun z hz ↦ hComponentSubsetDomain hC hz.2).integrableOn_compact
          (compact_inter_boundaryComponent (Γ := Γ) hΓ hKD hD hC)
    exact hIntKC.mono_set interior_subset
  rw [hInteriorDecomp]
  simpa [components] using
    (MeasureTheory.integral_biUnion_finset (μ := volume) (t := components)
      (s := fun C ↦ interior (K ∩ C))
      (hs := fun _ _ ↦ isOpen_interior.measurableSet)
      (h's := hInteriorDisjoint)
      (hf := fun C hC ↦ hIntegrableInterior hC))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: exact interior coordinate
half-formulas on each connected boundary block assemble to the total half-formulas on `interior
K`. -/
private theorem coordinateHalfFormulas_onInterior_of_componentReduction
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior K, dPdy z) := by
  classical
  let components : Finset (Set ℂ) :=
    Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))
  have hBlockQ :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        components.sum
          (fun C =>
            (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) := by
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
    simpa [components] using
      (sum_curveIntegral_eq_sum_component_blocks
        (Γ := Γ) (D := D) (ω := (P dx + (0 : ℂ → ℝ) dy))
          : (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) = _)
  have hInteriorIntegralQ :
      ∫ z in interior K, dQdx z =
        components.sum (fun C => ∫ z in interior (K ∩ C), dQdx z) := by
    simpa [components] using
      (boundaryComponentInteriorIntegral_sum
        (Γ := Γ) hΓ hKD hD hdQdx_cont : _)
  have hInteriorIntegralP :
      ∫ z in interior K, dPdy z =
        components.sum (fun C => ∫ z in interior (K ∩ C), dPdy z) := by
    simpa [components] using
      (boundaryComponentInteriorIntegral_sum
        (Γ := Γ) hΓ hKD hD hdPdy_cont : _)
  constructor
  · calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
          components.sum
            (fun C =>
              (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) := hBlockQ
      _ = components.sum (fun C => ∫ z in interior (K ∩ C), dQdx z) := by
        refine Finset.sum_congr rfl ?_
        intro C hC
        exact
          (boundaryComponentBlock_coordinateHalfFormulas
            (Γ := Γ) hΓ hKD hD hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx hC).1
      _ = ∫ z in interior K, dQdx z := hInteriorIntegralQ.symm
  · calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
          components.sum
            (fun C =>
              (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
                (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) := hBlockP
      _ = components.sum (fun C => -∫ z in interior (K ∩ C), dPdy z) := by
        refine Finset.sum_congr rfl ?_
        intro C hC
        exact
          (boundaryComponentBlock_coordinateHalfFormulas
            (Γ := Γ) hΓ hKD hD hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx hC).2
      _ = -∫ z in interior K, dPdy z := by
        rw [hInteriorIntegralP]
        simp

-- Proof sketch: reduce the compact region to the direct interior approximation package already
-- assembled in the support modules, convert that package to the two exact coordinate half-formulas,
-- and then recombine the horizontal and vertical contour contributions.
/-- Theorem II.1-extra-22: if `Γ` is the oriented boundary of a compact set `K`, and the real
coefficient functions `P` and `Q` are continuously differentiable on an open neighborhood `D` of
`K`, then the boundary integral of `P dx + Q dy` along `Γ` equals the
area integral of
`∂Q/∂x - ∂P/∂y` over `K`. -/
theorem orientedBoundary_green_riemann_formula
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + Q dy) z) =
      ∫ z in K, (dQdx z - dPdy z) := by
  have hsplit_each :
      ∀ i,
        ∫ᶜ z in (Γ i).toPath, (P dx + Q dy) z =
          ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z +
            ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z := by
    intro i
    -- Split each boundary component integral before summing over the family.
    exact
      boundaryPath_curveIntegral_split_coordinateHalfForms
        (Γ := Γ) hΓ hKD hP_cont hQ_cont i
  have hHalfInterior :
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
          ∫ z in interior K, dQdx z) ∧
        ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
          -∫ z in interior K, dPdy z) := by
    -- Reduce the exact interior identities to the connected boundary-component blocks.
    -- Then reassemble those componentwise formulas over `interior K`.
    exact
      coordinateHalfFormulas_onInterior_of_componentReduction
        (Γ := Γ) hΓ hKD hD hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx
  have hfrontier_zero : volume (frontier K) = 0 :=
    frontierVolume_eq_zero_of_isOrientedBoundary hΓ
  have hQ_half :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in K, dQdx z := by
    have hQ_set :
        ∫ z in interior K, dQdx z = ∫ z in K, dQdx z :=
      setIntegral_interior_eq_of_null_frontier hfrontier_zero
    calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
          ∫ z in interior K, dQdx z := hHalfInterior.1
      _ = ∫ z in K, dQdx z := hQ_set
  have hP_half :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in K, dPdy z := by
    have hP_set :
        ∫ z in interior K, dPdy z = ∫ z in K, dPdy z :=
      setIntegral_interior_eq_of_null_frontier hfrontier_zero
    calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
          -∫ z in interior K, dPdy z := hHalfInterior.2
      _ = -∫ z in K, dPdy z := by rw [hP_set]
  have hdPdy_int : IntegrableOn dPdy K := by
    -- Continuous derivatives on the compact region are integrable on the final set integral.
    exact (hdPdy_cont.mono hKD).integrableOn_compact hΓ.isCompact
  have hdQdx_int : IntegrableOn dQdx K := by
    -- The same compactness argument gives integrability for `dQdx`.
    exact (hdQdx_cont.mono hKD).integrableOn_compact hΓ.isCompact
  -- Add the two half-formulas and collapse the resulting sum of set integrals to the target
  -- integrand `dQdx - dPdy`.
  calc
    (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + Q dy) z) =
        ∑ i,
          (∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z +
            ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hsplit_each i
    _ = (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) +
          ∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z := by
      rw [Finset.sum_add_distrib]
    _ = (-∫ z in K, dPdy z) + ∫ z in K, dQdx z := by
      rw [hP_half, hQ_half]
    _ = (∫ z in K, -dPdy z) + ∫ z in K, dQdx z := by
      -- Rewrite the negated set integral as the set integral of the negated integrand.
      rw [← integral_neg]
    _ = ∫ z in K, (dQdx z - dPdy z) := by
      -- The last algebraic normalization is isolated as a helper so the main proof stays flat.
      exact
        coordinateHalfSetIntegrals_eq_setIntegral_sub
          hΓ.isCompact.measurableSet hdPdy_int hdQdx_int
