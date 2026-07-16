import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackageBridges
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».BoundaryGeometry

open MeasureTheory
open scoped BigOperators

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: restricting the boundary family to
one connected-component key `C` carries along the oriented-boundary data and all regularity
hypotheses needed for the Green-Riemann approximation package. -/
theorem subtypeBoundaryBlock_restrictionData
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
    let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
    let Kc : Set ℂ := K ∩ C
    IsOrientedBoundaryOf Kc ΓC ∧
      IsOpen C ∧
      IsConnected C ∧
      Kc ⊆ C ∧
      C ⊆ D ∧
      ContinuousOn P C ∧
      ContinuousOn Q C ∧
      ContinuousOn dPdy C ∧
      ContinuousOn dQdx C ∧
      (∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im) ∧
      (∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  let Kc : Set ℂ := K ∩ C
  have hΓC : IsOrientedBoundaryOf Kc ΓC :=
    subtypeBoundaryPaths_isOrientedBoundaryOf_inter_boundaryComponent hΓ hKD hD_open hC
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hC_connected : IsConnected C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).2
  have hKcC : Kc ⊆ C := Set.inter_subset_right
  have hCD : C ⊆ D := boundaryComponent_subset_domain (Γ := Γ) hC
  have hP_contC : ContinuousOn P C := hP_cont.mono hCD
  have hQ_contC : ContinuousOn Q C := hQ_cont.mono hCD
  have hdPdy_contC : ContinuousOn dPdy C := hdPdy_cont.mono hCD
  have hdQdx_contC : ContinuousOn dQdx C := hdQdx_cont.mono hCD
  have hP_dyC :
      ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im := by
    -- Restrict the vertical derivative hypothesis from `D` to the chosen component `C`.
    intro z hz
    exact hP_dy z (hCD hz)
  have hQ_dxC :
      ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re := by
    -- The horizontal derivative hypothesis restricts in the same way.
    intro z hz
    exact hQ_dx z (hCD hz)
  exact
    ⟨hΓC, hC_open, hC_connected, hKcC, hCD, hP_contC, hQ_contC, hdPdy_contC, hdQdx_contC,
      hP_dyC, hQ_dxC⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: filtering the original boundary family
by the component key `C` is definitionally the same as summing over the subtype family carrying
that key. -/
theorem subtypeBoundaryBlock_reindexContourSums
    {ι : Type u} [Fintype ι] {D : Set ℂ} (Γ : ι → ClosedPath ℂ) {C : Set ℂ}
    {P Q : ℂ → ℝ} :
    let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
    let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
    (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
        ∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) ∧
      (((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
        ∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  constructor
  · -- Reindex the `Q dy` contour block by the subtype carrying the chosen key `C`.
    simpa [ιC, ΓC] using
      (Finset.sum_toFinset_eq_subtype
        (p := fun i : ι => connectedComponentIn D ((Γ i).toPath 0) = C)
        (f := fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z))
  · -- Apply the same subtype reindexing to the `P dx` contour block.
    simpa [ιC, ΓC] using
      (Finset.sum_toFinset_eq_subtype
        (p := fun i : ι => connectedComponentIn D ((Γ i).toPath 0) = C)
        (f := fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a direct approximation package for the
restricted subtype family over one component key `C` transports verbatim to the filtered contour
block in the original family. -/
theorem subtypeBoundaryBlock_reindexApproximationPackage
    {ι : Type u} [Fintype ι] {D Kc : Set ℂ} (Γ : ι → ClosedPath ℂ) {C : Set ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hApproxC :
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
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
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
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  have hReindex :=
    subtypeBoundaryBlock_reindexContourSums
      (Γ := Γ) (D := D) (C := C) (P := P) (Q := Q)
  rcases hApproxC with ⟨U, eQ, eP, hU_subset, hU_meas, hStage, hSetQ, hSetP, heQ, heP⟩
  refine ⟨U, eQ, eP, hU_subset, hU_meas, ?_, hSetQ, hSetP, heQ, heP⟩
  intro n
  constructor
  · -- Transport the `Q dy` stage identity from the subtype package back to the filtered block.
    exact hReindex.1.trans (hStage n).1
  · -- The `P dx` identity follows by the same subtype-to-filtered reindexing.
    exact hReindex.2.trans (hStage n).2

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: exact subtype-family half-formulas on
`interior Kc` package immediately into the measurable direct approximation family for the filtered
component block. -/
theorem subtypeBoundaryBlock_directSetApproximationPackage_of_subtypeCoordinateHalfFormulas
    {ι : Type u} [Fintype ι] {D Kc : Set ℂ} (Γ : ι → ClosedPath ℂ) {C : Set ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hQSubtype :
      let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
      let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
      (∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior Kc, dQdx z)
    (hPSubtype :
      let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
      let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
      (∑ i : ιC, ∫ᶜ z in (ΓC i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior Kc, dPdy z) :
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
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  have hApproxSubtype :
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
    -- Package the exact subtype-family equalities as the constant approximation family on
    -- `interior Kc`.
    exact
      directSetApproximationPackage_of_coordinateHalfFormulasOnInterior
        (Γ := ΓC) (K := Kc) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
        (by simpa [ιC, ΓC] using hQSubtype)
        (by simpa [ιC, ΓC] using hPSubtype)
  have hApproxSubtypeBlock :
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
    -- Rephrase the subtype package in the `let`-bound normal form expected by the reindex bridge.
    simpa [ιC, ΓC] using hApproxSubtype
  -- The remaining work is only the earlier reindex transport from subtype sums to filtered sums.
  exact
    subtypeBoundaryBlock_reindexApproximationPackage
      (Γ := Γ) (D := D) (Kc := Kc) (C := C) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      hApproxSubtypeBlock
