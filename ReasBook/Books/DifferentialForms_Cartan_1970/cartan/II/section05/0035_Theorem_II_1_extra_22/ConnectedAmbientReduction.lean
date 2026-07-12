import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».RectangleExhaustion
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».RootedBoundaryLoops

open MeasureTheory
open scoped BigOperators

universe u

namespace ConnectedSetApproximationSupport

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the ambient set `C` is
connected and contains `K`, every boundary-loop base point has connected-component key exactly
`C`. -/
theorem boundaryComponentKey_eq_ambient_of_connectedAmbient
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C) (i : ι) :
    connectedComponentIn C ((Γ i).toPath 0) = C := by
  have hzC : (Γ i).toPath 0 ∈ C :=
    rangeToPathSubsetDomainOfOrientedBoundary hΓ hKC i ⟨0, by simp⟩
  -- The connected component is always contained in `C`, and connectedness of `C` forces the
  -- reverse inclusion once the base point is known to lie in `C`.
  exact
    Set.Subset.antisymm
      (connectedComponentIn_subset C ((Γ i).toPath 0))
      (hC_connected.2.subset_connectedComponentIn hzC (by intro z hz; exact hz))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: after the component key is normalized
to the ambient connected set `C`, filtering `Finset.univ` by that key does nothing. -/
theorem boundaryComponentFilter_eq_univ_of_connectedAmbient
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C) :
    (Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C) =
      Finset.univ := by
  classical
  -- Every predicate in the filter is definitionally `True` after the connected-ambient
  -- normalization above.
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    simp
  · intro _
    exact boundaryComponentKey_eq_ambient_of_connectedAmbient hΓ hKC hC_connected i

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the ambient set `C` is
connected, any contour block sum filtered by the component key `C` is already the total sum. -/
theorem connectedAmbient_componentFilter_sum_eq_total
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C)
    {β : Type*} [AddCommMonoid β] (f : ι → β) :
    ((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum f) =
      ∑ i, f i := by
  -- Rewrite the filtered index family to `Finset.univ`; connectedness of `C` already forces
  -- every boundary loop to carry the same component key.
  rw [boundaryComponentFilter_eq_univ_of_connectedAmbient hΓ hKC hC_connected]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once a connected ambient set `C`
already carries the single-block approximation package keyed by `C`, removing that unique filter
reduces the package to the total contour sums and yields the exact interior coordinate
half-formulas. -/
theorem connectedAmbientCoordinateHalfFormulas_ofSingleBlockApproximation
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n,
              (((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum
                    (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                (((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum
                    (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) =
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
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior K, dPdy z) := by
  rcases hApprox with ⟨U, eQ, eP, hStage, hSetQ, hSetP, heQ, heP⟩
  have hApproxTotal :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n,
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
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
    refine ⟨U, eQ, eP, ?_, hSetQ, hSetP, heQ, heP⟩
    intro n
    constructor
    · -- Connectedness identifies the filtered `Q dy` contour block with the full boundary sum.
      calc
        (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
            ((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)) := by
          symm
          exact
            connectedAmbient_componentFilter_sum_eq_total
              (hΓ := hΓ) (hKC := hKC) (hC_connected := hC_connected)
              (f := fun i => ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z)
        _ = (∫ z in U n, dQdx z) + eQ n := (hStage n).1
    · -- The same connected-ambient normalization removes the filter from the `P dx` contour sum.
      calc
        (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
            ((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)) := by
          symm
          exact
            connectedAmbient_componentFilter_sum_eq_total
              (hΓ := hΓ) (hKC := hKC) (hC_connected := hC_connected)
              (f := fun i => ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z)
        _ = -(∫ z in U n, dPdy z) + eP n := (hStage n).2
  -- After removing the redundant connected-component filter, the generic approximation consumer
  -- gives the exact half-formulas on `interior K`.
  exact
    coordinateHalfFormulas_onInterior_of_setApproximation
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx) hApproxTotal

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the exact interior coordinate
half-formulas are already known, the asymptotic rectangle-boundary stage package is only the
formal combination of rectangle exhaustion with the existing stage-to-interior limit theorem. -/
theorem existsAsymptoticRectangleBoundaryStages_of_coordinateHalfFormulasOnInterior
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hK_compact : IsCompact K) (hKC : K ⊆ C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hHalfQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ ζ in interior K, dQdx ζ)
    (hHalfP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        -∫ ζ in interior K, dPdy ζ) :
    ∃ N : ℕ → ℕ,
      ∃ z w : ∀ n, Fin (N n) → ℂ,
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  rcases IsCompact.exists_finiteOrderedRectangleExhaustionOnInterior hK_compact with
    ⟨N, z, w, hOrdered, hRectSubset, hDisj, hVolume⟩
  rcases
      orderedRectangleBoundaryStageLimits_onInterior
        (K := K) (C := C) hK_compact hKC hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx
        hOrdered hRectSubset hDisj hVolume with
    ⟨hStageQ, hStageP⟩
  refine ⟨N, z, w, hOrdered, hRectSubset, hDisj, ?_, ?_, hVolume⟩
  · -- Once the target contour sum is identified with the interior `dQdx` integral, the
    -- rectangle-stage limit theorem already gives the required asymptotic `Q dy` convergence.
    simpa [hHalfQ] using hStageQ
  · -- Apply the same interior-half-formula substitution to the `P dx` rectangle stages.
    simpa [hHalfP] using hStageP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: any connected-open direct
set-approximation package already upgrades formally to the asymptotic rectangle-boundary stage
package via the generic direct-package and interior-half-formula consumers. -/
theorem IsOrientedBoundaryOf.existsAsymptoticRectangleBoundaryStagesInConnectedOpen_of_directSetApproximationPackage
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ) (_hKC : K ⊆ C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (_hP_cont : ContinuousOn P C) (_hQ_cont : ContinuousOn Q C)
    (_hdPdy_cont : ContinuousOn dPdy C) (_hdQdx_cont : ContinuousOn dQdx C)
    (_hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (_hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n, U n ⊆ interior K) ∧
            (∀ n, MeasurableSet (U n)) ∧
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
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ∃ N : ℕ → ℕ,
      ∃ z w : ∀ n, Fin (N n) → ℂ,
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  have hApproxCore :
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
    rcases hApprox with ⟨U, eQ, eP, -, -, hStage, hSetQ, hSetP, heQ, heP⟩
    exact ⟨U, eQ, eP, hStage, hSetQ, hSetP, heQ, heP⟩
  -- First convert the direct package into the exact interior half-formulas on `interior K`.
  obtain ⟨hHalfQ, hHalfP⟩ :=
    coordinateHalfFormulas_onInterior_of_setApproximation
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx) hApproxCore
  -- Then the generic rectangle-exhaustion wrapper upgrades those half-formulas to the desired
  -- asymptotic stage theorem.
  exact
    existsAsymptoticRectangleBoundaryStages_of_coordinateHalfFormulasOnInterior
      (Γ := Γ) (C := C) (K := K) (_hΓ.isCompact) _hKC
      _hP_cont _hQ_cont _hdPdy_cont _hdQdx_cont _hP_dy _hQ_dx hHalfQ hHalfP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once a rooted boundary loop and a
rooted rectangle-stage loop family share the same basepoint, any contour comparison
`γStage n → γ` can be repackaged as the exact rectangle-stage package with explicit scalar errors.
-/
theorem rootedBoundaryLoopStageComparison_toExactPackage
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    {z0 : ℂ} {γ : Path z0 z0} {γStage : ∀ n : ℕ, Path z0 z0}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hBoundaryQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hBoundaryP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hStageQ :
      ∀ n,
        ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hStageP :
      ∀ n,
        ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hContourQ :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)))
    (hContourP :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ∃ eQ : ℕ → ℝ,
      ∃ eP : ℕ → ℝ,
        (∀ n,
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
            ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n)) ∧
        Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
        Filter.Tendsto eP Filter.atTop (nhds 0) ∧
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  let eQ : ℕ → ℝ := fun n ↦
    (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ) -
      ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ
  let eP : ℕ → ℝ := fun n ↦
    (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ) -
      ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ
  refine ⟨eQ, eP, ?_, ?_, ?_, hOrdered, hRectSubset, hDisj, hVolume⟩
  · intro n
    constructor
    · -- Rewrite the target contour sum and the stage sum through the rooted loops, then store the
      -- difference as the explicit `Q dy` error.
      dsimp [eQ]
      rw [hBoundaryQ, hStageQ n]
      ring
    · -- The same transport packages the `P dx` discrepancy as an explicit scalar error.
      dsimp [eP]
      rw [hBoundaryP, hStageP n]
      ring
  · -- Once the stage-loop contours converge to the rooted boundary loop contour, the `Q dy`
    -- discrepancy tends to zero by subtraction from the constant target sequence.
    have hErrorQ :
        Filter.Tendsto
          (fun n ↦
            (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ) -
              ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds
            ((∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ) -
              (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ))) := by
      exact tendsto_const_nhds.sub hContourQ
    simpa [eQ] using hErrorQ
  · -- The horizontal half-form errors vanish by the same constant-minus-convergent argument.
    have hErrorP :
        Filter.Tendsto
          (fun n ↦
            (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ) -
              ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds
            ((∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ) -
              (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ))) := by
      exact tendsto_const_nhds.sub hContourP
    simpa [eP] using hErrorP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the rooted boundary loop and the
rooted rectangle-stage loop family are known to have the same two contour limits, the exact
coordinate half-formulas follow by passing through the exact rectangle-stage and direct
set-approximation packages. -/
theorem coordinateHalfFormulas_onInterior_of_rootedBoundaryLoopComparison
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    {z0 : ℂ} {γ : Path z0 z0} {γStage : ∀ n : ℕ, Path z0 z0}
    (hK_compact : IsCompact K) (hKC : K ⊆ C)
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hBoundaryQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hBoundaryP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hStageQ :
      ∀ n,
        ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hStageP :
      ∀ n,
        ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hContourQ :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)))
    (hContourP :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        -∫ z in interior K, dPdy z) := by
  rcases
      rootedBoundaryLoopStageComparison_toExactPackage
        (Γ := Γ) (P := P) (Q := Q) (N := N) (z := z) (w := w)
        hOrdered hRectSubset hDisj hBoundaryQ hBoundaryP hStageQ hStageP hContourQ hContourP
        hVolume with
    ⟨eQ, eP, hStage, heQ, heP, hOrdered', hRectSubset', hDisj', hVolume'⟩
  have hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n, U n ⊆ interior K) ∧
            (∀ n, MeasurableSet (U n)) ∧
            (∀ n,
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
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
            Filter.Tendsto eP Filter.atTop (nhds 0) :=
    directSetApproximationPackage_of_exactRectangleStagePackage
      (Γ := Γ) (C := C) (K := K) hK_compact hKC
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx
      ⟨N, z, w, eQ, eP, hOrdered', hRectSubset', hDisj', hStage, heQ, heP, hVolume'⟩
  rcases hApprox with ⟨U, eQ', eP', hU_subset, hU_meas, hStage', hSetQ, hSetP, heQ', heP'⟩
  have hApproxCore :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n,
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
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
    exact ⟨U, eQ', eP', hStage', hSetQ, hSetP, heQ', heP'⟩
  -- Once the rooted comparison has been converted into a direct set-approximation package, the
  -- generic approximation endgame yields the two exact half-formulas.
  exact
    coordinateHalfFormulas_onInterior_of_setApproximation
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx) hApproxCore

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the rooted-loop contour
comparison is available, the connected-open asymptotic rectangle-stage theorem is just the formal
composition of the exact-package wrapper with the asymptotic consumer. -/
theorem asymptoticRectangleBoundaryStages_of_rootedBoundaryLoopComparison
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    {z0 : ℂ} {γ : Path z0 z0} {γStage : ∀ n : ℕ, Path z0 z0}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hBoundaryQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hBoundaryP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hStageQ :
      ∀ n,
        ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hStageP :
      ∀ n,
        ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hContourQ :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)))
    (hContourP :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ∃ N : ℕ → ℕ,
      ∃ z w : ∀ n, Fin (N n) → ℂ,
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  -- First package the rooted comparison as an exact rectangle-stage family with vanishing scalar
  -- errors, then feed that exact package into the generic asymptotic consumer.
  rcases
      rootedBoundaryLoopStageComparison_toExactPackage
        (Γ := Γ) (P := P) (Q := Q) (N := N) (z := z) (w := w)
        hOrdered hRectSubset hDisj hBoundaryQ hBoundaryP hStageQ hStageP hContourQ hContourP
        hVolume with
    ⟨eQ, eP, hStage, heQ, heP, hOrdered', hRectSubset', hDisj', hVolume'⟩
  exact
    asymptoticRectangleBoundaryStages_of_exactPackage
      hOrdered' hRectSubset' hDisj' hStage heQ heP hVolume'


end ConnectedSetApproximationSupport
