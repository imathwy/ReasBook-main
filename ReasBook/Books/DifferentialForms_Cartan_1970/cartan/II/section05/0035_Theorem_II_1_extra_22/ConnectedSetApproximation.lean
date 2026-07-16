import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».ConnectedAmbientReduction
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22».SubtypeBoundaryBlocks

open MeasureTheory
open scoped BigOperators
open ConnectedSetApproximationSupport

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the only remaining connected-open
geometric blocker is to show that the rooted rectangle-stage loop family has the same two contour
limits as the rooted boundary loop. -/
theorem rootedBoundaryLoopStageHalfFormContours_tendstoBoundaryLoop_of_halfFormulas
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    {z0 : ℂ} {γ : Path z0 z0} {γStage : ∀ n : ℕ, Path z0 z0}
    (hBoundaryQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
    (hBoundaryP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)
    (hHalfQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ ζ in interior K, dQdx ζ)
    (hHalfP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        -∫ ζ in interior K, dPdy ζ)
    (hStageContourQ :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dQdx ζ)))
    (hStageContourP :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (-∫ ζ in interior K, dPdy ζ))) :
    Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ)) := by
  constructor
  · -- Once the total boundary contour is identified with the interior `dQdx` integral, the
    -- rooted stage-loop limit can be retargeted to the rooted boundary loop by rewriting the
    -- limit point.
    have hTargetQ :
        ∫ ζ in interior K, dQdx ζ =
          ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ := by
      calc
        ∫ ζ in interior K, dQdx ζ =
            ∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ := hHalfQ.symm
        _ = ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ := hBoundaryQ
    simpa [hTargetQ] using hStageContourQ
  · -- The same rewrite identifies the `P dx` target `-∫ dPdy` with the rooted boundary-loop
    -- contour value.
    have hTargetP :
        -∫ ζ in interior K, dPdy ζ =
          ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ := by
      calc
        -∫ ζ in interior K, dPdy ζ =
            ∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ := hHalfP.symm
        _ = ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ := hBoundaryP
    simpa [hTargetP] using hStageContourP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: stagewise contour identities let the
rectangle-boundary interior limits be transported directly to the rooted stage-loop family. -/
theorem rootedRectangleStageContourInteriorLimits_of_stageIdentities
    {K : Set ℂ} {P Q dPdy dQdx : ℂ → ℝ}
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    {z0 : ℂ} {γStage : ∀ n : ℕ, Path z0 z0}
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
    (hRectangleQ :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dQdx ζ)))
    (hRectangleP :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (-∫ ζ in interior K, dPdy ζ))) :
    Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dQdx ζ)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (-∫ ζ in interior K, dPdy ζ)) := by
  constructor
  · -- Rewrite the rooted stage-loop `Q dy` contours to the rectangle-stage family before taking
    -- the known rectangle-boundary limit.
    refine Filter.Tendsto.congr' ?_ hRectangleQ
    exact Filter.Eventually.of_forall fun n ↦ (hStageQ n).symm
  · -- Apply the same stagewise rewrite to transport the `P dx` interior limit.
    refine Filter.Tendsto.congr' ?_ hRectangleP
    exact Filter.Eventually.of_forall fun n ↦ (hStageP n).symm

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the only remaining connected-open
ambient approximation input is the single-component block package keyed by the ambient set `C`;
once that package is available, the generic set-approximation endgame yields the two interior
coordinate half-formulas. -/
theorem coordinateHalfFormulas_of_connectedAmbientComponentApproximation
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
    · -- Connectedness makes the filtered `Q dy` block sum equal to the total contour sum.
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
    · -- The same normalization removes the filter from the `P dx` block identity.
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
  -- Once the stage identities have been normalized to the total contour sums, the generic
  -- approximation-to-half-formula theorem finishes the connected-ambient case.
  exact
    coordinateHalfFormulas_onInterior_of_setApproximation
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx) hApproxTotal

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a connected-open single-block
approximation package already suffices to prove the exact interior half-formulas, so later rooted
boundary-loop transports can consume a package API instead of duplicating the same filter-removal
argument. -/
theorem
    IsOrientedBoundaryOf.coordinateHalfFormulas_onInteriorInConnectedOpen_ofConnectedAmbientSingleBlockApproximation
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ) (_hKC : K ⊆ C)
    (_hC_connected : IsConnected C)
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
  -- The earlier connected-ambient consumer already removes the unique block filter in a connected
  -- ambient set, so the package itself is the only genuinely missing input here.
  exact
    _root_.coordinateHalfFormulas_of_connectedAmbientComponentApproximation
      (hΓ := _hΓ) (hKC := _hKC) (hC_connected := _hC_connected) hApprox
