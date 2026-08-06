import Mathlib.Analysis.Convex.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_5_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FundamentalGroup
open scoped unitInterval

private def circleLoopLift (γ : Path (1 : Circle) 1) :
    Path (0 : ℝ) (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ⟧) : ℝ) :=
  { toContinuousMap :=
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ)
    source' :=
      real_fourierChar_isCoveringMap.liftPath_zero γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ)
    target' := by
      simpa using (circleFundamentalGroupLiftEndpoint_spec γ).symm }

private theorem circleLoopLift_target_eq_one (γ : Path (1 : Circle) 1) :
    Real.fourierChar (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ⟧) : ℝ) = (1 : Circle) := by
  change (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ⟧)).1 ∈
      Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle)
  exact (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ⟧)).2

private theorem circleLoopLift_map_cast
    (γ : Path (1 : Circle) 1) {y : ℝ}
    (hy : (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ⟧) : ℝ) = y)
    (hend : Real.fourierChar y = (1 : Circle)) :
    (((circleLoopLift γ).cast rfl hy.symm).map Real.continuous_fourierChar).cast
        (by simp) hend.symm =
      γ := by
  ext s
  simpa [circleLoopLift, hy, Path.cast_coe, Path.map_coe, Function.comp_apply] using
    congrFun (fourierChar_liftPath_spec γ).1 s

private theorem circleLoopLift_endpoint_eq
    {γ₀ γ₁ : Path (1 : Circle) 1}
    (hindex :
      circleFundamentalGroupLiftIndex (fromPath ⟦γ₀⟧) =
        circleFundamentalGroupLiftIndex (fromPath ⟦γ₁⟧)) :
    (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₀⟧) : ℝ) =
      circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₁⟧) := by
  calc
    (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₀⟧) : ℝ) =
        ((circleFundamentalGroupLiftIndex (fromPath ⟦γ₀⟧) : ℤ) : ℝ) := by
          symm
          exact circleFundamentalGroupLiftIndex_eq_endpoint _
    _ = ((circleFundamentalGroupLiftIndex (fromPath ⟦γ₁⟧) : ℤ) : ℝ) := by
          simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hindex
    _ = circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₁⟧) := by
          exact circleFundamentalGroupLiftIndex_eq_endpoint _

/-- Lemma 1.5.10: the lift-index map `j : π₁(S¹, 1) → ℤ`, represented by
`circleFundamentalGroupLiftIndex`, is injective. -/
-- Proof sketch: represent loop classes by actual loops, lift both loops through the covering map
-- `Real.fourierChar : ℝ → S¹` starting at `0`, and use equality of lift indices to identify their
-- endpoints. Since `ℝ` is simply connected, the two lifted paths are homotopic; mapping that
-- homotopy down to `S¹` shows the original loops are homotopic.
theorem circleFundamentalGroupLiftIndex_injective :
    Function.Injective circleFundamentalGroupLiftIndex := by
  intro γ₀ γ₁ hindex
  revert hindex
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro γ₀ γ₁ hindex
  have hEndpoint : (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₀⟧) : ℝ) =
      circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₁⟧) :=
    circleLoopLift_endpoint_eq hindex
  have hend :
      Real.fourierChar (circleFundamentalGroupLiftEndpoint (fromPath ⟦γ₀⟧) : ℝ) = (1 : Circle) :=
    circleLoopLift_target_eq_one γ₀
  have hstart : Real.fourierChar (0 : ℝ) = (1 : Circle) := by
    simp
  have hlifted :
      (circleLoopLift γ₀).Homotopic ((circleLoopLift γ₁).cast rfl hEndpoint) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmapped :
      (((circleLoopLift γ₀).map Real.continuous_fourierChar).cast
          hstart.symm hend.symm).Homotopic
        ((((circleLoopLift γ₁).cast rfl hEndpoint).map Real.continuous_fourierChar).cast
          hstart.symm hend.symm) := by
    simpa [hstart, hEndpoint, hend] using
      Path.Homotopic.map hlifted ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  have hmap₀ :
      (((circleLoopLift γ₀).map Real.continuous_fourierChar).cast
          hstart.symm hend.symm) =
        γ₀ :=
    circleLoopLift_map_cast γ₀ rfl hend
  have hmap₁ :
      ((((circleLoopLift γ₁).cast rfl hEndpoint).map Real.continuous_fourierChar).cast
          hstart.symm hend.symm) =
        γ₁ :=
    circleLoopLift_map_cast γ₁ hEndpoint.symm hend
  simpa using
    (FundamentalGroupoid.fromPath_eq_iff_homotopic γ₀ γ₁).2 (hmap₀.symm ▸ hmap₁.symm ▸ hmapped)

/-- Two based loop classes in `π₁(S¹, 1)` have the same lift index exactly when they coincide. -/
theorem circleFundamentalGroupLiftIndex_eq_iff
    {γ₀ γ₁ : FundamentalGroup Circle (1 : Circle)} :
    circleFundamentalGroupLiftIndex γ₀ = circleFundamentalGroupLiftIndex γ₁ ↔ γ₀ = γ₁ :=
  circleFundamentalGroupLiftIndex_injective.eq_iff
