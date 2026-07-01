import Mathlib
import cartan.IV.section17.«0009_Exercise_1»
import cartan.IV.section17.«0012_Exercise_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Laplacian
open scoped InnerProductSpace

-- Domain sampling note: in this chapter the source-facing owner for holomorphicity on an open set
-- is `DifferentiableOn ℂ` from `IV/section17/0001_Definition_IV_5_extra_1.lean`, while
-- `AnalyticOnNhd ℂ` is a derived bridge/view. For the target conclusion, the source-facing owner
-- is `IsSubharmonicOn` from `IV/section17/0012_Exercise_4.lean`, and its Laplacian reformulation
-- is the derived bridge `isSubharmonicOn_iff_nonneg_laplacianWithin`.

/-- Helper for Example IV.5-extra-5: the logarithmic squared-modulus potential is `C²` on the
open domain of a holomorphic function. -/
lemma contDiffOn_log_one_add_norm_sq
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) :
    ContDiffOn ℝ 2 (fun z : ℂ ↦ Real.log (1 + ‖f z‖ ^ 2)) D := by
  -- First pass from holomorphicity to real smoothness for `f`.
  have hcontf : ContDiffOn ℝ 2 f D :=
    (hf.analyticOnNhd hD).restrictScalars.contDiffOn_of_completeSpace
  -- Then build the positive logarithm input `1 + ‖f z‖^2`.
  have hone : ContDiffOn ℝ 2 (fun _ : ℂ ↦ (1 : ℝ)) D := contDiffOn_const
  have hnorm : ContDiffOn ℝ 2 (fun z : ℂ ↦ ‖f z‖ ^ 2) D := hcontf.norm_sq ℂ
  have hbase : ContDiffOn ℝ 2 (fun z : ℂ ↦ 1 + ‖f z‖ ^ 2) D := hone.add hnorm
  -- Positivity of `1 + ‖f z‖^2` makes `Real.log` smooth on the range.
  refine hbase.log ?_
  intro z hz
  have hpos : 0 < 1 + ‖f z‖ ^ 2 := by
    positivity
  exact hpos.ne'

/-- Helper for Example IV.5-extra-5: on an open set, the within-Laplacian of
`z ↦ log (1 + ‖f z‖^2)` agrees with the ordinary Laplacian. -/
lemma laplacianWithin_log_one_add_norm_sq_eq
    {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D)
    (hcont : ContDiffOn ℝ 2 (fun z : ℂ ↦ Real.log (1 + ‖f z‖ ^ 2)) D)
    {z : ℂ} (hz : z ∈ D) :
    (Δ[D] fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z =
      Δ (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z := by
  -- Rewrite both Laplacians through second iterated derivatives on the complex plane.
  rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane
      (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) hD.uniqueDiffOn hz,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane
      (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2))]
  -- On an open set, the within-derivatives coincide with the ordinary derivatives.
  have hiter :
      iteratedFDerivWithin ℝ 2 (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) D z =
        iteratedFDeriv ℝ 2 (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z :=
    iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn
      ((hcont z hz).contDiffAt (hD.mem_nhds hz)) hz
  rw [hiter]

/-- Helper for Example IV.5-extra-5: the Laplacian of `z ↦ log (1 + ‖f z‖^2)` is pointwise
nonnegative on the open holomorphic domain. -/
lemma log_one_add_norm_sq_nonneg_laplacianWithin_at
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {z : ℂ} (hz : z ∈ D) :
    0 ≤ (Δ[D] fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z := by
  have hcont : ContDiffOn ℝ 2 (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) D :=
    contDiffOn_log_one_add_norm_sq hD hf
  -- First move from the within-Laplacian to the ordinary Laplacian on the open set.
  rw [laplacianWithin_log_one_add_norm_sq_eq hD hcont hz]
  -- Then insert the explicit Exercise 1 formula.
  rw [laplacian_log_one_add_normSq_of_holomorphicOn hD hf hz]
  -- The quotient is nonnegative because both numerator and denominator are nonnegative.
  positivity

/--
Example IV.5-extra-5. If `f` is holomorphic on the open set `D`, then
`z ↦ log (1 + |f z|^2)` is subharmonic on `D`.
-/
theorem holomorphic_log_one_add_norm_sq_isSubharmonicOn
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) :
    IsSubharmonicOn (fun z ↦ Real.log (1 + ‖f z‖ ^ 2)) D := by
  have hcont : ContDiffOn ℝ 2 (fun z : ℂ ↦ Real.log (1 + ‖f z‖ ^ 2)) D :=
    contDiffOn_log_one_add_norm_sq hD hf
  -- Route correction: keep the source-faithful Laplacian criterion route from Exercise 4,
  -- then discharge the pointwise nonnegativity by the explicit Exercise 1 Laplacian formula.
  refine (isSubharmonicOn_iff_nonneg_laplacianWithin hD hcont).2 ?_
  intro z hz
  -- The pointwise Laplacian is nonnegative by the explicit formula from Exercise 1.
  exact log_one_add_norm_sq_nonneg_laplacianWithin_at hD hf hz

/--
Example IV.5-extra-5, Laplacian reformulation. If `f` is holomorphic on the open set `D`, then
`z ↦ log (1 + |f z|^2)` has nonnegative Laplacian on `D`.
-/
theorem holomorphic_log_one_add_norm_sq_nonneg_laplacianWithin
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) :
    ∀ z ∈ D, 0 ≤ (Δ[D] fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z := by
  intro z hz
  -- Reuse the pointwise nonnegativity statement proved above.
  exact log_one_add_norm_sq_nonneg_laplacianWithin_at hD hf hz
