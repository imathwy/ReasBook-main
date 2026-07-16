import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0007_Remark_III_5_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».WeightedLogPeriodicity
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».RectangleBoundaryBridge

open Filter
open scoped BigOperators Topology unitInterval
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: every lattice class has a representative in any chosen period
parallelogram. -/
lemma exists_mem_periodParallelogram_sub_lattice
    (z z₀ : ℂ) :
    ∃ w : ℂ, w ∈ L.periodParallelogram z₀ ∧ w - z ∈ L.lattice := by
  let c : Fin 2 → ℝ := L.basis.equivFun (z - z₀)
  let w : ℂ := z₀ + Int.fract (c 0) • L.ω₁ + Int.fract (c 1) • L.ω₂
  refine ⟨w, ?_, ?_⟩
  · -- The fractional coordinates stay in `[0, 1)`, so they define a point of the chosen
    -- period parallelogram.
    refine ⟨Int.fract (c 0), Int.fract (c 1), Int.fract_nonneg _, ?_, Int.fract_nonneg _, ?_, rfl⟩
    · exact le_of_lt (Int.fract_lt_one _)
    · exact le_of_lt (Int.fract_lt_one _)
  · -- Subtracting the integer parts of the basis coordinates produces the required lattice
    -- translation from `z` to the chosen representative `w`.
    have hcoords : z - z₀ = c 0 * L.ω₁ + c 1 * L.ω₂ := by
      simpa [c, smul_eq_mul] using (L.basis.sum_equivFun (z - z₀)).symm
    have hz' : z = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by
      calc
        z = z₀ + (z - z₀) := by ring
        _ = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by rw [hcoords]
    have hwz :
        w - z = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
      calc
        w - z =
            (Int.fract (c 0) - c 0) * L.ω₁ + (Int.fract (c 1) - c 1) * L.ω₂ := by
              rw [hz']
              simp [w]
              ring
        _ = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
              have h0 :
                  ((↑(Int.fract (c 0)) : ℂ) - ↑(c 0)) = (((-⌊c 0⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h0r : (c 0 - (⌊c 0⌋ : ℝ)) - c 0 = (-((⌊c 0⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h0r
              have h1 :
                  ((↑(Int.fract (c 1)) : ℂ) - ↑(c 1)) = (((-⌊c 1⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h1r : (c 1 - (⌊c 1⌋ : ℝ)) - c 1 = (-((⌊c 1⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h1r
              rw [h0, h1]
    exact L.mem_lattice.mpr ⟨-⌊c 0⌋, -⌊c 1⌋, hwz.symm⟩

/-- Helper for Proposition 5.2: every period parallelogram is compact. -/
lemma isCompact_periodParallelogram (z₀ : ℂ) :
    IsCompact (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ → ℂ := fun t ↦ z₀ + t.1 • L.ω₁ + t.2 • L.ω₂
  have he : Continuous e := by
    -- The affine-coordinate parametrization is continuous in both real variables.
    continuity
  have himage :
      e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = L.periodParallelogram z₀ := by
    ext z
    constructor
    · rintro ⟨⟨t₁, t₂⟩, ht, rfl⟩
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨t₁, t₂, ht₁.1, ht₁.2, ht₂.1, ht₂.2, rfl⟩
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      exact ⟨⟨t₁, t₂⟩, ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, rfl⟩
  -- Compactness comes from the closed unit square via the affine parametrization.
  rw [← himage]
  exact (isCompact_Icc.prod isCompact_Icc).image he

/-- Helper for Proposition 5.2: the basis-coordinate homeomorphism identifies a real pair
`(t₁, t₂)` with the linear combination `t₁ ω₁ + t₂ ω₂`. -/
lemma basis_pair_homeomorph_apply (p : ℝ × ℝ) :
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the inverse basis map through the standard `Fin 2` coordinates.
  calc
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
        L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) := by
          rfl
    _ = ∑ i : Fin 2,
          L.basis.equivFun
            (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i •
            L.basis i := by
          simpa using
            (L.basis.sum_equivFun
              (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p))).symm
    _ = ∑ i : Fin 2, ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) i • L.basis i := by
          congr with i
          exact congrArg (fun a : ℝ ↦ a • L.basis i)
            (congrFun
              (L.basis.equivFunL.apply_symm_apply
                ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i)
    _ = p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simp [Fin.sum_univ_two]

/-- Helper for Proposition 5.2: the affine period-coordinate homeomorphism sends the standard
unit square to the period parallelogram. -/
def periodParallelogramCoordinateHomeomorph (z₀ : ℂ) : ℂ ≃ₜ ℂ :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀))

/-- Helper for Proposition 5.2: the period-coordinate homeomorphism has the expected affine
formula in terms of the period basis. -/
theorem periodParallelogramCoordinateHomeomorph_apply
    (z₀ z : ℂ) :
    periodParallelogramCoordinateHomeomorph (L := L) z₀ z = z₀ + z.re • L.ω₁ + z.im • L.ω₂ := by
  -- Read the homeomorphism through the real and imaginary coordinates of `z`.
  change
    z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
      (Complex.equivRealProd z) : ℂ) =
      z₀ + z.re • L.ω₁ + z.im • L.ω₂
  rw [basis_pair_homeomorph_apply]
  simpa [smul_eq_mul, add_assoc]

/-- Helper for Proposition 5.2: the explicit four-edge loop around a period parallelogram. -/
def periodParallelogramBoundaryPath (z₀ : ℂ) : Path z₀ z₀ :=
  let z₁ := z₀ + L.ω₁
  let z₂ := z₀ + L.ω₁ + L.ω₂
  let z₃ := z₀ + L.ω₂
  (Path.segment z₀ z₁).trans
    ((Path.segment z₁ z₂).trans
      ((Path.segment z₂ z₃).trans
        (Path.segment z₃ z₀)))

/-- Helper for Proposition 5.2: the period-parallelogram boundary loop is the image of the
standard unit-square boundary under the period-coordinate homeomorphism. -/
theorem periodParallelogramBoundaryPath_eq_map_standardRectangle
    (z₀ : ℂ) :
      periodParallelogramBoundaryPath (L := L) z₀ =
      ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).map
        (periodParallelogramCoordinateHomeomorph (L := L) z₀).continuous).cast
        (by
          simpa using
            (periodParallelogramCoordinateHomeomorph_apply (L := L) z₀ 0).symm)
        (by
          simpa using
            (periodParallelogramCoordinateHomeomorph_apply (L := L) z₀ 0).symm) := by
  ext t
  -- Both paths follow the same four affine sides after transporting the standard rectangle by the
  -- period-coordinate homeomorphism.
  simp [periodParallelogramBoundaryPath, axisParallelRectangleBoundaryPath, Path.trans_apply,
    periodParallelogramCoordinateHomeomorph_apply, AffineMap.lineMap_apply]
  split_ifs <;> ring

/-- Helper for Proposition 5.2: the period-coordinate homeomorphism sends the closed unit square
to the chosen period parallelogram. -/
theorem periodParallelogram_eq_image_standardRectangle
    (z₀ : ℂ) :
    periodParallelogramCoordinateHomeomorph (L := L) z₀ '' Complex.Rectangle 0 (1 + Complex.I) =
      L.periodParallelogram z₀ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (0 ≤ w.re ∧ w.re ≤ 1) ∧ 0 ≤ w.im ∧ w.im ≤ 1 := by
      simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using hw
    refine ⟨w.re, w.im, hw'.1.1, hw'.1.2, hw'.2.1, hw'.2.2, ?_⟩
    -- Read the image point through the real and imaginary coordinates of `w`.
    simpa using periodParallelogramCoordinateHomeomorph_apply (L := L) z₀ w
  · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
    refine ⟨t₁ + t₂ * Complex.I, ?_, ?_⟩
    · simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using
        And.intro (And.intro ht₁0 ht₁1) (And.intro ht₂0 ht₂1)
    · -- The standard square point with coordinates `(t₁, t₂)` maps to the requested period-cell
      -- point.
      simpa using
        (periodParallelogramCoordinateHomeomorph_apply (L := L) z₀ (t₁ + t₂ * Complex.I))

/-- Helper for Proposition 5.2: the explicit period-parallelogram boundary loop is piecewise
differentiable because it is a concatenation of four affine segments. -/
theorem periodParallelogramBoundaryPath_isPiecewiseDifferentiable
    (z₀ : ℂ) :
    (periodParallelogramBoundaryPath (L := L) z₀).IsPiecewiseDifferentiable := by
  let z₁ : ℂ := z₀ + L.ω₁
  let z₂ : ℂ := z₀ + L.ω₁ + L.ω₂
  let z₃ : ℂ := z₀ + L.ω₂
  have h₁ : (Path.segment z₀ z₁).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₀ z₁
  have h₂ : (Path.segment z₁ z₂).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₁ z₂
  have h₃ : (Path.segment z₂ z₃).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₂ z₃
  have h₄ : (Path.segment z₃ z₀).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₃ z₀
  -- Reassociate the four-segment loop through the generic concatenation theorem.
  simpa [periodParallelogramBoundaryPath, z₁, z₂, z₃] using
    Path.IsPiecewiseDifferentiable.trans h₁
      (Path.IsPiecewiseDifferentiable.trans h₂
        (Path.IsPiecewiseDifferentiable.trans h₃ h₄))

/-- Helper for Proposition 5.2: the range of the explicit boundary loop is exactly the frontier
of the period parallelogram. -/
lemma periodParallelogramBoundaryPath_range_eq_frontier
    (z₀ : ℂ) :
    Set.range (periodParallelogramBoundaryPath (L := L) z₀) =
      frontier (L.periodParallelogram z₀) := by
  have hrect_range :
      Set.range (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)) =
        frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
    let zw := Complex.mk (1 + Complex.I).re (Complex.im 0)
    let wz := Complex.mk (Complex.re 0) (1 + Complex.I).im
    -- Expand the concatenation into the four oriented sides.
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    rw [range_segment_horizontal (Complex.re 0) (1 + Complex.I).re (Complex.im 0)]
    rw [range_segment_vertical (Complex.im 0) (1 + Complex.I).im (1 + Complex.I).re]
    rw [range_segment_horizontal (1 + Complex.I).re (Complex.re 0) (1 + Complex.I).im]
    rw [range_segment_vertical (1 + Complex.I).im (Complex.im 0) (Complex.re 0)]
    -- The four side ranges are exactly the four edge pieces of the frontier.
    rw [complex_rectangle_frontier_eq_edge_union 0 (1 + Complex.I)]
    ext x
    simp [Set.uIcc, min_comm, max_comm, or_assoc, zw, wz]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    have ht :
        periodParallelogramBoundaryPath (L := L) z₀ t =
          periodParallelogramCoordinateHomeomorph (L := L) z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
      -- Evaluate the boundary-path image formula at the chosen boundary parameter.
      simpa using
        congrArg (fun γ : Path z₀ z₀ ↦ γ t)
          (periodParallelogramBoundaryPath_eq_map_standardRectangle (L := L) z₀)
    have hrect :
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t ∈
          frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
      -- The standard rectangle boundary path covers the full frontier.
      rw [← hrect_range]
      exact ⟨t, rfl⟩
    have himage :
        periodParallelogramCoordinateHomeomorph (L := L) z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) ∈
          frontier (L.periodParallelogram z₀) := by
      -- Transport the frontier membership through the period-coordinate homeomorphism.
      have :
          periodParallelogramCoordinateHomeomorph (L := L) z₀
              (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) ∈
            periodParallelogramCoordinateHomeomorph (L := L) z₀ ''
              frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
        exact ⟨axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t, hrect, rfl⟩
      rwa [(periodParallelogramCoordinateHomeomorph (L := L) z₀).image_frontier,
        periodParallelogram_eq_image_standardRectangle (L := L) z₀] at this
    simpa [ht] using himage
  · intro hz
    have hz' : z ∈ frontier (L.periodParallelogram z₀) := hz
    have hz'' :
        z ∈
          periodParallelogramCoordinateHomeomorph (L := L) z₀ ''
            frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
      -- Pull the frontier point back through the coordinate homeomorphism.
      have hzImage :
          z ∈ frontier
            (periodParallelogramCoordinateHomeomorph (L := L) z₀ ''
              Complex.Rectangle 0 (1 + Complex.I)) := by
        simpa [periodParallelogram_eq_image_standardRectangle (L := L) z₀] using hz'
      rw [← (periodParallelogramCoordinateHomeomorph (L := L) z₀).image_frontier] at hzImage
      exact hzImage
    rcases hz'' with ⟨w, hw, rfl⟩
    have hwRange : w ∈ Set.range (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)) := by
      -- The standard rectangle boundary path covers the entire rectangle frontier.
      rw [hrect_range]
      exact hw
    rcases hwRange with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    have ht :
        periodParallelogramBoundaryPath (L := L) z₀ t =
          periodParallelogramCoordinateHomeomorph (L := L) z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
      -- Reuse the same pointwise image formula to recover the actual slanted boundary point.
      simpa using
        congrArg (fun γ : Path z₀ z₀ ↦ γ t)
          (periodParallelogramBoundaryPath_eq_map_standardRectangle (L := L) z₀)
    exact ht

/-- Helper for Proposition 5.2: the period coordinates also define a real affine equivalence on
`Plane`. -/
def periodParallelogramCoordinateAffineEquiv
    (z₀ : ℂ) : Plane ≃ᴬ[ℝ] Plane :=
  let e : Plane ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm
  (e.toContinuousAffineEquiv.trans (ContinuousAffineEquiv.constVAdd ℝ ℂ z₀)).trans
    Complex.equivRealProdCLM.toContinuousAffineEquiv

/-- Helper for Proposition 5.2: the real affine period-coordinate map sends the pair `(t, u)` to
the corresponding affine period combination. -/
theorem periodParallelogramCoordinateAffineEquiv_apply
    (z₀ : ℂ) (p : Plane) :
    Complex.equivRealProdCLM.symm
        (periodParallelogramCoordinateAffineEquiv (L := L) z₀ p) =
      z₀ + p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the affine equivalence through the period-basis coordinates.
  have hbasis :
      (L.basis.equivFunL.symm ![p.1, p.2] : ℂ) = p.1 • L.ω₁ + p.2 • L.ω₂ := by
    simpa using (basis_pair_homeomorph_apply (L := L) p)
  calc
    Complex.equivRealProdCLM.symm
        (periodParallelogramCoordinateAffineEquiv (L := L) z₀ p) =
          (ContinuousAffineEquiv.constVAdd ℝ ℂ z₀) (L.basis.equivFunL.symm ![p.1, p.2]) := by
            simpa [periodParallelogramCoordinateAffineEquiv] using
              (Complex.equivRealProdCLM.left_inv
                ((ContinuousAffineEquiv.constVAdd ℝ ℂ z₀) (L.basis.equivFunL.symm ![p.1, p.2])))
    _ = z₀ + (L.basis.equivFunL.symm ![p.1, p.2] : ℂ) := by rfl
    _ = z₀ + p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simpa [add_assoc] using congrArg (fun z : ℂ ↦ z₀ + z) hbasis

/-- Helper for Proposition 5.2: the `Plane` affine chart and the complex homeomorphism describe
the same period-coordinate change of variables. -/
theorem periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph
    (z₀ : ℂ) (p : Plane) :
    Complex.equivRealProdCLM.symm
        (periodParallelogramCoordinateAffineEquiv (L := L) z₀ p) =
      periodParallelogramCoordinateHomeomorph (L := L) z₀
        (Complex.equivRealProdCLM.symm p) := by
  -- Both coordinate owners expand to the same affine combination in the period basis.
  rw [periodParallelogramCoordinateAffineEquiv_apply,
    periodParallelogramCoordinateHomeomorph_apply]
  simp [Complex.equivRealProdCLM_symm_apply, add_assoc]

/-- Helper for Proposition 5.2: the slanted boundary real curve is the period-coordinate image of
the standard rectangle boundary real curve. -/
theorem periodParallelogramBoundary_realCurve_eq_standardRectangle
    (z₀ : ℂ) (t : ℝ) :
    ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t =
      periodParallelogramCoordinateAffineEquiv (L := L) z₀
        (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
  apply (Complex.equivRealProdCLM.symm).injective
  -- Compare both plane-valued curves through the corresponding complex-valued paths.
  change (periodParallelogramBoundaryPath (L := L) z₀).extend t =
    Complex.equivRealProdCLM.symm
      (periodParallelogramCoordinateAffineEquiv (L := L) z₀
        (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t))
  have hmap :
      (periodParallelogramBoundaryPath (L := L) z₀).extend t =
        periodParallelogramCoordinateHomeomorph (L := L) z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the path-level map theorem at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (periodParallelogramBoundaryPath_eq_map_standardRectangle (L := L) z₀)
  rw [hmap, periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph]
  rfl

/-- Helper for Proposition 5.2: equality of two points on the explicit period-parallelogram
boundary loop forces equality of the parameters, except for the endpoint identification `0 ~ 1`.
-/
theorem periodParallelogramBoundaryPath_simple_eq_or_endpoints
    (z₀ : ℂ) {s t : I}
    (hst :
      periodParallelogramBoundaryPath (L := L) z₀ s =
        periodParallelogramBoundaryPath (L := L) z₀ t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hs :
      periodParallelogramBoundaryPath (L := L) z₀ s =
        periodParallelogramCoordinateHomeomorph (L := L) z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s) := by
    -- Evaluate the transported boundary-path identity at the parameter `s`.
    simpa using
      congrArg (fun γ : Path z₀ z₀ ↦ γ s)
        (periodParallelogramBoundaryPath_eq_map_standardRectangle (L := L) z₀)
  have ht :
      periodParallelogramBoundaryPath (L := L) z₀ t =
        periodParallelogramCoordinateHomeomorph (L := L) z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
    -- The same transport formula holds at the parameter `t`.
    simpa using
      congrArg (fun γ : Path z₀ z₀ ↦ γ t)
        (periodParallelogramBoundaryPath_eq_map_standardRectangle (L := L) z₀)
  have hrect :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s =
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t := by
    -- Injectivity of the period-coordinate homeomorphism reduces to the unit rectangle.
    apply (periodParallelogramCoordinateHomeomorph (L := L) z₀).injective
    calc
      periodParallelogramCoordinateHomeomorph (L := L) z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s) =
          periodParallelogramBoundaryPath (L := L) z₀ s := hs.symm
      _ = periodParallelogramBoundaryPath (L := L) z₀ t := hst
      _ =
          periodParallelogramCoordinateHomeomorph (L := L) z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := ht
  -- Delegate simplicity to the already imported unit-rectangle boundary theorem.
  exact unitRectangleBoundaryPath_simple_eq_or_endpoints hrect

/-- Helper for Proposition 5.2: every regular parameter on the slanted boundary lies on one of
the four open affine side intervals. -/
theorem periodParallelogramBoundary_regularParameterCases
    (z₀ : ℂ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ
        ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t₀ ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t₀ ∈ Set.Ioo (7 / 8) (1 : ℝ) := by
  let e := periodParallelogramCoordinateAffineEquiv (L := L) z₀
  have heDiff :
      DifferentiableAt ℝ (fun p : Plane ↦ e.symm p)
        (((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t₀) := by
    -- The inverse affine coordinate map is differentiable at every point.
    simpa [e] using
      (e.symm.toContinuousAffineMap.contDiff.differentiable one_ne_zero
        (((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t₀))
  have hrectDiffAux :
      DifferentiableWithinAt ℝ
        (fun t ↦ e.symm (((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t))
        (Set.Icc (0 : ℝ) 1) t₀ :=
    heDiff.comp_differentiableWithinAt t₀ hdiff
  have hrectDiff :
      DifferentiableWithinAt ℝ
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ := by
    -- Pull the regularity back to the unit rectangle through the inverse affine chart.
    refine hrectDiffAux.congr ?_ ?_
    · intro t ht
      have hcurve := periodParallelogramBoundary_realCurve_eq_standardRectangle (L := L) z₀ t
      calc
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t =
            e.symm
              (e
                (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
                  t)) := by
              simp [e]
        _ = e.symm (((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t) := by
              rw [hcurve]
    · have hcurve := periodParallelogramBoundary_realCurve_eq_standardRectangle (L := L) z₀ t₀
      calc
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t₀ =
            e.symm
              (e
                (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
                  t₀)) := by
              simp [e]
        _ = e.symm (((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t₀) := by
              rw [hcurve]
  -- The unit-rectangle regular-parameter classifier now applies verbatim.
  simpa using unitRectangle_regularParameterCases ht₀ hrectDiff

/-- Helper for Proposition 5.2: a standard-rectangle boundary-straightening chart transports
along the period-coordinate affine map to a chart for the period-parallelogram boundary. -/
theorem mapStandardRectangleBoundaryChart
    (z₀ : ℂ) {t₀ : ℝ}
    {δ : OpenPartialHomeomorph Plane Plane}
    (hδ :
      IsBoundaryStraighteningAt (Complex.Rectangle 0 (1 + Complex.I))
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t₀ δ) :
    IsBoundaryStraighteningAt (L.periodParallelogram z₀)
      ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t₀
      (δ.trans
        (periodParallelogramCoordinateAffineEquiv (L := L) z₀).toHomeomorph.toOpenPartialHomeomorph) := by
  let e := periodParallelogramCoordinateAffineEquiv (L := L) z₀
  let τ : OpenPartialHomeomorph Plane Plane := e.toHomeomorph.toOpenPartialHomeomorph
  have heCont : ContDiffOn ℝ 1 e (Set.univ : Set Plane) := by
    simpa using e.toContinuousAffineMap.contDiff.contDiffOn
  have heSymmCont : ContDiffOn ℝ 1 e.symm (Set.univ : Set Plane) := by
    simpa using e.symm.toContinuousAffineMap.contDiff.contDiffOn
  have heSymmTarget : ContDiffOn ℝ 1 e.symm ((δ.trans τ).target) := by
    exact heSymmCont.mono (by intro p hp; simp)
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The transported chart keeps the same parameter-strip source because the affine target map
    -- is globally defined.
    simpa [τ, OpenPartialHomeomorph.trans_source] using hδ.basePoint_mem_source
  · intro p hp
    -- The source restriction in the parameter plane is unchanged by the global affine target map.
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp
    exact hδ.source_subset hpδ
  · -- The transported forward map is the composition of two affine `C¹` maps on the same source.
    simpa [τ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_apply, Function.comp_def]
      using
        (heCont.comp hδ.contDiffOn (by intro p hp; simp))
  · -- The inverse transported chart is the inverse affine map composed with the original inverse.
    simpa [τ, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_apply, Function.comp_def]
      using
        (hδ.contDiffOn_symm.comp heSymmTarget
          (by
            intro p hp
            simp [τ, OpenPartialHomeomorph.trans_target] at hp
            exact hp))
  · intro t ht
    have htδ : t ∈ δ.horizontalAxisDomain := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, τ, OpenPartialHomeomorph.trans_source]
        using ht
    -- On the horizontal axis, the transported chart is just the affine target map applied to the
    -- standard rectangle boundary point.
    calc
      (δ.trans τ) (t, 0) = τ (δ (t, 0)) := by
        simp [τ, OpenPartialHomeomorph.trans_apply]
      _ = e (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
        rw [hδ.map_horizontal_axis htδ]
        rfl
      _ = ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t := by
        simpa using
          (periodParallelogramBoundary_realCurve_eq_standardRectangle (L := L) z₀ t).symm
  · -- The horizontal-axis image is determined by the transported forward chart formula.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htδ : t ∈ δ.horizontalAxisDomain := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, τ, OpenPartialHomeomorph.trans_source]
        using ht
    calc
      (δ.trans τ) (t, 0) = τ (δ (t, 0)) := by
        simp [τ, OpenPartialHomeomorph.trans_apply]
      _ = e (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
        rw [hδ.map_horizontal_axis htδ]
        rfl
      _ = ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t := by
        simpa using
          (periodParallelogramBoundary_realCurve_eq_standardRectangle (L := L) z₀ t).symm
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp.1
    have hneg : p.2 < 0 := hp.2
    have hxImage :
        Complex.equivRealProdCLM.symm ((δ.trans τ) p) ∈
          periodParallelogramCoordinateHomeomorph (L := L) z₀ ''
            (Complex.Rectangle 0 (1 + Complex.I)) := by
      rw [periodParallelogram_eq_image_standardRectangle (L := L) z₀]
      exact hz.2
    have hxRect :
        Complex.equivRealProdCLM.symm (δ p) ∈ Complex.Rectangle 0 (1 + Complex.I) := by
      rcases hxImage with ⟨x, hx, hxEq⟩
      have hcoord :
          periodParallelogramCoordinateHomeomorph (L := L) z₀
              (Complex.equivRealProdCLM.symm (δ p)) =
            Complex.equivRealProdCLM.symm ((δ.trans τ) p) := by
        simpa [τ, OpenPartialHomeomorph.trans_apply] using
          (periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph (L := L) z₀ (δ p))
      have hxEq' :
          periodParallelogramCoordinateHomeomorph (L := L) z₀ x =
            periodParallelogramCoordinateHomeomorph (L := L) z₀
              (Complex.equivRealProdCLM.symm (δ p)) := by
        exact hxEq.trans hcoord.symm
      have : x = Complex.equivRealProdCLM.symm (δ p) :=
        (periodParallelogramCoordinateHomeomorph (L := L) z₀).injective hxEq'
      simpa [this] using hx
    have hzRectImage :
        Complex.equivRealProdCLM.symm (δ p) ∈
          (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {q : Plane | q.2 < 0}))) ∩
            Complex.Rectangle 0 (1 + Complex.I) := by
      refine ⟨?_, hxRect⟩
      refine ⟨δ p, ?_, rfl⟩
      exact ⟨p, ⟨hpδ, hneg⟩, rfl⟩
    exact Set.eq_empty_iff_forall_notMem.mp hδ.exterior_on_right
      (Complex.equivRealProdCLM.symm (δ p)) hzRectImage
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp.1
    have hpos : 0 < p.2 := hp.2
    have hxRect :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      have hzRectImage :
          Complex.equivRealProdCLM.symm (δ p) ∈
            Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {q : Plane | 0 < q.2})) := by
        refine ⟨δ p, ?_, rfl⟩
        exact ⟨p, ⟨hpδ, hpos⟩, rfl⟩
      exact hδ.interior_on_left hzRectImage
    have hxImage :
        periodParallelogramCoordinateHomeomorph (L := L) z₀
            (Complex.equivRealProdCLM.symm (δ p)) ∈
          periodParallelogramCoordinateHomeomorph (L := L) z₀ ''
            interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      exact ⟨Complex.equivRealProdCLM.symm (δ p), hxRect, rfl⟩
    have hcoord :
        periodParallelogramCoordinateHomeomorph (L := L) z₀
            (Complex.equivRealProdCLM.symm (δ p)) =
          Complex.equivRealProdCLM.symm ((δ.trans τ) p) := by
      simpa [τ, OpenPartialHomeomorph.trans_apply] using
        (periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph (L := L) z₀ (δ p))
    have hxInterior :
        Complex.equivRealProdCLM.symm ((δ.trans τ) p) ∈ interior (L.periodParallelogram z₀) := by
      rw [(periodParallelogramCoordinateHomeomorph (L := L) z₀).image_interior,
        periodParallelogram_eq_image_standardRectangle (L := L) z₀] at hxImage
      exact hcoord ▸ hxImage
    simpa [τ, OpenPartialHomeomorph.trans_apply] using hxInterior

/-- Helper for Proposition 5.2: every regular parameter on the explicit period-parallelogram
boundary admits a boundary-straightening chart. -/
theorem periodParallelogramBoundary_exists_boundary_straightening
    (z₀ : ℂ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ
        ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (L.periodParallelogram z₀)
        ((periodParallelogramBoundaryPath (L := L) z₀).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: classify the regular parameter on the unit rectangle, choose the
  -- corresponding branch chart there, then transport it through the affine period coordinates.
  rcases periodParallelogramBoundary_regularParameterCases
      (L := L) z₀ ht₀ hdiff with
    htbottom | htright | httop | htleft
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_bottom_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htbottom
    refine ⟨_, mapStandardRectangleBoundaryChart (L := L) z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_right_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htright
    refine ⟨_, mapStandardRectangleBoundaryChart (L := L) z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_top_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) httop
    refine ⟨_, mapStandardRectangleBoundaryChart (L := L) z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_left_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htleft
    refine ⟨_, mapStandardRectangleBoundaryChart (L := L) z₀ hδ⟩

/-- Helper for Proposition 5.2: the explicit four-edge period-parallelogram loop is the singleton
oriented boundary family of the translated period cell. -/
theorem periodParallelogramBoundary_isOrientedBoundaryOf
    (z₀ : ℂ) :
    IsOrientedBoundaryOf (L.periodParallelogram z₀)
      (fun _ : Unit ↦ (periodParallelogramBoundaryPath (L := L) z₀).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (periodParallelogramBoundaryPath (L := L) z₀).toClosedPath
  change IsOrientedBoundaryOf (L.periodParallelogram z₀) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- Compactness already follows from the affine image description of the period cell.
    exact isCompact_periodParallelogram (L := L) z₀
  · rintro ⟨⟩
    -- The singleton contour inherits the explicit four-segment piecewise differentiability.
    simpa [Γ] using periodParallelogramBoundaryPath_isPiecewiseDifferentiable (L := L) z₀
  · rintro ⟨⟩ s t hst
    -- Simplicity is exactly the transported unit-rectangle injectivity statement.
    exact periodParallelogramBoundaryPath_simple_eq_or_endpoints (L := L) z₀ hst
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ).toPath)) =
          Set.range (periodParallelogramBoundaryPath (L := L) z₀) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        cases i
        simpa [Γ, Path.toClosedPath] using hi
      · intro hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨(), ?_⟩
        simpa [Γ, Path.toClosedPath] using hx
    -- Rewrite the singleton-family range equality back to the explicit loop frontier theorem.
    simpa using
      hboundary.trans (periodParallelogramBoundaryPath_range_eq_frontier (L := L) z₀)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The local geometric input is exactly the explicit boundary-straightening theorem above.
    exact
      periodParallelogramBoundary_exists_boundary_straightening
        (L := L) z₀ ht₀ hdiff hderiv

