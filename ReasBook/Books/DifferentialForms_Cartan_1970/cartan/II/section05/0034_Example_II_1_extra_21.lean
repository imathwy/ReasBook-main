import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0034_Example_II_1_extra_21».BoundaryStraightening
import DifferentialForms_Cartan_1970.cartan.II.section05.«0034_Example_II_1_extra_21».Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- Helper for Example II.1-extra-21: equality of two points on the rectangle boundary path
forces equality of the parameters, except for the endpoint identification `0 ~ 1`. -/
lemma axis_parallel_rectangle_boundary_path_simple_eq_or_endpoints
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {s t : I}
    (hst : axisParallelRectangleBoundaryPath z w s = axisParallelRectangleBoundaryPath z w t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  let br : ℂ := Complex.mk w.re z.im
  let tl : ℂ := Complex.mk z.re w.im
  have hsFib := axis_parallel_rectangle_boundary_path_corner_fibers z w hRe hIm (t := s)
  have htFib := axis_parallel_rectangle_boundary_path_corner_fibers z w hRe hIm (t := t)
  have hs_z : axisParallelRectangleBoundaryPath z w s = z ↔ s = (0 : I) ∨ s = (1 : I) := hsFib.1
  have ht_z : axisParallelRectangleBoundaryPath z w t = z ↔ t = (0 : I) ∨ t = (1 : I) := htFib.1
  have hs_br :
      axisParallelRectangleBoundaryPath z w s = br ↔
        s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using hsFib.2.1
  have ht_br :
      axisParallelRectangleBoundaryPath z w t = br ↔
        t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using htFib.2.1
  have hs_w : axisParallelRectangleBoundaryPath z w s = w ↔
      s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := hsFib.2.2.1
  have ht_w : axisParallelRectangleBoundaryPath z w t = w ↔
      t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := htFib.2.2.1
  have hs_tl :
      axisParallelRectangleBoundaryPath z w s = tl ↔
        s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using hsFib.2.2.2
  have ht_tl :
      axisParallelRectangleBoundaryPath z w t = tl ↔
        t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using htFib.2.2.2
  -- Separate the boundary parameters into endpoint, corner, and open-side cases.
  rcases axis_parallel_rectangle_boundary_parameter_cases s with
    hs0 | hsbottom | hshalf | hsright | hs34 | hstop | hs78 | hsleft | hs1
  · have hs' : s = (0 : I) := Subtype.ext hs0
    have htz : axisParallelRectangleBoundaryPath z w t = z := by
      have hsz : axisParallelRectangleBoundaryPath z w s = z := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_zero z w
      calc
        axisParallelRectangleBoundaryPath z w t =
            axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = z := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inl <| by simpa [hs', ht0]
    · exact Or.inr <| Or.inl <| by simp [hs', ht1]
  · have hscoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe hsbottom
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        simpa [hsEq] using hscoord.2
      linarith [hre.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        simpa [br, hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have him : w.im = z.im := by simpa [hsEq] using hscoord.1
      exact (hIm.ne him.symm).elim
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have him : w.im = z.im := by simpa [tl, hsEq] using hscoord.1
      exact (hIm.ne him.symm).elim
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inl ⟨hsbottom, htbottom⟩) hst
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = w.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have him : z.im = w.im := by
        calc
          z.im = (axisParallelRectangleBoundaryPath z w s).im := by simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w t).im := by
            simpa using congrArg Complex.im hst
          _ = w.im := htcoord.1
      exact (hIm.ne him).elim
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = z.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.1]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hshalf
    have hstbr : axisParallelRectangleBoundaryPath z w t = br := by
      have hsbr : axisParallelRectangleBoundaryPath z w s = br := by
        simpa [br, hs'] using axis_parallel_rectangle_boundary_path_half z w
      calc
        axisParallelRectangleBoundaryPath z w t =
            axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = br := hsbr
    exact Or.inl <| by simpa [hs', ht_br.mp hstbr]
  · have hscoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm hsright
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have hre : z.re = w.re := by simpa [hsEq] using hscoord.1
      exact (hRe.ne hre).elim
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have him : z.im ∈ Set.Ioo z.im w.im := by
        simpa [br, hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have him : w.im ∈ Set.Ioo z.im w.im := by
        simpa [hsEq] using hscoord.2
      linarith [him.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have hre : z.re = w.re := by simpa [tl, hsEq] using hscoord.1
      exact (hRe.ne hre).elim
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = w.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inl ⟨hsright, htright⟩) hst
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = w.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re = w.re := by
        calc
          z.re = (axisParallelRectangleBoundaryPath z w t).re := by simpa using htcoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w s).re := by
            simpa using congrArg Complex.re hst.symm
          _ = w.re := hscoord.1
      exact (hRe.ne hre).elim
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext hs34
    have hstw : axisParallelRectangleBoundaryPath z w t = w := by
      have hsw : axisParallelRectangleBoundaryPath z w s = w := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      calc
        axisParallelRectangleBoundaryPath z w t =
            axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = w := hsw
    exact Or.inl <| by simpa [hs', ht_w.mp hstw]
  · have hscoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe hstop
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have him : z.im = w.im := by simpa [hsEq] using hscoord.1
      exact (hIm.ne him).elim
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have him : z.im = w.im := by simpa [br, hsEq] using hscoord.1
      exact (hIm.ne him).elim
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        simpa [hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        simpa [tl, hsEq] using hscoord.2
      linarith [hre.1]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have him : z.im = w.im := by
        calc
          z.im = (axisParallelRectangleBoundaryPath z w t).im := by simpa using htcoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w s).im := by
            simpa using congrArg Complex.im hst.symm
          _ = w.im := hscoord.1
      exact (hIm.ne him).elim
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := htcoord.1
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = w.re := htre
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inr <| Or.inl ⟨hstop, httop⟩) hst
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = z.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.1]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext hs78
    have hsttl : axisParallelRectangleBoundaryPath z w t = tl := by
      have hstl : axisParallelRectangleBoundaryPath z w s = tl := by
        simpa [tl, hs'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      calc
        axisParallelRectangleBoundaryPath z w t =
            axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = tl := hstl
    exact Or.inl <| by simpa [hs', ht_tl.mp hsttl]
  · have hscoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm hsleft
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have him : z.im ∈ Set.Ioo z.im w.im := by
        simpa [hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have hre : w.re = z.re := by simpa [br, hsEq] using hscoord.1
      exact (hRe.ne hre.symm).elim
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have hre : w.re = z.re := by simpa [hsEq] using hscoord.1
      exact (hRe.ne hre.symm).elim
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have him : w.im ∈ Set.Ioo z.im w.im := by
        simpa [tl, hsEq] using hscoord.2
      linarith [him.2]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = z.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.1]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : z.re = w.re := by
        calc
          z.re = (axisParallelRectangleBoundaryPath z w s).re := by simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w t).re := by
            simpa using congrArg Complex.re hst
          _ = w.re := htcoord.1
      exact (hRe.ne hre).elim
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have him : w.im ∈ Set.Ioo z.im w.im := by
        have htim : (axisParallelRectangleBoundaryPath z w t).im = w.im := htcoord.1
        have hsim : (axisParallelRectangleBoundaryPath z w s).im = w.im := by
          calc
            (axisParallelRectangleBoundaryPath z w s).im =
                (axisParallelRectangleBoundaryPath z w t).im := by
                  simpa using congrArg Complex.im hst
            _ = w.im := htim
        simpa [hsim] using hscoord.2
      linarith [him.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inr <| Or.inr ⟨hsleft, htleft⟩) hst
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (1 : I) := Subtype.ext hs1
    have htz : axisParallelRectangleBoundaryPath z w t = z := by
      have hsz : axisParallelRectangleBoundaryPath z w s = z := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_one z w
      calc
        axisParallelRectangleBoundaryPath z w t =
            axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = z := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inr <| Or.inr <| by simp [hs', ht0]
    · exact Or.inl <| by simpa [hs', ht1]

/-- Helper for Example II.1-extra-21: the lower-right corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_half
    (z w : ℂ) (hRe : z.re < w.re) (_hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  -- Compare the one-sided tangent coming from the bottom edge with the one from the right edge.
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have hleftMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have hrightMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  let bottom : ℝ → Plane := fun t ↦ (AffineMap.lineMap z.re w.re (2 * t), z.im)
  let right : ℝ → Plane := fun t ↦ (w.re, AffineMap.lineMap z.im w.im (4 * t - 2))
  have hbottomEq :
      Set.EqOn γ bottom (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap z (Complex.mk w.re z.im) (2 * t) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_bottom_side z w ht
    ext
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_right_side z w ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hbottomDeriv :
      HasDerivWithinAt bottom ((2 * (w.re - z.re), 0) : Plane)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.re w.re (2 * t))
          (2 * (w.re - z.re)) (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.re) (b := w.re) (x := 2 * (1 / 2 : ℝ))).comp
          (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2) using 1
      ring
    simpa [bottom] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (1 / 2 : ℝ) z.im).hasDerivWithinAt
  have hrightDeriv :
      HasDerivWithinAt right (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.im w.im (4 * t - 2))
          (4 * (w.im - z.im)) (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.im) (b := w.im) (x := 4 * (1 / 2 : ℝ) - 2)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 4).sub_const 2) using 1
      ring
    simpa [right] using
      (hasDerivAt_const (1 / 2 : ℝ) w.re).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have hbottomγ :
      HasDerivWithinAt γ ((2 * (w.re - z.re), 0) : Plane)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    exact hbottomDeriv.congr_of_mem hbottomEq (by constructor <;> norm_num)
  have hrightγ :
      HasDerivWithinAt γ (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    exact hrightDeriv.congr_of_mem hrightEq (by constructor <;> norm_num)
  have hleftUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (0 : ℝ) (1 / 2 : ℝ)) ?_ ?_
    · refine ⟨1 / 4, ?_⟩
      simpa [interior_Icc] using
        (show (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have hrightUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) ?_ ?_
    · refine ⟨5 / 8, ?_⟩
      simpa [interior_Icc] using
        (show (5 / 8 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : ((2 * (w.re - z.re), 0) : Plane) = (((0 : ℝ), 4 * (w.im - z.im)) : Plane) := by
    calc
      ((2 * (w.re - z.re), 0) : Plane)
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact hbottomγ.derivWithin hleftUD
      _ = d := hleftMain.derivWithin hleftUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact hrightMain.derivWithin hrightUD
      _ = (((0 : ℝ), 4 * (w.im - z.im)) : Plane) := hrightγ.derivWithin hrightUD
  have hre : 2 * (w.re - z.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 4 * (w.im - z.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith

/-- Helper for Example II.1-extra-21: the upper-right corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_three_quarters
    (z w : ℂ) (hRe : z.re < w.re) (_hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ)
  -- Compare the incoming right-edge tangent with the outgoing top-edge tangent.
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have hrightMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have htopMain : HasDerivWithinAt γ d (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  let right : ℝ → Plane := fun t ↦ (w.re, AffineMap.lineMap z.im w.im (4 * t - 2))
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap w.re z.re (8 * t - 6), w.im)
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_right_side z w ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_top_side z w ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightDeriv :
      HasDerivWithinAt right (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.im w.im (4 * t - 2))
          (4 * (w.im - z.im)) (3 / 4 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.im) (b := w.im) (x := 4 * (3 / 4 : ℝ) - 2)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 4).sub_const 2) using 1
      ring
    simpa [right] using
      (hasDerivAt_const (3 / 4 : ℝ) w.re).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have htopDeriv :
      HasDerivWithinAt top ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.re z.re (8 * t - 6))
          (8 * (z.re - w.re)) (3 / 4 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (AffineMap.hasDerivAt_lineMap (a := w.re) (b := z.re) (x := 8 * (3 / 4 : ℝ) - 6)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 8).sub_const 6)
    simpa [top] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (3 / 4 : ℝ) w.im).hasDerivWithinAt
  have hrightγ :
      HasDerivWithinAt γ (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    exact hrightDeriv.congr_of_mem hrightEq (by constructor <;> norm_num)
  have htopγ :
      HasDerivWithinAt γ ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    exact htopDeriv.congr_of_mem htopEq (by constructor <;> norm_num)
  have hrightUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) ?_ ?_
    · refine ⟨5 / 8, ?_⟩
      simpa [interior_Icc] using
        (show (5 / 8 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have htopUD :
      UniqueDiffWithinAt ℝ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) ?_ ?_
    · refine ⟨13 / 16, ?_⟩
      simpa [interior_Icc] using
        (show (13 / 16 : ℝ) ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : (((0 : ℝ), 4 * (w.im - z.im)) : Plane) = ((8 * (z.re - w.re), 0) : Plane) := by
    calc
      (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
          = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
            symm
            exact hrightγ.derivWithin hrightUD
      _ = d := hrightMain.derivWithin hrightUD
      _ = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
            symm
            exact htopMain.derivWithin htopUD
      _ = ((8 * (z.re - w.re), 0) : Plane) := htopγ.derivWithin htopUD
  have hre : 8 * (z.re - w.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 4 * (w.im - z.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith

/-- Helper for Example II.1-extra-21: the upper-left corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_seven_eighths
    (z w : ℂ) (hRe : z.re < w.re) (_hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ)
  -- Compare the incoming top-edge tangent with the outgoing left-edge tangent.
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have htopMain : HasDerivWithinAt γ d (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hleftMain : HasDerivWithinAt γ d (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap w.re z.re (8 * t - 6), w.im)
  let left : ℝ → Plane := fun t ↦ (z.re, AffineMap.lineMap w.im z.im (8 * t - 7))
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_top_side z w ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hleftEq :
      Set.EqOn γ left (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk z.re w.im) z (8 * t - 7) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_left_side z w ht
    ext
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopDeriv :
      HasDerivWithinAt top ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.re z.re (8 * t - 6))
          (8 * (z.re - w.re)) (7 / 8 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := w.re) (b := z.re) (x := 8 * (7 / 8 : ℝ) - 6)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 6) using 1
      ring
    simpa [top] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (7 / 8 : ℝ) w.im).hasDerivWithinAt
  have hleftDeriv :
      HasDerivWithinAt left (((0 : ℝ), 8 * (z.im - w.im)) : Plane)
        (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.im z.im (8 * t - 7))
          (8 * (z.im - w.im)) (7 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (AffineMap.hasDerivAt_lineMap (a := w.im) (b := z.im) (x := 8 * (7 / 8 : ℝ) - 7)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 7)
    simpa [left] using
      (hasDerivAt_const (7 / 8 : ℝ) z.re).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have htopγ :
      HasDerivWithinAt γ ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    exact htopDeriv.congr_of_mem htopEq (by constructor <;> norm_num)
  have hleftγ :
      HasDerivWithinAt γ (((0 : ℝ), 8 * (z.im - w.im)) : Plane)
        (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    exact hleftDeriv.congr_of_mem hleftEq (by constructor <;> norm_num)
  have htopUD :
      UniqueDiffWithinAt ℝ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) ?_ ?_
    · refine ⟨13 / 16, ?_⟩
      simpa [interior_Icc] using
        (show (13 / 16 : ℝ) ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have hleftUD :
      UniqueDiffWithinAt ℝ (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (7 / 8 : ℝ) (1 : ℝ)) ?_ ?_
    · refine ⟨15 / 16, ?_⟩
      simpa [interior_Icc] using
        (show (15 / 16 : ℝ) ∈ Set.Ioo (7 / 8 : ℝ) (1 : ℝ) by constructor <;> norm_num)
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : ((8 * (z.re - w.re), 0) : Plane) = (((0 : ℝ), 8 * (z.im - w.im)) : Plane) := by
    calc
      ((8 * (z.re - w.re), 0) : Plane)
          = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
            symm
            exact htopγ.derivWithin htopUD
      _ = d := htopMain.derivWithin htopUD
      _ = derivWithin γ (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
            symm
            exact hleftMain.derivWithin hleftUD
      _ = (((0 : ℝ), 8 * (z.im - w.im)) : Plane) := hleftγ.derivWithin hleftUD
  have hre : 8 * (z.re - w.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 8 * (z.im - w.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith

/-- Helper for Example II.1-extra-21: a regular interior parameter of the rectangle boundary path
must lie on exactly one of the four open side intervals, because the three intermediate corner
parameters are not differentiable. -/
lemma axis_parallel_rectangle_boundary_regular_parameter_mem_side_interval
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t₀ ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t₀ ∈ Set.Ioo (7 / 8) (1 : ℝ) := by
  let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  -- The parameter split leaves only the four open side intervals after excluding the corners.
  rcases axis_parallel_rectangle_boundary_parameter_cases t with
    ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
  · exact (ht₀.1.ne' ht0).elim
  · exact Or.inl htbottom
  · exact
      False.elim <|
        (axis_parallel_rectangle_boundary_not_differentiable_at_half z w hRe hIm)
          (by
            have ht0 : t₀ = 1 / 2 := by simpa [t] using hthalf
            simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inl htright
  · exact
      False.elim <|
        (axis_parallel_rectangle_boundary_not_differentiable_at_three_quarters z w hRe hIm)
          (by
            have ht0 : t₀ = 3 / 4 := by simpa [t] using ht34
            simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl httop
  · exact
      False.elim <|
        (axis_parallel_rectangle_boundary_not_differentiable_at_seven_eighths z w hRe hIm)
          (by
            have ht0 : t₀ = 7 / 8 := by simpa [t] using ht78
            simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htleft
  · exact (ht₀.2.ne ht1).elim

/-- Helper for Cartan section05 0034_Example_II_1_extra_21: every regular non-corner parameter on
the rectangle boundary lies on one affine side, so the corresponding explicit straightening chart
applies. -/
lemma axis_parallel_rectangle_boundary_path_exists_boundary_straightening
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (_hderiv :
      derivWithin ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the corner-exclusion/classification step is now finished, so only the
  -- explicit strip-chart construction for the four affine side models remains.
  rcases
      axis_parallel_rectangle_boundary_regular_parameter_mem_side_interval
        z w hRe hIm ht₀ hdiff with
    htbottom | htright | httop | htleft
  · -- On the bottom branch, the upward transverse direction points into the rectangle.
    exact axis_parallel_rectangle_boundary_bottom_branch_exists_boundary_chart z w hRe hIm htbottom
  · -- On the right branch, the inward transverse direction points to decreasing real part.
    exact axis_parallel_rectangle_boundary_right_branch_exists_boundary_chart z w hRe hIm htright
  · -- On the top branch, the inward transverse direction points to decreasing imaginary part.
    exact axis_parallel_rectangle_boundary_top_branch_exists_boundary_chart z w hRe hIm httop
  · -- On the left branch, the inward transverse direction points to increasing real part.
    exact axis_parallel_rectangle_boundary_left_branch_exists_boundary_chart z w hRe hIm htleft

/-- Cartan section05 0034_Example_II_1_extra_21 (Example II.1-extra-21): if `z` is the
lower-left corner and `w` the upper-right corner of a nondegenerate axis-parallel rectangle, then
the canonical boundary path gives a singleton family that is an oriented boundary of
`Complex.Rectangle z w`. -/
theorem axisParallelRectangleBoundary_isOrientedBoundaryOf (z w : ℂ)
    (hRe : z.re < w.re) (hIm : z.im < w.im) :
    IsOrientedBoundaryOf (Complex.Rectangle z w)
      (fun _ : Unit ↦ (axisParallelRectangleBoundaryPath z w).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (axisParallelRectangleBoundaryPath z w).toClosedPath
  change IsOrientedBoundaryOf (Complex.Rectangle z w) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The rectangle is the product of two compact real intervals.
    simpa [Complex.Rectangle] using isCompact_uIcc.reProdIm isCompact_uIcc
  · rintro ⟨⟩
    -- The singleton loop inherits the known piecewise differentiability of the rectangle boundary.
    simpa [Γ] using
      axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable z w
  · rintro ⟨⟩ s t hst
    -- Delegate the loop simplicity to the explicit side-by-side coordinate analysis.
    exact axis_parallel_rectangle_boundary_path_simple_eq_or_endpoints z w hRe hIm hst
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ) : C(I, ℂ))) =
          Set.range (axisParallelRectangleBoundaryPath z w) := by
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
    -- Rewrite the singleton union back to the boundary-path image, then invoke the frontier
    -- theorem.
    simpa [ClosedPath.range_toPath] using
      hboundary.trans (axisParallelRectangleBoundaryPath_range_eq_frontier z w)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- Delegate the regular-point chart to the side-local affine straightening helper.
    exact axis_parallel_rectangle_boundary_path_exists_boundary_straightening
      z w hRe hIm ht₀ hdiff hderiv
