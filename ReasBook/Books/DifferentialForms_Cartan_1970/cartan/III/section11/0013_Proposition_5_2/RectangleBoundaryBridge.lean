import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0034_Example_II_1_extra_21».BoundaryStraightening

open scoped unitInterval

noncomputable section

/-- Helper for Proposition 5.2: equality of two points on the unit-rectangle boundary path
forces equality of the parameters, except for the endpoint identification `0 ~ 1`. -/
lemma unitRectangleBoundaryPath_simple_eq_or_endpoints
    {s t : I}
    (hst :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s =
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  let br : ℂ := 1
  let tl : ℂ := Complex.I
  have hsFib :=
    axis_parallel_rectangle_boundary_path_corner_fibers
      0 (1 + Complex.I) (by norm_num) (by norm_num) (t := s)
  have htFib :=
    axis_parallel_rectangle_boundary_path_corner_fibers
      0 (1 + Complex.I) (by norm_num) (by norm_num) (t := t)
  have hs_z :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = 0 ↔
        s = (0 : I) ∨ s = (1 : I) := hsFib.1
  have ht_z :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 ↔
        t = (0 : I) ∨ t = (1 : I) := htFib.1
  have hs_br :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = br ↔
        s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using hsFib.2.1
  have ht_br :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br ↔
        t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using htFib.2.1
  have hs_w :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = 1 + Complex.I ↔
        s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := hsFib.2.2.1
  have ht_w :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I ↔
        t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := htFib.2.2.1
  have hs_tl :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = tl ↔
        s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using hsFib.2.2.2
  have ht_tl :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl ↔
        t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using htFib.2.2.2
  -- Separate the boundary parameters into endpoint, corner, and open-side cases.
  rcases axis_parallel_rectangle_boundary_parameter_cases s with
    hs0 | hsbottom | hshalf | hsright | hs34 | hstop | hs78 | hsleft | hs1
  · have hs' : s = (0 : I) := Subtype.ext hs0
    have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
      have hsz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = 0 := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_zero 0 (1 + Complex.I)
      calc
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t =
            axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s := hst.symm
        _ = 0 := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inl <| by simpa [hs', ht0]
    · exact Or.inr <| Or.inl <| by simp [hs', ht1]
  · have hscoord :=
      axis_parallel_rectangle_boundary_path_bottom_coordinates 0 (1 + Complex.I) (by norm_num)
        hsbottom
    have hs_ne_z : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 0 := by
      intro hsEq
      have hre : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [hsEq] using hscoord.2
      linarith [hre.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ br := by
      intro hsEq
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [br, hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_w : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 1 + Complex.I := by
      intro hsEq
      have him : 1 = 0 := by simpa [hsEq] using hscoord.1
      norm_num at him
    have hs_ne_tl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ tl := by
      intro hsEq
      have him : 1 = 0 := by simpa [tl, hsEq] using hscoord.1
      norm_num at him
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective 0 (1 + Complex.I)
          (by norm_num) (by norm_num) (Or.inl ⟨hsbottom, htbottom⟩) hst
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half 0 (1 + Complex.I)
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_right_coordinates 0 (1 + Complex.I) (by norm_num)
          htright
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have hsre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re := by
                  simpa using congrArg Complex.re hst
            _ = (1 : ℝ) := by simpa using htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I := by
        simpa [ht'] using
          axis_parallel_rectangle_boundary_path_three_quarters 0 (1 + Complex.I)
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_top_coordinates 0 (1 + Complex.I) (by norm_num)
          httop
      have him : (0 : ℝ) = 1 := by
        calc
          0 = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).im := by
                simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im := by
                simpa using congrArg Complex.im hst
          _ = (1 : ℝ) := by simpa using htcoord.1
      norm_num at him
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl := by
        simpa [tl, ht'] using
          axis_parallel_rectangle_boundary_path_seven_eighths 0 (1 + Complex.I)
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_left_coordinates 0 (1 + Complex.I) (by norm_num)
          htleft
      have hre : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        have hsre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re = 0 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re := by
                  simpa using congrArg Complex.re hst
            _ = 0 := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.1]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hshalf
    have hstbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br := by
      have hsbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = br := by
        simpa [br, hs'] using axis_parallel_rectangle_boundary_path_half 0 (1 + Complex.I)
      calc
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t =
            axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s := hst.symm
        _ = br := hsbr
    exact Or.inl <| by simpa [hs', ht_br.mp hstbr]
  · have hscoord :=
      axis_parallel_rectangle_boundary_path_right_coordinates 0 (1 + Complex.I) (by norm_num)
        hsright
    have hs_ne_z : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 0 := by
      intro hsEq
      have hre : (0 : ℝ) = 1 := by simpa [hsEq] using hscoord.1
      norm_num at hre
    have hs_ne_br : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ br := by
      intro hsEq
      have him : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [br, hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_w : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 1 + Complex.I := by
      intro hsEq
      have him : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [hsEq] using hscoord.2
      linarith [him.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ tl := by
      intro hsEq
      have hre : (0 : ℝ) = 1 := by simpa [tl, hsEq] using hscoord.1
      norm_num at hre
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_bottom_coordinates 0 (1 + Complex.I) (by norm_num)
          htbottom
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = (1 : ℝ) := by simpa using hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half 0 (1 + Complex.I)
      exact (hs_ne_br (hst.trans htbr)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective 0 (1 + Complex.I)
          (by norm_num) (by norm_num) (Or.inr <| Or.inl ⟨hsright, htright⟩) hst
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I := by
        simpa [ht'] using
          axis_parallel_rectangle_boundary_path_three_quarters 0 (1 + Complex.I)
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_top_coordinates 0 (1 + Complex.I) (by norm_num)
          httop
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = (1 : ℝ) := by simpa using hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl := by
        simpa [tl, ht'] using
          axis_parallel_rectangle_boundary_path_seven_eighths 0 (1 + Complex.I)
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_left_coordinates 0 (1 + Complex.I) (by norm_num)
          htleft
      have hre : (0 : ℝ) = 1 := by
        calc
          0 = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re := by
                simpa using htcoord.1.symm
          _ = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re := by
                simpa using congrArg Complex.re hst.symm
          _ = (1 : ℝ) := by simpa using hscoord.1
      norm_num at hre
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext hs34
    have hstw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I := by
      have hsw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = 1 + Complex.I := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_three_quarters 0 (1 + Complex.I)
      calc
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t =
            axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s := hst.symm
        _ = 1 + Complex.I := hsw
    exact Or.inl <| by simpa [hs', ht_w.mp hstw]
  · have hscoord :=
      axis_parallel_rectangle_boundary_path_top_coordinates 0 (1 + Complex.I) (by norm_num)
        hstop
    have hs_ne_z : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 0 := by
      intro hsEq
      have him : (0 : ℝ) = 1 := by simpa [hsEq] using hscoord.1
      norm_num at him
    have hs_ne_br : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ br := by
      intro hsEq
      have him : (0 : ℝ) = 1 := by simpa [br, hsEq] using hscoord.1
      norm_num at him
    have hs_ne_w : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 1 + Complex.I := by
      intro hsEq
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ tl := by
      intro hsEq
      have hre : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [tl, hsEq] using hscoord.2
      linarith [hre.1]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_bottom_coordinates 0 (1 + Complex.I) (by norm_num)
          htbottom
      have him : (1 : ℝ) = 0 := by
        calc
          1 = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).im := by
                simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im := by
                simpa using congrArg Complex.im hst
          _ = (0 : ℝ) := by simpa using htcoord.1
      norm_num at him
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half 0 (1 + Complex.I)
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_right_coordinates 0 (1 + Complex.I) (by norm_num)
          htright
      have hre : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re = 1 := by
          simpa using htcoord.1
        have hsre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re := by
                  simpa using congrArg Complex.re hst
            _ = 1 := htre
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I := by
        simpa [ht'] using
          axis_parallel_rectangle_boundary_path_three_quarters 0 (1 + Complex.I)
      exact (hs_ne_w (hst.trans htw)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective 0 (1 + Complex.I)
          (by norm_num) (by norm_num) (Or.inr <| Or.inr <| Or.inl ⟨hstop, httop⟩) hst
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl := by
        simpa [tl, ht'] using
          axis_parallel_rectangle_boundary_path_seven_eighths 0 (1 + Complex.I)
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_left_coordinates 0 (1 + Complex.I) (by norm_num)
          htleft
      have him : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htim : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).im := by
                  simpa using congrArg Complex.im hst.symm
            _ = (1 : ℝ) := by simpa using hscoord.1
        simpa [htim] using htcoord.2
      linarith [him.2]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext hs78
    have hsttl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl := by
      have hstl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = tl := by
        simpa [tl, hs'] using axis_parallel_rectangle_boundary_path_seven_eighths 0 (1 + Complex.I)
      calc
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t =
            axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s := hst.symm
        _ = tl := hstl
    exact Or.inl <| by simpa [hs', ht_tl.mp hsttl]
  · have hscoord :=
      axis_parallel_rectangle_boundary_path_left_coordinates 0 (1 + Complex.I) (by norm_num)
        hsleft
    have hs_ne_z : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 0 := by
      intro hsEq
      have him : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ br := by
      intro hsEq
      have hre : (1 : ℝ) = 0 := by simpa [br, hsEq] using hscoord.1
      norm_num at hre
    have hs_ne_w : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ 1 + Complex.I := by
      intro hsEq
      have hre : (1 : ℝ) = 0 := by simpa [hsEq] using hscoord.1
      norm_num at hre
    have hs_ne_tl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s ≠ tl := by
      intro hsEq
      have him : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [tl, hsEq] using hscoord.2
      linarith [him.2]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_bottom_coordinates 0 (1 + Complex.I) (by norm_num)
          htbottom
      have hre : 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htre : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re = 0 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = 0 := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.1]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half 0 (1 + Complex.I)
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_right_coordinates 0 (1 + Complex.I) (by norm_num)
          htright
      have hre : (0 : ℝ) = 1 := by
        calc
          0 = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).re := by
                simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).re := by
                simpa using congrArg Complex.re hst
          _ = (1 : ℝ) := by simpa using htcoord.1
      norm_num at hre
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 1 + Complex.I := by
        simpa [ht'] using
          axis_parallel_rectangle_boundary_path_three_quarters 0 (1 + Complex.I)
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord :=
        axis_parallel_rectangle_boundary_path_top_coordinates 0 (1 + Complex.I) (by norm_num)
          httop
      have him : 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        have htim : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im = 1 := by
          simpa using htcoord.1
        have hsim : (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).im = 1 := by
          calc
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s).im =
                (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t).im := by
                  simpa using congrArg Complex.im hst
            _ = 1 := htim
        simpa [hsim] using hscoord.2
      linarith [him.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = tl := by
        simpa [tl, ht'] using
          axis_parallel_rectangle_boundary_path_seven_eighths 0 (1 + Complex.I)
      exact (hs_ne_tl (hst.trans httl)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective 0 (1 + Complex.I)
          (by norm_num) (by norm_num) (Or.inr <| Or.inr <| Or.inr ⟨hsleft, htleft⟩) hst
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one 0 (1 + Complex.I)
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (1 : I) := Subtype.ext hs1
    have htz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t = 0 := by
      have hsz : axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s = 0 := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_one 0 (1 + Complex.I)
      calc
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t =
            axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s := hst.symm
        _ = 0 := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inr <| Or.inr <| by simp [hs', ht0]
    · exact Or.inl <| by simpa [hs', ht1]

/-- Helper for Proposition 5.2: the lower-right unit-rectangle corner is a genuine corner of the
boundary path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
private lemma unitRectangleBoundary_not_differentiable_at_half :
    ¬ DifferentiableWithinAt ℝ
      ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
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
  let bottom : ℝ → Plane := fun t ↦ (AffineMap.lineMap (0 : ℝ) 1 (2 * t), 0)
  let right : ℝ → Plane := fun t ↦ (1, AffineMap.lineMap (0 : ℝ) 1 (4 * t - 2))
  have hbottomEq :
      Set.EqOn γ bottom (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap 0 1 (2 * t) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_bottom_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap 1 (1 + Complex.I) (4 * t - 2) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_right_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hbottomDeriv :
      HasDerivWithinAt bottom ((2 : ℝ), 0) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap (0 : ℝ) 1 (2 * t)) 2 (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := (0 : ℝ)) (b := 1) (x := 2 * (1 / 2 : ℝ))).comp
          (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2) using 1
      ring
    simpa [bottom] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (1 / 2 : ℝ) (0 : ℝ)).hasDerivWithinAt
  have hrightDeriv :
      HasDerivWithinAt right ((0 : ℝ), 4) (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap (0 : ℝ) 1 (4 * t - 2)) 4 (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := (0 : ℝ)) (b := 1) (x := 4 * (1 / 2 : ℝ) - 2)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 4).sub_const 2) using 1
      ring
    simpa [right] using
      (hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have hbottomγ :
      HasDerivWithinAt γ ((2 : ℝ), 0) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    exact hbottomDeriv.congr_of_mem hbottomEq (by constructor <;> norm_num)
  have hrightγ :
      HasDerivWithinAt γ ((0 : ℝ), 4) (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
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
  have hcompare : ((2 : ℝ), (0 : ℝ)) = ((0 : ℝ), (4 : ℝ)) := by
    calc
      ((2 : ℝ), 0) = derivWithin γ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
        symm
        exact hbottomγ.derivWithin hleftUD
      _ = d := hleftMain.derivWithin hleftUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
        symm
        exact hrightMain.derivWithin hrightUD
      _ = ((0 : ℝ), 4) := hrightγ.derivWithin hrightUD
  have hre : (2 : ℝ) = 0 := by simpa using congrArg Prod.fst hcompare
  norm_num at hre

/-- Helper for Proposition 5.2: the upper-right unit-rectangle corner is a genuine corner of the
boundary path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
private lemma unitRectangleBoundary_not_differentiable_at_three_quarters :
    ¬ DifferentiableWithinAt ℝ
      ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
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
  let right : ℝ → Plane := fun t ↦ (1, AffineMap.lineMap (0 : ℝ) 1 (4 * t - 2))
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap 1 (0 : ℝ) (8 * t - 6), 1)
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap 1 (1 + Complex.I) (4 * t - 2) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_right_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap (1 + Complex.I) Complex.I (8 * t - 6) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_top_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightDeriv :
      HasDerivWithinAt right ((0 : ℝ), 4) (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap (0 : ℝ) 1 (4 * t - 2)) 4 (3 / 4 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := (0 : ℝ)) (b := 1) (x := 4 * (3 / 4 : ℝ) - 2)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 4).sub_const 2) using 1
      ring
    simpa [right] using
      (hasDerivAt_const (3 / 4 : ℝ) (1 : ℝ)).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have htopDeriv :
      HasDerivWithinAt top ((-8 : ℝ), 0) (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap 1 (0 : ℝ) (8 * t - 6)) (-8) (3 / 4 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (AffineMap.hasDerivAt_lineMap (a := (1 : ℝ)) (b := 0) (x := 8 * (3 / 4 : ℝ) - 6)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 8).sub_const 6)
    simpa [top] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (3 / 4 : ℝ) (1 : ℝ)).hasDerivWithinAt
  have hrightγ :
      HasDerivWithinAt γ ((0 : ℝ), 4) (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    exact hrightDeriv.congr_of_mem hrightEq (by constructor <;> norm_num)
  have htopγ :
      HasDerivWithinAt γ ((-8 : ℝ), 0) (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
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
  have hcompare : ((0 : ℝ), (4 : ℝ)) = ((-8 : ℝ), (0 : ℝ)) := by
    calc
      ((0 : ℝ), 4) = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
        symm
        exact hrightγ.derivWithin hrightUD
      _ = d := hrightMain.derivWithin hrightUD
      _ = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
        symm
        exact htopMain.derivWithin htopUD
      _ = ((-8 : ℝ), 0) := htopγ.derivWithin htopUD
  have him : (4 : ℝ) = 0 := by simpa using congrArg Prod.snd hcompare
  norm_num at him

/-- Helper for Proposition 5.2: the upper-left unit-rectangle corner is a genuine corner of the
boundary path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
private lemma unitRectangleBoundary_not_differentiable_at_seven_eighths :
    ¬ DifferentiableWithinAt ℝ
      ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ) := by
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
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
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap 1 (0 : ℝ) (8 * t - 6), 1)
  let left : ℝ → Plane := fun t ↦ (0, AffineMap.lineMap 1 (0 : ℝ) (8 * t - 7))
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap (1 + Complex.I) Complex.I (8 * t - 6) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_top_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hleftEq :
      Set.EqOn γ left (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.toPath.extend t =
          AffineMap.lineMap Complex.I 0 (8 * t - 7) := by
      simpa [Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_eqOn_left_side 0 (1 + Complex.I) ht
    ext
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopDeriv :
      HasDerivWithinAt top ((-8 : ℝ), 0) (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap 1 (0 : ℝ) (8 * t - 6)) (-8) (7 / 8 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := (1 : ℝ)) (b := 0) (x := 8 * (7 / 8 : ℝ) - 6)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 6) using 1
      ring
    simpa [top] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (7 / 8 : ℝ) (1 : ℝ)).hasDerivWithinAt
  have hleftDeriv :
      HasDerivWithinAt left ((0 : ℝ), -8) (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap 1 (0 : ℝ) (8 * t - 7)) (-8) (7 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (AffineMap.hasDerivAt_lineMap (a := (1 : ℝ)) (b := 0) (x := 8 * (7 / 8 : ℝ) - 7)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 7)
    simpa [left] using
      (hasDerivAt_const (7 / 8 : ℝ) (0 : ℝ)).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have htopγ :
      HasDerivWithinAt γ ((-8 : ℝ), 0) (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    exact htopDeriv.congr_of_mem htopEq (by constructor <;> norm_num)
  have hleftγ :
      HasDerivWithinAt γ ((0 : ℝ), -8) (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
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
  have hcompare : ((-8 : ℝ), (0 : ℝ)) = ((0 : ℝ), (-8 : ℝ)) := by
    calc
      ((-8 : ℝ), 0) = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
        symm
        exact htopγ.derivWithin htopUD
      _ = d := htopMain.derivWithin htopUD
      _ = derivWithin γ (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
        symm
        exact hleftMain.derivWithin hleftUD
      _ = ((0 : ℝ), -8) := hleftγ.derivWithin hleftUD
  have hre : (-8 : ℝ) = 0 := by simpa using congrArg Prod.fst hcompare
  norm_num at hre

/-- Helper for Proposition 5.2: every regular parameter on the unit-rectangle boundary lies on
one of the four open affine side intervals. -/
lemma unitRectangle_regularParameterCases
    {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t₀ ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t₀ ∈ Set.Ioo (7 / 8) (1 : ℝ) := by
  let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  -- The parameter split leaves only the four open side intervals after excluding the three
  -- nondifferentiable corner parameters.
  rcases axis_parallel_rectangle_boundary_parameter_cases t with
    ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
  · exact (ht₀.1.ne' ht0).elim
  · exact Or.inl htbottom
  · exact
      False.elim <|
        unitRectangleBoundary_not_differentiable_at_half
          (by
            have htEq : t₀ = 1 / 2 := by simpa [t] using hthalf
            simpa [htEq] using hdiff)
  · exact Or.inr <| Or.inl htright
  · exact
      False.elim <|
        unitRectangleBoundary_not_differentiable_at_three_quarters
          (by
            have htEq : t₀ = 3 / 4 := by simpa [t] using ht34
            simpa [htEq] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl httop
  · exact
      False.elim <|
        unitRectangleBoundary_not_differentiable_at_seven_eighths
          (by
            have htEq : t₀ = 7 / 8 := by simpa [t] using ht78
            simpa [htEq] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htleft
  · exact (ht₀.2.ne ht1).elim
