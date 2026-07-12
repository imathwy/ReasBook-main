import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».BoundaryTraceContinuity

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Exercise 8: a point with coordinates on the closed rectangle and lying on one of
its four sides belongs to the frontier of the open rectangle. -/
lemma exercise8_mem_frontier_rectangle_of_coords {k : Exercise8Modulus} {u : ℂ}
    (hre :
      u.re ∈ Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k))
    (him : u.im ∈ Icc (0 : ℝ) (exercise8_complete_imaginary_period k))
    (hboundary :
      u.re = -exercise8_complete_real_period k ∨
        u.re = exercise8_complete_real_period k ∨
          u.im = 0 ∨ u.im = exercise8_complete_imaginary_period k) :
    u ∈ frontier (exercise8_open_rectangle k) := by
  -- The open rectangle is a real-imaginary product, so its frontier is the union of the four
  -- closed sides.
  have hreal :
      -exercise8_complete_real_period k < exercise8_complete_real_period k := by
    linarith [exercise8_complete_real_period_pos k]
  have himag : (0 : ℝ) < exercise8_complete_imaginary_period k :=
    exercise8_complete_imaginary_period_pos k
  rw [exercise8_open_rectangle, Complex.frontier_reProdIm]
  rcases hboundary with hre_left | hre_right | him_bottom | him_top
  · right
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [frontier_Ioo hreal]
      simp [hre_left]
    · have himClosed :
          u.im ∈ closure (Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)) := by
        rw [show
          closure (Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)) =
            Icc (0 : ℝ) (exercise8_complete_imaginary_period k) from
            closure_Ioo (show (0 : ℝ) ≠ exercise8_complete_imaginary_period k from
              Ne.symm ((exercise8_complete_imaginary_period_pos k).ne'))]
        exact him
      exact himClosed
  · right
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [frontier_Ioo hreal]
      simp [hre_right]
    · have himClosed :
          u.im ∈ closure (Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)) := by
        rw [show
          closure (Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)) =
            Icc (0 : ℝ) (exercise8_complete_imaginary_period k) from
            closure_Ioo (show (0 : ℝ) ≠ exercise8_complete_imaginary_period k from
              Ne.symm ((exercise8_complete_imaginary_period_pos k).ne'))]
        exact him
      exact himClosed
  · left
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simpa [closure_Ioo hreal.ne] using hre
    · rw [frontier_Ioo himag]
      simp [him_bottom]
  · left
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simpa [closure_Ioo hreal.ne] using hre
    · rw [frontier_Ioo himag]
      simp [him_top]

/-- Helper for Exercise 8: every value of the finite real-axis trace lies on the perimeter of the
fundamental rectangle. -/
lemma exercise8_boundary_trace_mem_frontier_rectangle (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_trace k x ∈ frontier (exercise8_open_rectangle k) := by
  by_cases hx_nonneg : 0 ≤ x
  · -- On the nonnegative side we follow the textbook bottom, right, and top branches.
    by_cases hx_le_one : x ≤ 1
    · have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx_nonneg, hx_le_one⟩
      have hinner :
          exercise8_inner_primitive k x ∈ Icc (0 : ℝ) (exercise8_complete_real_period k) :=
        exercise8_inner_primitive_mem_Icc (k := k) hxIcc
      have hre_bottom :
          exercise8_inner_primitive k x ∈
            Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
        rcases hinner with ⟨h0, hK⟩
        constructor <;> linarith
      have hEq :
          exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
        rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
        simpa [exercise8_boundary_inner_branch] using
          exercise8_boundary_value_eq_inner (k := k) hxIcc
      refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
      · -- Along the bottom edge, the real part is the partial primitive from `0` to `x`.
        simpa [hEq, exercise8_boundary_inner_branch_eq_inner_primitive] using hre_bottom
      · -- The bottom edge has imaginary part `0`, which lies in the closed vertical interval.
        have him0 :
            (0 : ℝ) ∈ Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
          exact ⟨le_rfl, (exercise8_complete_imaginary_period_pos k).le⟩
        simpa [hEq, exercise8_boundary_inner_branch_eq_inner_primitive] using him0
      · -- This branch sits on the bottom side `Im u = 0`.
        exact Or.inr (Or.inr (Or.inl (by
          simpa [hEq, exercise8_boundary_inner_branch_eq_inner_primitive])))
    · have hx_one : 1 ≤ x := le_of_lt (not_le.mp hx_le_one)
      by_cases hx_le_inv : x ≤ 1 / (k : ℝ)
      · have hxIcc : x ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := ⟨hx_one, hx_le_inv⟩
        have hright :
            exercise8_right_primitive k x ∈
              Icc (0 : ℝ) (exercise8_complete_imaginary_period k) :=
          exercise8_right_primitive_mem_Icc (k := k) hxIcc
        have hEq :
            exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
          rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) hx_one hx_le_inv
        refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
        · -- The right edge has constant real part `K`.
          have hKmem :
              exercise8_complete_real_period k ∈
                Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
            constructor
            · linarith [exercise8_complete_real_period_pos k]
            · rfl
          simpa [hEq, exercise8_boundary_right_branch_eq_right_primitive] using hKmem
        · -- Its imaginary part is the increasing right-edge primitive.
          simpa [hEq, exercise8_boundary_right_branch_eq_right_primitive] using hright
        · -- This branch lies on the right side `Re u = K`.
          exact Or.inr (Or.inl (by
            simpa [hEq, exercise8_boundary_right_branch_eq_right_primitive]))
      · have hx_top : 1 / (k : ℝ) ≤ x := by
          exact le_of_not_ge hx_le_inv
        let y : ℝ := 1 / ((k : ℝ) * x)
        have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
          simpa [y] using exercise8_top_branch_argument_mem_Icc (k := k) hx_top
        have hinner :
            exercise8_inner_primitive k y ∈ Icc (0 : ℝ) (exercise8_complete_real_period k) :=
          exercise8_inner_primitive_mem_Icc (k := k) hyIcc
        have hre_top :
            exercise8_inner_primitive k y ∈
              Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
          rcases hinner with ⟨h0, hK⟩
          constructor <;> linarith
        have hEq :
            exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
          rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
          simpa [exercise8_boundary_top_branch] using
            exercise8_boundary_value_eq_top (k := k) hx_top
        refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
        · -- On the top edge, the real part is the bottom-edge primitive evaluated at `1 / (k x)`.
          simpa [hEq, exercise8_boundary_top_branch_eq_inner_composition, y] using hre_top
        · -- The top edge has constant imaginary part `K'`.
          have himK :
              exercise8_complete_imaginary_period k ∈
                Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
            exact ⟨(exercise8_complete_imaginary_period_pos k).le, le_rfl⟩
          simpa [hEq, exercise8_boundary_top_branch_eq_inner_composition, y] using himK
        · -- This branch lies on the top side `Im u = K'`.
          exact Or.inr (Or.inr (Or.inr (by
            simpa [hEq, exercise8_boundary_top_branch_eq_inner_composition, y])))
  · -- The negative side is obtained by Schwarz reflection of the same three positive branches.
    let y : ℝ := -x
    have hy_pos : 0 < y := by
      dsimp [y]
      linarith
    have hreflect :
        exercise8_boundary_trace k x = -star (exercise8_boundary_trace k y) := by
      calc
        exercise8_boundary_trace k x = exercise8_boundary_trace k (-y) := by simp [y]
        _ = -star (exercise8_boundary_trace k y) := by
          simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k y
    by_cases hy_le_one : y ≤ 1
    · have hyIcc : y ∈ Icc (0 : ℝ) 1 := ⟨hy_pos.le, hy_le_one⟩
      have hinner :
          exercise8_inner_primitive k y ∈ Icc (0 : ℝ) (exercise8_complete_real_period k) :=
        exercise8_inner_primitive_mem_Icc (k := k) hyIcc
      have hreNeg :
          -(exercise8_inner_primitive k y) ∈
            Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
        rcases hinner with ⟨h0, hK⟩
        constructor <;> linarith
      have hEqPos :
          exercise8_boundary_trace k y = exercise8_boundary_inner_branch k y := by
        rw [show exercise8_boundary_trace k y = exercise8_boundary_value k y by rfl]
        simpa [exercise8_boundary_inner_branch] using
          exercise8_boundary_value_eq_inner (k := k) hyIcc
      have hEq :
          exercise8_boundary_trace k x = ((-(exercise8_inner_primitive k y) : ℝ) : ℂ) := by
        calc
          exercise8_boundary_trace k x = -star (exercise8_boundary_trace k y) := hreflect
          _ = -star (exercise8_boundary_inner_branch k y) := by rw [hEqPos]
          _ = ((-(exercise8_inner_primitive k y) : ℝ) : ℂ) := by
            rw [exercise8_boundary_inner_branch_eq_inner_primitive]
            simp
      refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
      · -- Reflection across the imaginary axis negates the bottom-edge real coordinate.
        simpa [hEq] using hreNeg
      · -- The reflected bottom edge still has imaginary part `0`.
        have him0 :
            (0 : ℝ) ∈ Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
          exact ⟨le_rfl, (exercise8_complete_imaginary_period_pos k).le⟩
        simpa [hEq] using him0
      · -- Reflection keeps the point on the bottom side.
        exact Or.inr (Or.inr (Or.inl (by
          simpa [hEq])))
    · have hy_one : 1 ≤ y := le_of_lt (not_le.mp hy_le_one)
      by_cases hy_le_inv : y ≤ 1 / (k : ℝ)
      · have hyIcc : y ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := ⟨hy_one, hy_le_inv⟩
        have hright :
            exercise8_right_primitive k y ∈
              Icc (0 : ℝ) (exercise8_complete_imaginary_period k) :=
          exercise8_right_primitive_mem_Icc (k := k) hyIcc
        have hreLeft :
            -exercise8_complete_real_period k ∈
              Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
          constructor
          · rfl
          · linarith [exercise8_complete_real_period_pos k]
        have hEqPos :
            exercise8_boundary_trace k y = exercise8_boundary_right_branch k y := by
          rw [show exercise8_boundary_trace k y = exercise8_boundary_value k y by rfl]
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) hy_one hy_le_inv
        have hEq :
            exercise8_boundary_trace k x =
              (-exercise8_complete_real_period k : ℂ) +
                ((exercise8_right_primitive k y : ℝ) : ℂ) * Complex.I := by
          calc
            exercise8_boundary_trace k x = -star (exercise8_boundary_trace k y) := hreflect
            _ = -star (exercise8_boundary_right_branch k y) := by rw [hEqPos]
            _ =
                (-exercise8_complete_real_period k : ℂ) +
                  ((exercise8_right_primitive k y : ℝ) : ℂ) * Complex.I := by
                  rw [exercise8_boundary_right_branch_eq_right_primitive]
                  simpa [add_comm, add_left_comm, add_assoc]
        refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
        · -- Reflecting the right edge lands on the left side `Re u = -K`.
          simpa [hEq] using hreLeft
        · -- The reflected imaginary coordinate is the same right-edge primitive.
          simpa [hEq] using hright
        · exact Or.inl (by
          simpa [hEq])
      · have hy_top : 1 / (k : ℝ) ≤ y := by
          exact le_of_not_ge hy_le_inv
        let t : ℝ := 1 / ((k : ℝ) * y)
        have htIcc : t ∈ Icc (0 : ℝ) 1 := by
          simpa [t] using exercise8_top_branch_argument_mem_Icc (k := k) hy_top
        have hinner :
            exercise8_inner_primitive k t ∈ Icc (0 : ℝ) (exercise8_complete_real_period k) :=
          exercise8_inner_primitive_mem_Icc (k := k) htIcc
        have hreNeg :
            -(exercise8_inner_primitive k t) ∈
              Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) := by
          rcases hinner with ⟨h0, hK⟩
          constructor <;> linarith
        have hEqPos :
            exercise8_boundary_trace k y = exercise8_boundary_top_branch k y := by
          rw [show exercise8_boundary_trace k y = exercise8_boundary_value k y by rfl]
          simpa [exercise8_boundary_top_branch] using
            exercise8_boundary_value_eq_top (k := k) hy_top
        have hEq :
            exercise8_boundary_trace k x =
              ((-(exercise8_inner_primitive k t) : ℝ) : ℂ) +
                (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
          calc
            exercise8_boundary_trace k x = -star (exercise8_boundary_trace k y) := hreflect
            _ = -star (exercise8_boundary_top_branch k y) := by rw [hEqPos]
            _ =
                ((-(exercise8_inner_primitive k t) : ℝ) : ℂ) +
                  (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
                  rw [exercise8_boundary_top_branch_eq_inner_composition]
                  simp [t]
        refine exercise8_mem_frontier_rectangle_of_coords (k := k) ?_ ?_ ?_
        · -- Reflecting the positive top branch negates only its real coordinate.
          simpa [hEq] using hreNeg
        · -- The top edge keeps the same imaginary coordinate `K'` after reflection.
          have himK :
              exercise8_complete_imaginary_period k ∈
                Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
            exact ⟨(exercise8_complete_imaginary_period_pos k).le, le_rfl⟩
          simpa [hEq] using himK
        · exact Or.inr (Or.inr (Or.inr (by
          simpa [hEq])))

lemma exercise8_boundary_trace_range_subset_frontier_rectangle (k : Exercise8Modulus) :
    Set.range (exercise8_boundary_trace k) ⊆ frontier (exercise8_open_rectangle k) := by
  -- The pointwise perimeter statement immediately yields the range inclusion.
  rintro _ ⟨x, rfl⟩
  exact exercise8_boundary_trace_mem_frontier_rectangle k x

/-- Helper for Cartan section26 0018_Exercise_8: the bottom-edge primitive fills the whole real
interval `[0, K]` on the compact parameter interval `[0, 1]`. -/
lemma exercise8_inner_primitive_image_Icc
    (k : Exercise8Modulus) :
    (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 =
      Icc (0 : ℝ) (exercise8_complete_real_period k) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Every bottom-edge primitive value already lies between `0` and `K`.
    exact exercise8_inner_primitive_mem_Icc (k := k) hx
  · intro hy
    have hcontComplex := exercise8_inner_primitive_complex_continuousOn_Icc k
    have hcont :
        ContinuousOn (fun x : ℝ => exercise8_inner_primitive k x) (Icc (0 : ℝ) 1) := by
      -- Read continuity of the real primitive back from its complexified owner.
      simpa using Complex.continuous_re.comp_continuousOn' hcontComplex
    have hzero : exercise8_inner_primitive k 0 = 0 := by
      -- The primitive starts from the basepoint integral `∫_0^0 = 0`.
      simp [exercise8_inner_primitive]
    have hone : exercise8_inner_primitive k 1 = exercise8_complete_real_period k := by
      have honeComplex :
          ((exercise8_inner_primitive k 1 : ℝ) : ℂ) = exercise8_complete_real_period k := by
        -- Compare the named primitive at `1` with the public boundary-value owner `f(1) = K`.
        calc
          ((exercise8_inner_primitive k 1 : ℝ) : ℂ) = exercise8_boundary_inner_branch k 1 := by
            simpa using (exercise8_boundary_inner_branch_eq_inner_primitive k 1).symm
          _ = exercise8_boundary_value k 1 := by
            symm
            simpa [exercise8_boundary_inner_branch] using
              exercise8_boundary_value_eq_inner (k := k) (x := 1) (by simp)
          _ = exercise8_complete_real_period k := by
            simpa using exercise8_boundary_value_one k
      exact by simpa using congrArg Complex.re honeComplex
    have hsurj :
        Icc (exercise8_inner_primitive k 0) (exercise8_inner_primitive k 1) ⊆
          (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 :=
      intermediate_value_Icc (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => exercise8_inner_primitive k x) zero_le_one hcont
    -- The intermediate value theorem upgrades the endpoint owner to the full interval image.
    exact hsurj (by simpa [hzero, hone] using hy)

/-- Helper for Cartan section26 0018_Exercise_8: the right-edge primitive fills the whole
imaginary-period interval `[0, K']` on `[1, 1 / k]`. -/
lemma exercise8_right_primitive_image_Icc
    (k : Exercise8Modulus) :
    (fun x : ℝ => exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) =
      Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Every right-edge primitive value already lies between `0` and `K'`.
    exact exercise8_right_primitive_mem_Icc (k := k) hx
  · intro hy
    have hcont := exercise8_right_primitive_continuousOn_Icc k
    have hone : exercise8_right_primitive k 1 = 0 := by
      -- The right-edge primitive also starts from a zero-length integral.
      simp [exercise8_right_primitive]
    have hinvK :
        exercise8_right_primitive k (1 / (k : ℝ)) = exercise8_complete_imaginary_period k := by
      have hvertex :
          exercise8_boundary_right_branch k (1 / (k : ℝ)) =
            exercise8_complete_real_period k +
              exercise8_complete_imaginary_period k * Complex.I := by
        -- Rewrite the boundary owner at `1 / k` through the right-edge branch.
        calc
          exercise8_boundary_right_branch k (1 / (k : ℝ)) =
              exercise8_boundary_value k (1 / (k : ℝ)) := by
                symm
                simpa [exercise8_boundary_right_branch] using
                  exercise8_boundary_value_eq_right (k := k)
                    (x := 1 / (k : ℝ))
                    (by
                      have hk_inv_ge_one : 1 ≤ 1 / (k : ℝ) := by
                        exact
                          (one_le_div (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k).le
                      exact hk_inv_ge_one)
                    le_rfl
          _ =
              exercise8_complete_real_period k +
                exercise8_complete_imaginary_period k * Complex.I := by
                simpa using exercise8_boundary_value_inv_k k
      have hvertexImag := congrArg Complex.im <|
        calc
          (exercise8_complete_real_period k : ℂ) +
              ((exercise8_right_primitive k (1 / (k : ℝ)) : ℝ) : ℂ) * Complex.I =
            exercise8_boundary_right_branch k (1 / (k : ℝ)) := by
              simpa using (exercise8_boundary_right_branch_eq_right_primitive k (1 / (k : ℝ))).symm
          _ =
            exercise8_complete_real_period k +
              exercise8_complete_imaginary_period k * Complex.I := hvertex
      simpa using hvertexImag
    have hinvK_inv :
        exercise8_right_primitive k ((k : ℝ)⁻¹) = exercise8_complete_imaginary_period k := by
      simpa [one_div] using hinvK
    have hsurj :
        Icc (exercise8_right_primitive k 1)
            (exercise8_right_primitive k (1 / (k : ℝ))) ⊆
          (fun x : ℝ => exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) :=
      intermediate_value_Icc (a := (1 : ℝ)) (b := (1 / (k : ℝ)))
        (f := fun x : ℝ => exercise8_right_primitive k x)
        (by
          have hk_inv_ge_one : 1 ≤ 1 / (k : ℝ) := by
            exact (one_le_div (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k).le
          exact hk_inv_ge_one)
        hcont
    -- The intermediate value theorem upgrades the endpoint owner to the whole right-edge image.
    exact hsurj (by simpa [hone, hinvK_inv] using hy)

/-- Helper for Cartan section26 0018_Exercise_8: the finite boundary trace misses the top midpoint
only because that point appears at the compactified end `x = +∞`; along the top branch, the
reciprocal argument tends to `0`, so the trace tends to `i K'`. -/
lemma exercise8_boundary_trace_tendsto_top_midpoint_atTop
    (k : Exercise8Modulus) :
    Filter.Tendsto (exercise8_boundary_trace k) Filter.atTop
      (nhds ((exercise8_complete_imaginary_period k : ℂ) * Complex.I)) := by
  have htop :
      (fun x : ℝ ↦ exercise8_boundary_trace k x) =ᶠ[Filter.atTop]
        exercise8_boundary_top_branch k := by
    -- Far enough to the right, the repaired trace is exactly the textbook top-edge branch.
    filter_upwards [Filter.eventually_ge_atTop (1 / (k : ℝ))] with x hx
    rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
    exact exercise8_boundary_value_eq_top (k := k) (x := x) hx
  have harg :
      Filter.Tendsto (fun x : ℝ ↦ 1 / ((k : ℝ) * x)) Filter.atTop (nhds 0) := by
    -- The reciprocal top-edge parameter is a constant multiple of `x⁻¹`.
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ ((k : ℝ)⁻¹)) Filter.atTop
        (nhds ((k : ℝ)⁻¹))).mul tendsto_inv_atTop_zero)
  have harg_mem :
      ∀ᶠ x : ℝ in Filter.atTop, 1 / ((k : ℝ) * x) ∈ Icc (0 : ℝ) 1 := by
    -- Beyond `1 / k`, the reciprocal parameter already lies in the bottom-edge interval.
    filter_upwards [Filter.eventually_ge_atTop (1 / (k : ℝ))] with x hx
    simpa using exercise8_top_branch_argument_mem_Icc (k := k) hx
  have harg_within :
      Filter.Tendsto (fun x : ℝ ↦ 1 / ((k : ℝ) * x)) Filter.atTop
        (nhdsWithin 0 (Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ harg harg_mem
  have hinner :
      Filter.Tendsto
        (fun x : ℝ => ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ))
        Filter.atTop (nhds 0) := by
    -- The inner primitive is continuous at `0` on `[0,1]`, and its value there is `0`.
    have hcont0 :
        ContinuousWithinAt (fun y : ℝ => ((exercise8_inner_primitive k y : ℝ) : ℂ))
          (Icc (0 : ℝ) 1) 0 := by
      exact (exercise8_inner_primitive_complex_continuousOn_Icc k) (x := 0) (by simp)
    have hzero :
        (((exercise8_inner_primitive k 0 : ℝ) : ℂ)) = 0 := by
      simp [exercise8_inner_primitive]
    simpa [hzero] using hcont0.tendsto.comp harg_within
  have htopBranch :
      Filter.Tendsto (exercise8_boundary_top_branch k) Filter.atTop
        (nhds ((exercise8_complete_imaginary_period k : ℂ) * Complex.I)) := by
    -- Unfold the top-edge branch and send the shrinking inner primitive to `0`.
    have hconst :
        Filter.Tendsto
          (fun _ : ℝ ↦ (exercise8_complete_imaginary_period k : ℂ) * Complex.I)
          Filter.atTop
          (nhds ((exercise8_complete_imaginary_period k : ℂ) * Complex.I)) :=
      tendsto_const_nhds
    have hsum := hconst.add hinner
    convert hsum using 1
    · funext x
      simp [exercise8_boundary_top_branch_eq_inner_composition, one_div, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
    · simp
  exact Filter.Tendsto.congr' htop.symm htopBranch

/-- Helper for Cartan section26 0018_Exercise_8: the positive half of the top edge, including the
midpoint `i K'`, already lies in the closure of the repaired boundary trace. -/
lemma exercise8_top_half_edge_mem_closure_boundaryTrace
    (k : Exercise8Modulus) {u : ℂ}
    (hu_im : u.im = exercise8_complete_imaginary_period k) :
    0 ≤ u.re → u.re ≤ exercise8_complete_real_period k →
      u ∈ closure (Set.range (exercise8_boundary_trace k)) := by
  intro hre0 hreK
  by_cases hre_zero : u.re = 0
  · have hu_mid :
        u = (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
      -- On the top side, zero real part identifies the missing midpoint `i K'`.
      apply Complex.ext <;> simp [hu_im, hre_zero]
    subst hu_mid
    -- The midpoint is not a finite trace value, but it is the `atTop` limit of the top branch.
    refine mem_closure_of_tendsto (exercise8_boundary_trace_tendsto_top_midpoint_atTop k) ?_
    exact Filter.Eventually.of_forall fun x ↦ ⟨x, rfl⟩
  · have hre_pos : 0 < u.re := lt_of_le_of_ne hre0 (Ne.symm hre_zero)
    have hu_range :
        u.re ∈ (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
      rw [exercise8_inner_primitive_image_Icc]
      exact ⟨hre0, hreK⟩
    rcases hu_range with ⟨y, hy_mem, hy_eq⟩
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      apply hre_zero
      rw [← hy_eq, hy_zero]
      simp [exercise8_inner_primitive]
    have hy_pos : 0 < y := lt_of_le_of_ne hy_mem.1 hy_ne.symm
    let x : ℝ := 1 / ((k : ℝ) * y)
    have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
    have hx_top : 1 / (k : ℝ) ≤ x := by
      by_cases hy_one : y = 1
      · subst hy_one
        dsimp [x]
        simpa using (le_rfl : 1 / (k : ℝ) ≤ 1 / (k : ℝ))
      · have hy_lt_one : y < 1 := lt_of_le_of_ne hy_mem.2 hy_one
        exact (exercise8_topReciprocalParameter_gt_invK k ⟨hy_pos, hy_lt_one⟩).le
    have hx_arg : 1 / ((k : ℝ) * x) = y := by
      dsimp [x]
      field_simp [hk_ne, hy_ne]
    have hu_eq :
        u =
          (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
            ((exercise8_inner_primitive k y : ℝ) : ℂ) := by
      -- The chosen `y` records the real coordinate, while `hu_im` fixes the top-edge height.
      apply Complex.ext <;> simp [hu_im, hy_eq]
    have htrace_top :
        exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
      -- Once `x ≥ 1 / k`, the public boundary trace is exactly the top-edge branch.
      rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
      simpa [exercise8_boundary_top_branch] using
        exercise8_boundary_value_eq_top (k := k) (x := x) hx_top
    have htrace : exercise8_boundary_trace k x = u := by
      -- Rewrite the top branch through the reciprocal substitution and the selected parameter `y`.
      calc
        exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := htrace_top
        _ =
            (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
              ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) := by
              rw [exercise8_boundary_top_branch_eq_inner_composition]
        _ =
            (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
              ((exercise8_inner_primitive k y : ℝ) : ℂ) := by rw [hx_arg]
        _ = u := hu_eq.symm
    -- Positive top-half points are already exact boundary-trace values, hence belong to the
    -- closure of the trace range.
    exact subset_closure ⟨x, htrace⟩

/-- Helper for Cartan section26 0018_Exercise_8: every finite real boundary-trace value is a
limit of interior Abel values, so it already belongs to the closure of the Abel image. -/
lemma exercise8_boundary_trace_mem_closure_abelImage
    (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_trace k x ∈ closure (Set.range (exercise8_abel_integral k)) := by
  have hupper_closure : (x : ℂ) ∈ closure UpperHalfPlane.upperHalfPlaneSet := by
    -- Every real boundary point is accumulated by the strict upper half-plane through a short
    -- vertical segment.
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · have him_pos : 0 < ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I).im := by
        simp
        linarith
      simpa [UpperHalfPlane.upperHalfPlaneSet] using him_pos
    · have hhalf_nonneg : 0 ≤ ε / 2 := by
        linarith
      have hnormOfReal : ‖((ε / 2 : ℝ) : ℂ)‖ = |ε / 2| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (ε / 2))
      calc
        dist (x : ℂ) ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)
            = ‖(x : ℂ) - ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by
              rw [dist_eq_norm]
        _ = ‖-(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by ring_nf
        _ = ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ := by rw [norm_neg]
        _ = ‖((ε / 2 : ℝ) : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
        _ = |ε / 2| * ‖Complex.I‖ := by rw [hnormOfReal]
        _ = |ε / 2| * 1 := by rw [Complex.norm_I]
        _ = ε / 2 := by rw [abs_of_nonneg hhalf_nonneg]; ring
        _ < ε := by linarith
  haveI : (nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hupper_closure
  by_cases hx : x = 0
  · subst hx
    have hlimit := exercise8_abel_integral_tendsto_boundary_trace_zero k
    -- The direct `0`-limit approaches the Abel image through upper-half-plane points.
    refine mem_closure_of_tendsto hlimit ?_
    exact Filter.Eventually.of_forall fun w ↦ ⟨UpperHalfPlane.ofComplex w, rfl⟩
  · have hlimit := exercise8_abel_integral_tendsto_boundary_trace_nonzero_real k hx
    -- The same closure argument works for every nonzero real boundary point.
    refine mem_closure_of_tendsto hlimit ?_
    exact Filter.Eventually.of_forall fun w ↦ ⟨UpperHalfPlane.ofComplex w, rfl⟩

/-- Helper for Cartan section26 0018_Exercise_8: the missing top midpoint `i K'` is also in the
closure of the Abel image because it is the `atTop` limit of finite boundary-trace values. -/
lemma exercise8_topMidpoint_mem_closure_abelImage
    (k : Exercise8Modulus) :
    (exercise8_complete_imaginary_period k : ℂ) * Complex.I ∈
      closure (Set.range (exercise8_abel_integral k)) := by
  have hlimit := exercise8_boundary_trace_tendsto_top_midpoint_atTop k
  have hmem :
      ∀ᶠ x : ℝ in Filter.atTop,
        exercise8_boundary_trace k x ∈ closure (Set.range (exercise8_abel_integral k)) :=
    Filter.Eventually.of_forall fun x ↦ exercise8_boundary_trace_mem_closure_abelImage k x
  -- Passing to the limit only adds a redundant outer closure on the target.
  simpa [closure_closure] using mem_closure_of_tendsto hlimit hmem

/-- Helper for Cartan section26 0018_Exercise_8: the entire closure of the repaired boundary trace
already sits inside the closure of the Abel image. This packages the proved finite-boundary and
top-midpoint limits into one owner theorem for the remaining rectangle-image work. -/
lemma exercise8_boundaryTraceClosure_subset_closure_abelImage
    (k : Exercise8Modulus) :
    closure (Set.range (exercise8_boundary_trace k)) ⊆
      closure (Set.range (exercise8_abel_integral k)) := by
  -- The target closure is closed, so it suffices to check the generating range itself.
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨x, rfl⟩
  exact exercise8_boundary_trace_mem_closure_abelImage k x

/-- Helper for Cartan section26 0018_Exercise_8: every frontier point of the target rectangle is
already a limit of finite boundary-trace values. The only genuinely closure-only point is the top
midpoint `i K'`; the remaining sides are exact boundary-trace values. -/
lemma exercise8_frontier_rectangle_subset_closure_boundaryTrace
    (k : Exercise8Modulus) :
    frontier (exercise8_open_rectangle k) ⊆ closure (Set.range (exercise8_boundary_trace k)) := by
  intro u hu
  have hreal :
      -exercise8_complete_real_period k < exercise8_complete_real_period k := by
    linarith [exercise8_complete_real_period_pos k]
  have himag : (0 : ℝ) < exercise8_complete_imaginary_period k :=
    exercise8_complete_imaginary_period_pos k
  rw [exercise8_open_rectangle, Complex.frontier_reProdIm, closure_Ioo hreal.ne,
    frontier_Ioo himag, closure_Ioo himag.ne, frontier_Ioo hreal] at hu
  rcases hu with hu_horizontal | hu_vertical
  · rw [Complex.mem_reProdIm] at hu_horizontal
    rcases hu_horizontal with ⟨hre, him⟩
    rcases him with hu_bottom | hu_top
    · -- On the bottom edge, the real coordinate is filled exactly by the bottom branch and its
      -- Schwarz reflection.
      by_cases hre_nonneg : 0 ≤ u.re
      · have hu_range :
            u.re ∈ (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
          rw [exercise8_inner_primitive_image_Icc]
          exact ⟨hre_nonneg, hre.2⟩
        rcases hu_range with ⟨x, hx_mem, hx_eq⟩
        have htrace_eq :
            exercise8_boundary_trace k x = u := by
          have hbranch :
              exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
            rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
            simpa [exercise8_boundary_inner_branch] using
              exercise8_boundary_value_eq_inner (k := k) hx_mem
          calc
            exercise8_boundary_trace k x = ((exercise8_inner_primitive k x : ℝ) : ℂ) := by
              rw [hbranch, exercise8_boundary_inner_branch_eq_inner_primitive]
            _ = ((u.re : ℝ) : ℂ) := by
              exact congrArg (fun t : ℝ => (t : ℂ)) hx_eq
            _ = u := by
              apply Complex.ext <;> simp [hu_bottom]
        exact subset_closure ⟨x, htrace_eq⟩
      · have hu_range :
            -u.re ∈ (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
          rw [exercise8_inner_primitive_image_Icc]
          constructor
          · linarith
          · linarith [hre.1]
        rcases hu_range with ⟨x, hx_mem, hx_eq⟩
        have htrace_eq :
            exercise8_boundary_trace k (-x) = u := by
          have hbranch :
              exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
            rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
            simpa [exercise8_boundary_inner_branch] using
              exercise8_boundary_value_eq_inner (k := k) hx_mem
          calc
            exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
              simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
            _ = -star (exercise8_boundary_inner_branch k x) := by rw [hbranch]
            _ = ((u.re : ℝ) : ℂ) := by
              rw [exercise8_boundary_inner_branch_eq_inner_primitive]
              simp [hx_eq]
            _ = u := by
              apply Complex.ext <;> simp [hu_bottom]
        exact subset_closure ⟨-x, htrace_eq⟩
    · -- On the top edge, the positive half is already packaged; the negative half is obtained by
      -- reflecting the positive top branch.
      by_cases hre_nonneg : 0 ≤ u.re
      · exact exercise8_top_half_edge_mem_closure_boundaryTrace k hu_top hre_nonneg hre.2
      · by_cases hre_zero : u.re = 0
        · have hre_nonneg_zero : 0 ≤ u.re := by
            simpa [hre_zero] using (show (0 : ℝ) ≤ 0 by exact le_rfl)
          exact exercise8_top_half_edge_mem_closure_boundaryTrace k hu_top hre_nonneg_zero
            (by simpa using hre.2)
        · have hu_neg : u.re < 0 := lt_of_not_ge hre_nonneg
          have hu_range :
              -u.re ∈ (fun x : ℝ => exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
            rw [exercise8_inner_primitive_image_Icc]
            constructor
            · linarith
            · linarith [hre.1]
          rcases hu_range with ⟨y, hy_mem, hy_eq⟩
          have hy_ne : y ≠ 0 := by
            intro hy0
            apply hre_zero
            have hzero : exercise8_inner_primitive k 0 = 0 := by
              simp [exercise8_inner_primitive]
            have : -u.re = 0 := by simpa [hy0, hzero] using hy_eq.symm
            linarith
          have hy_pos : 0 < y := lt_of_le_of_ne hy_mem.1 hy_ne.symm
          let x : ℝ := 1 / ((k : ℝ) * y)
          have hx_top : 1 / (k : ℝ) ≤ x := by
            by_cases hy_one : y = 1
            · subst hy_one
              dsimp [x]
              simpa using (le_rfl : 1 / (k : ℝ) ≤ 1 / (k : ℝ))
            · have hy_lt_one : y < 1 := lt_of_le_of_ne hy_mem.2 hy_one
              exact (exercise8_topReciprocalParameter_gt_invK k ⟨hy_pos, hy_lt_one⟩).le
          have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
          have hx_arg : 1 / ((k : ℝ) * x) = y := by
            dsimp [x]
            field_simp [hk_ne, hy_ne]
          have htrace_eq :
              exercise8_boundary_trace k (-x) = u := by
            have hbranch :
                exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
              rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
              simpa [exercise8_boundary_top_branch] using
                exercise8_boundary_value_eq_top (k := k) (x := x) hx_top
            calc
              exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
                simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
              _ = -star (exercise8_boundary_top_branch k x) := by rw [hbranch]
              _ =
                  (-((exercise8_inner_primitive k y : ℝ) : ℂ)) +
                    (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
                    rw [exercise8_boundary_top_branch_eq_inner_composition, hx_arg]
                    simp [add_comm, add_left_comm, add_assoc]
              _ =
                  ((u.re : ℝ) : ℂ) +
                    (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
                    simp [hy_eq]
              _ = u := by
                    have hu_top_eq : u.im = exercise8_complete_imaginary_period k := by
                      simpa using hu_top
                    apply Complex.ext <;> simp [hu_top_eq]
          exact subset_closure ⟨-x, htrace_eq⟩
  · rw [Complex.mem_reProdIm] at hu_vertical
    rcases hu_vertical with ⟨hre, him⟩
    rcases hre with hu_left | hu_right
    · -- The left side is the reflected right-edge branch.
      have hu_range :
          u.im ∈ (fun x : ℝ => exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) := by
        rw [exercise8_right_primitive_image_Icc]
        exact him
      rcases hu_range with ⟨x, hx_mem, hx_eq⟩
      have htrace_eq :
          exercise8_boundary_trace k (-x) = u := by
        have hbranch :
            exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
          rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) hx_mem.1 hx_mem.2
        calc
          exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
            simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
          _ = -star (exercise8_boundary_right_branch k x) := by rw [hbranch]
          _ =
              (-exercise8_complete_real_period k : ℂ) +
                ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
                  rw [exercise8_boundary_right_branch_eq_right_primitive]
                  simp [add_comm, add_left_comm, add_assoc]
          _ =
              (-exercise8_complete_real_period k : ℂ) +
                ((u.im : ℝ) : ℂ) * Complex.I := by
                  exact congrArg
                    (fun t : ℝ =>
                      (-exercise8_complete_real_period k : ℂ) + (t : ℂ) * Complex.I) hx_eq
          _ = u := by
              have hu_left_eq : u.re = -exercise8_complete_real_period k := by
                simpa using hu_left
              apply Complex.ext <;> simp [hu_left_eq]
      exact subset_closure ⟨-x, htrace_eq⟩
    · -- The right side is filled exactly by the right-edge primitive.
      have hu_range :
          u.im ∈ (fun x : ℝ => exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) := by
        rw [exercise8_right_primitive_image_Icc]
        exact him
      rcases hu_range with ⟨x, hx_mem, hx_eq⟩
      have htrace_eq :
          exercise8_boundary_trace k x = u := by
        have hbranch :
            exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
          rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) hx_mem.1 hx_mem.2
        calc
          exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := hbranch
          _ =
              (exercise8_complete_real_period k : ℂ) +
                ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
                  rw [exercise8_boundary_right_branch_eq_right_primitive]
          _ =
              (exercise8_complete_real_period k : ℂ) +
                ((u.im : ℝ) : ℂ) * Complex.I := by
                  exact congrArg
                    (fun t : ℝ =>
                      (exercise8_complete_real_period k : ℂ) + (t : ℂ) * Complex.I) hx_eq
          _ = u := by
              have hu_right_eq : u.re = exercise8_complete_real_period k := by
                simpa using hu_right
              apply Complex.ext <;> simp [hu_right_eq]
      exact subset_closure ⟨x, htrace_eq⟩

/-- Helper for Cartan section26 0018_Exercise_8: the rectangle frontier package transports
directly from the repaired boundary trace to the Abel image closure. -/
lemma exercise8_frontier_rectangle_subset_closure_abelImage
    (k : Exercise8Modulus) :
    frontier (exercise8_open_rectangle k) ⊆ closure (Set.range (exercise8_abel_integral k)) := by
  intro u hu
  exact exercise8_boundaryTraceClosure_subset_closure_abelImage k
    (exercise8_frontier_rectangle_subset_closure_boundaryTrace k hu)

/-- The source-facing inverse of the Exercise 8 Abelian integral on the fundamental rectangle. -/
def IsExercise8RectangleInverse
    (k : Exercise8Modulus) (G : exercise8_open_rectangle k → UpperHalfPlane) : Prop :=
  (∀ u : exercise8_open_rectangle k, exercise8_abel_integral k (G u) = u) ∧
    (∀ z : UpperHalfPlane, exercise8_abel_integral k z ∈ exercise8_open_rectangle k) ∧
    ∀ z : UpperHalfPlane,
      ∀ hz : exercise8_abel_integral k z ∈ exercise8_open_rectangle k,
        G ⟨exercise8_abel_integral k z, hz⟩ = z

/-- A meromorphic doubly-periodic extension of the Exercise 8 rectangle inverse. -/
def IsExercise8Inverse (k : Exercise8Modulus) (F : ℂ → ℂ) : Prop :=
  ∃ G : exercise8_open_rectangle k → UpperHalfPlane,
    IsExercise8RectangleInverse k G ∧
      Meromorphic F ∧
      HasPeriodLattice (exercise8_period_pair k) F ∧
      (∀ u : exercise8_open_rectangle k, F u = G u)
