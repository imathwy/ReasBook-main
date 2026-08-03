import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap04.Proposition_4_11
import BauschkeLean.Chap23.Proposition_23_10
import BauschkeLean.Chap23.Proposition_23_21
import BauschkeLean.Chap25.Definition_25_10

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` only surfaced unrelated generic monotonicity lemmas, so
-- this file follows the verified local owners `ofFunction`, `CocoerciveOn`,
-- `FirmlyNonexpansiveOn`, `residualMap`, `J[...]`, `{}^[γ]`, and `IsThreeStarMonotone`.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 25.20 (1): if `T : D → H` is `β`-cocoercive for some `β ∈ ℝ_{++}`, then the
singleton-valued operator `ofFunction D T` is `3*` monotone. -/
theorem ofFunction_isThreeStarMonotone_of_cocoerciveOn
    {D : Set H} {T : D → H} {β : ERealFunction.PosReal}
    (hT : CocoerciveOn (β : ℝ) D T) :
    (ofFunction D T).IsThreeStarMonotone := by
  rw [isThreeStarMonotone_iff]
  rintro ⟨x, u⟩ ⟨hx_dom, hu_range⟩
  rcases (mem_dom_iff (ofFunction D T) x).1 hx_dom with ⟨v, hv⟩
  rcases hv with ⟨hx, rfl⟩
  rcases (mem_range_iff (ofFunction D T) u).1 hu_range with ⟨z, hz⟩
  rcases hz with ⟨hz, rfl⟩
  rw [ERealFunction.mem_dom_iff_ne_top]
  rw [fitzpatrickFunction]
  let C : ℝ :=
    ⟪(x : H), T ⟨z, hz⟩⟫_ℝ + ‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ))
  refine ne_of_lt <| lt_of_le_of_lt (iSup_le fun p ↦ ?_) (EReal.coe_lt_top C)
  rcases p.2 with ⟨hy, hp⟩
  rw [hp]
  let w : H := T ⟨z, hz⟩ - T ⟨p.1.1, hy⟩
  have hcoco :
      (β : ℝ) * ‖w‖ ^ (2 : ℕ) ≤ ⟪z - p.1.1, w⟫_ℝ := by
    simpa [w] using hT.ineq ⟨z, hz⟩ ⟨p.1.1, hy⟩
  have hlin :
      -(‖(x : H) - z‖ * ‖w‖) ≤ ⟪(x : H) - z, w⟫_ℝ := by
    have hlin₀ :
        ⟪-((x : H) - z), w⟫_ℝ ≤ ‖-((x : H) - z)‖ * ‖w‖ := real_inner_le_norm _ _
    have hlin' :
        -⟪(x : H) - z, w⟫_ℝ ≤ ‖(x : H) - z‖ * ‖w‖ := by
      simpa only [inner_neg_left, norm_neg] using hlin₀
    nlinarith
  have hsplit :
      ⟪(x : H) - p.1.1, w⟫_ℝ = ⟪(x : H) - z, w⟫_ℝ + ⟪z - p.1.1, w⟫_ℝ := by
    have hdecomp : (x : H) - p.1.1 = ((x : H) - z) + (z - p.1.1) := by
      abel_nf
    rw [hdecomp, inner_add_left]
  have hgap :
      -‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) ≤ ⟪(x : H) - p.1.1, w⟫_ℝ := by
    have hquad :
        -‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) ≤
          (β : ℝ) * ‖w‖ ^ (2 : ℕ) - ‖(x : H) - z‖ * ‖w‖ := by
      have hβ4 : 0 < 4 * (β : ℝ) := by
        nlinarith [β.2]
      have hsq : 0 ≤ (2 * (β : ℝ) * ‖w‖ - ‖(x : H) - z‖) ^ (2 : ℕ) := sq_nonneg _
      refine (div_le_iff₀ hβ4).2 ?_
      nlinarith [hT.pos, hsq]
    have hsum :
        (β : ℝ) * ‖w‖ ^ (2 : ℕ) - ‖(x : H) - z‖ * ‖w‖ ≤
          ⟪(x : H) - z, w⟫_ℝ + ⟪z - p.1.1, w⟫_ℝ := by
      nlinarith [hcoco, hlin]
    rw [hsplit]
    exact le_trans hquad hsum
  have hrepr :
      ⟪p.1.1, T ⟨z, hz⟩⟫_ℝ + ⟪(x : H), T ⟨p.1.1, hy⟩⟫_ℝ -
          ⟪p.1.1, T ⟨p.1.1, hy⟩⟫_ℝ =
        ⟪(x : H), T ⟨z, hz⟩⟫_ℝ - ⟪(x : H) - p.1.1, w⟫_ℝ := by
    rw [show w = T ⟨z, hz⟩ - T ⟨p.1.1, hy⟩ by rfl]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  have hbound :
      ⟪p.1.1, T ⟨z, hz⟩⟫_ℝ + ⟪(x : H), T ⟨p.1.1, hy⟩⟫_ℝ -
          ⟪p.1.1, T ⟨p.1.1, hy⟩⟫_ℝ ≤
        C := by
    rw [hrepr]
    have hgap' : -⟪(x : H) - p.1.1, w⟫_ℝ ≤ ‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) := by
      have hgap'' :
          -⟪(x : H) - p.1.1, w⟫_ℝ ≤ -(-‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ))) :=
        neg_le_neg hgap
      have hneg :
          -(-‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ))) =
            ‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) := by
        ring_nf
      rw [hneg] at hgap''
      exact hgap''
    have hsum :
        -⟪(x : H) - p.1.1, w⟫_ℝ + ⟪(x : H), T ⟨z, hz⟩⟫_ℝ ≤
          ‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) + ⟪(x : H), T ⟨z, hz⟩⟫_ℝ :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hgap' ⟪(x : H), T ⟨z, hz⟩⟫_ℝ
    calc
      ⟪(x : H), T ⟨z, hz⟩⟫_ℝ - ⟪(x : H) - p.1.1, w⟫_ℝ
          ≤ ⟪(x : H), T ⟨z, hz⟩⟫_ℝ + ‖(x : H) - z‖ ^ (2 : ℕ) / (4 * (β : ℝ)) := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
      _ = C := by rfl
  exact_mod_cast hbound

/-- Example 25.20 (2): if `T : D → H` is firmly nonexpansive on `D`, then the singleton-valued
operator `ofFunction D T` is `3*` monotone. -/
theorem ofFunction_isThreeStarMonotone_of_firmlyNonexpansiveOn
    {D : Set H} {T : D → H}
    (hT : FirmlyNonexpansiveOn D T) :
    (ofFunction D T).IsThreeStarMonotone := by
  have hCoco : CocoerciveOn ((1 : ERealFunction.PosReal) : ℝ) D T := by
    refine ⟨by norm_num, ?_⟩
    intro x y
    simpa using hT x y
  simpa using ofFunction_isThreeStarMonotone_of_cocoerciveOn hCoco

/-- Example 25.20 (3): if `A : H → 2^H` is monotone, `γ ∈ ℝ_{++}`, and `T : D → H` realizes the
resolvent `J[γ • A]`, then `ofFunction D T` is `3*` monotone. -/
theorem ofFunction_isThreeStarMonotone_of_eq_resolvent
    {D : Set H} {T : D → H} {A : SetValuedOperator H H}
    (hA : A.IsMonotone) {γ : ERealFunction.PosReal}
    (hT : ofFunction D T = J[((γ : ℝ) • A)]) :
    (ofFunction D T).IsThreeStarMonotone := by
  let γnn : NNReal := ⟨(γ : ℝ), γ.2.le⟩
  have hγA : ((γ : ℝ) • A).IsMonotone := by
    simpa [γnn] using SetValuedOperator.IsMonotone.smul hA γnn
  have hFirm : FirmlyNonexpansiveOn D T := by
    exact
      (isMonotone_iff_firmlyNonexpansiveOn_of_resolvent_eq_ofFunction
        ((γ : ℝ) • A) D T hT.symm).1 hγA
  exact ofFunction_isThreeStarMonotone_of_firmlyNonexpansiveOn hFirm

/-- Example 25.20 (4): if `A : H → 2^H` is monotone, `γ ∈ ℝ_{++}`, and `T : D → H` realizes the
Yosida approximation `{}^[γ] A`, then `ofFunction D T` is `3*` monotone. -/
theorem ofFunction_isThreeStarMonotone_of_eq_yosidaApproximation
    {D : Set H} {T : D → H} {A : SetValuedOperator H H}
    (hA : A.IsMonotone) {γ : ERealFunction.PosReal}
    (hT : ofFunction D T = {}^[γ]A) :
    (ofFunction D T).IsThreeStarMonotone := by
  have hCoco : CocoerciveOn (γ : ℝ) D T := by
    exact
      (cocoerciveOn_iff_exists_isMonotone_yosidaApproximation_eq_ofFunction D T γ).2
        ⟨A, hA, hT.symm⟩
  exact ofFunction_isThreeStarMonotone_of_cocoerciveOn hCoco

/-- Example 25.20 (5): if the residual map `Id - T`, realized as `residualMap D T`, is
nonexpansive, then the singleton-valued operator `ofFunction D T` is `3*` monotone. -/
theorem ofFunction_isThreeStarMonotone_of_lipschitzWith_one_residualMap
    {D : Set H} {T : D → H}
    (hT : LipschitzWith 1 (residualMap D T)) :
    (ofFunction D T).IsThreeStarMonotone := by
  let βhalf : ERealFunction.PosReal := ⟨1 / 2, by norm_num⟩
  have hResidualCoco :
      CocoerciveOn (βhalf : ℝ) D (residualMap D (residualMap D T)) :=
    (lipschitzWith_one_iff_residualMap_cocoerciveOn_half (residualMap D T)).1 hT
  have hCoco : CocoerciveOn (βhalf : ℝ) D T := by
    refine ⟨hResidualCoco.1, ?_⟩
    intro x y
    simpa [residualMap] using hResidualCoco.2 x y
  exact ofFunction_isThreeStarMonotone_of_cocoerciveOn hCoco

end SetValuedOperator
