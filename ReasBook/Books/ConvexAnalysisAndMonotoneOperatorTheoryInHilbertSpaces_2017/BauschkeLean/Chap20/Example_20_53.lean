import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 20.53: a skew-adjoint continuous linear map has vanishing quadratic
pairing `⟪y, A y⟫_ℝ`. -/
private theorem inner_map_self_eq_zero_of_adjoint_eq_neg
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) (y : H) :
    ⟪y, A y⟫_ℝ = 0 := by
  -- Rewrite `⟪y, A y⟫` through the adjoint and use the skew-adjoint hypothesis.
  have hskew : ⟪y, A y⟫_ℝ = -⟪y, A y⟫_ℝ := by
    calc
      ⟪y, A y⟫_ℝ = ⟪A y, y⟫_ℝ := by rw [real_inner_comm]
      _ = ⟪y, A.adjoint y⟫_ℝ := by
        simpa [ContinuousLinearMap.adjoint] using
          (ContinuousLinearMap.adjoint_inner_right A y y).symm
      _ = ⟪y, (-A) y⟫_ℝ := by rw [hA]
      _ = -⟪y, A y⟫_ℝ := by simp
  linarith

/-- Helper for Example 20.53: the Fitzpatrick function of the singleton-valued operator induced by
`A` rewrites to the supremum of the residual linear functional `y ↦ ⟪y, u - A x⟫_ℝ`. -/
private theorem fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup_inner_residual
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ⨆ y : H, ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) := by
  -- Expand the graph-indexed supremum and normalize each graph-point summand.
  rw [SetValuedOperator.fitzpatrickFunction]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro p
    rcases p with ⟨⟨y, v⟩, hp⟩
    rw [SetValuedOperator.mem_graph] at hp
    have hp' : v = A y := by
      simpa [Set.mem_singleton_iff] using hp
    subst v
    have hxy : ⟪x, A y⟫_ℝ = -⟪y, A x⟫_ℝ := by
      calc
        ⟪x, A y⟫_ℝ = ⟪A y, x⟫_ℝ := by rw [real_inner_comm]
        _ = ⟪y, A.adjoint x⟫_ℝ := by
          simpa [ContinuousLinearMap.adjoint] using
            (ContinuousLinearMap.adjoint_inner_right A y x).symm
        _ = ⟪y, (-A) x⟫_ℝ := by rw [hA]
        _ = -⟪y, A x⟫_ℝ := by simp
    have hscalar :
        ((⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ : ℝ) : EReal) =
          ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) := by
      -- Use skew-adjointness to eliminate the diagonal term and identify the residual pairing.
      apply congrArg (fun t : ℝ => (t : EReal))
      calc
        ⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ
            = ⟪y, u⟫_ℝ - ⟪y, A x⟫_ℝ - ⟪y, A y⟫_ℝ := by
                rw [hxy]
                abel_nf
        _ = ⟪y, u - A x⟫_ℝ - ⟪y, A y⟫_ℝ := by rw [← inner_sub_right]
        _ = ⟪y, u - A x⟫_ℝ := by
          rw [inner_map_self_eq_zero_of_adjoint_eq_neg A hA y, sub_zero]
    rw [hscalar]
    exact le_iSup (fun y : H ↦ ((⟪y, u - A x⟫_ℝ : ℝ) : EReal)) y
  · refine iSup_le ?_
    intro y
    have hy_graph : (y, A y) ∈ gra A.toSetValuedOperator := by
      rw [SetValuedOperator.mem_graph]
      simp
    let p : gra A.toSetValuedOperator := ⟨(y, A y), hy_graph⟩
    have hxy : ⟪x, A y⟫_ℝ = -⟪y, A x⟫_ℝ := by
      calc
        ⟪x, A y⟫_ℝ = ⟪A y, x⟫_ℝ := by rw [real_inner_comm]
        _ = ⟪y, A.adjoint x⟫_ℝ := by
          simpa [ContinuousLinearMap.adjoint] using
            (ContinuousLinearMap.adjoint_inner_right A y x).symm
        _ = ⟪y, (-A) x⟫_ℝ := by rw [hA]
        _ = -⟪y, A x⟫_ℝ := by simp
    have hscalar :
        ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) =
          ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) := by
      -- The canonical graph witness `(y, A y)` gives the same normalized residual summand.
      apply congrArg (fun t : ℝ => (t : EReal))
      change ⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ = ⟪y, u - A x⟫_ℝ
      calc
        ⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ
            = ⟪y, u⟫_ℝ - ⟪y, A x⟫_ℝ - ⟪y, A y⟫_ℝ := by
                rw [hxy]
                abel_nf
        _ = ⟪y, u - A x⟫_ℝ - ⟪y, A y⟫_ℝ := by rw [← inner_sub_right]
        _ = ⟪y, u - A x⟫_ℝ := by
          rw [inner_map_self_eq_zero_of_adjoint_eq_neg A hA y, sub_zero]
    have hp_le :
        ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) ≤
          ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) := by
      rw [hscalar]
    exact le_iSup_of_le p hp_le

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 20.53: if `w ≠ 0`, then the residual linear functional
`y ↦ ⟪y, w⟫_ℝ` is unbounded above, so its `EReal` supremum is `⊤`. -/
private theorem iSup_coe_realInner_eq_top_of_ne_zero
    (w : H) (hw : w ≠ 0) :
    (⨆ y : H, ((⟪y, w⟫_ℝ : ℝ) : EReal)) = ⊤ := by
  -- Push any finite upper bound past a real midpoint, then exceed it along the ray `ℝ≥0 • w`.
  rw [iSup_eq_top]
  intro b hb
  rcases (EReal.lt_iff_exists_real_btwn).mp hb with ⟨r, hbr, -⟩
  have hnorm_sq_pos : 0 < ‖w‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hw)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r / (‖w‖ ^ 2) < n := exists_nat_gt (r / (‖w‖ ^ 2))
  have hrn : r < (n : ℝ) * ‖w‖ ^ 2 := by
    exact (_root_.div_lt_iff₀ hnorm_sq_pos).mp hn
  have hinner_cast :
      ((⟪(n : ℝ) • w, w⟫_ℝ : ℝ) : EReal) = (((n : ℝ) * ‖w‖ ^ 2 : ℝ) : EReal) := by
    congr 1
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  refine ⟨(n : ℝ) • w, ?_⟩
  refine lt_trans hbr ?_
  rw [hinner_cast]
  exact EReal.coe_lt_coe_iff.mpr hrn

end

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the skew-adjoint hypothesis forces `⟪y, A y⟫_ℝ = 0`, so the
-- supremand becomes `⟪y, u - A x⟫_ℝ`. If `u = A x`, every term is `0`; if `u ≠ A x`, choose `y`
-- along `u - A x` to make the supremum equal `⊤`. This is exactly the graph indicator.
/-- Example 20.53: if `A.adjoint = -A`, then the Fitzpatrick function of the singleton-valued
operator induced by `A` is the extended-real indicator of its graph. -/
theorem fitzpatrickFunction_eq_indicator_graph_of_adjoint_eq_neg
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) :
    F[A.toSetValuedOperator] =
      (ι[gra A.toSetValuedOperator]).asEReal := by
  funext p
  rcases p with ⟨x, u⟩
  by_cases hxu : u = A x
  · have hgraph : (x, u) ∈ gra A.toSetValuedOperator := by
      rw [SetValuedOperator.mem_graph]
      simp [hxu]
    -- On the graph, the normalized residual is identically zero, so both sides evaluate to `0`.
    calc
      F[A.toSetValuedOperator] (x, u)
          = ⨆ y : H, ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) := by
              rw [fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup_inner_residual A hA]
      _ = 0 := by simp [hxu]
      _ = (ι[gra A.toSetValuedOperator] (x, u) : EReal) := by
            simp [ERealFunction.indicator_apply, hgraph]
  · have hnot_graph : (x, u) ∉ gra A.toSetValuedOperator := by
      simpa [SetValuedOperator.mem_graph, Set.mem_singleton_iff] using hxu
    have hresidual : u - A x ≠ 0 := by
      intro hzero
      apply hxu
      exact sub_eq_zero.mp hzero
    -- Off the graph, the residual is nonzero, so the normalized supremum is unbounded above.
    calc
      F[A.toSetValuedOperator] (x, u)
          = ⨆ y : H, ((⟪y, u - A x⟫_ℝ : ℝ) : EReal) := by
              rw [fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup_inner_residual A hA]
      _ = ⊤ := iSup_coe_realInner_eq_top_of_ne_zero (u - A x) hresidual
      _ = (ι[gra A.toSetValuedOperator] (x, u) : EReal) := by
            simp [ERealFunction.indicator_apply, hnot_graph]

end ContinuousLinearMap
