import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import BauschkeLean.Chap10.Definition_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section Seminormed

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- The norm, viewed as an extended-real-valued function, is sublinear. -/
theorem norm_sublinear : Sublinear (fun x : H ↦ (‖x‖ : EReal)) := by
  refine ⟨?_, ?_⟩
  · intro a ha x
    simp [EReal.real_smul_def, EReal.coe_mul, norm_smul, Real.norm_of_nonneg ha.le]
  · intro x y _ _
    change ((‖x + y‖ : ℝ) : EReal) ≤ (‖x‖ : EReal) + (‖y‖ : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact norm_add_le x y

/-- The squared norm is convex on the whole space of a real seminormed vector space. -/
theorem norm_sq_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ ‖x‖ ^ 2) := by
  exact (convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set H) (norm : H → ℝ)).pow
    (fun x _ ↦ norm_nonneg x) 2

end Seminormed

section NontrivialNormed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]

/-- On a nontrivial real normed space, the norm is not linear. -/
theorem norm_not_linear : ¬ IsLinearMap ℝ (norm : H → ℝ) := by
  intro hlin
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hsmul : ‖x‖ = -‖x‖ := by
    simpa using hlin.map_smul (-1 : ℝ) x
  have hnorm : ‖x‖ = 0 := by linarith
  exact hx (norm_eq_zero.mp hnorm)

-- Proof sketch: the norm is positively homogeneous and convex, but linearity would force
-- `‖(-1) • x‖ = (-1) • ‖x‖` for a nonzero vector `x`.
/-- Example 10.4 (i): if `H ≠ {0}`, then the norm is sublinear, but not linear. -/
theorem norm_sublinear_and_not_linear :
    Sublinear (fun x : H ↦ (‖x‖ : EReal)) ∧
      ¬ IsLinearMap ℝ (norm : H → ℝ) :=
  ⟨norm_sublinear, norm_not_linear⟩

/-- On a nontrivial real normed space, the squared norm is not positively homogeneous. -/
theorem norm_sq_not_positivelyHomogeneous :
    ¬ PositivelyHomogeneous (fun x : H ↦ ‖x‖ ^ 2) := by
  intro hph
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hscale : (2 * ‖x‖) ^ 2 = 2 * ‖x‖ ^ 2 := by
    simpa [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using
      hph.map_smul_of_pos (by norm_num : 0 < (2 : ℝ)) x
  have hsq_pos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  nlinarith

/-- On a nontrivial real normed space, the squared norm, viewed as an extended-real-valued
function, is not sublinear. -/
theorem norm_sq_not_sublinear :
    ¬ Sublinear (fun x : H ↦ (‖x‖ ^ 2 : EReal)) := by
  intro hsub
  have hph : PositivelyHomogeneous (fun x : H ↦ ‖x‖ ^ 2) := by
    intro a ha x
    have hscale :
        ((‖a • x‖ ^ 2 : ℝ) : EReal) = ((a * ‖x‖ ^ 2 : ℝ) : EReal) := by
      simpa [EReal.real_smul_def, EReal.coe_mul] using
        hsub.positivelyHomogeneous.map_smul_of_pos ha x
    exact EReal.coe_eq_coe_iff.mp hscale
  exact norm_sq_not_positivelyHomogeneous hph

-- Proof sketch: convexity of the squared norm is standard, while sublinearity would imply positive
-- homogeneity; evaluating at the scalar `2` contradicts quadratic scaling on a nonzero vector.
/-- Example 10.4 (ii): if `H ≠ {0}`, then the squared norm is convex, but not sublinear. -/
theorem norm_sq_convex_and_not_sublinear :
    ConvexOn ℝ (Set.univ : Set H) (fun x ↦ ‖x‖ ^ 2) ∧
      ¬ Sublinear (fun x : H ↦ (‖x‖ ^ 2 : EReal)) :=
  ⟨norm_sq_convexOn_univ, norm_sq_not_sublinear⟩

end NontrivialNormed
