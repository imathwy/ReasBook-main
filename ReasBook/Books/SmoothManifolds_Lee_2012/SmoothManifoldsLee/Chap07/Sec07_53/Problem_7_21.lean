import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_53.Problem_7_20

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` is unavailable in this environment; local mathlib/repository inspection
-- verified that the hint "isomorphic groups have isomorphic centers" is already available as
-- `Subgroup.centerCongr`.

open scoped MatrixGroups

/-- Problem 7-21 (1): if `n > 1`, then `O(n)` is not group-isomorphic to the direct product
`SO(n) × O(1)`. -/
theorem orthogonalGroup_not_mulEquiv_specialOrthogonal_prod_orthogonal_one
    {n : ℕ} (hn : 1 < n) :
    ¬ Nonempty
      ((Matrix.orthogonalGroup (Fin n) ℝ) ≃*
        (Matrix.specialOrthogonalGroup (Fin n) ℝ × Matrix.orthogonalGroup (Fin 1) ℝ)) := sorry

/-- Problem 7-21 (2): if `n > 1`, then `U(n)` is not group-isomorphic to the direct product
`SU(n) × U(1)`. -/
theorem unitaryGroup_not_mulEquiv_specialUnitary_prod_unitary_one
    {n : ℕ} (hn : 1 < n) :
    ¬ Nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ) ≃*
        (Matrix.specialUnitaryGroup (Fin n) ℂ × Matrix.unitaryGroup (Fin 1) ℂ)) := sorry

/-- Problem 7-21 (3): if `n > 1`, then `GL(n, ℝ)` is not group-isomorphic to the direct product
`SL(n, ℝ) × ℝˣ`. -/
theorem generalLinearGroup_real_not_mulEquiv_specialLinear_prod_units
    {n : ℕ} (hn : 1 < n) :
    ¬ Nonempty
      ((Matrix.GeneralLinearGroup (Fin n) ℝ) ≃* (SL(n, ℝ) × ℝˣ)) := sorry

/-- Problem 7-21 (4): if `n > 1`, then `GL(n, ℂ)` is not group-isomorphic to the direct product
`SL(n, ℂ) × ℂˣ`. -/
theorem generalLinearGroup_complex_not_mulEquiv_specialLinear_prod_units
    {n : ℕ} (hn : 1 < n) :
    ¬ Nonempty
      ((Matrix.GeneralLinearGroup (Fin n) ℂ) ≃* (SL(n, ℂ) × ℂˣ)) := sorry
