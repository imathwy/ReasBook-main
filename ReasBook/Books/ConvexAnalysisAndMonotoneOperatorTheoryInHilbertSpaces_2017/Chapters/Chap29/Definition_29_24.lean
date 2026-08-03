import Mathlib.Analysis.InnerProductSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H]

noncomputable section

-- Semantic recall: `real_inner_self_eq_norm_sq` is the mathlib owner relating squared norms to
-- inner products; this item itself introduces the textbook halfspace and piecewise projection
-- formulas as explicit definitions.

section

variable [InnerProductSpace ℝ H]

/-- Definition 29.24 (1): the halfspace
`H(x, y) = {z ∈ H | ⟪z - y, x - y⟫ ≤ 0}` from (29.38). -/
def specialPolyhedronHalfspace (x y : H) : Set H :=
  {z | ⟪z - y, x - y⟫_ℝ ≤ 0}

/-- Membership in `specialPolyhedronHalfspace x y` is exactly the defining inner-product
inequality. -/
theorem mem_specialPolyhedronHalfspace_iff (x y z : H) :
    z ∈ specialPolyhedronHalfspace x y ↔ ⟪z - y, x - y⟫_ℝ ≤ 0 :=
  Iff.rfl

/-- The scalar `χ = ⟪x - y, y - z⟫` from (29.39). -/
def specialPolyhedronChi (x y z : H) : ℝ :=
  ⟪x - y, y - z⟫_ℝ

/-- `specialPolyhedronChi` is the inner product `⟪x - y, y - z⟫`. -/
theorem specialPolyhedronChi_def (x y z : H) :
    specialPolyhedronChi x y z = ⟪x - y, y - z⟫_ℝ :=
  rfl

end

/-- The scalar `μ = ‖x - y‖^2` from (29.39). -/
def specialPolyhedronMu (x y : H) : ℝ :=
  ‖x - y‖ ^ 2

/-- `specialPolyhedronMu` is the squared norm `‖x - y‖^2`. -/
theorem specialPolyhedronMu_def (x y : H) :
    specialPolyhedronMu x y = ‖x - y‖ ^ 2 :=
  rfl

/-- The scalar `ν = ‖y - z‖^2` from (29.39). -/
def specialPolyhedronNu (y z : H) : ℝ :=
  ‖y - z‖ ^ 2

/-- `specialPolyhedronNu` is the squared norm `‖y - z‖^2`. -/
theorem specialPolyhedronNu_def (y z : H) :
    specialPolyhedronNu y z = ‖y - z‖ ^ 2 :=
  rfl

section

variable [InnerProductSpace ℝ H]

/-- The scalar `ρ = μν - χ^2` from (29.39). -/
def specialPolyhedronRho (x y z : H) : ℝ :=
  specialPolyhedronMu x y * specialPolyhedronNu y z - specialPolyhedronChi x y z ^ 2

/-- `specialPolyhedronRho` is the scalar `μν - χ^2`. -/
theorem specialPolyhedronRho_def (x y z : H) :
    specialPolyhedronRho x y z =
      specialPolyhedronMu x y * specialPolyhedronNu y z - specialPolyhedronChi x y z ^ 2 :=
  rfl

/-- The first branch condition for `specialPolyhedronQ`: `ρ = 0` and `χ ≥ 0`. -/
def SpecialPolyhedronQFirstCase (x y z : H) : Prop :=
  specialPolyhedronRho x y z = 0 ∧ 0 ≤ specialPolyhedronChi x y z

/-- `SpecialPolyhedronQFirstCase x y z` is classically decidable. -/
noncomputable instance instDecidableSpecialPolyhedronQFirstCase (x y z : H) :
    Decidable (SpecialPolyhedronQFirstCase x y z) := by
  classical
  unfold SpecialPolyhedronQFirstCase
  infer_instance

/-- In `SpecialPolyhedronQFirstCase`, one has `ρ = 0`. -/
theorem SpecialPolyhedronQFirstCase.rho_eq_zero
    {x y z : H} (h : SpecialPolyhedronQFirstCase x y z) :
    specialPolyhedronRho x y z = 0 :=
  h.1

/-- In `SpecialPolyhedronQFirstCase`, one has `χ ≥ 0`. -/
theorem SpecialPolyhedronQFirstCase.chi_nonneg
    {x y z : H} (h : SpecialPolyhedronQFirstCase x y z) :
    0 ≤ specialPolyhedronChi x y z :=
  h.2

/-- The second branch condition for `specialPolyhedronQ`: `ρ > 0` and `χν ≥ ρ`. -/
def SpecialPolyhedronQSecondCase (x y z : H) : Prop :=
  0 < specialPolyhedronRho x y z ∧
    specialPolyhedronChi x y z * specialPolyhedronNu y z ≥ specialPolyhedronRho x y z

/-- `SpecialPolyhedronQSecondCase x y z` is classically decidable. -/
noncomputable instance instDecidableSpecialPolyhedronQSecondCase (x y z : H) :
    Decidable (SpecialPolyhedronQSecondCase x y z) := by
  classical
  unfold SpecialPolyhedronQSecondCase
  infer_instance

/-- In `SpecialPolyhedronQSecondCase`, one has `ρ > 0`. -/
theorem SpecialPolyhedronQSecondCase.rho_pos
    {x y z : H} (h : SpecialPolyhedronQSecondCase x y z) :
    0 < specialPolyhedronRho x y z :=
  h.1

/-- In `SpecialPolyhedronQSecondCase`, one has `χν ≥ ρ`. -/
theorem SpecialPolyhedronQSecondCase.chi_mul_nu_ge
    {x y z : H} (h : SpecialPolyhedronQSecondCase x y z) :
    specialPolyhedronChi x y z * specialPolyhedronNu y z ≥ specialPolyhedronRho x y z :=
  h.2

/-- Definition 29.24 (2): the map `Q` from Definition 29.24, written with the scalar auxiliaries
`χ`, `μ`, `ν`, and `ρ` from (29.39). -/
def specialPolyhedronQ (x y z : H) : H :=
  if _ : SpecialPolyhedronQFirstCase x y z then
    z
  else if _ : SpecialPolyhedronQSecondCase x y z then
    x + (1 + specialPolyhedronChi x y z / specialPolyhedronNu y z) • (z - y)
  else
    y + (specialPolyhedronNu y z / specialPolyhedronRho x y z) •
      (specialPolyhedronChi x y z • (x - y) + specialPolyhedronMu x y • (z - y))

/-- In the branch `ρ = 0` and `χ ≥ 0`, the map `specialPolyhedronQ` returns `z`. -/
theorem specialPolyhedronQ_of_rho_eq_zero_of_chi_nonneg
    (x y z : H)
    (hrho : specialPolyhedronRho x y z = 0)
    (hchi : 0 ≤ specialPolyhedronChi x y z) :
    specialPolyhedronQ x y z = z := by
  simp [specialPolyhedronQ, SpecialPolyhedronQFirstCase, hrho, hchi]

/-- In the branch `ρ > 0` and `χν ≥ ρ`, the map `specialPolyhedronQ` is given by the second
formula from Definition 29.24. -/
theorem specialPolyhedronQ_of_rho_pos_of_chi_mul_nu_ge
    (x y z : H)
    (hrho : 0 < specialPolyhedronRho x y z)
    (hchi : specialPolyhedronChi x y z * specialPolyhedronNu y z ≥ specialPolyhedronRho x y z) :
    specialPolyhedronQ x y z =
      x + (1 + specialPolyhedronChi x y z / specialPolyhedronNu y z) • (z - y) := by
  simp [specialPolyhedronQ, SpecialPolyhedronQFirstCase, SpecialPolyhedronQSecondCase,
    hrho.ne', hrho, hchi]

/-- In the branch `ρ > 0` and `χν < ρ`, the map `specialPolyhedronQ` is given by the third
formula from Definition 29.24. -/
theorem specialPolyhedronQ_of_rho_pos_of_chi_mul_nu_lt
    (x y z : H)
    (hrho : 0 < specialPolyhedronRho x y z)
    (hchi : specialPolyhedronChi x y z * specialPolyhedronNu y z <
      specialPolyhedronRho x y z) :
    specialPolyhedronQ x y z =
      y + (specialPolyhedronNu y z / specialPolyhedronRho x y z) •
        (specialPolyhedronChi x y z • (x - y) + specialPolyhedronMu x y • (z - y)) := by
  simp [specialPolyhedronQ, SpecialPolyhedronQFirstCase, SpecialPolyhedronQSecondCase,
    hrho.ne', hrho, not_le_of_gt hchi]

end

end
