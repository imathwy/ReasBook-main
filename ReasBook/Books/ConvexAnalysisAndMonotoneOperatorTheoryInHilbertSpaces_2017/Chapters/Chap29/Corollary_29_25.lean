import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap29.Definition_29_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {x y z : H}

local notation "C" => specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z
local notation "χ" => specialPolyhedronChi x y z
local notation "ρ" => specialPolyhedronRho x y z
local notation "emptyCase" => ρ = 0 ∧ χ < 0
local notation "feasibleCase" => (ρ = 0 ∧ 0 ≤ χ) ∨ 0 < ρ
local notation "canonicalFeasibleCase" => SpecialPolyhedronQFirstCase x y z ∨ 0 < ρ

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection owners, while
-- the verified local API for Corollary 29.25 is `specialPolyhedronHalfspace`,
-- `specialPolyhedronQ`, and the project-local metric projector notation `P[C, hC]`.

/-- The feasible branch in Corollary 29.25 is exactly `[(ρ = 0 and χ ≥ 0)] or ρ > 0`; this is
the source-facing formulation of the canonical branch
`SpecialPolyhedronQFirstCase x y z ∨ 0 < ρ`. -/
theorem specialPolyhedronHalfspaceInter_feasibleCase_iff :
    feasibleCase ↔ canonicalFeasibleCase :=
  Iff.rfl

/-- Corollary 29.25 (1): for
`C = specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z`, exactly one of the two
source cases holds: either `ρ = 0` and `χ < 0`, or `[(ρ = 0 and χ ≥ 0)] or ρ > 0`, where
`χ = ⟪x - y, y - z⟫` and `ρ = ‖x - y‖^2 * ‖y - z‖^2 - χ^2`. -/
theorem specialPolyhedronHalfspaceInter_case_partition :
    Xor' emptyCase feasibleCase := sorry

/-- Corollary 29.25 (2): if `ρ = 0` and `χ < 0`, then
`C = specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z` is empty. -/
theorem specialPolyhedronHalfspaceInter_eq_empty_of_rho_eq_zero_of_chi_neg
    (hrho : ρ = 0) (hchi : χ < 0) :
    C = ∅ := sorry

/-- Corollary 29.25 (3): if `[(ρ = 0 and χ ≥ 0)] or ρ > 0`, then
`C = specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z` is nonempty. -/
theorem specialPolyhedronHalfspaceInter_nonempty_of_feasible_case
    (hcase : feasibleCase) :
    Set.Nonempty C := sorry

variable [CompleteSpace H]

/-- Under the feasible branch of Corollary 29.25, the intersection
`specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z` is Chebyshev. -/
theorem specialPolyhedronHalfspaceInter_isChebyshev_of_feasible_case
    (hcase : feasibleCase) :
    IsChebyshev C := sorry

/-- Corollary 29.25 (4): if `[(ρ = 0 and χ ≥ 0)] or ρ > 0`, then formula `(29.41)` holds:
the metric projection of `x` onto
`C = specialPolyhedronHalfspace x y ∩ specialPolyhedronHalfspace y z` is `Q(x, y, z)`. -/
theorem projectionPoint_specialPolyhedronHalfspaceInter_eq_specialPolyhedronQ_of_feasible_case
    (hcase : feasibleCase) :
    P[C, specialPolyhedronHalfspaceInter_isChebyshev_of_feasible_case hcase] x =
      specialPolyhedronQ x y z := sorry

end
