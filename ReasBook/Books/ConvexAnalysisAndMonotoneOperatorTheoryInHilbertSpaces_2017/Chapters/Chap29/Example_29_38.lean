import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap07.Definition_7_14
import BauschkeLean.Chap07.Proposition_7_16
import BauschkeLean.Chap08.Proposition_8_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Set
open ERealFunction

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

-- Semantic recall: `lean_leansearch` surfaced mathlib's dual-space `NormedSpace.polar`, but the
-- verified project owner for the textbook polar set is the Chapter 7 set-valued notation `Cᵒ⊙`,
-- together with the Chapter 3 metric projector `projectionPoint`.

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "hCpolar" =>
  isChebyshev_of_nonempty_isClosed_convex
    (Exists.intro 0 (Set.zero_mem_polarSet C))
    (Set.polarSet_isClosed C)
    (Set.polarSet_convex C)

/-- The scalar equation in Example 29.38 for a positive parameter `ν ∈ ℝ_{++}`. -/
def SatisfiesPolarProjectionEquation
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (z : H) (ν : PosReal) : Prop :=
  let pC := P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
  (ν : ℝ) =
    ⟪z - (ν : ℝ) • pC (((ν : ℝ)⁻¹) • z),
      (ν : ℝ) • pC (((ν : ℝ)⁻¹) • z)⟫_ℝ

/-- A positive parameter solves the scalar equation of Example 29.38 exactly when it satisfies the
defining inner-product identity. -/
@[simp] theorem satisfiesPolarProjectionEquation_iff (z : H) (ν : PosReal) :
    SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z ν ↔
      (ν : ℝ) = ⟪z - (ν : ℝ) • P[C, hC] (((ν : ℝ)⁻¹) • z),
        (ν : ℝ) • P[C, hC] (((ν : ℝ)⁻¹) • z)⟫_ℝ :=
  Iff.rfl

/-- Example 29.38 (1): if `C` is a nonempty bounded closed convex subset of a real Hilbert space
and `z ∉ Cᵒ⊙`, then the scalar equation
`ν = ⟪z - ν • P[C, hC] ((ν : ℝ)⁻¹ • z),
ν • P[C, hC] ((ν : ℝ)⁻¹ • z)⟫_ℝ` has a unique solution
`ν ∈ ℝ_{++}`. -/
theorem existsUnique_posReal_projectionEquation_of_not_mem_polarSet
    (hC_bounded : Bornology.IsBounded C) {z : H} (hz : z ∉ Cᵒ⊙) :
    ∃! ν : PosReal,
      SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z ν := sorry

/-- Example 29.38 (2): if `ν̄` is the unique positive solution of the scalar equation, then
`P[Cᵒ⊙, hCpolar] z = z - ν̄ • P[C, hC] (ν̄⁻¹ • z)`. -/
theorem projectionPoint_polarSet_eq_sub_smul_projectionPoint_of_projectionEquation
    {z : H} {νbar : PosReal}
    (hνbar : SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z νbar)
    (hνbar_unique :
      ∀ ν : PosReal,
        SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z ν → ν = νbar) :
    P[Cᵒ⊙, hCpolar] z = z - (νbar : ℝ) • P[C, hC] (((νbar : ℝ)⁻¹) • z) := sorry

/-- Example 29.38 (3): if `ν̄` is the unique positive solution of the scalar equation, then
`ν̄ = ⟪P[Cᵒ⊙, hCpolar] z, z - P[Cᵒ⊙, hCpolar] z⟫_ℝ`. -/
theorem eq_real_inner_projectionPoint_polarSet_residual_of_projectionEquation
    {z : H} {νbar : PosReal}
    (hνbar : SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z νbar)
    (hνbar_unique :
      ∀ ν : PosReal,
        SatisfiesPolarProjectionEquation hC_nonempty hC_closed hC_convex z ν → ν = νbar) :
    (νbar : ℝ) = ⟪P[Cᵒ⊙, hCpolar] z, z - P[Cᵒ⊙, hCpolar] z⟫_ℝ := sorry

end
