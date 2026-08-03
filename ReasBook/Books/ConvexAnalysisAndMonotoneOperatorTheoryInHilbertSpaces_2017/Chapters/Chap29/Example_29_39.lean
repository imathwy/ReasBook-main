import Mathlib.Analysis.Matrix.Order
import BauschkeLean.Chap29.Proposition_29_37

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction

/- Source/core/bridge triage for Example 29.39:
- `source-facing`: the quadratic objective on `ℝ^N` and the displayed matrix resolvent formula.
- `core/canonical`: `lowerLevelSet f.toEReal.asEReal ζ` and the projection API from
  Proposition 29.37.
- `bridge/view`: this file specializes the Chapter 29 lower-level-set projection owner to the
  concrete quadratic matrix model. -/

-- Semantic recall: Proposition 29.37 already formalizes the projector of a lower level set as a
-- proximal point. This file specializes that owner surface to the concrete quadratic matrix model
-- from Example 29.39.

section

variable {N : ℕ}

/-- The quadratic objective from Example 29.39 on `ℝ^N`, represented as `Fin N → ℝ`. -/
noncomputable def example29_39_quadratic
    (A : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) :
    (Fin N → ℝ) → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (A.mulVec x) + dotProduct x u

/-- Evaluating `example29_39_quadratic` expands to the displayed quadratic-plus-affine formula. -/
@[simp] theorem example29_39_quadratic_apply
    (A : Matrix (Fin N) (Fin N) ℝ) (u x : Fin N → ℝ) :
    example29_39_quadratic A u x =
      (1 / 2 : ℝ) * dotProduct x (A.mulVec x) + dotProduct x u := rfl

section QuadraticLowerLevelSet

variable (A : Matrix (Fin N) (Fin N) ℝ) (u z : Fin N → ℝ) {ζ : ℝ}

local notation "f" => example29_39_quadratic A u

/-- The Example 29.39 quadratic lower level set is Chebyshev under the source assumptions, so the
canonical projection point `P[C, hC] z` is available on the Chapter 29 lower-level-set owner
surface. -/
theorem example29_39_lowerLevelSet_isChebyshev
    (hA_symm : A.IsSymm) (hA_psd : A.PosSemidef)
    (hζ :
      ζ ∈ Set.Ioo (sInf (Set.range f)) (f z)) :
    IsChebyshev (lowerLevelSet (example29_39_quadratic A u).toEReal.asEReal ζ) := sorry

/-- Example 29.39 (1): for the quadratic function
`f(x) = (1 / 2) ⟪x, A x⟫ + ⟪x, u⟫` with symmetric positive semidefinite matrix `A`,
if `ζ ∈ ]inf f(ℝ^N), f(z)[` and `C = lev_{≤ ζ} f`, then the metric projection of `z`
onto `C` lies on the level set `f = ζ` and is given by the resolvent formula
`(Id + ν̄ A)⁻¹ (z - ν̄ u)` for some `ν̄ ∈ ℝ_{++}`. -/
theorem exists_posReal_projectionPoint_eq_level_and_matrix_inverse
    (hA_symm : A.IsSymm) (hA_psd : A.PosSemidef)
    (hζ : ζ ∈ Set.Ioo (sInf (Set.range f)) (f z)) :
    ∃ νbar : PosReal,
      let C := lowerLevelSet (example29_39_quadratic A u).toEReal.asEReal ζ
      f (P[C, example29_39_lowerLevelSet_isChebyshev A u z hA_symm hA_psd hζ] z) = ζ ∧
        P[C, example29_39_lowerLevelSet_isChebyshev A u z hA_symm hA_psd hζ] z =
          (((1 : Matrix (Fin N) (Fin N) ℝ) + (νbar : ℝ) • A)⁻¹).mulVec
            (z - (νbar : ℝ) • u) := sorry

/-- Example 29.39 (2): with the same quadratic data and lower level set
`C = lev_{≤ ζ} f`, any vector `x` satisfying the system
`f(x) = ζ` and `x = (Id + ν̄ A)⁻¹ (z - ν̄ u)` for some `ν̄ ∈ ℝ_{++}` must
coincide with the metric projection of `z` onto `C`; hence that system has a
unique solution in `x`. -/
theorem eq_projectionPoint_of_eq_level_and_matrix_inverse
    (hA_symm : A.IsSymm) (hA_psd : A.PosSemidef)
    (hζ : ζ ∈ Set.Ioo (sInf (Set.range f)) (f z))
    {νbar : PosReal} {x : Fin N → ℝ}
    (hx_level : f x = ζ)
    (hx_inverse :
      x =
        (((1 : Matrix (Fin N) (Fin N) ℝ) + (νbar : ℝ) • A)⁻¹).mulVec
          (z - (νbar : ℝ) • u)) :
    x =
      P[lowerLevelSet (example29_39_quadratic A u).toEReal.asEReal ζ,
        example29_39_lowerLevelSet_isChebyshev A u z hA_symm hA_psd hζ] z := sorry

end QuadraticLowerLevelSet

end
