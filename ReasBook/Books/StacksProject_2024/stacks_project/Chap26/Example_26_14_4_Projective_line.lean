import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PolynomialAlgebra

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: mathlib already provides the canonical scheme owner `AlgebraicGeometry.Proj`
-- together with the projective-spectrum basic-open and affine-scheme API.

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section ProjectiveLine

variable (k : Type u) [Field k]

/-- The standard grading on the two-variable polynomial ring over `k`. -/
abbrev projectiveLineGrading : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The first homogeneous coordinate on the standard projective line model. -/
abbrev projectiveLineX : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0

/-- The second homogeneous coordinate on the standard projective line model. -/
abbrev projectiveLineY : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 1

/-- The standard homogeneous coordinates on `k[X,Y]`, indexed by `Fin 2`. -/
abbrev projectiveLineCoordinate (i : Fin 2) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X i

/-- Example 26.14.4 (Projective line) (1): the projective line over a field `k` is the canonical
projective spectrum of the standard grading on `k[X,Y]`. -/
@[stacks 01JE]
abbrev projectiveLine : Scheme :=
  Proj (projectiveLineGrading k)

/-- The standard chart `D_+(X)` on the projective line `P^1_k`. -/
@[stacks 01JE]
abbrev projectiveLineChartX : (Proj (projectiveLineGrading k)).Opens :=
  Proj.basicOpen (projectiveLineGrading k) (projectiveLineX k)

/-- The standard chart `D_+(Y)` on the projective line `P^1_k`. -/
@[stacks 01JE]
abbrev projectiveLineChartY : (Proj (projectiveLineGrading k)).Opens :=
  Proj.basicOpen (projectiveLineGrading k) (projectiveLineY k)

/-- The standard affine open `D_+(Y - X)` on `P^1_k`, corresponding to the complement of `1`. -/
@[stacks 01JE]
abbrev projectiveLineAwayOne : (Proj (projectiveLineGrading k)).Opens :=
  Proj.basicOpen (projectiveLineGrading k) (projectiveLineY k - projectiveLineX k)

/-- The first homogeneous coordinate has degree `1` in the standard grading on `k[X,Y]`. -/
theorem projectiveLineX_mem_grading_one :
    projectiveLineX k ∈ projectiveLineGrading k 1 := by
  simpa [projectiveLineX, MvPolynomial.mem_homogeneousSubmodule] using
    (MvPolynomial.isHomogeneous_X k (0 : Fin 2))

/-- The second homogeneous coordinate has degree `1` in the standard grading on `k[X,Y]`. -/
theorem projectiveLineY_mem_grading_one :
    projectiveLineY k ∈ projectiveLineGrading k 1 := by
  simpa [projectiveLineY, MvPolynomial.mem_homogeneousSubmodule] using
    (MvPolynomial.isHomogeneous_X k (1 : Fin 2))

/-- The linear form `Y - X` has degree `1` in the standard grading on `k[X,Y]`. -/
theorem projectiveLineY_sub_X_mem_grading_one :
    projectiveLineY k - projectiveLineX k ∈ projectiveLineGrading k 1 := by
  exact (projectiveLineGrading k 1).sub_mem
    (projectiveLineY_mem_grading_one k)
    (projectiveLineX_mem_grading_one k)

/-- The two standard coordinates generate `k[X,Y]` over `k`. -/
theorem projectiveLine_adjoin_XY :
    Algebra.adjoin (projectiveLineGrading k 0) (Set.range (projectiveLineCoordinate k)) = ⊤ := by
  sorry

/-- Example 26.14.4 (Projective line) (2): the two standard basic opens `D_+(X)` and `D_+(Y)`
cover `P^1_k`. -/
@[stacks 01JE]
theorem projectiveLineCharts_cover :
    projectiveLineChartX k ⊔ projectiveLineChartY k = ⊤ := by
  have hcover :
      (⨆ i : Fin 2, Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k i)) = ⊤ := by
    simpa [projectiveLineCoordinate] using
      (Proj.iSup_basicOpen_eq_top' (projectiveLineGrading k)
        (projectiveLineCoordinate k)
        (fun i ↦ by
          fin_cases i
          · exact ⟨1, projectiveLineX_mem_grading_one k⟩
          · exact ⟨1, projectiveLineY_mem_grading_one k⟩)
        (projectiveLine_adjoin_XY k))
  have hiSup_two :
      (⨆ i : Fin 2, Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k i)) =
        projectiveLineChartX k ⊔ projectiveLineChartY k := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i ↦ ?_
      fin_cases i
      · simpa [projectiveLineChartX, projectiveLineChartY, projectiveLineCoordinate] using
          (le_sup_left :
            Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k 0) ≤
              projectiveLineChartX k ⊔ projectiveLineChartY k)
      · simpa [projectiveLineChartX, projectiveLineChartY, projectiveLineCoordinate] using
          (le_sup_right :
            Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k 1) ≤
              projectiveLineChartX k ⊔ projectiveLineChartY k)
    · refine sup_le ?_ ?_
      · simpa [projectiveLineChartX, projectiveLineCoordinate] using
          (le_iSup
            (fun i : Fin 2 ↦ Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k i))
            0)
      · simpa [projectiveLineChartY, projectiveLineCoordinate] using
          (le_iSup
            (fun i : Fin 2 ↦ Proj.basicOpen (projectiveLineGrading k) (projectiveLineCoordinate k i))
            1)
  rw [← hiSup_two]
  exact hcover

/-- Example 26.14.4 (Projective line) (3): the standard chart `D_+(X)` of `P^1_k` is affine. -/
@[stacks 01JE]
theorem projectiveLineChartX_isAffineOpen :
    IsAffineOpen (projectiveLineChartX k) := by
  simpa [projectiveLineChartX] using
    (Proj.isAffineOpen_basicOpen (projectiveLineGrading k) (projectiveLineX k)
      (projectiveLineX_mem_grading_one k) (by decide))

/-- Example 26.14.4 (Projective line) (4): the standard chart `D_+(Y)` of `P^1_k` is affine. -/
@[stacks 01JE]
theorem projectiveLineChartY_isAffineOpen :
    IsAffineOpen (projectiveLineChartY k) := by
  simpa [projectiveLineChartY] using
    (Proj.isAffineOpen_basicOpen (projectiveLineGrading k) (projectiveLineY k)
      (projectiveLineY_mem_grading_one k) (by decide))

/-- Example 26.14.4 (Projective line) (5): the projective line over a field is not affine. -/
@[stacks 01JE]
theorem projectiveLine_not_isAffine :
    ¬ IsAffine (projectiveLine k) := sorry

/-- Example 26.14.4 (Projective line) (6): the open subset `P^1_k \setminus {1}`, represented by
`D_+(Y - X)`, is affine. -/
@[stacks 01JE]
theorem projectiveLineAwayOne_isAffineOpen :
    IsAffineOpen (projectiveLineAwayOne k) := by
  simpa [projectiveLineAwayOne] using
    (Proj.isAffineOpen_basicOpen (projectiveLineGrading k)
      (projectiveLineY k - projectiveLineX k)
      (projectiveLineY_sub_X_mem_grading_one k) (by decide))

end ProjectiveLine

end AlgebraicGeometry
