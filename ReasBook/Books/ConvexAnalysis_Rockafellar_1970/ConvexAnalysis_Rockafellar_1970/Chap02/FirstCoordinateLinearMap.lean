import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

section

local notation "R1" => EuclideanSpace ℝ (Fin 1)
local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Bridge/view utilities for the recurring first-coordinate projection examples in Chapter 2.

- `realToFin1` and `fin1ToReal` are the canonical linear identifications between `ℝ` and
  `R¹ = EuclideanSpace ℝ (Fin 1)`.
- `firstCoordinateLinearMap` is the first-coordinate projection `R² → R¹`.

These declarations are not new source-facing mathematics; they are the shared coordinate bridge
used to express textbook first-coordinate formulas through the chapter owner
`Function.linearImage`.
-/

/-- The canonical linear identification of `ℝ` with `EuclideanSpace ℝ (Fin 1)`. -/
def realToFin1 : ℝ →ₗ[ℝ] R1 :=
  ((LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm.toLinearEquiv).toLinearMap

/-- The canonical linear identification of `EuclideanSpace ℝ (Fin 1)` with `ℝ`. -/
def fin1ToReal : R1 →ₗ[ℝ] ℝ :=
  (((EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ)).toLinearMap)

/-- `fin1ToReal` is the inverse of the canonical bridge `realToFin1`. -/
@[simp] theorem fin1ToReal_realToFin1 (x : ℝ) :
    fin1ToReal (realToFin1 x) = x := by
  simp [realToFin1, fin1ToReal]

/-- `realToFin1` is the inverse of the canonical bridge `fin1ToReal`. -/
@[simp] theorem realToFin1_fin1ToReal (x : R1) :
    realToFin1 (fin1ToReal x) = x := by
  ext i
  fin_cases i
  simp [realToFin1, fin1ToReal]

/-- The first-coordinate projection `R² → R¹`. -/
def firstCoordinateLinearMap : R2 →ₗ[ℝ] R1 :=
  realToFin1.comp (EuclideanSpace.projₗ (0 : Fin 2))

/-- The adjoint of `firstCoordinateLinearMap` inserts the scalar in the first coordinate. -/
theorem firstCoordinateLinearMap_adjoint_apply (x : R1) :
    firstCoordinateLinearMap.adjoint x = EuclideanSpace.single (0 : Fin 2) (fin1ToReal x) := by
  have hrealToFin1 : LinearMap.adjoint realToFin1 = fin1ToReal := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro u v
    simp [realToFin1, fin1ToReal, PiLp.inner_apply]
  have hproj :
      LinearMap.adjoint (EuclideanSpace.projₗ (0 : Fin 2)) =
        ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro u v
    simp [LinearMap.smulRight_apply, PiLp.inner_apply]
  have hadjoint :
      firstCoordinateLinearMap.adjoint =
        fin1ToReal.smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by
    rw [firstCoordinateLinearMap, LinearMap.adjoint_comp, hrealToFin1, hproj]
    ext y i
    fin_cases i <;> simp [LinearMap.comp_apply, LinearMap.smulRight_apply]
  rw [hadjoint]
  ext i
  fin_cases i <;> simp [LinearMap.smulRight_apply]

/-- The adjoint of `firstCoordinateLinearMap` sends the canonical scalar coordinate bridge to the
first basis vector insertion. -/
@[simp] theorem firstCoordinateLinearMap_adjoint_realToFin1 (x : ℝ) :
    firstCoordinateLinearMap.adjoint (realToFin1 x) = EuclideanSpace.single (0 : Fin 2) x := by
  simp [firstCoordinateLinearMap_adjoint_apply]

end
