module

public import Mathlib.Topology.Compactification.OnePoint.Sphere

@[expose] public section

open Metric Module

namespace OnePoint

/-- The one-point compactification of `ℝ` as the unit circle. -/
noncomputable def realHomeomorphSphere :
    OnePoint ℝ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- The one-point compactification of `ℝ²` as the unit sphere `S²`. -/
noncomputable def planeHomeomorphSphere :
    OnePoint (EuclideanSpace ℝ (Fin 2)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- The extended complex plane as the unit sphere `S²`. -/
noncomputable def complexHomeomorphSphere :
    OnePoint ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp)

end OnePoint
