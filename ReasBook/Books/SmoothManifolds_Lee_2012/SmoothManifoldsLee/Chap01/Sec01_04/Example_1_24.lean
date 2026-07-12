import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

universe u

section Linear

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The basis coordinate map sends a coordinate vector to the corresponding linear combination of
the basis vectors. -/
theorem basis_coordinate_apply
    (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
    ((EuclideanSpace.equiv (Fin (Module.finrank ℝ V)) ℝ).toLinearEquiv.trans b.equivFun.symm) x =
      ∑ i, x i • b i := by
  simp

end Linear

section Smooth

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) in
/- Example 1.24 (1): the chart determined by an ordered basis is the canonical diffeomorphism
obtained from `EuclideanSpace.equiv`, `Basis.equivFun`, and
`ContinuousLinearEquiv.toDiffeomorph`. -/
#check
  (let e : V ≃ₗ[ℝ] Fin (Module.finrank ℝ V) → ℝ := b.equivFun
   (((EuclideanSpace.equiv (Fin (Module.finrank ℝ V)) ℝ).trans
        e.symm.toContinuousLinearEquiv).toDiffeomorph :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃ₘ[ℝ] V))

/-- The change-of-coordinates map from the coordinates defined by `b` to those defined by `b'`. -/
def basis_coordinate_change
    (b b' : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
  let e : V ≃ₗ[ℝ] Fin (Module.finrank ℝ V) → ℝ := b.equivFun
  let e' : V ≃ₗ[ℝ] Fin (Module.finrank ℝ V) → ℝ := b'.equivFun
  ((EuclideanSpace.equiv (Fin (Module.finrank ℝ V)) ℝ).trans
      ((e.symm.trans e').toContinuousLinearEquiv)).trans
    (EuclideanSpace.equiv (Fin (Module.finrank ℝ V)) ℝ).symm

/-- Example 1.24 (2): the transition map between the charts defined by two ordered bases of `V`
is an invertible linear map and hence a diffeomorphism. -/
theorem basis_coordinate_change_contDiff
    (b b' : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    ContDiff ℝ ⊤ (basis_coordinate_change b b') :=
  (basis_coordinate_change b b').contDiff

/- Lee's finite-dimensional model-space example is a specialization of the canonical
`IsManifold 𝓘(ℝ, V) ⊤ V` instance, which in fact holds for every real normed vector space. -/
#check (inferInstance : IsManifold 𝓘(ℝ, V) ⊤ V)

end Smooth
