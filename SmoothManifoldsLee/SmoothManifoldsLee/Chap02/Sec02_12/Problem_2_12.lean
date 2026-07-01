import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projectivization.Action

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

universe u

variable {n : ℕ}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The complex-linear equivalence sending the standard coordinates on `ℂ^n` to the given basis
of `V`. -/
def complex_basis_projectivization_linearEquiv (b : Module.Basis (Fin n) ℂ V) :
    EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] V :=
  (EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv.trans b.equivFun.symm

/-- The projectivized map determined by a complex basis of `V`. -/
def complex_basis_projectivization_map (b : Module.Basis (Fin n) ℂ V) :
    ℙ ℂ (EuclideanSpace ℂ (Fin n)) → ℙ ℂ V :=
  Projectivization.map (complex_basis_projectivization_linearEquiv b).toLinearMap
    (complex_basis_projectivization_linearEquiv b).injective

/-- A smooth structure on the complex projectivization `ℙ ℂ V`, modeled on `ℂ^(n - 1)` as a real
smooth manifold. -/
structure ComplexProjectivizationSmoothStructure (n : ℕ) (V : Type u) [NormedAddCommGroup V]
    [NormedSpace ℂ V] where
  /-- The chosen topology on `ℙ ℂ V`. -/
  instTopologicalSpace : TopologicalSpace (ℙ ℂ V)
  /-- The chosen charted-space structure on `ℙ ℂ V` with model `ℂ^(n - 1)`. -/
  instChartedSpace : ChartedSpace (EuclideanSpace ℂ (Fin (n - 1))) (ℙ ℂ V)
  /-- The chosen charted-space structure is smooth with respect to the standard real model on
  `ℂ^(n - 1)`. -/
  instIsManifold : IsManifold (𝓘(ℝ, EuclideanSpace ℂ (Fin (n - 1)))) ∞ (ℙ ℂ V)

attribute [instance] ComplexProjectivizationSmoothStructure.instTopologicalSpace
attribute [instance] ComplexProjectivizationSmoothStructure.instChartedSpace
attribute [instance] ComplexProjectivizationSmoothStructure.instIsManifold

namespace ComplexProjectivizationSmoothStructure

-- Local API note: no semantic `lean_leansearch` tool was available in this session, so the
-- diffeomorphism surface below follows mathlib's canonical `Diffeomorph I J M N n` API.

/-- A smooth structure on `ℙ ℂ V` is basis-compatible with the chosen standard smooth structure on
`ℙ ℂ (ℂ^n)` if every basis-induced projectivization map is a diffeomorphism. -/
def BasisCompatible (S : ComplexProjectivizationSmoothStructure n V)
    (Sstd : ComplexProjectivizationSmoothStructure n (EuclideanSpace ℂ (Fin n))) : Prop :=
  letI := S.instTopologicalSpace
  letI := S.instChartedSpace
  letI := S.instIsManifold
  letI := Sstd.instTopologicalSpace
  letI := Sstd.instChartedSpace
  letI := Sstd.instIsManifold
  ∀ b : Module.Basis (Fin n) ℂ V,
    ∃ Φ : Diffeomorph
        (𝓘(ℝ, EuclideanSpace ℂ (Fin (n - 1))))
        (𝓘(ℝ, EuclideanSpace ℂ (Fin (n - 1))))
        (ℙ ℂ (EuclideanSpace ℂ (Fin n))) (ℙ ℂ V) (⊤ : ℕ∞ω),
      (Φ : ℙ ℂ (EuclideanSpace ℂ (Fin n)) → ℙ ℂ V) = complex_basis_projectivization_map b

end ComplexProjectivizationSmoothStructure

-- Proof sketch: transport the standard smooth structure on `ℙ ℂ (ℂ^n)` across any complex basis
-- of `V`. Change-of-basis maps are induced by complex linear automorphisms of `ℂ^n`, hence are
-- smooth as maps between the underlying real manifolds, so the resulting maximal smooth atlas is
-- independent of the chosen basis.
/-- Problem 2-12: if `V` is a complex `n`-dimensional vector space with `n ≥ 1`, then `ℙ ℂ V`
admits a unique smooth real `2(n - 1)`-manifold structure, equivalently a unique smooth structure
modeled on `ℂ^(n - 1)`, for which every basis-induced map
`ℙ ℂ (EuclideanSpace ℂ (Fin n)) → ℙ ℂ V` is a diffeomorphism. -/
theorem complex_projectivization_exists_unique_basis_compatible_smoothStructure
    [FiniteDimensional ℂ V] (hn : Module.finrank ℂ V = n) (hn₁ : 1 ≤ n)
    (Sstd : ComplexProjectivizationSmoothStructure n (EuclideanSpace ℂ (Fin n))) :
    ∃! S : ComplexProjectivizationSmoothStructure n V, S.BasisCompatible Sstd := sorry
