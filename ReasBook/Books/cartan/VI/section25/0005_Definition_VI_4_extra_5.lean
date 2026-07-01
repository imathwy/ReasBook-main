import Mathlib
import cartan.VI.section25.«0001_Definition_VI_4_extra_1»

open scoped Manifold

universe u v u'

/-!
Definition VI.4-extra-5 has three source-facing pieces:

* an isomorphism of complex manifolds is a homeomorphism whose map and inverse are holomorphic;
* two analytic structures on the same topological space are equivalent when all mixed coordinate
  changes are holomorphic isomorphisms;
* the reusable Lean owner for a complex manifold should be the ambient charted-space/manifold
  typeclass surface, not a quotient package of all possible atlases.
-/

namespace Homeomorph

section IsComplexManifoldIso

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type u'} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Definition VI.4-extra-5 (1): a homeomorphism of one-dimensional complex manifolds is an
isomorphism when it is holomorphic and its inverse is holomorphic. -/
def IsComplexManifoldIso (φ : X ≃ₜ Y) : Prop :=
  φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)

theorem isComplexManifoldIso_iff (φ : X ≃ₜ Y) :
    φ.IsComplexManifoldIso ↔
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ.symm := by
  simp [IsComplexManifoldIso, OpenPartialHomeomorph.MDifferentiable, mdifferentiableOn_univ]

theorem isComplexManifoldIso_refl :
    (Homeomorph.refl X).IsComplexManifoldIso := by
  simp [IsComplexManifoldIso, OpenPartialHomeomorph.MDifferentiable, mdifferentiableOn_id]

theorem IsComplexManifoldIso.symm {φ : X ≃ₜ Y} (hφ : φ.IsComplexManifoldIso) :
    φ.symm.IsComplexManifoldIso := by
  simpa [isComplexManifoldIso_iff, and_comm] using hφ

theorem IsComplexManifoldIso.trans
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] {φ : X ≃ₜ Y} {ψ : Y ≃ₜ Z}
    (hφ : φ.IsComplexManifoldIso) (hψ : ψ.IsComplexManifoldIso) :
    (φ.trans ψ).IsComplexManifoldIso := by
  simpa [IsComplexManifoldIso, Homeomorph.trans_toOpenPartialHomeomorph] using
    OpenPartialHomeomorph.MDifferentiable.trans hφ hψ

end IsComplexManifoldIso

end Homeomorph

/-- A chosen analytic structure on a fixed topological space, represented by the explicit
one-dimensional complex atlas introduced in Definition VI.4-extra-1. -/
abbrev ComplexManifoldStructure (X : Type u) [TopologicalSpace X] : Type (max u (v + 1)) :=
  ComplexManifoldAtlas.{u, v} X

namespace ComplexManifoldStructure

/-- Definition VI.4-extra-5 (2): two analytic structures on the same topological space are
equivalent when every coordinate of one atlas and every coordinate of the other have holomorphic
transition maps. This is the source-level atlas equivalence relation; it is not the main Lean
owner for working with manifolds. -/
def Equivalent {X : Type u} [TopologicalSpace X]
    (S T : ComplexManifoldStructure.{u, v} X) : Prop :=
  ∀ i : S.Index, ∀ j : T.Index,
    ((S.chart i).symm ≫ₕ T.chart j).IsHolomorphicIsoOn
      (((S.chart i).symm ≫ₕ T.chart j).source)
      (((S.chart i).symm ≫ₕ T.chart j).target)

/-- Equivalence of analytic structures is reflexive. -/
theorem equivalent_refl {X : Type u} [TopologicalSpace X]
    (S : ComplexManifoldStructure.{u, v} X) : Equivalent S S := by
  intro i j
  simpa [Equivalent] using S.holomorphic_transition j i

/-- Cartan's "class of equivalent analytic structures" on a fixed topological space. This keeps
source wording without forcing a quotient construction into the main Lean owner: a class is a
nonempty family of atlases whose members are pairwise compatible in the mixed-coordinate sense
above. -/
structure StructureClass (X : Type u) [TopologicalSpace X] : Type (max u (v + 1)) where
  structures : Set (ComplexManifoldStructure.{u, v} X)
  nonempty : structures.Nonempty
  pairwise_equivalent : ∀ S ∈ structures, ∀ T ∈ structures, Equivalent S T

end ComplexManifoldStructure

/-- Definition VI.4-extra-5 (3), reusable Lean owner: a complex manifold is a Hausdorff
topological space equipped with a chosen one-dimensional complex charted-space structure whose
coordinate changes are holomorphic. The choice of representative atlas is carried by the ambient
`ChartedSpace ℂ X`; source-level families of mutually compatible atlases are available
separately as `ComplexManifoldStructure.StructureClass`. -/
class ComplexManifold (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop extends
    T2Space X, IsManifold 𝓘(ℂ) 1 X

/-- A Hausdorff one-dimensional complex analytic manifold is a complex manifold. -/
instance instComplexManifoldOfT2IsManifold (X : Type u) [TopologicalSpace X]
    [ChartedSpace ℂ X] [T2Space X] [IsManifold 𝓘(ℂ) 1 X] :
    ComplexManifold X where
  toT2Space := inferInstance
  toIsManifold := inferInstance
