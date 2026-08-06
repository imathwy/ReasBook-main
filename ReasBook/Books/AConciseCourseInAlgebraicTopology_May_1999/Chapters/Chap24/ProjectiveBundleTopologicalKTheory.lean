import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_8

open CategoryTheory
open scoped ProjectiveBundleNotation

universe u v

section

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {E : ComplexPlaneBundle n X}

/-- The continuous map `P(E) ⟶ X` underlying the projective-bundle projection. -/
noncomputable def projectiveBundleProjMap (E : ComplexPlaneBundle n X) :
    TopCat.of (P(E)) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨projectiveBundleProj E, projectiveBundleProj_continuous E⟩

/-- A source-facing owner for the actual topological-`K`-theory pullback
`K(X) → K(P(E))` induced by `projectiveBundleProjMap`. -/
class ProjectiveBundleTopologicalKTheory (E : ComplexPlaneBundle n X) [CompactSpace X]
    [CompactSpace (P(E))] where
  /-- The actual pullback ring homomorphism on topological `K`-theory induced by
  `projectiveBundleProjMap`. -/
  pullback :
    complexKTheory X →+* complexKTheory (P(E))
  /-- Pullback of an honest complex vector bundle along `projectiveBundleProj E`. -/
  pullbackBundle :
    ComplexVectorBundle.Presentation X →
      ComplexVectorBundle.Presentation (P(E))
  /-- The underlying bundle family of `pullbackBundle V` is the actual pullback family along
  `projectiveBundleProj E`. -/
  pullbackBundle_spec :
    ∀ V : ComplexVectorBundle.Presentation X,
      (pullbackBundle V).bundle = projectiveBundleProj E *ᵖ V.bundle
  /-- On honest bundle classes, `pullback` agrees with pullback of vector bundles along
  `projectiveBundleProjMap`. -/
  pullback_on_toVirtualPresentation :
    ∀ V : ComplexVectorBundle.Presentation X,
      pullback (ComplexVectorBundle.toVirtualPresentation V) =
        ComplexVectorBundle.toVirtualPresentation (pullbackBundle V)

/-- The chosen surface `ProjectiveBundleTopologicalKTheory` provides the canonical
`K(X)`-algebra structure on `K(P(E))`. -/
noncomputable instance projectiveBundleTopologicalKTheory_algebra [CompactSpace X]
    [CompactSpace (P(E))]
    [topologicalKTheory : ProjectiveBundleTopologicalKTheory E] :
    Algebra
      (complexKTheory X)
      (complexKTheory (P(E))) :=
  topologicalKTheory.pullback.toAlgebra

/-- The actual tautological class `[H]` in `K(P(E))`, defined directly from the tautological
line bundle on `P(E)`. -/
noncomputable abbrev projectiveBundleTautologicalClass
    [TopologicalSpace (Bundle.TotalSpace ℂ (projectiveBundleTautologicalLine E))]
    [FiberBundle ℂ (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ ℂ (projectiveBundleTautologicalLine E)] :
    complexKTheory (P(E)) :=
  ComplexVectorBundle.toVirtualPresentation
    (ComplexVectorBundle.Presentation.ofFamily ℂ (projectiveBundleTautologicalLine E))

/-- `projectiveBundleTautologicalClass` is the direct virtual class of the actual tautological
line bundle on `P(E)`. -/
theorem projectiveBundleTautologicalClass_def
    [TopologicalSpace (Bundle.TotalSpace ℂ (projectiveBundleTautologicalLine E))]
    [FiberBundle ℂ (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ ℂ (projectiveBundleTautologicalLine E)] :
    (projectiveBundleTautologicalClass : complexKTheory (P(E))) =
      ComplexVectorBundle.toVirtualPresentation
        (ComplexVectorBundle.Presentation.ofFamily ℂ (projectiveBundleTautologicalLine E)) := rfl

/-- The chosen pullback datum for `P(E) → X` gives the canonical Chapter 24
presentation-level pullback witness on `complexKTheory`. -/
theorem ProjectiveBundleTopologicalKTheory.isComplexKTheoryPresentationPullback
    [CompactSpace X] [CompactSpace (P(E))]
    (topologicalKTheory : ProjectiveBundleTopologicalKTheory E) :
    IsComplexKTheoryPresentationPullback
      (projectiveBundleProjMap E)
      topologicalKTheory.pullback := by
  refine ⟨topologicalKTheory.pullbackBundle, topologicalKTheory.pullbackBundle_spec, ?_⟩
  intro V
  exact topologicalKTheory.pullback_on_toVirtualPresentation V

/-- For the canonical `K(X)`-algebra structure on `K(P(E))`, the algebra map is the actual
pullback map. -/
theorem ProjectiveBundleTopologicalKTheory.algebraMap_eq_pullback
    [CompactSpace X] [CompactSpace (P(E))]
    [topologicalKTheory : ProjectiveBundleTopologicalKTheory E] :
    algebraMap (complexKTheory X) (complexKTheory (P(E))) = topologicalKTheory.pullback := by
  simpa using RingHom.algebraMap_toAlgebra topologicalKTheory.pullback

end
