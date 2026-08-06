import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_2_1

open Bundle
open scoped Manifold

universe u v

-- Semantic recall via `lean_leansearch`: `exists_embedding_euclidean_of_compact` supplies the
-- ambient Whitney-embedding recall. Chapter 23 already treats real `q`-plane bundles by their
-- raw fiber families together with the ambient `VectorBundle ℝ (Fin q → ℝ) _` owner, so this
-- file factors the reusable bundle data into a small support owner and keeps the Pontryagin-Thom
-- construction itself source-facing.

/-- The ambient Euclidean space `ℝ^(n + q)` used in Construction 25.2.2. -/
abbrev AmbientEuclideanSpace (n q : ℕ) :=
  EuclideanSpace ℝ (Fin (n + q))

/-- A chosen normed real `q`-plane bundle over `B`. This is the reusable bundle owner underlying
the chosen normal bundle in Construction 25.2.2; the complement condition for a specific
embedding is recorded separately by `IsNormalBundleFor`. -/
structure NormedRealPlaneBundle (q : ℕ) (B : Type u) [TopologicalSpace B] where
  /-- The fiber family of the chosen bundle. -/
  fiber : B → Type v
  /-- The topology on the total space. -/
  totalSpace_topology : TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) fiber)
  /-- The topology on each fiber. -/
  fiber_topology : ∀ x, TopologicalSpace (fiber x)
  /-- The additive commutative group structure on each fiber. -/
  fiber_addCommGroup : ∀ x, AddCommGroup (fiber x)
  /-- The real module structure on each fiber. -/
  fiber_module : ∀ x, Module ℝ (fiber x)
  /-- Each fiber is a normed additive commutative group. -/
  fiberNormedAddCommGroup : ∀ x, NormedAddCommGroup (fiber x)
  /-- Each fiber is a real normed vector space. -/
  fiberNormedSpace : ∀ x, NormedSpace ℝ (fiber x)
  /-- The chosen local triviality data. -/
  fiberBundle : FiberBundle (Fin q → ℝ) fiber
  /-- The vector-bundle structure with model fiber `Fin q → ℝ`. -/
  vectorBundle : VectorBundle ℝ (Fin q → ℝ) fiber

attribute [instance] NormedRealPlaneBundle.totalSpace_topology
attribute [instance] NormedRealPlaneBundle.fiber_topology
attribute [instance] NormedRealPlaneBundle.fiber_addCommGroup
attribute [instance] NormedRealPlaneBundle.fiber_module
attribute [instance] NormedRealPlaneBundle.fiberNormedAddCommGroup
attribute [instance] NormedRealPlaneBundle.fiberNormedSpace
attribute [instance] NormedRealPlaneBundle.fiberBundle
attribute [instance] NormedRealPlaneBundle.vectorBundle

/-- The complement condition expressing that a chosen normed real `q`-plane bundle over `M.M`
is a normal bundle for the embedding `e : M.M → ℝ^(n + q)`. -/
def IsNormalBundleFor
    (n q : ℕ) (M : ClosedSmoothManifold n)
    (e : M.M → AmbientEuclideanSpace n q)
    (ν : NormedRealPlaneBundle q M.M) : Prop :=
  ∀ x : M.M,
    Manifold.IsImmersionAtOfComplement (ν.fiber x) (𝓡 n)
      (modelWithCornersSelf ℝ (AmbientEuclideanSpace n q)) ⊤ e x

/-- The zero-section point of the closed Thom disk bundle over `x`. -/
noncomputable def thomZeroDiskBundlePoint
    {q : ℕ} {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin q → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin q → ℝ) E]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
    (x : B) : ThomDiskBundle q E :=
  thomDiskBundleRadialPoint q E x (0 : E x)

/-- The fiberwise action of a pullback bundle isomorphism, expressed directly in the target fiber
`γ (f x)` to avoid exposing coercion-shaped pullback instances in downstream statements. -/
def pullbackRealPlaneBundleIsoApply
    (q : ℕ) {X : Type*} [TopologicalSpace X] (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin q → ℝ) E]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    {BO : Type u} [TopologicalSpace BO] (f : ContinuousMap X BO) (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    [∀ b, NormedAddCommGroup (γ b)] [∀ b, NormedSpace ℝ (γ b)]
    (φ : pullbackRealPlaneBundleIso q E f γ) (x : X) (v : E x) :
    γ (f x) :=
  show γ (f x) from (φ ⟨x, v⟩).2

/-- A Thom-space comparison attached to a classifying isomorphism of real `q`-plane bundles is
determined by the induced fiberwise map on finite Thom points and by preserving the collapsed
point at infinity. -/
structure PullbackThomComparison
    (q : ℕ) {X : Type*} [TopologicalSpace X] (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin q → ℝ) E]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    {BO : Type u} [TopologicalSpace BO] (f : ContinuousMap X BO) (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    [∀ b, NormedAddCommGroup (γ b)] [∀ b, NormedSpace ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace q BO γ]
    (φ : pullbackRealPlaneBundleIso q E f γ) where
  /-- The induced map on Thom spaces. -/
  toContinuousMap : ContinuousMap (ThomSpace q E) (TO q BO γ)
  /-- On finite Thom-space points, the comparison acts fiberwise by the classifying bundle
  isomorphism. -/
  map_finite (x : X) (v : E x) :
      toContinuousMap (thomSpaceMk q E x (OnePoint.some v)) =
        thomSpaceMk q γ (f x)
          (OnePoint.some (pullbackRealPlaneBundleIsoApply q E f γ φ x v))
  /-- The comparison preserves the collapsed point at infinity. -/
  map_infty (x : X) :
      toContinuousMap (thomSpaceMk q E x (OnePoint.infty : OnePoint (E x))) =
        thomSpaceMk q γ (f x) (OnePoint.infty : OnePoint (γ (f x)))

/-- A geometric Pontryagin-Thom collapse to the Thom space of a chosen normal bundle consists of a
collapse map together with tubular-neighborhood data showing that the map is the usual collapse
onto the disk bundle of the normal bundle, with complement sent to the Thom-space point at
infinity. -/
structure GeometricPontryaginThomCollapse
    (n q : ℕ) (M : ClosedSmoothManifold n)
    (e : M.M → AmbientEuclideanSpace n q)
    (ν : NormedRealPlaneBundle q M.M) where
  /-- The collapse map into the Thom space of the chosen normal bundle. -/
  toContinuousMap :
    ContinuousMap (TopCat.sphere.{0} (n + q)) (ThomSpace q ν.fiber)
  /-- A chosen identification of the ambient one-point compactification with the source sphere
  model. -/
  sphereHomeomorphOnePoint :
    TopCat.sphere.{0} (n + q) ≃ₜ OnePoint (AmbientEuclideanSpace n q)
  /-- The tubular neighborhood on which the collapse remembers finite normal data. -/
  tubularNeighborhood : Set (AmbientEuclideanSpace n q)
  /-- The chosen tubular neighborhood is open. -/
  isOpen_tubularNeighborhood : IsOpen tubularNeighborhood
  /-- The embedded manifold lies inside the chosen tubular neighborhood. -/
  embeddingRange_subset_tubularNeighborhood : Set.range e ⊆ tubularNeighborhood
  /-- The tubular neighborhood is identified with the closed unit disk bundle of the chosen normal
  bundle. -/
  tubularNeighborhoodHomeomorphDiskBundle :
    tubularNeighborhood ≃ₜ ThomDiskBundle q ν.fiber
  /-- Along the embedded manifold, the tubular neighborhood identification agrees with the zero
  section of the normal disk bundle. -/
  embedding_to_zeroSection (x : M.M) :
      tubularNeighborhoodHomeomorphDiskBundle
          ⟨e x, embeddingRange_subset_tubularNeighborhood ⟨x, rfl⟩⟩ =
        thomZeroDiskBundlePoint ν.fiber x
  /-- Inside the tubular neighborhood, the collapse map is the canonical disk-bundle map to the
  Thom space. -/
  map_of_mem_tubularNeighborhood (x : tubularNeighborhood) :
      toContinuousMap (sphereHomeomorphOnePoint.symm (OnePoint.some x.1)) =
        thomDiskBundleToThomSpace q ν.fiber (tubularNeighborhoodHomeomorphDiskBundle x)
  /-- Outside the tubular neighborhood, the collapse map lands in the collapsed infinity subset of
  the Thom space. -/
  map_of_not_mem_tubularNeighborhood (x : AmbientEuclideanSpace n q)
      (hx : x ∉ tubularNeighborhood) :
      toContinuousMap (sphereHomeomorphOnePoint.symm (OnePoint.some x)) ∈
        thomInfinitySubset q ν.fiber
  /-- The point at infinity in the ambient one-point compactification is sent to the Thom-space
  point at infinity. -/
  map_at_infty :
      toContinuousMap
          (sphereHomeomorphOnePoint.symm
            (OnePoint.infty : OnePoint (AmbientEuclideanSpace n q))) ∈
        thomInfinitySubset q ν.fiber

/-- A Pontryagin-Thom collapse map associated to an embedding into `ℝ^(n + q)`, with target the
chosen Thom-space model `TO q BO γ`. -/
abbrev PontryaginThomCollapseMap
    (n q : ℕ) (BO : Type u) [TopologicalSpace BO] (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    [∀ b, NormedAddCommGroup (γ b)] [∀ b, NormedSpace ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace q BO γ] :=
  ContinuousMap (TopCat.sphere.{0} (n + q)) (TO q BO γ)

/-- Construction 25.2.2. A Pontryagin-Thom construction attached to an embedding into
`ℝ^(n + q)` consists of a chosen normal `q`-plane bundle, a classifying map into the chosen
universal `q`-plane bundle, the induced Thom-space comparison attached to the classifying bundle
isomorphism, and a geometric collapse to the Thom space of the chosen normal bundle exhibited by
tubular-neighborhood data. The textbook collapse map `S^(n + q) → TO q` is then the derived
composition `PontryaginThomConstruction.collapseMap`. -/
structure PontryaginThomConstruction
    (n q : ℕ) (BO : Type u) [TopologicalSpace BO] (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    [∀ b, NormedAddCommGroup (γ b)] [∀ b, NormedSpace ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace q BO γ]
    (M : ClosedSmoothManifold n)
    (e : M.M → AmbientEuclideanSpace n q) where
  /-- The chosen ambient map is smooth. -/
  isSmooth :
    ContMDiff (𝓡 n) (modelWithCornersSelf ℝ (AmbientEuclideanSpace n q)) ⊤ e
  /-- The chosen ambient map is a closed embedding. -/
  isClosedEmbedding : Topology.IsClosedEmbedding e
  /-- The chosen normal `q`-plane bundle determined by the embedding. -/
  normalBundle : NormedRealPlaneBundle q M.M
  /-- The chosen bundle is complementary to the tangent directions of the embedding. -/
  isComplement : IsNormalBundleFor n q M e normalBundle
  /-- A chosen classifying map of the normal bundle into the universal `q`-plane bundle. -/
  classifyingMap : ContinuousMap M.M BO
  /-- The chosen normal bundle is identified with the pullback of the universal bundle along the
  chosen classifying map. -/
  classifiesNormalBundle : pullbackRealPlaneBundleIso q normalBundle.fiber classifyingMap γ
  /-- The comparison from the Thom space of the chosen normal bundle to `TO q BO γ`, constrained
  by the classifying bundle isomorphism on finite Thom points and on the point at infinity. -/
  normalThomComparisonData :
    PullbackThomComparison q normalBundle.fiber classifyingMap γ classifiesNormalBundle
  /-- The Pontryagin-Thom collapse to the Thom space of the chosen normal bundle, recorded with
  geometric tubular-neighborhood data tying it to the embedding `e`. -/
  collapseToNormalThom :
    GeometricPontryaginThomCollapse n q M e normalBundle

namespace PontryaginThomConstruction

open GeometricPontryaginThomCollapse

variable {n q : ℕ}
variable {BO : Type u} [TopologicalSpace BO]
variable {γ : BO → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
variable [∀ b, NormedAddCommGroup (γ b)] [∀ b, NormedSpace ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace q BO γ]
variable {M : ClosedSmoothManifold n}
variable {e : M.M → AmbientEuclideanSpace n q}

/-- The classifying Thom-space comparison attached to a Pontryagin-Thom construction. -/
abbrev normalThomComparison
    (pt : PontryaginThomConstruction n q BO γ M e) :
    ContinuousMap (ThomSpace q pt.normalBundle.fiber) (TO q BO γ) :=
  pt.normalThomComparisonData.toContinuousMap

/-- The geometric Pontryagin-Thom collapse map into the Thom space of the chosen normal bundle. -/
abbrev collapseToNormalThomMap
    (pt : PontryaginThomConstruction n q BO γ M e) :
    ContinuousMap (TopCat.sphere.{0} (n + q)) (ThomSpace q pt.normalBundle.fiber) :=
  pt.collapseToNormalThom.toContinuousMap

/-- The chosen bundle in a Pontryagin-Thom construction is complementary to the tangent
directions of the embedding. -/
theorem normalBundle_isComplement
    (pt : PontryaginThomConstruction n q BO γ M e) :
    IsNormalBundleFor n q M e pt.normalBundle :=
  pt.isComplement

/-- On finite Thom-space points, the normal Thom comparison acts fiberwise by the chosen
classifying bundle isomorphism. -/
@[simp] theorem normalThomComparison_apply_finite
    (pt : PontryaginThomConstruction n q BO γ M e) (x : M.M) (v : pt.normalBundle.fiber x) :
    pt.normalThomComparison (thomSpaceMk q pt.normalBundle.fiber x (OnePoint.some v)) =
      thomSpaceMk q γ (pt.classifyingMap x)
        (OnePoint.some
          (pullbackRealPlaneBundleIsoApply
            q pt.normalBundle.fiber pt.classifyingMap γ pt.classifiesNormalBundle x v)) :=
  pt.normalThomComparisonData.map_finite x v

/-- On the collapsed point at infinity, the normal Thom comparison preserves the Thom-space
basepoint. -/
@[simp] theorem normalThomComparison_apply_infty
    (pt : PontryaginThomConstruction n q BO γ M e) (x : M.M) :
    pt.normalThomComparison
        (thomSpaceMk q pt.normalBundle.fiber x
          (OnePoint.infty : OnePoint (pt.normalBundle.fiber x))) =
      thomSpaceMk q γ (pt.classifyingMap x)
        (OnePoint.infty : OnePoint (γ (pt.classifyingMap x))) :=
  pt.normalThomComparisonData.map_infty x

/-- Inside the chosen tubular neighborhood, the collapse map is the canonical map from the normal
disk bundle to the Thom space. -/
theorem collapseToNormalThomMap_apply_of_mem_tubularNeighborhood
    (pt : PontryaginThomConstruction n q BO γ M e)
    (x : pt.collapseToNormalThom.tubularNeighborhood) :
    pt.collapseToNormalThomMap
        ((sphereHomeomorphOnePoint pt.collapseToNormalThom).symm (OnePoint.some x.1)) =
      thomDiskBundleToThomSpace q pt.normalBundle.fiber
        (pt.collapseToNormalThom.tubularNeighborhoodHomeomorphDiskBundle x) :=
  pt.collapseToNormalThom.map_of_mem_tubularNeighborhood x

/-- Outside the chosen tubular neighborhood, the collapse map lands in the Thom-space infinity
subset. -/
theorem collapseToNormalThomMap_mem_thomInfinitySubset_of_not_mem_tubularNeighborhood
    (pt : PontryaginThomConstruction n q BO γ M e)
    (x : AmbientEuclideanSpace n q)
    (hx : x ∉ pt.collapseToNormalThom.tubularNeighborhood) :
    pt.collapseToNormalThomMap
        ((sphereHomeomorphOnePoint pt.collapseToNormalThom).symm (OnePoint.some x)) ∈
      thomInfinitySubset q pt.normalBundle.fiber :=
  pt.collapseToNormalThom.map_of_not_mem_tubularNeighborhood x hx

/-- The textbook Pontryagin-Thom collapse map into `TO q BO γ`, obtained by transporting the
normal-bundle Thom collapse map along the chosen classifying data. -/
noncomputable def collapseMap
    (pt : PontryaginThomConstruction n q BO γ M e) :
    PontryaginThomCollapseMap n q BO γ :=
  pt.normalThomComparison.comp pt.collapseToNormalThomMap

/-- Unfolding `collapseMap` recovers the composite through the Thom space of the chosen normal
bundle and its classifying comparison map to `TO q BO γ`. -/
@[simp] theorem collapseMap_def
    (pt : PontryaginThomConstruction n q BO γ M e) :
    pt.collapseMap = pt.normalThomComparison.comp pt.collapseToNormalThomMap :=
  rfl

end PontryaginThomConstruction
