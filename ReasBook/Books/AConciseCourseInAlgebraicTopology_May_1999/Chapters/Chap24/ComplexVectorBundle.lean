import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.FiniteDimensional

universe u v

open Bundle

namespace ComplexVectorBundle

/-- A chosen presentation of an honest finite-rank complex vector bundle over `X`, using an
ambient family `bundle : X → Type v` together with its `VectorBundle ℂ fiber bundle` structure. -/
structure Presentation (X : Type u) [TopologicalSpace X] where
  /-- The chosen model fiber of the bundle. -/
  fiber : Type v
  /-- The additive normed-group structure on the model fiber. -/
  [fiberNormedAddCommGroup : NormedAddCommGroup fiber]
  /-- The complex vector-space structure on the model fiber. -/
  [fiberNormedSpace : NormedSpace ℂ fiber]
  /-- The model fiber is finite-dimensional over `ℂ`. -/
  [finiteDimensional : FiniteDimensional ℂ fiber]
  /-- The family of fibers over `X`. -/
  bundle : X → Type v
  /-- The topology on the total space of the bundle. -/
  [totalSpaceTopologicalSpace : TopologicalSpace (Bundle.TotalSpace fiber bundle)]
  /-- The topology on each fiber. -/
  [bundleTopologicalSpace : ∀ x : X, TopologicalSpace (bundle x)]
  /-- The family is locally trivial over `X`. -/
  [fiberBundle : FiberBundle fiber bundle]
  /-- Each fiber is an additive commutative group. -/
  [bundleAddCommGroup : ∀ x : X, AddCommGroup (bundle x)]
  /-- Each fiber is a complex vector space. -/
  [bundleModule : ∀ x : X, Module ℂ (bundle x)]
  /-- The local trivializations are fiberwise complex-linear. -/
  [vectorBundle : VectorBundle ℂ fiber bundle]

section

variable {X : Type u} [TopologicalSpace X]

/-- The chosen model fiber of a bundle presentation carries its stored normed-group structure. -/
instance (V : Presentation X) : NormedAddCommGroup V.fiber :=
  V.fiberNormedAddCommGroup

/-- The chosen model fiber of a bundle presentation carries its stored complex vector-space
structure. -/
instance (V : Presentation X) : NormedSpace ℂ V.fiber :=
  V.fiberNormedSpace

/-- The chosen model fiber of a bundle presentation is finite-dimensional over `ℂ`. -/
instance (V : Presentation X) : FiniteDimensional ℂ V.fiber :=
  V.finiteDimensional

/-- The total space of a bundle presentation carries its stored topology. -/
instance (V : Presentation X) : TopologicalSpace (Bundle.TotalSpace V.fiber V.bundle) :=
  V.totalSpaceTopologicalSpace

/-- Each fiber of a bundle presentation carries its stored topology. -/
instance (V : Presentation X) (x : X) : TopologicalSpace (V.bundle x) :=
  V.bundleTopologicalSpace x

/-- A bundle presentation carries its stored fiber-bundle structure. -/
instance (V : Presentation X) : FiberBundle V.fiber V.bundle :=
  V.fiberBundle

/-- Each fiber of a bundle presentation carries its stored additive-group structure. -/
instance (V : Presentation X) (x : X) : AddCommGroup (V.bundle x) :=
  V.bundleAddCommGroup x

/-- Each fiber of a bundle presentation carries its stored complex module structure. -/
instance (V : Presentation X) (x : X) : Module ℂ (V.bundle x) :=
  V.bundleModule x

/-- A bundle presentation carries its stored vector-bundle structure. -/
instance (V : Presentation X) : VectorBundle ℂ V.fiber V.bundle :=
  V.vectorBundle

/-- An isomorphism of complex vector bundles over `X`, given by a homeomorphism of total spaces
whose restriction to each fiber is complex-linear. -/
structure Iso (V W : Presentation X) where
  /-- The induced homeomorphism of total spaces over the common base `X`. -/
  toHomeomorph : Bundle.TotalSpace V.fiber V.bundle ≃ₜ Bundle.TotalSpace W.fiber W.bundle
  /-- The induced complex-linear equivalence on each fiber. -/
  fiberLinear : ∀ x : X, V.bundle x ≃ₗ[ℂ] W.bundle x
  /-- On each fiber, the total-space map is the stated linear equivalence. -/
  toHomeomorph_mk :
    ∀ (x : X) (v : V.bundle x),
      toHomeomorph (Bundle.TotalSpace.mk x v) = Bundle.TotalSpace.mk x (fiberLinear x v)

namespace Presentation

/-- The presentation attached to an ambient complex vector bundle family over `X`. -/
def ofFamily (fiber : Type v) [NormedAddCommGroup fiber] [NormedSpace ℂ fiber]
    [FiniteDimensional ℂ fiber] (bundle : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace fiber bundle)]
    [(x : X) → TopologicalSpace (bundle x)] [FiberBundle fiber bundle]
    [(x : X) → AddCommGroup (bundle x)] [(x : X) → Module ℂ (bundle x)]
    [VectorBundle ℂ fiber bundle] : Presentation X where
  fiber := fiber
  bundle := bundle

end Presentation

/-- The trivial rank-`m` complex vector bundle over `X`, presented in the ambient fiber universe
by lifting the standard coordinate fiber `Fin m → ℂ`. -/
noncomputable def trivialRank (X : Type u) [TopologicalSpace X] (m : ℕ) : Presentation X where
  fiber := ULift.{v} (Fin m → ℂ)
  bundle := Bundle.Trivial X (ULift.{v} (Fin m → ℂ))

/-- The Whitney sum of two finite-rank complex vector bundles over `X`. -/
noncomputable def whitneySum (V W : Presentation X) : Presentation X where
  fiber := V.fiber × W.fiber
  bundle := V.bundle ×ᵇ W.bundle

end

end ComplexVectorBundle
