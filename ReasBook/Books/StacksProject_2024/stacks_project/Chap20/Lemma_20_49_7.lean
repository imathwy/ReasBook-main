import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_47_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DModX)

local instance perfectObjectProperty_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms PerfectObj := by
  change ObjectProperty.IsClosedUnderIsomorphisms
    ((IsPerfect : ObjectProperty (ModuleDerived (opensRingedSite X))))
  exact RingedSite.DerivedCategory.isPerfect_isClosedUnderIsomorphisms

/- Domain-style sampling for Lemma 20.49.7:
- primary domain: perfect objects of `D(𝒪_X)` on a ringed space and their closure under
  distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `SheafOfModules.RingedSite.perfectObjectProperty_isTriangulated`,
  `SheafOfModules.RingedSite.isPerfect_obj₁_of_distinguished_triangle`,
  `SheafOfModules.RingedSite.isPerfect_obj₂_of_distinguished_triangle`,
  `SheafOfModules.RingedSite.isPerfect_obj₃_of_distinguished_triangle`;
- best owner abstraction:
  `source-facing`: the three ringed-space perfectness clauses for distinguished triangles below;
  `core/canonical`: the Chapter 21 ringed-site owner
    `ObjectProperty.IsTriangulated
      (IsPerfect : ObjectProperty (ModuleDerived (opensRingedSite X)))`;
  `bridge/view`: `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect` is exactly the
    opens-ringed-site specialization of that owner, so the Chapter 20 statements are thin
    specializations of the Chapter 21 instance and companion theorems.
- primitive vs. derived:
  primitive data are the distinguished triangle `T` and the perfectness owner
  `DerivedCategory.IsPerfect`;
  derived API is the ringed-space specialization of the Chapter 21 triangulated closure and its
  three source-facing consequences.
-/

/-- Lemma 20.49.7: perfect objects of `D(𝒪_X)` form a triangulated object property.
Equivalently, in a distinguished triangle, if two of the three objects are perfect, then so is
the third. -/
@[stacks 08CR]
instance perfectObjectProperty_isTriangulated :
    ObjectProperty.IsTriangulated PerfectObj := by
  change ObjectProperty.IsTriangulated
    ((IsPerfect : ObjectProperty (ModuleDerived (opensRingedSite X))))
  exact SheafOfModules.RingedSite.perfectObjectProperty_isTriangulated

-- Proof sketch: combine Lemma `20.49.5`, which characterizes perfect objects by
-- pseudo-coherence and local finite tor dimension, with Lemma `20.47.4 (1)` for the
-- pseudo-coherent part and Lemma `20.48.6 (1)` for the tor-amplitude part on each member of a
-- local open cover. In the refined API this is the ringed-space specialization of the Chapter 21
-- ringed-site theorem.
/-- Lemma 20.49.7 (1): let `(X, 𝒪_X)` be a ringed space and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `K` and `L` are
perfect, then `M` is perfect. -/
@[stacks 08CR]
theorem isPerfect_obj₃_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₂ : DerivedCategory.IsPerfect T.obj₂) :
    DerivedCategory.IsPerfect T.obj₃ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ PerfectObj T hT h₁ h₂

-- Proof sketch: use Lemma `20.49.5` to reduce perfectness to pseudo-coherence plus local finite
-- tor dimension; then apply Lemma `20.47.4 (2)` and Lemma `20.48.6 (2)` to the distinguished
-- triangle and reassemble the two conditions.
/-- Lemma 20.49.7 (2): let `(X, 𝒪_X)` be a ringed space and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `K` and `M` are
perfect, then `L` is perfect. -/
@[stacks 08CR]
theorem isPerfect_obj₂_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₂ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ PerfectObj T hT h₁ h₃

-- Proof sketch: again reduce via Lemma `20.49.5`, then use Lemma `20.47.4 (3)` for
-- pseudo-coherence and Lemma `20.48.6 (3)` for the local tor-amplitude bounds to propagate
-- perfectness to the first vertex.
/-- Lemma 20.49.7 (3): let `(X, 𝒪_X)` be a ringed space and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `L` and `M` are
perfect, then `K` is perfect. -/
@[stacks 08CR]
theorem isPerfect_obj₁_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : DerivedCategory.IsPerfect T.obj₂) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₁ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₁ PerfectObj T hT h₂ h₃

end AlgebraicGeometry.RingedSpace
