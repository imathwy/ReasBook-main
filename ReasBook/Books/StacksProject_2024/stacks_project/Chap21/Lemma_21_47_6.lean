import StacksProject_2024.stacks_project.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {X : RingedSite.{u, v}}
variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "DMod" => ModuleDerived X
local notation "PerfectObj" => (IsPerfect : ObjectProperty DMod)
local notation "SitePerfect" => IsPerfect

/- Domain-style sampling for Lemma 21.47.6:
- primary domain: perfect objects of `D(𝒪_X)` on a bundled ringed site, viewed as an
  object property and closed under distinguished triangles;
- sampled owner declarations:
  `RingedSite.DerivedCategory.IsPerfect`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.ext_of_isTriangulatedClosed₁`,
  `ObjectProperty.ext_of_isTriangulatedClosed₂`,
  `ObjectProperty.ext_of_isTriangulatedClosed₃`;
- best owner abstraction: the canonical owner is the bundled ringed-site object property
  `PerfectObj`, so this file should expose `ObjectProperty.IsTriangulated PerfectObj` directly and
  treat the three textbook clauses only as thin companions;
- primitive vs. derived:
  primitive data are the Chapter 21 owner predicate `RingedSite.DerivedCategory.IsPerfect` and its
  existing isomorphism invariance from Definition `21.47.1`;
  derived API is the triangulated closure of that object property together with the three
  distinguished-triangle clauses recovered from the owner instance;
- source/core/bridge triage:
  `source-facing`: the three numbered perfectness clauses for distinguished triangles in
    `ModuleDerived X`;
  `core/canonical`: `ObjectProperty.IsTriangulated PerfectObj`;
  `bridge/view`: the generic `ObjectProperty.ext_of_isTriangulatedClosed₁/₂/₃` consequences.

This file targets the `core/canonical` layer, with the source-facing clauses retained only as
owner-derived companions. Any presentation by `RingedSite.ofCommRingSheaf J 𝒪` is a specialization
of this bundled surface, not part of the exported API here.
-/

local instance : ObjectProperty.IsClosedUnderIsomorphisms PerfectObj :=
  RingedSite.DerivedCategory.isPerfect_isClosedUnderIsomorphisms

/-- Lemma 21.47.6: perfect objects of `D(𝒪_X)` on a ringed site form a triangulated
object property. Equivalently, in a distinguished triangle, if two of the three objects are
perfect, then so is the third. -/
@[stacks 08G9]
instance perfectObjectProperty_isTriangulated :
    ObjectProperty.IsTriangulated PerfectObj := by
  sorry

omit [∀ U : X, (localizedRestriction X U).Additive]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

/-- Lemma 21.47.6 (1): let `(𝒞, 𝒪)` be a ringed site and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `K` and `L` are
perfect, then `M` is perfect. -/
@[stacks 08G9]
theorem isPerfect_obj₃_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : SitePerfect T.obj₁) (h₂ : SitePerfect T.obj₂) :
    SitePerfect T.obj₃ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ PerfectObj T hT h₁ h₂

/-- Lemma 21.47.6 (2): let `(𝒞, 𝒪)` be a ringed site and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `K` and `M` are
perfect, then `L` is perfect. -/
@[stacks 08G9]
theorem isPerfect_obj₂_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : SitePerfect T.obj₁) (h₃ : SitePerfect T.obj₃) :
    SitePerfect T.obj₂ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ PerfectObj T hT h₁ h₃

/-- Lemma 21.47.6 (3): let `(𝒞, 𝒪)` be a ringed site and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(𝒪_X)`. If `L` and `M` are
perfect, then `K` is perfect. -/
@[stacks 08G9]
theorem isPerfect_obj₁_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : SitePerfect T.obj₂) (h₃ : SitePerfect T.obj₃) :
    SitePerfect T.obj₁ := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₁ PerfectObj T hT h₂ h₃

end

end SheafOfModules.RingedSite
