import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_pushforward_along_derived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.33.2:
- primary domain: Mayer-Vietoris distinguished triangles in `D(𝒪_X)` written with
  derived restriction to open subspaces and derived direct image along the open inclusions;
- sampled owner declarations:
  `modulePushforwardFromOpenAlongDerivedUnitNatTrans`,
  `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans`,
  `modulePushforwardFromOpenDerived`,
  `Triangle.mk`;
- best owner abstraction:
  `source-facing`: the Mayer-Vietoris distinguished triangle
    `R(𝟙_X)_* E ⟶ Rj_{U,*}(E|_U) ⊞ Rj_{V,*}(E|_V) ⟶
      Rj_{U ∩ V,*}(E|_{U ∩ V}) ⟶ R(𝟙_X)_* E⟦(1 : ℤ)⟧`,
    together with the objectwise identification `R(𝟙_X)_* E ≅ E`;
  `core/canonical`: the Chapter 20 open-subspace owner layer
    `modulePushforwardFromOpenAlongDerivedUnitNatTrans (𝟙 X) U`,
    `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans (𝟙 X) h`,
    `modulePushforwardFromOpenDerived U`, and `Triangle.mk`;
  `bridge/view`: the theorem-level identity-pushforward comparisons
    `ringedSpaceModuleDerivedPushforward_id_isomorphic` and
    `ringedSpaceModuleDerivedPushforward_obj_id_isomorphic`.
- primitive data: the opens `U, V`, the cover equation `U ⊔ V = ⊤`, and the derived object `E`;
- derived API: the canonical unit and overlap-restriction natural transformations, together with
  the source-facing distinguished triangle statement below.

Source/core/bridge triage:
- `source-facing`: `ringedSpaceModule_derivedMayerVietoris_triangle`;
- `core/canonical`: `modulePushforwardFromOpenAlongDerivedUnitNatTrans`,
  `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans`,
  `modulePushforwardFromOpenDerived`, and `Triangle.mk`;
- `bridge/view`: `ringedSpaceModuleDerivedPushforward_id_isomorphic` and
  `ringedSpaceModuleDerivedPushforward_obj_id_isomorphic`.

This file therefore stays at the source-facing layer: it states the direct-image
Mayer-Vietoris triangle itself, while reusing the chapter-owned open restriction and open
pushforward functors on the theorem surface. -/

section

variable {X : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "RPush[" U "]" => modulePushforwardFromOpenAlongDerived (𝟙 X) U
local notation "RIdPush" => moduleDerivedPushforward (𝟙 X)

local instance : Abelian (RingedSpace.Modules X) := RingedSpace.modules_abelian X

local instance : CategoryWithHomology (RingedSpace.Modules X) :=
  CategoryTheory.categoryWithHomology_of_abelian

local instance :
    (RingedSpace.Hom.pushforward (𝟙 X)).Additive := by
  simpa using RingedSpace.Hom.pushforward_additive (𝟙 X)

-- Proof sketch: choose a K-injective complex representing `E`, identify the three displayed
-- terms with the pushforwards of its restrictions to `U`, `V`, and `U ∩ V`, use the classical
-- Mayer-Vietoris short exact sequence of complexes for the cover `U ∪ V = X`, and then apply
-- the distinguished triangle attached to a short exact sequence of complexes in the derived
-- category. The companion bridge theorem below identifies `R(𝟙_X)_* E` with the textbook vertex
-- `E`.

/-- The identity-specialized derived pushforward functor is canonically isomorphic to the identity
on `D(𝒪_X)`. -/
theorem ringedSpaceModuleDerivedPushforward_id_isomorphic :
    IsIsomorphic RIdPush (𝟭 DModX) := by
  sorry

/-- Objectwise companion to `ringedSpaceModuleDerivedPushforward_id_isomorphic`. -/
theorem ringedSpaceModuleDerivedPushforward_obj_id_isomorphic (E : DModX) :
    IsIsomorphic ((RIdPush).obj E) E := by
  rcases ringedSpaceModuleDerivedPushforward_id_isomorphic with ⟨e⟩
  exact ⟨e.app E⟩

/- Lemma 20.33.2: if a ringed space `X` is covered by two opens `U` and `V`, then the canonical
identity-pushforward Mayer-Vietoris triangle
`R(𝟙_X)_* E ⟶ Rj_{U,*}(E|_U) ⊞ Rj_{V,*}(E|_V) ⟶
Rj_{U ∩ V,*}(E|_{U ∩ V}) ⟶ R(𝟙_X)_* E⟦(1 : ℤ)⟧`
is distinguished for every `E ∈ D(𝒪_X)`. The companion theorem
`ringedSpaceModuleDerivedPushforward_obj_id_isomorphic` recovers the textbook presentation with
`E` in the left and right vertices. -/
@[stacks 08BV]
theorem ringedSpaceModule_derivedMayerVietoris_triangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ∃ δ : RPush[U ⊓ V] ⟶ RIdPush ⋙ shiftFunctor DModX (1 : ℤ),
      ∀ E : DModX,
        Triangle.mk
            ((biprod.lift
              (modulePushforwardFromOpenAlongDerivedUnitNatTrans (𝟙 X) U)
              (modulePushforwardFromOpenAlongDerivedUnitNatTrans (𝟙 X) V)).app E)
            ((biprod.desc
              (modulePushforwardFromOpenAlongDerivedRestrictionNatTrans (𝟙 X)
                inf_le_left)
              (-(modulePushforwardFromOpenAlongDerivedRestrictionNatTrans (𝟙 X)
                inf_le_right))).app E)
            (δ.app E) ∈ distTriang DModX := by
  sorry

/-- Objectwise companion to `ringedSpaceModule_derivedMayerVietoris_triangle`. -/
theorem ringedSpaceModuleDerivedMayerVietorisTriangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (E : DModX) :
    ∃ δ : (RPush[U ⊓ V]).obj E ⟶ ((RIdPush).obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((biprod.lift
            (modulePushforwardFromOpenAlongDerivedUnitNatTrans (𝟙 X) U)
            (modulePushforwardFromOpenAlongDerivedUnitNatTrans (𝟙 X) V)).app E)
          ((biprod.desc
            (modulePushforwardFromOpenAlongDerivedRestrictionNatTrans (𝟙 X)
              inf_le_left)
            (-(modulePushforwardFromOpenAlongDerivedRestrictionNatTrans (𝟙 X)
              inf_le_right))).app E)
          δ ∈ distTriang DModX := by
  obtain ⟨δ, hδ⟩ := ringedSpaceModule_derivedMayerVietoris_triangle U V hUV
  exact ⟨δ.app E, hδ E⟩

end

end AlgebraicGeometry.RingedSpace
