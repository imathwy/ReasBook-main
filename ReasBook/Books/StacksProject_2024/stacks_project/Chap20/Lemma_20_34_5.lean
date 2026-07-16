import StacksProject_2024.stacks_project.Chap20.Sections_on_open_global
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_4

open CategoryTheory
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceClosedSubsetDerived
open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.34.5:
- primary domain: the localization triangle for derived global sections with support in a closed
  subset and derived sections on the open complement, valued over `Γ(X, 𝒪_X)`;
- inspected owner declarations:
  `moduleDerivedGlobalSections`,
  `closedSubsetModuleGlobalSectionsWithSupportDerived`,
  `closedSubsetModuleGlobalSectionsWithSupportFunctor`,
  `moduleSectionsRestrictionToGlobalDerived`,
  `moduleDerivedSectionsOverGlobal`;
- best owner abstraction:
  `source-facing`: the distinguished triangle
    `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`;
  `core/canonical`: the Chapter 20 owners `moduleDerivedGlobalSections`,
  `globalSectionsRing`, `closedSubsetModuleGlobalSectionsWithSupportFunctor`,
  `closedSubsetModuleGlobalSectionsWithSupportDerived`, and
  `moduleDerivedSectionsOverGlobal`;
  `bridge/view`: this file, which states the localization triangle directly in terms of those
    existing owners, keeping the open-complement term read through the chapter bridge
    `moduleDerivedSectionsOverGlobal` and characterizing the first two maps via the clean
    localization model obtained by applying `RΓ(X,-)` to Lemma `20.34.6`.
- primitive data: `X`, `Z`, and the closedness proof `hZ`;
- derived API: the distinguished triangle below.
-/

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DΓX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "RΓ" => moduleDerivedGlobalSections X

local notation "U" => closedSubsetOpenComplement hZ
local notation "RΓU" => moduleDerivedSectionsOverGlobal X U

-- Proof sketch: apply the exact derived global-sections functor `RΓ(X,-)` to the localization
-- triangle of Lemma `20.34.6`, then identify the open-complement term with the chapter owner
-- `moduleDerivedSectionsOverGlobal X U`.
/-- Lemma 20.34.5: for a ringed space `(X, 𝒪_X)`, a closed subset `Z ⊆ X`, and open complement
`U = X \ Z`, the canonical forget-support and restriction morphisms
`RΓ_Z(X, K) ⟶ RΓ(X, K)` and `RΓ(X, K) ⟶ RΓ(U, K)` extend to a distinguished triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
in `D(Γ(X, 𝒪_X))`. Here `RΓ_Z(X,-)` is the chapter owner
`closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ`, and `RΓ(U,-)` is formalized by the
chapter owner `moduleDerivedSectionsOverGlobal X U`, viewed in `D(Γ(X, 𝒪_X))` by restriction of
scalars along `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_X)`. This is the derived-global-sections image of the
localization triangle of Lemma `20.34.6`. -/
@[stacks 0G71]
theorem derivedGlobalSectionsWithSupport_distinguishedTriangle :
    ∃ δ : RΓU ⟶ RΓ_[hZ] ⋙ shiftFunctor DΓX (1 : ℤ),
      ∀ K : DModX,
        Triangle.mk
            ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app K)
            ((moduleDerivedSectionsOverGlobalRestrictionNatTrans X U).app K)
            (δ.app K) ∈
          distTriang DΓX := by
  sorry

/-- Objectwise companion to Lemma 20.34.5: for each `K ∈ D(𝒪_X)`, there are morphisms
`RΓ_Z(X, K) ⟶ RΓ(X, K)` and `RΓ(X, K) ⟶ RΓ(U, K)` given by the canonical forget-support and
restriction maps, and a morphism `δ_K : RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`, forming a distinguished
triangle. -/
theorem derivedGlobalSectionsWithSupport_triangle
    (K : DModX) :
    ∃ δ : (RΓU).obj K ⟶ ((RΓ_[hZ]).obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app K)
          ((moduleDerivedSectionsOverGlobalRestrictionNatTrans X U).app K)
          δ ∈
        distTriang DΓX := by
  obtain ⟨δ, hδ⟩ := derivedGlobalSectionsWithSupport_distinguishedTriangle hZ
  exact ⟨δ.app K, hδ K⟩

end

end AlgebraicGeometry.RingedSpace
