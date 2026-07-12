import StacksProject_2024.Chap20.Lemma_20_34_1
import StacksProject_2024.Chap20.Lemma_20_33_6

open CategoryTheory
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace
open ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetDerived

section

variable {X : RingedSpace.{u}} {Z : Set X}
variable (hZ : IsClosed Z)

/- Domain-style sampling for Lemma 20.34.6:
- primary domain: the localization triangle on `D(𝒪_X)` attached to a closed subset and
  its open complement;
- sampled owner declarations:
  `ModuleDerived`,
  `modulePushforwardFromOpenDerived`,
  `closedSubsetModulePushforwardDerived`,
  `closedSubsetModuleSectionsWithSupportDerived`;
- best owner abstraction:
  `source-facing`: the localization triangle
    `i_*R𝓗_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ i_*R𝓗_Z(K)[1]`;
  `core/canonical`: the Chapter 20 derived owners `R𝓗[hZ]`, `i⋆[hZ]`,
    `moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U`;
  `bridge/view`: the chapter-owned comparison morphisms supplied by the derived adjunctions
    from Lemmas `20.33.6` and `20.34.1`.

Primitive data are just `X`, `Z`, and `hZ`. The closed-subset and open-complement derived
functors are already owned upstream, so this file should state the source-facing triangle using
those owners rather than redeclare a parallel sheaf-module presentation of `D(𝒪_U)` or
its restriction/pushforward functors.
-/

local notation "DModX" => ModuleDerived X
local notation "U" => closedSubsetOpenComplement hZ
local notation "R𝓗ZPush" => R𝓗[hZ] ⋙ i⋆[hZ]
local notation "RPushU" =>
  moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U

-- Proof sketch: choose a functorial K-injective resolution of each object of `D(𝒪_X)`.
-- Restriction to the open complement preserves K-injective complexes, so `Rj_*` is computed by
-- the underived pushforward of the restricted resolution. The right adjoint `𝓗_Z`
-- likewise computes `R𝓗_Z` on the same resolution because it preserves K-injectives.
-- Applying the underived short exact sequence
-- `0 → i_* 𝓗_Z(I) → I → j_*(I|_U) → 0`
-- from Lemma `20.8.1` degreewise produces the desired functorial distinguished triangle.
/-- Lemma 20.34.6: for a ringed space `(X, 𝒪_X)` and a closed subset `Z ⊆ X` with open
complement `U = Zᶜ`, the localization triangle
`i_* R𝓗_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ i_* R𝓗_Z(K)[1]`
is realized functorially in `D(𝒪_X)`. Here `i_* R𝓗_Z` is formalized by `R𝓗ZPush`, while
`Rj_*(K|_U)` is formalized by the canonical composite owner `RPushU`. -/
@[stacks 0G72]
theorem closedSubsetDerived_localCohomology_distinguishedTriangle :
    ∃ δ : RPushU ⟶ R𝓗ZPush ⋙ shiftFunctor DModX (1 : ℤ),
      ∀ K : DModX,
        Triangle.mk
            ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K)
            ((moduleRestrictionToOpenDerivedUnitNatTrans U).app K)
            (δ.app K) ∈ distTriang DModX := sorry

/-- Objectwise companion to Lemma 20.34.6: for each `K ∈ D(𝒪_X)`, the canonical counit
`i_* R𝓗_Z(K) ⟶ K` and canonical unit `K ⟶ Rj_*(K|_U)` extend to a distinguished triangle. -/
theorem closedSubsetDerived_localCohomology_triangle
    (K : DModX) :
    ∃ δ : (RPushU).obj K ⟶ (R𝓗ZPush).obj K⟦(1 : ℤ)⟧,
      Triangle.mk
          ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K)
          ((moduleRestrictionToOpenDerivedUnitNatTrans U).app K)
          δ ∈ distTriang DModX := by
  obtain ⟨δ, hδ⟩ := closedSubsetDerived_localCohomology_distinguishedTriangle hZ
  exact ⟨δ.app K, hδ K⟩

end

end AlgebraicGeometry.RingedSpace
