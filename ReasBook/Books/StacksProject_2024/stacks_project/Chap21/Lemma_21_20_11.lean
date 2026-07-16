import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_9
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open SheafOfModules.RingedSite
  (coextendAlong ringedSiteModuleCategory restrictionAlong restrictionAlong_exact)

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.20.11:
- primary domain: same-site change of rings for sheaves of modules on a ringed site and
  preservation of `CochainComplex.IsKInjective` under exact adjunctions;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `restrictionAlong`,
  `coextendAlong`,
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction: the source-facing same-site coextension functor `coextendAlong α`,
  viewed as the canonical right adjoint of the Chapter 18 owner `restrictionAlong α`;
- primitive data: the morphism of structure sheaves `α : 𝒪 ⟶ 𝒪'` and the K-injective complex
  `I`;
- derived API: the K-injectivity statement for the induced coextension-of-scalars complex.

Source/core/bridge triage:
- `source-facing`: the coextension/internal-Hom complex `Hom_𝒪(𝒪', I^•)`, realized by
  `coextendAlong α`;
- `core/canonical`: `ringedSiteModuleCategory`, `restrictionAlong`, `coextendAlong`, and
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: the owner-level Chapter 18 facts `restrictionAlong_exact` and the
  `IsLeftAdjoint` instance on `restrictionAlong α`.

The earlier version kept the theorem organized around a chosen right adjoint of same-site
restriction. The refined statement instead uses the source-facing owner `coextendAlong α`, so the
public API is phrased in terms of the coextension/local-Hom functor rather than implementation
choice data.
-/

-- Proof sketch: `coextendAlong α` is, by construction, the canonical right adjoint of the
-- same-site restriction functor `restrictionAlong α`. Apply Lemma `13.31.9` to that adjunction,
-- using the owner-level exactness theorem `restrictionAlong_exact α`.
instance coextendAlong_mapHomologicalComplex_isKInjective
    (α : 𝒪 ⟶ 𝒪')
    [(restrictionAlong α).IsLeftAdjoint]
    (I : CochainComplex (Mod(𝒪)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((coextendAlong α).mapHomologicalComplex (up ℤ)).obj I) := by
  exact right_adjoint_preserves_isKInjective_of_exact_left_adjoint
    (coextendAlong α) (restrictionAlong α)
    (Adjunction.ofIsLeftAdjoint (restrictionAlong α))
    (restrictionAlong_exact α) I

/-- Lemma 21.20.11: for a site, a map of sheaves of rings `𝒪 ⟶ 𝒪'`, and a K-injective complex
`I^•` of `𝒪`-modules, the coextension-of-scalars complex
`((coextendAlong α).mapHomologicalComplex (up ℤ)).obj I`, representing `Hom_𝒪(𝒪', I^•)`, is
K-injective as a complex of `𝒪'`-modules. -/
@[stacks 093Z]
theorem changeOfRingsCoextendComplex_isKInjective
    (α : 𝒪 ⟶ 𝒪')
    [(restrictionAlong α).IsLeftAdjoint]
    (I : CochainComplex (Mod(𝒪)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((coextendAlong α).mapHomologicalComplex (up ℤ)).obj I) :=
  inferInstance

end
