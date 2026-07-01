import Mathlib
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the fixed site. -/
private abbrev ringedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringSheaf J 𝒪)

/-- A same-site morphism of structure sheaves, written in the form expected by
`SheafOfModules.pushforward`. -/
private abbrev sameSiteStructureMap (𝒪 𝒪' : Sheaf J CommRingCat.{u}) :=
  ringSheaf J 𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj (ringSheaf J 𝒪')

-- Proof sketch: the textbook functor `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', -)` is
-- characterized as the right adjoint of restriction of scalars along
-- `\mathcal O \to \mathcal O'`. This declaration records that canonical adjoint on module sheaves.
/-- Restriction of scalars along a same-site morphism of sheaves of rings has its canonical right
adjoint. -/
private instance instPushforwardIsLeftAdjoint
    (p : sameSiteStructureMap 𝒪 𝒪') :
    (SheafOfModules.pushforward p).IsLeftAdjoint := sorry

/-- The coextension-of-scalars functor on module sheaves representing
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', -)`. -/
private abbrev changeOfRingsCoextend
    (p : sameSiteStructureMap 𝒪 𝒪') :
    ringedSiteModules 𝒪 ⥤ ringedSiteModules 𝒪' :=
  (SheafOfModules.pushforward p).rightAdjoint

-- Proof sketch: restriction of scalars on module sheaves is exact because it does not change the
-- underlying sheaf of abelian groups and only modifies the scalar action along the map of sheaves
-- of rings.
/-- Restriction of scalars along a same-site morphism of sheaves of rings is exact on module
sheaves. -/
private theorem changeOfRingsPushforward_exact
    (p : sameSiteStructureMap 𝒪 𝒪') :
    exactFunctor (ringedSiteModules 𝒪') (ringedSiteModules 𝒪)
      (SheafOfModules.pushforward p) := sorry

-- Proof sketch: apply Lemma `13.31.9` to the adjunction between restriction of scalars
-- `SheafOfModules.pushforward p` and its right adjoint `changeOfRingsCoextend p`. The exactness
-- input is `changeOfRingsPushforward_exact p`, and Lemma `18.27.8` identifies the resulting right
-- adjoint on complexes with the textbook complex
-- `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', \mathcal I^\bullet)`.
/-- Lemma 21.20.11: for a site, a map of sheaves of rings `\mathcal O \to \mathcal O'`, and a
K-injective complex `\mathcal I^\bullet` of `\mathcal O`-modules, the coextension-of-scalars
complex representing `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', \mathcal I^\bullet)` is
K-injective as a complex of `\mathcal O'`-modules. -/
theorem changeOfRingsCoextendComplex_isKInjective
    (p : sameSiteStructureMap 𝒪 𝒪')
    (I : CochainComplex (ringedSiteModules 𝒪) ℤ) [I.IsKInjective] :
    let F := changeOfRingsCoextend p
    let K :=
      ((F.mapHomologicalComplex (up ℤ)).obj I)
    CochainComplex.IsKInjective K := sorry

end
