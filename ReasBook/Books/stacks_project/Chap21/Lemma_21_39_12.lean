import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- The `RingCat`-valued structure sheaf on a category, viewed through the chaotic topology. -/
private abbrev chaoticRingSheaf :
    Sheaf (⊥ : GrothendieckTopology C) RingCat.{max u v} :=
  (sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of `\mathcal O`-modules on the chaotic site. -/
private abbrev moduleOnCategory :=
  SheafOfModules (chaoticRingSheaf 𝒪)

variable {𝒪' : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v}}
variable [Abelian (moduleOnCategory 𝒪)]

/-- The target structure sheaf `\mathcal O'`, regarded by restriction of scalars as an
`\mathcal O`-module. -/
private abbrev targetAsSourceModule (α : 𝒪 ⟶ 𝒪') :
    moduleOnCategory 𝒪 :=
  (SheafOfModules.restrictScalars
      ((sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).map α)).obj
    (SheafOfModules.unit (chaoticRingSheaf 𝒪'))

-- Proof sketch: resolve `K` by complexes built from the flat generators `j_{U!}\mathcal O_U`,
-- compare the chosen derived lower shriek of `K` with the chosen derived lower shriek of
-- `K \otimes_{\mathcal O}^{\mathbf L} \mathcal O'`, and use the hypothesis that the structure
-- module map becomes an isomorphism after `L\pi_!` to descend the comparison from the generators
-- to all of `D(\mathcal O)`.
/-- Lemma 21.39.12: for a category with the chaotic topology and a morphism of sheaves of rings
`\mathcal O \to \mathcal O'`, if the induced map
`L\pi_!(\mathcal O) \to L\pi_!(\mathcal O')` is an isomorphism, then every object `K` of
`D(\mathcal O)` has the same derived lower shriek as its derived tensor product
`K \otimes_{\mathcal O}^{\mathbf L} \mathcal O'`. Here `structureModuleMap` is the chosen
`\mathcal O`-linear realization of the ring map on unit modules, and the functors
`derivedLowerShriek` and `derivedTensorWithStructureMap` are the chosen models of these two
derived constructions. -/
lemma derivedLowerShriek_isomorphic_after_tensor_structureSheafChange
    (α : 𝒪 ⟶ 𝒪')
    (structureModuleMap :
      SheafOfModules.unit (chaoticRingSheaf 𝒪) ⟶ targetAsSourceModule 𝒪 α)
    (derivedLowerShriek :
      DerivedCategory (moduleOnCategory 𝒪) ⥤ DerivedCategory AddCommGrpCat.{max u v})
    (derivedTensorWithStructureMap :
      DerivedCategory (moduleOnCategory 𝒪) ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (hα : IsIso
      (derivedLowerShriek.map
        ((DerivedCategory.singleFunctor (moduleOnCategory 𝒪) (0 : ℤ)).map
          structureModuleMap)))
    (K : DerivedCategory (moduleOnCategory 𝒪)) :
    IsIsomorphic
      (derivedLowerShriek.obj K)
      (derivedLowerShriek.obj (derivedTensorWithStructureMap.obj K)) := sorry

end CategoryTheory.ModulesOnCategory
