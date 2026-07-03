import Mathlib
import StacksProject_2024.Chap18.Lemma_18_27_9
import StacksProject_2024.Chap21.Definition_21_17_2
import StacksProject_2024.Chap21.Lemma_21_34_4
import StacksProject_2024.Chap21.Lemma_21_34_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).PreservesZeroMorphisms]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).PreservesZeroMorphisms]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]

/-- The canonical morphism
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)`
induced by precomposition with `f` and postcomposition with `g`. -/
noncomputable def ringedSiteModuleComplexInternalHomMap
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : L' ⟶ L) (g : I' ⟶ I) :
    ringedSiteModuleComplexInternalHom L I' ⟶
      ringedSiteModuleComplexInternalHom L' I :=
  ringedSiteModuleComplexInternalHomPost g ≫
    ringedSiteModuleComplexInternalHomPre f

-- Proof sketch: apply Lemma `21.34.6` on every localization `(\mathcal C/U, \mathcal O_U)` to
-- identify the degree-zero cohomology sheaf of each internal-Hom complex with the presheaf
-- `U ↦ Hom_{D(\mathcal O_U)}(L|_U, M|_U)`. The quasi-isomorphisms `f` and `g` identify the source
-- and target representatives of the same derived objects, so this map induces isomorphisms on all
-- cohomology sheaves. Therefore the canonical map of internal-Hom complexes is a quasi-isomorphism.
/-- Lemma 21.34.7: for a ringed site `(\mathcal C, \mathcal O)`, if
`(\mathcal I')^\bullet \to \mathcal I^\bullet` is a quasi-isomorphism of K-injective complexes of
`\mathcal O`-modules and `(\mathcal L')^\bullet \to \mathcal L^\bullet` is a quasi-isomorphism of
complexes of `\mathcal O`-modules, then the induced morphism
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)`
is a quasi-isomorphism. -/
theorem quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : L' ⟶ L) (g : I' ⟶ I)
    (hfi : QuasiIso f) (hgi : QuasiIso g)
    (hI' :
      ∀ {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (α : K ⟶ I'),
        K.Acyclic → Nonempty (Homotopy α 0))
    (hI :
      ∀ {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (α : K ⟶ I),
        K.Acyclic → Nonempty (Homotopy α 0))
    [∀ i, (ringedSiteModuleComplexInternalHom L I').HasHomology i]
    [∀ i, (ringedSiteModuleComplexInternalHom L' I).HasHomology i] :
    QuasiIso (ringedSiteModuleComplexInternalHomMap f g) := sorry

end

end SheafOfModules.RingedSite
