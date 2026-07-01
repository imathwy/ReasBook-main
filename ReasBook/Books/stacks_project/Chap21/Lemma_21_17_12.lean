import Mathlib
import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed
site `(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteModules (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (ringedSiteModules 𝒪)]
variable [HasZeroObject (ringedSiteModules 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModules 𝒪)]
variable [Abelian (ringedSiteModules 𝒪)]
variable [CategoryWithHomology (ringedSiteModules 𝒪)]
variable [HasCountableCoproducts (ringedSiteModules 𝒪)]
variable [MonoidalCategory (ringedSiteModules 𝒪)]
variable [MonoidalPreadditive (ringedSiteModules 𝒪)]
variable [HasColimits (ringedSiteModules 𝒪)]
variable [(curriedTensor (ringedSiteModules 𝒪)).Additive]
variable [∀ X : ringedSiteModules 𝒪,
  ((curriedTensor (ringedSiteModules 𝒪)).obj X).Additive]
variable [∀ (X Y : CochainComplex (ringedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (ringedSiteModules 𝒪))]

-- Proof sketch: choose a quasi-isomorphism `K^• ⟶ F^•` from a K-flat complex using Lemma
-- `21.17.11`. Lemma `21.17.3` shows that tensoring this comparison with either `P^•` or `Q^•`
-- gives quasi-isomorphisms on the vertical maps, and tensoring the quasi-isomorphism `α` with the
-- K-flat complex `K^•` gives a quasi-isomorphism on the top horizontal map. The commutative
-- square then forces the bottom horizontal map to be a quasi-isomorphism.
/-- Lemma 21.17.12: if `α : \mathcal P^\bullet ⟶ \mathcal Q^\bullet` is a quasi-isomorphism
between K-flat cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C,
\mathcal O)`, then for every cochain complex `\mathcal F^\bullet` the induced map
`\mathrm{Tot}(\mathrm{id}_{\mathcal F^\bullet} \otimes \alpha) :
\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal P^\bullet) ⟶
\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal Q^\bullet)` is a quasi-isomorphism.
-/
theorem quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (F P Q : CochainComplex (ringedSiteModules 𝒪) ℤ)
    (hP : CochainComplex.IsKFlat P) (hQ : CochainComplex.IsKFlat Q)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) α) := sorry

end SheafOfModules.RingedSite
