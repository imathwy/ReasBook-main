import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_59_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (RingedSiteModules 𝒪)]
variable [HasZeroObject (RingedSiteModules 𝒪)]
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ X : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules 𝒪))]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site and closure of
  K-flatness under totalized tensor products;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the owner is the predicate `K.IsKFlat` on cochain complexes, and the
  tensor product complex is the canonical derived object `HomologicalComplex.tensorObj K L`;
- primitive vs derived: the primitive data are only the complexes `K`, `L` and their K-flatness
  hypotheses. The tensor product complex is derived from the ambient monoidal structure, so this
  ringed-site file should expose only the specialization of the owner theorem rather than a
  parallel local statement.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: specialization of that owner theorem to `SheafOfModules.RingedSite`. -/

/- Lemma 21.17.5: if `\mathcal K^\bullet` and `\mathcal L^\bullet` are K-flat cochain complexes of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, then the totalized tensor
product `\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet)` is K-flat. This
is exactly the specialization of the canonical owner theorem
`CochainComplex.tensorObj_isKFlat_of_isKFlat` to `RingedSiteModules 𝒪`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end SheafOfModules.RingedSite
