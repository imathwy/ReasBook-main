import Mathlib
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site and their
  stability under sequential colimits;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.isKFlat_colimit_of_isFiltered`;
- best owner abstraction: the ambient owner category is `ringedSiteModuleCategory J 𝒪`, and the
  K-flatness predicate is the generic owner `(K : CochainComplex Mod ℤ).IsKFlat`;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The colimit complex and its K-flatness are derived from the ambient
  colimit and the owner predicate, so this file should not keep a parallel local module-category
  alias or a local K-flat wrapper in the theorem surface.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of sequential-colimit stability for K-flat
  complexes;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪` and `CochainComplex.IsKFlat`;
- `bridge/view`: none. This file should state the ringed-site theorem directly using those owners.

The module-category theorem `CochainComplex.isKFlat_colimit_of_isFiltered` is the owner
declaration in the same domain; the present file keeps the genuinely new ringed-site sequential
specialization rather than a duplicate local wrapper around the ambient category or predicate. -/

-- Proof sketch: tensor an arbitrary acyclic complex `ℱ^•` with the sequential diagram `F`.
-- Termwise tensor products commute with the colimit, so
-- `Tot(ℱ^• ⊗ colim_i K_i^•)` is identified with the colimit of the acyclic tensor complexes
-- `Tot(ℱ^• ⊗ K_i^•)`. Exactness of filtered colimits on sheaves of modules then implies that this
-- colimit tensor complex is acyclic.
/-- Lemma 21.17.9: for a system `\mathcal K_1^\bullet \to \mathcal K_2^\bullet \to \cdots` of
K-flat cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, the
sequential colimit `\mathop{\mathrm{colim}}_i \mathcal K_i^\bullet` is K-flat. -/
theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex Mod ℤ)
    [HasColimit F]
    (hF : ∀ i : ℕ, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end SheafOfModules.RingedSite
