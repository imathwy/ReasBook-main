import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Definition 21.17.2:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the Chapter 15 owner predicate `CochainComplex.IsKFlat` on
  `CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ`;
- primitive vs derived: the primitive data are only the complex `K`, while preservation of
  acyclic complexes under totalized tensoring is exactly the companion theorem
  `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `\mathcal O`-modules on a
  ringed site;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: no extra bridge is needed, because the ringed-site notion is exactly this owner
  specialized to `ringedSiteModuleCategory J 𝒪`. -/

/- Definition 21.17.2: a cochain complex `\mathcal K^\bullet` of `\mathcal O`-modules on a
ringed site `(\mathcal C, \mathcal O)` is K-flat if for every acyclic cochain complex
`\mathcal F^\bullet`, the totalized tensor product
`\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal K^\bullet)` is acyclic. This is the
canonical owner `CochainComplex.IsKFlat` specialized to `ringedSiteModuleCategory J 𝒪`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

section

variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Preadditive Mod]
variable [HasZeroObject Mod]
variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [(curriedTensor Mod).Additive]
variable [∀ ℱ : Mod, ((curriedTensor Mod).obj ℱ).Additive]
variable (K : CochainComplex Mod ℤ)

/- Source-facing specialization: for a ringed site `(\mathcal C, \mathcal O)`, Definition
21.17.2 uses exactly the Chapter 15 owner predicate and its canonical iff-formulation on
`ringedSiteModuleCategory J 𝒪`. -/
#check K.IsKFlat
#check CochainComplex.isKFlat_iff K

end

end SheafOfModules.RingedSite
