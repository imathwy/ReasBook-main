import Mathlib
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Definition 21.17.14:
- primary domain: the monoidal homological algebra of sheaves of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CategoryTheory.Tor`,
  `SheafOfModules`,
  `SheafOfModules.RingedSite.derivedTensorProduct`;
- best owner abstraction: the ambient module category owner is `ringedSiteModuleCategory J 𝒪`,
  and the `p`-th Tor construction is the canonical bifunctor `Tor Mod p`;
- primitive data versus derived API: primitive data are only the ringed site and the ambient
  monoidal/projective-resolution structure on `Mod`; the object
  `((Tor Mod p).obj ℱ).obj 𝒢` is derived API obtained by evaluating the canonical owner.

Source/core/bridge triage:
- `source-facing`: the object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`;
- `core/canonical`: `Tor Mod p`;
- `bridge/view`: this file is only the ringed-site specialization of that canonical owner, so it
  should reuse `ringedSiteModuleCategory` and `Tor` directly rather than reintroducing a local
  category alias. -/

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)]
variable (p : ℕ)

/- Definition 21.17.14: for a ringed site `(\mathcal C, \mathcal O)`, the `p`-th Tor on
`Mod(\mathcal O)` is the canonical monoidal `Tor` bifunctor. Evaluated at `\mathcal F` and
`\mathcal G`, it is the source object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`,
which the text describes as `H^{-p}(\mathcal F \otimes_\mathcal O^{\mathbf L} \mathcal G)`. -/
#check (Tor Mod p)

variable (ℱ 𝒢 : Mod)

/- Companion recall: evaluating the canonical Tor bifunctor at `\mathcal F` and `\mathcal G`
gives the object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`. -/
#check (((Tor Mod p).obj ℱ).obj 𝒢)
