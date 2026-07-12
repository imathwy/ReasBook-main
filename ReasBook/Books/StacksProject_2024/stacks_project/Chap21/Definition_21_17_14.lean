import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

recall CategoryTheory.Tor

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Domain-style sampling for Definition 21.17.14:
- primary domain: monoidal homological algebra of sheaves of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CategoryTheory.Tor`,
  `SheafOfModules.RingedSite.derivedTensorProduct`;
- best owner abstraction: the ambient owner category is `ringedSiteModuleCategory J 𝒪`, and the
  `p`-th Tor construction is the canonical bifunctor `Tor Mod p`;
- primitive data versus derived API: the primitive data are only the ringed site and the ambient
  monoidal/projective-resolution structure on `Mod`; the object `((Tor Mod p).obj ℱ).obj 𝒢` is
  derived API obtained by evaluating the canonical owner.

Source/core/bridge triage:
- `source-facing`: the object `Tor_p^𝒪(ℱ, 𝒢)`;
- `core/canonical`: `CategoryTheory.Tor`;
- `bridge/view`: this file is only the ringed-site specialization of that canonical owner, so it
  should recall `CategoryTheory.Tor` directly, use `ringedSiteModuleCategory` from its owner
  file, and expose only the thin object-level bridge and notation for evaluating that bifunctor on
  sheaves. -/

variable [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasProjectiveResolutions (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪

/-- Helper for Definition 21.17.14: the ambient category `Mod` of sheaves of `𝒪`-modules is
abelian via the canonical `SheafOfModules` owner instance. -/
local instance : Abelian Mod := SheafOfModules.instAbelian (ringSheaf J 𝒪)

/- The source object `Tor_p^𝒪(ℱ, 𝒢)` is the evaluation of the canonical bifunctor `Tor Mod p`
on the two module sheaves. -/
/-- Definition 21.17.14 specialized to a ringed site: the `p`-th Tor object of two `𝒪`-modules
is the value of the canonical bifunctor `Tor Mod p`. -/
@[stacks 08FF]
abbrev tor (p : ℕ) (ℱ 𝒢 : Mod) : Mod :=
  (((Tor Mod p).obj ℱ).obj 𝒢)

/- Textbook notation for the ringed-site Tor object `Tor[p](ℱ, 𝒢)`. -/
namespace RingedSiteTor

set_option quotPrecheck false in
scoped notation "Tor[" p "](" ℱ ", " 𝒢 ")" => SheafOfModules.RingedSite.tor p ℱ 𝒢

end RingedSiteTor

open scoped RingedSiteTor

end

end SheafOfModules.RingedSite
