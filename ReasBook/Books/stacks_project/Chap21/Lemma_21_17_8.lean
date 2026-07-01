import Mathlib
import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]

/- Domain-style sampling for Lemma 21.17.8:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the ambient module category is the Chapter 18 owner
  `ringedSiteModuleCategory J 𝒪`, and K-flatness is the Chapter 15 owner predicate `K.IsKFlat`
  on complexes in that category;
- primitive data: the complex `K`, the bounded-above hypothesis, and termwise flatness of the
  modules `K.X n`;
- derived API: the K-flatness conclusion.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion on the ringed site;
- `core/canonical`: `ringedSiteModuleCategory` and `CochainComplex.IsKFlat`;
- `bridge/view`: this specialization of the canonical K-flat owner to ringed-site modules.
-/

-- Proof sketch: let `ℒ` be an acyclic complex of `\mathcal O`-modules. Write `ℒ` as the
-- termwise filtered colimit of its bounded-above truncations `τ_{\le m} ℒ`, so the total tensor
-- product with `K` is the corresponding filtered colimit of the total tensors with these
-- truncations. It is therefore enough to treat bounded-above acyclic `ℒ`. For such `ℒ`, apply the
-- homology spectral sequence of the double complex `ℒ ⊗ K`; the `E₁`-page is
-- `H^p(ℒ ⊗ K^q)`, which vanishes because each term `K^q` is flat and `ℒ` is acyclic. Hence the
-- total tensor product is acyclic, so `K` is K-flat.
/-- Lemma 21.17.8: a bounded above cochain complex of flat `\mathcal O`-modules on a ringed site
`(\mathcal C, \mathcal O)` is K-flat, expressed in the canonical owner predicate `K.IsKFlat`.
-/
theorem isKFlat_of_boundedAbove_of_flat
    (K : CochainComplex Mod ℤ)
    (hbounded : IsBoundedAbove K)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    K.IsKFlat := sorry

end SheafOfModules.RingedSite
