import Mathlib
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable {S : ShortComplex (CochainComplex Mod ℤ)}

/- Domain-style sampling for Lemma 21.17.7:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site in a short
  exact sequence;
- inspected owner declarations:
  `ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃_of_flat_X₃`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the primitive owner data are the short complex `S` and its short
  exactness proof `hS : S.ShortExact`; the three K-flatness conclusions are derived API attached
  to the owner namespace `CategoryTheory.ShortComplex.ShortExact`;
- primitive vs derived: primitive data are only `S`, `hS`, and the termwise flatness hypothesis on
  `S.X₃`; the K-flatness of `S.X₁`, `S.X₂`, `S.X₃` remains theorem-level derived API.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of the short-exact two-out-of-three K-flatness
  criterion from the Stacks Project;
- `core/canonical`: the short-exact owner namespace `CategoryTheory.ShortComplex.ShortExact`;
- `bridge/view`: the owner predicate `CochainComplex.IsKFlat` on the three terms of `S`. -/

-- Proof sketch: for any acyclic complex `L`, Lemma `18.28.9` gives a short exact sequence of
-- tensor complexes
-- `0 ⟶ Tot(L ⊗ K₁) ⟶ Tot(L ⊗ K₂) ⟶ Tot(L ⊗ K₃) ⟶ 0`
-- because the terms of `K₃` are flat. If `K₁` and `K₂` are K-flat, the first two tensor complexes
-- are acyclic, so the third is acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 21.17.7 (1): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_2^\bullet` are K-flat, then `\mathcal K_3^\bullet` is K-flat. -/
theorem isKFlat_X₃_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: tensor the given short exact sequence with an arbitrary acyclic complex and use
-- Lemma `18.28.9` to preserve short exactness under the termwise flatness hypothesis on
-- `\mathcal K_3^\bullet`. If `K₁` and `K₃` are K-flat, the outer tensor complexes are acyclic, so
-- the middle one is acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 21.17.7 (2): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_2^\bullet` is K-flat. -/
theorem isKFlat_X₂_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: after tensoring with an arbitrary acyclic complex, Lemma `18.28.9` again gives a
-- short exact sequence of tensor complexes because the terms of `K₃` are flat. If `K₂` and `K₃`
-- are K-flat, the last two tensor complexes are acyclic, and the first becomes acyclic by the
-- associated long exact sequence on cohomology sheaves.
/-- Lemma 21.17.7 (3): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_2^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_1^\bullet` is K-flat. -/
theorem isKFlat_X₁_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact
