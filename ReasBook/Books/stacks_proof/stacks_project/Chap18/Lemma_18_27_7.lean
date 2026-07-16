import Mathlib
import stacks_proof.stacks_project.Chap18.Lemma_18_19_2
-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.27.7:
- primary domain: monoidal closed categories of presheaves and sheaves of modules;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  the canonical instance `PreservesColimits (tensorLeft A)`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the public owner is the left-tensor functor `tensorLeft ℱ`, with colimit preservation already
  supplied canonically by the internal-Hom adjunction `ihom.adjunction ℱ`;
- primitive data:
  a fixed module object `ℱ` in the ambient monoidal closed module category;
- derived API:
  the `PreservesColimits (tensorLeft ℱ)` instance, together with its presheaf and ringed-site
  specializations.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that tensoring on the left with a fixed module commutes
  with arbitrary colimits on `PMod(𝒪)` and `Mod(𝒪)`;
- `core/canonical`: `tensorLeft ℱ` and its canonical `PreservesColimits` instance;
- `bridge/view`: the specializations below to presheaf modules and to the chapter owner
  `ringedSiteModuleCategory J 𝒪`.

Primitive-vs-derived split:
- primitive data: only the ambient monoidal closed module category and the chosen object `ℱ`;
- derived API: colimit preservation of `tensorLeft ℱ`. No local theorem wrapper is needed because
  the exact interface is already owned upstream.
-/

section PresheafModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
local notation "PMod" => PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)
variable [MonoidalCategory PMod]
variable [MonoidalClosed PMod]
variable (ℱ : PMod)

/- Lemma 18.27.7 (1): for a presheaf of rings `𝒪` and a fixed presheaf of `𝒪`-modules `ℱ`, the
functor `𝒢 ↦ ℱ ⊗ 𝒢` on `PMod(𝒪)` commutes with arbitrary colimits. This is exactly the canonical
instance `PreservesColimits (tensorLeft ℱ)`. -/
#check
  (show PreservesColimits (tensorLeft ℱ : PMod ⥤ PMod) from
    (ihom.adjunction ℱ).leftAdjoint_preservesColimits)

end PresheafModules

section RingedSiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
local notation "ModOJ" => ringedSiteModuleCategory J 𝒪
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable (ℱ : ModOJ)

/- Lemma 18.27.7 (2): on a ringed site `(C, J, 𝒪)`, for a fixed sheaf of `𝒪`-modules `ℱ`, the
functor `𝒢 ↦ ℱ ⊗ 𝒢` on `Mod(𝒪)` commutes with arbitrary colimits. This is the same canonical
owner instance `PreservesColimits (tensorLeft ℱ)`, expressed on the chapter owner category
`ringedSiteModuleCategory J 𝒪`. -/
#check
  (show PreservesColimits (tensorLeft ℱ : ModOJ ⥤ ModOJ) from
    (ihom.adjunction ℱ).leftAdjoint_preservesColimits)

end RingedSiteModules
