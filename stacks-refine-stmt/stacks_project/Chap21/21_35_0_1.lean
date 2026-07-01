import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

section

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Abelian Mod]
variable [MonoidalCategory (DerivedCategory Mod)]
variable [BraidedCategory (DerivedCategory Mod)]
variable [MonoidalClosed (DerivedCategory Mod)]

local notation "D" => DerivedCategory Mod

/- Domain-style sampling for 21.35.0.1:
- primary domain: the closed monoidal structure on the derived category `D(\mathcal O)` of sheaves
  of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ihom.adjunction`,
  `MonoidalClosed.uncurry`,
  `MonoidalClosed.internalHomAdjunction₂.homEquiv`,
  `β_`;
- best owner abstraction: the chapter owner is `ringedSiteModuleCategory J 𝒪`; on its derived
  category `D = DerivedCategory (ringedSiteModuleCategory J 𝒪)`, the core closed-monoidal owner
  is `ihom.adjunction L`, and the Stacks Project tensor order `K ⊗ L` is obtained by transporting
  that owner along the braiding `β_ K L`.

Source/core/bridge triage:
- `source-facing`: the textbook bijection
  `Hom(K, R\mathcal H\!\mathit{om}(L, M)) ≃ Hom(K ⊗^{\mathbf L} L, M)`;
- `core/canonical`: `(ihom.adjunction L).homEquiv K M`;
- `bridge/view`: transport across `(β_ K L).symm.homCongr (Iso.refl M)` from `L ⊗ K` to `K ⊗ L`.

Primitive data versus derived API:
- primitive data: the chapter owner category `ringedSiteModuleCategory J 𝒪` and its derived
  category `D`, together with the monoidal closed structure and braiding on `D`;
- derived API: the textbook-order Hom-bijection, obtained from the owner adjunction plus the
  braiding.

This numbered item is recall-only: it should not keep a parallel ringed-site-specific owner
definition. -/

/- Core recall: the owner equivalence is `ihom.adjunction`; the Stacks Project tensor order
`K ⊗ L` is its transport across the braiding `β_ K L`. -/
recall ihom.adjunction

/- Specialized check for 21.35.0.1. -/
#check
  fun (K L M : D) ↦
    ((((ihom.adjunction L).homEquiv K M).symm.trans
        ((β_ K L).symm.homCongr (Iso.refl M))) :
      (K ⟶ (ihom L).obj M) ≃ (K ⊗ L ⟶ M))

-- Proof sketch: start from the closed-monoidal adjunction
-- `Hom(L ⊗ K, M) ≃ Hom(K, (ihom L).obj M)` and then transport along the braiding
-- `β_ K L : K ⊗ L ≅ L ⊗ K` to rewrite the source tensor factor order into the textbook form.
/-- Applying the derived internal-Hom adjunction sends a morphism
`K ⟶ R\mathcal H\!\mathit{om}(L, M)` to the corresponding morphism
`K \otimes_\mathcal O^{\mathbf L} L ⟶ M`. -/
theorem ringedSiteDerivedInternalHomAdjunction_apply
    {K L M : D}
    (f : K ⟶ (ihom L).obj M) :
    ((((ihom.adjunction L).homEquiv K M).symm.trans
        ((β_ K L).symm.homCongr (Iso.refl M))) f) =
      (β_ K L).hom ≫ MonoidalClosed.uncurry f := sorry

end

end

end SheafOfModules.RingedSite
