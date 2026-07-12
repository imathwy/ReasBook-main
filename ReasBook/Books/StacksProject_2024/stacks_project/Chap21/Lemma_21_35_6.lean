import StacksProject_2024.Chap21.RingedSiteDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
section

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.35.6:
- primary domain: the braided closed monoidal structure on the derived category
  `D(𝒪)`;
- sampled owner declarations:
  `RingedSiteDerived`,
  `ringedSiteModuleCategory`,
  `ihom`,
  `MonoidalClosed.comp`,
  `β_`;
- best owner abstraction:
  the canonical owner is the ambient closed-monoidal composition morphism
  `MonoidalClosed.comp`; the ringed-site statement is its source-order braided transport;
- primitive data:
  the derived category `D(𝒪)` with its braided monoidal closed structure, and objects
  `K`, `L`, `M : D(𝒪)`;
- derived API:
  the source-order comparison morphism below.

Source/core/bridge triage:
- `source-facing`: the textbook composition morphism `(L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M)`;
- `core/canonical`: `MonoidalClosed.comp`;
- `bridge/view`: the braiding `β_ (L ⟹ M) (K ⟹ L)` transporting the source tensor factors into
  the owner order expected by `MonoidalClosed.comp`.

This numbered item is therefore a thin `bridge/view` layer, not a second owner: the previous file
duplicated the bridge with an extra `_def` theorem, so the refinement keeps only the bridge itself.
-/

/-- Lemma 21.35.6: for objects `K`, `L`, and `M` of `D(𝒪)` on a ringed site, there is a
canonical composition morphism `(L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M)`, where `A ⟹ B` formalizes the
derived internal Hom `Rℋom(A, B)`. This is the braided source-order transport of the owner
composition morphism `MonoidalClosed.comp`. -/
@[stacks 0A98]
noncomputable def ringedSiteDerivedInternalHomComposition
    (K L M : D) :
    (L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M) :=
  (β_ (L ⟹ M) (K ⟹ L)).hom ≫ MonoidalClosed.comp K L M

end

end

end SheafOfModules.RingedSite
