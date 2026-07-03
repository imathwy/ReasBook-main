import Mathlib
import StacksProject_2024.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.48.5:
- primary domain: the symmetric monoidal structure on the derived category of sheaves of modules on
  a ringed site;
- sampled owner declarations:
  `RingedSiteModules`,
  `DerivedCategory`,
  `SymmetricCategory`,
  `SymmetricCategory.symmetry`;
- best owner abstraction: `SymmetricCategory (DerivedCategory (RingedSiteModules J 𝒪))`;
- primitive data: the ringed-site module category `RingedSiteModules J 𝒪`, its derived category,
  and the ambient monoidal/symmetric structure on that derived category;
- derived API: the canonical braiding `β_` and the symmetry theorem
  `SymmetricCategory.symmetry`.

Source/core/bridge triage:
- `source-facing`: the commutativity constraint for derived tensor product on `D(\mathcal O)` is
  involutive;
- `core/canonical`: `SymmetricCategory DMod` for `DMod := DerivedCategory (RingedSiteModules J 𝒪)`;
- `bridge/view`: the specialization of `SymmetricCategory.symmetry` to objects of `D(\mathcal O)`.

This item is bridge/view only. The previous local wheel duplicated the canonical owner
`SymmetricCategory.symmetry`; the refined file now recalls that owner directly on the chapter
vocabulary `D(\mathcal O)` without importing unrelated ringed-site restriction API.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [MonoidalCategory DMod]
variable [SymmetricCategory DMod]

/- Lemma 21.48.5: for the derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on
a ringed site, the symmetry relation for the derived-tensor braiding is exactly the canonical
theorem `SymmetricCategory.symmetry` specialized to `D(\mathcal O)`. -/
recall SymmetricCategory.symmetry (X Y : DMod) :
  (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

end

end SheafOfModules.RingedSite
