import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_27_6
import StacksProject_2024.Chap21.RingedSiteDerivedBasic

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
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

/- Domain-style sampling for Lemma 21.35.8:
- primary domain: the tensor-internal-Hom unit in the braided closed monoidal derived category
  `D = RingedSiteDerived J 𝒪`;
- sampled owner declarations:
  `RingedSiteDerived`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right`;
- best owner abstraction:
  the canonical owner is the generic categorical morphism
  `MonoidalClosed.tensorInternalHomUnit`; Lemma `21.35.8` is only its ringed-site derived-category
  specialization to `D = RingedSiteDerived J 𝒪`;
- primitive data: the braided closed monoidal structure on `D` and the objects `K`, `L`;
- derived API:
  the specialized type of the generic unit morphism and its generic specification and naturality
  lemmas.

Primitive-vs-derived split:
- primitive data: the ambient derived category `D` and the closed-monoidal owner
  `MonoidalClosed.tensorInternalHomUnit`;
- derived API: the ringed-site specialization and the companion generic theorems.

Source/core/bridge triage:
- `source-facing`: the canonical morphism `K ⟶ (ihom L).obj (K ⊗ L)` on `D`;
- `core/canonical`: `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`;
- `bridge/view`: the ringed-site derived-category specialization and the generic companion
  theorems.

This numbered item is recall-only: it should not keep a parallel ringed-site-specific owner
declaration. -/

/- Lemma 21.35.8: the canonical morphism `K ⟶ (ihom L).obj (K ⊗ L)` on
`D = RingedSiteDerived J 𝒪` is the generic owner
`MonoidalClosed.tensorInternalHomUnit`
specialized to the ringed-site derived category. -/
recall tensorInternalHomUnit

/- Specialized check for Lemma 21.35.8. -/
#check
  (tensorInternalHomUnit : ∀ K L : D, K ⟶ (ihom L).obj (K ⊗ L))

/- The coevaluation-plus-braiding formula is the generic owner theorem
`MonoidalClosed.tensorInternalHomUnit_spec`. -/
recall tensorInternalHomUnit_spec

/- Naturality in the first variable is the generic owner theorem
`MonoidalClosed.tensorInternalHomUnit_natural_left`. -/
recall tensorInternalHomUnit_natural_left

/- Naturality in the second variable is the generic owner theorem
`MonoidalClosed.tensorInternalHomUnit_natural_right`. -/
recall tensorInternalHomUnit_natural_right

end

end SheafOfModules.RingedSite
