import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6
import StacksProject_2024.stacks_project.Chap21.RingedSiteDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Domain-style sampling for Lemma 21.35.2:
- primary domain: the braided closed monoidal structure on `D = RingedSiteDerived J 𝒪`;
- sampled owner declarations:
  `RingedSiteDerived`,
  `CategoryTheory.MonoidalClosed.internalHomTensorIso`,
  `MonoidalClosed.braidedHomEquiv`,
  `MonoidalClosed.braidedHomEquiv_symm_apply`,
  the theorem-surface notation `K ⟹ L`;
- best owner abstraction: this item is recall-only. Its source-facing content is exactly the
  generic owner `CategoryTheory.MonoidalClosed.internalHomTensorIso`, specialized to the derived
  category `D = RingedSiteDerived J 𝒪` of sheaves of `𝒪`-modules on a ringed site;
- primitive data: the ambient braided monoidal closed structure on `D` and the objects
  `K`, `L`, and `M`;
- derived API: the objectwise currying isomorphism
  `K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`.

Source/core/bridge triage:
- `source-facing`: the textbook objectwise isomorphism of Lemma `21.35.2`;
- `core/canonical`: `CategoryTheory.MonoidalClosed.internalHomTensorIso`;
- `bridge/view`: the ringed-site specialization of
  `MonoidalClosed.braidedHomEquiv_symm_apply`.
-/

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Lemma 21.35.2: for objects `K`, `L`, `M : D`, there is a canonical isomorphism
`K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`.
This is the generic owner theorem `CategoryTheory.MonoidalClosed.internalHomTensorIso`,
 specialized to `D = RingedSiteDerived J 𝒪`. Taking `H⁰(C, -)` recovers `21.35.0.1`. -/
recall CategoryTheory.MonoidalClosed.internalHomTensorIso

/- Specialized check for Lemma 21.35.2. -/
#check
  (internalHomTensorIso : ∀ K L M : D, (K ⟹ (L ⟹ M)) ≅ (K ⊗ L) ⟹ M)

/-- Applying the source-order tensor-internal-Hom owner `MonoidalClosed.braidedHomEquiv` to the
comparison of Lemma `21.35.2` identifies its underlying morphism with the corresponding owner-side
uncurrying composite. -/
theorem ringedSiteDerivedInternalHomTensorIso_spec (K L M : D) :
    (braidedHomEquiv (K ⟹ (L ⟹ M)) (K ⊗ L) M).symm (internalHomTensorIso K L M).hom =
      (β_ (K ⟹ (L ⟹ M)) (K ⊗ L)).hom ≫ uncurry (internalHomTensorIso K L M).hom := by
  simpa using
    MonoidalClosed.braidedHomEquiv_symm_apply (internalHomTensorIso K L M).hom

end

end SheafOfModules.RingedSite
