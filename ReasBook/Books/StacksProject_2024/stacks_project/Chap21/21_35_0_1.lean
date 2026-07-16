import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

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

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [BraidedCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [MonoidalClosed (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

local notation "D" => DerivedCategory (ringedSiteModuleCategory J 𝒪)
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for 21.35.0.1:
- primary domain: the closed monoidal structure on the derived category `D(\mathcal O)` of sheaves
  of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `braidedHomEquiv`,
  `MonoidalClosed.braidedHomEquiv_symm_apply`,
  `internalHomAdjunction₂.homEquiv`;
- best owner abstraction: the chapter owner is `braidedHomEquiv`; on the derived category
  `D = DerivedCategory (ringedSiteModuleCategory J 𝒪)`, it packages the closed-monoidal
  adjunction in the textbook tensor order `K ⊗ L`, obtained from
  `internalHomAdjunction₂.homEquiv` by transport across the braiding `β_ K L`.

Source/core/bridge triage:
- `source-facing`: the textbook bijection
  `Hom(K, L ⟹ M) ≃ Hom(K ⊗ L, M)`;
- `core/canonical`: `braidedHomEquiv`;
- `bridge/view`: the generic owner theorem
  `MonoidalClosed.braidedHomEquiv_symm_apply`.

Primitive data versus derived API:
- primitive data: the chapter owner category `ringedSiteModuleCategory J 𝒪` and its derived
  category `D`, together with the monoidal closed structure and braiding on `D`;
- derived API: the textbook-order Hom-bijection, obtained from the owner adjunction plus the
  braiding.

This numbered item is recall-only: it should not keep a parallel ringed-site-specific owner
definition. -/

/- Core recall: the textbook-order adjunction is the chapter owner `braidedHomEquiv`. -/
recall MonoidalClosed.braidedHomEquiv

/- Specialized check for the owner orientation. -/
#check
  (braidedHomEquiv : ∀ K L M : D, (K ⊗ L ⟶ M) ≃ (K ⟶ (ihom L).obj M))

/- 21.35.0.1 itself is the inverse, source-facing orientation of `braidedHomEquiv`. -/
/-- 21.35.0.1: for objects `K`, `L`, `M : D`, there is a canonical bijection
`Hom_D(K, L ⟹ M) ≃ Hom_D(K ⊗ L, M)`. This is the source-facing inverse of the owner
`MonoidalClosed.braidedHomEquiv`. -/
@[stacks 08J8]
abbrev ringedSiteDerivedTensorHomAdjunction (K L M : D) :
    (K ⟶ L ⟹ M) ≃ (K ⊗ L ⟶ M) :=
  (braidedHomEquiv K L M).symm

@[simp] theorem ringedSiteDerivedTensorHomAdjunction_apply
    {K L M : D} (f : K ⟶ L ⟹ M) :
    ringedSiteDerivedTensorHomAdjunction K L M f = (braidedHomEquiv K L M).symm f :=
  rfl

@[simp] theorem ringedSiteDerivedTensorHomAdjunction_symm_apply
    {K L M : D} (f : K ⊗ L ⟶ M) :
    (ringedSiteDerivedTensorHomAdjunction K L M).symm f = braidedHomEquiv K L M f :=
  rfl

/- Companion recall: the evaluation formula is the generic owner theorem
`MonoidalClosed.braidedHomEquiv_symm_apply`. -/
recall MonoidalClosed.braidedHomEquiv_symm_apply

end

end

end SheafOfModules.RingedSite
