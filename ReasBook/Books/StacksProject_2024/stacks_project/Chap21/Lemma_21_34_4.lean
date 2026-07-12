import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_27_6
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

/- Domain-style sampling for Lemma 21.34.4:
- primary domain: the closed braided monoidal structure on cochain complexes of `𝒪`-modules on
  a ringed site;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right`;
- best owner abstraction:
  `source-facing`: the canonical morphism `K ⟶ (ihom L).obj (K ⊗ L)` for complexes of
  `𝒪`-modules on a ringed site;
  `core/canonical`: `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`;
  `bridge/view`: the specialization of that generic owner and its companion theorems to the
    complex category `CpxO`.
- primitive data: the ambient braided closed monoidal structure on `CpxO` and the complexes `K`,
  `L`;
- derived API: the specialized type of the generic tensor-Hom unit and its generic specification
  and naturality theorems.

This numbered item is recall-only: it should not keep a parallel ringed-site-specific owner
declaration.
-/

/- Lemma 21.34.4: the canonical morphism `K ⟶ (ihom L).obj (K ⊗ L)` on `CpxO` is the generic
owner `MonoidalClosed.tensorInternalHomUnit` specialized to cochain complexes of `𝒪`-modules on a
ringed site. -/
recall tensorInternalHomUnit

/- Specialized check for Lemma 21.34.4. -/
#check
  (tensorInternalHomUnit : ∀ K L : CpxO, K ⟶ (ihom L).obj (K ⊗ L))

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
