import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Aux_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Opposite

universe uC vC uD vD

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Definition 24.33.1:
- primary domain: full subcategories of a derived category cut out by the pointwise isomorphism
  condition on derived restriction/base-change comparison maps;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`;
- source/core/bridge triage:
  `source-facing`: the Chapter 24 notation `QC(\mathcal A, d)`;
  `core/canonical`: the Chapter 21 full subcategory owner `QC`;
  `bridge/view`: the underlying object property `isQuasiCoherent`, whose full subcategory is `QC`.

This item introduces no new owner beyond the Chapter 21 construction, so the correct source-facing
surface is a direct recall of `QC` and its companion property rather than a redundant Chapter 24
alias.
-/

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒜.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/- Definition 24.33.1: in the differential-graded module situation above, `QC(\mathcal A, d)` is
the canonical full subcategory `QC`. Concretely, its objects are those `M` such that for every
arrow `U ⟶ V` in `\mathcal C`, the canonical map
`RΓ(V, M) ⊗^{\mathbf L}_{\mathcal A(V)} \mathcal A(U) ⟶ RΓ(U, M)` is an isomorphism in
`D(\mathcal A(U), d)`. -/
recall QC

/- Companion recall: the underlying object property cutting out `QC(\mathcal A, d)` is
`isQuasiCoherent`. -/
recall isQuasiCoherent

end

end CategoryTheory.ModulesOnCategory
