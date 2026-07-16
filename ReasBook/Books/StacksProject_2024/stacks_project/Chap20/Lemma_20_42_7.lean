import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.«20_42_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.42.7:
- primary domain: the braided closed monoidal structure on `D(𝒪_X)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right`;
- best owner abstraction: the canonical owner is the generic categorical morphism
  `MonoidalClosed.tensorInternalHomUnit`, defined in any braided monoidal closed category; the
  ringed-space statement is only its specialization to `RingedSpaceDerived X`;
- primitive data: a ringed space `X`, the braided closed monoidal structure on
  `RingedSpaceDerived X`, and objects `K`, `L`;
- derived API: the specialized type of the generic unit morphism and its generic specification and
  naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the textbook coevaluation morphism on `D(𝒪_X)`;
- `core/canonical`: `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`;
- `bridge/view`: the ringed-space specialization of that owner and its companion generic theorems.

This numbered item is recall-only: it should not keep a parallel ringed-space-specific owner
declaration. -/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

/- Lemma 20.42.7: the canonical morphism
`K ⟶ (L ⟹ (K ⊗ L))` on `RingedSpaceDerived X` is the generic owner
`MonoidalClosed.tensorInternalHomUnit` specialized to `D(𝒪_X)`. -/
recall tensorInternalHomUnit

/- Specialized check for Lemma 20.42.7. -/
#check
  (tensorInternalHomUnit : ∀ K L : DModX, K ⟶ L ⟹ (K ⊗ L))

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

end AlgebraicGeometry.RingedSpace
