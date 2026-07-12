import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.ObjectProperty

universe v u

/- Domain-style sampling for Definition 13.6.1:
- primary domain: saturated full subcategories of pretriangulated/triangulated categories,
  expressed as retract-stable object properties;
- inspected owner/bridge declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.prop_of_retract`,
  `ObjectProperty.retractClosure`,
  `CategoryTheory.trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`;
- best owner abstraction: `ObjectProperty.IsStableUnderRetracts`;
- primitive-vs-derived split:
  primitive data: the retract-closure axiom `of_retract`;
  derived API: closure under isomorphisms, biproduct/direct-summand closure in additive settings,
    the retract-closure owner `P.retractClosure`, and the Chapter 13 comparison with saturated
    multiplicative systems.

Source/core/bridge triage:
- `source-facing`: the Stacks notion that a full pretriangulated subcategory is saturated, i.e.
  closed under direct summands;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts`;
- `bridge/view`: downstream equivalences such as
  `trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`. -/

/- Definition 13.6.1: for an object property `P`, the textbook saturation condition on the
corresponding full pretriangulated subcategory is the canonical owner predicate
`P.IsStableUnderRetracts`; in additive/pretriangulated settings this is the same direct-summand
closure condition used in the source. -/
recall IsStableUnderRetracts

section

variable {C : Type u} [Category.{v} C] {P Q : ObjectProperty C}

/-- The intersection of retract-stable object properties is retract-stable. -/
instance [P.IsStableUnderRetracts] [Q.IsStableUnderRetracts] :
    (P ⊓ Q).IsStableUnderRetracts where
  of_retract r h := ⟨P.prop_of_retract r h.1, Q.prop_of_retract r h.2⟩

end

end CategoryTheory.ObjectProperty
