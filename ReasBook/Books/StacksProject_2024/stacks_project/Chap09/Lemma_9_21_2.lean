import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap09.Definition_9_21_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/- Domain-style sampling:
* primary domain: finite-dimensional Galois extensions and their automorphism groups;
* sampled owner declarations:
  `IsGalois`,
  `isGalois_iff`,
  `IsGalois.card_aut_eq_finrank`,
  `IsGalois.of_card_aut_eq_finrank`;
* best owner abstraction: the field-extension owner predicate `IsGalois F E`, already introduced
  in Definition 9.21.1;
* primitive data: fields `F`, `E`, an `F`-algebra structure on `E`, and finite dimensionality;
* derived API: the numerical criterion comparing `Nat.card Gal(E / F)` with `Module.finrank F E`
  is already split upstream into the two owner-direction theorems recalled below.

Layer triage:
* `source-facing`: Lemma 9.21.2 is the textbook finite-dimensional criterion for Galoisness;
* `core/canonical`: `IsGalois F E`;
* `bridge/view`: the cardinality equality `Nat.card Gal(E / F) = Module.finrank F E`.

So this file should reuse the two canonical owner theorems directly rather than keep a local `↔`
wrapper duplicating upstream API. -/
/- Lemma 9.21.2: for a finite field extension `E/F`, the forward implication
`IsGalois F E → Nat.card Gal(E / F) = Module.finrank F E` is the canonical owner theorem
`IsGalois.card_aut_eq_finrank`. -/
recall IsGalois.card_aut_eq_finrank

/- Companion recall: the converse implication
`Nat.card Gal(E / F) = Module.finrank F E → IsGalois F E` is the canonical owner theorem
`IsGalois.of_card_aut_eq_finrank`. -/
recall IsGalois.of_card_aut_eq_finrank

end
