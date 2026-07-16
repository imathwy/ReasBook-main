import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_3_10

-- Declarations for this item will be appended below by the statement pipeline.

namespace Representation

/-
Domain-style sampling:
* primary domain: finite-group character theory and complex representation theory.
* sampled owner declarations in this domain:
  `exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow`,
  `exists_smul_id_of_prime_pow_conjClass_card_of_character_ne_zero`,
  `quotient_mk_mem_center_of_exists_smul_id`.
* best owner abstraction: the existing Chapter `6` owner theorems already formalized in
  `Serre.Chap06.Exercise_6_6_5_10`.

Primitive data versus derived API:
* primitive source-facing data: the prime-power conjugacy-class hypothesis and the resulting
  irreducible-character existence statement.
* derived API: the scalar-action and quotient-centrality consequences attached to the same exercise.

Source/core/bridge triage:
* `source-facing`: Exercise `6-6.5-10` itself.
* `core/canonical`: the existing Chapter `6` theorem declarations of the same names.
* `bridge/view`: the two consequence theorems, which remain direct recalls rather than parallel
  redeclarations.
-/

/- Exercise 6-6.5-10: the source-facing existence statement already has the correct public owner in
`Serre.Chap06.Exercise_6_6_5_10`, so this file reuses it directly. -/
recall exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow

end Representation
