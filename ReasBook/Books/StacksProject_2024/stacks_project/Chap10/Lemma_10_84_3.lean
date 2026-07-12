import StacksProject_2024.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Ordinal

universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* primary domain: transfinite direct-sum devissages of modules and countable generation;
* sampled owner declarations:
  `Module.CountablyGenerated`,
  `Module.IsDirectSumOfCountablyGenerated`,
  the chapter owner `DirectSumDevissage`,
  and the derived predicate `DirectSumDevissage.IsKaplansky`;
* layer: `bridge/view`, since the theorem below compares the direct-sum owner predicate with the
  direct-sum devissage owner object.
-/

-- Proof sketch: well-order the summands in an internal direct-sum decomposition and take partial
-- sums to build a direct-sum devissage whose successor quotients are exactly the chosen countably
-- generated summands. Conversely, a Kaplansky direct-sum devissage reconstructs `M` as the
-- supremum of the successive countably generated quotient pieces.
/-- Lemma 10.84.3: an `R`-module is a direct sum of countably generated modules exactly when it
admits a Kaplansky devissage. -/
theorem isDirectSumOfCountablyGenerated_iff_hasKaplanskyDevissage :
    Module.IsDirectSumOfCountablyGenerated R M ↔
      ∃ D : DirectSumDevissage R M, D.IsKaplansky := sorry

end

end Module
