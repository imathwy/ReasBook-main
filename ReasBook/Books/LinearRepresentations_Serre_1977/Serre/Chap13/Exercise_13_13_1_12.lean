import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap13.Theorem_13_13_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Representation
open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]

/- Exercise 13-13.1-12: this exercise asks for an alternative proof of Theorem `13-13.1-6` by
reducing to cyclic subgroups and then using the cyclic-group analysis from Exercise `13-13.1-11`.
In the current API this exercise is a direct recall of the source-facing bridge theorem stating
that `ℚ ⊗ R_ℚ(G)` is spanned by the cyclic subgroup permutation characters `ℓ_C^G`. -/
recall characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ

end
