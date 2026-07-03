import Mathlib
import Serre.Chap13.Theorem_13_13_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Representation

open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]

/- Remark 13-13.1-10: Serre applies Theorem `13-13.1-6` to a finite Galois group `G = Gal(F / E)`
and a character `χ` realizable over `ℚ` to express the corresponding Artin `L`-function as a
product of fractional powers of Dedekind zeta functions of the fixed fields attached to cyclic
subgroups. In the current API this remark is a direct recall of the source-facing bridge theorem,
rather than a separate string-valued wrapper. -/
recall characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ

end
