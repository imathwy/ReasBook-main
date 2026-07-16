import StacksProject_2024.stacks_project.Chap10.Lemma_10_118_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.118.2 lives in the generic-freeness domain for finite type algebras and finite modules
over a domain. Sampled chapter/project owners in this domain are
`GenericFlatness.LocalizationCondition`,
`exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType`, and the chapter-level
freeness consequence `exists_nonzero_localization_away_module_free`. The best owner abstraction for
this item is the latter theorem: finite presentation of `S` and `M` only supplies the derived
instances `[Algebra.FiniteType R S]` and `[Module.Finite S M]`, so the stronger-hypothesis version
in the source is a `bridge/view` recall of the existing canonical chapter theorem rather than a new
owner. Primitive data are the rings/algebra/module; the freeness conclusion is derived API. -/
recall exists_nonzero_localization_away_module_free
