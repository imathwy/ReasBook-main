import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.148.1: for a ring map `R → S`, the statement that `S` is formally unramified
over `R` is the canonical mathlib predicate `Algebra.FormallyUnramified R S`. -/
recall Algebra.FormallyUnramified

/- Companion recall: the infinitesimal lifting formulation in the text is the existing theorem
`Algebra.FormallyUnramified.iff_comp_injective`, expressing formal unramifiedness as uniqueness of
lifts across square-zero thickenings. -/
recall Algebra.FormallyUnramified.iff_comp_injective
