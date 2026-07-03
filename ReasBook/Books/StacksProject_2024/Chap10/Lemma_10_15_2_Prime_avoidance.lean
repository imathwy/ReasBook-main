import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.15.2 (Prime avoidance): the canonical prime avoidance theorem states that if an ideal
is contained in the union of finitely many ideals and all but at most two of them are prime, then
it is contained in one of those ideals. Applied contrapositively to `J`, this yields an element of
`J` lying outside every `I_i`. -/
recall Ideal.subset_union_prime
