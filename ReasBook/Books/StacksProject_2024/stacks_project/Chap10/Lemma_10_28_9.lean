import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/-
Lemma 10.28.9 is the canonical mathlib theorem `Ideal.isPrime_of_maximally_disjoint`. The Stacks
formulation saying that `I` is maximal among the ideals disjoint from a multiplicative subset `S`
is exactly the source-facing `Maximal` packaging of the owner theorem's two hypotheses:
`Disjoint (I : Set R) (S : Set R)` and the fact that every strict over-ideal of `I` meets `S`.
-/
recall Ideal.isPrime_of_maximally_disjoint

end
