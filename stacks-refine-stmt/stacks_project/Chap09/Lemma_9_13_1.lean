import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 9.13.1: pairwise distinct multiplicative characters `χ₁, …, χₙ : G → L` of a monoid
with values in a field are linearly independent. This is the finite-family specialization of the
canonical mathlib theorem `linearIndependent_monoidHom`, which states that all multiplicative
characters `G →* L` are linearly independent as functions `G → L`; applying it to an injective
family `χ : Fin n → G →* L` gives the textbook statement. -/
recall linearIndependent_monoidHom
