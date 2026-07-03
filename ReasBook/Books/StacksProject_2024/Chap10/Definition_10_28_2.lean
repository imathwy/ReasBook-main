import Mathlib.RingTheory.Ideal.Oka
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.28.2: an Oka family of ideals of `R` is the canonical predicate
`Ideal.IsOka`, applied to the set family viewed as a predicate on ideals. The textbook clauses
`R ∈ 𝓕`, `(I : a) ∈ 𝓕`, and `(I, a) ∈ 𝓕` are exactly the fields `top` and `oka`, written in Lean
as `⊤ ∈ 𝓕`, `I.colon (Ideal.span {a}) ∈ 𝓕`, and `I ⊔ Ideal.span {a} ∈ 𝓕`. -/
recall Ideal.IsOka
