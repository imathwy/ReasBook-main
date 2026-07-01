import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.6.3: if `R → S` is of finite presentation and `α : R[x_1, ..., x_n] → S` is
surjective, then the kernel ideal of `α` in the polynomial ring `R[x_1, ..., x_n]` is finitely
generated. The owner abstraction is the canonical theorem
`Algebra.FinitePresentation.ker_fG_of_surjective`, which treats any surjective map of finitely
presented `R`-algebras; the polynomial presentation in the source is its source-facing
specialization, so this item is best kept as a direct recall rather than a parallel wrapper. -/
recall Algebra.FinitePresentation.ker_fG_of_surjective
