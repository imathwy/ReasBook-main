import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {F : Type u} [Field F]

/- Definition 9.16.2: for a nonconstant polynomial `P ∈ F[X]`, the field extension
`P.SplittingField/F` constructed in Lemma 9.16.1 is called the splitting field of `P` over `F`.
In mathlib this is the canonical owner `Polynomial.SplittingField P`; the source's nonconstancy
hypothesis is not part of the definition itself. -/
recall Polynomial.SplittingField (P : Polynomial F) : Type u
