import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 10.138.6: Lemma 10.138.5 extends from polynomial presentations to any surjective
`R`-algebra map `f : P →ₐ[R] A` whose source `P` is formally smooth over `R`. This is exactly the
canonical mathlib theorem `Algebra.FormallySmooth.iff_split_surjection`. -/
recall Algebra.FormallySmooth.iff_split_surjection
