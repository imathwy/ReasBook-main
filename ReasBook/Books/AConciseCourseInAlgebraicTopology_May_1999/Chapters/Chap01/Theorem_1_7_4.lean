import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.7.4 (1): the fundamental theorem of algebra says that every nonconstant complex
polynomial has a complex root; this is the canonical mathlib theorem `Complex.exists_root`,
which covers the textbook's monic normal form `x^n + c_1 x^(n - 1) + ... + c_n` with `n > 0`. -/
recall Complex.exists_root {f : Polynomial ℂ} (hf : 0 < f.degree) :
    ∃ z, f.IsRoot z

/- Theorem 1.7.4 (2): over `ℂ`, a complex polynomial has exactly `natDegree` many roots counted
with multiplicity; this is the canonical algebraically closed field root-count formula specialized
to `ℂ`. -/
theorem complex_card_roots_eq_natDegree {p : Polynomial ℂ} : p.roots.card = p.natDegree := by
  simpa using (IsAlgClosed.card_roots_eq_natDegree : p.roots.card = p.natDegree)
