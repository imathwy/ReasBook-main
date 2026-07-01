import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Basis sheaf condition generalizes to C-valued presheaves: the basis sheaf-property lemmas for
set-valued presheaves extend verbatim to `C`-valued basis presheaves by expressing the basis
sheaf condition through the canonical site-theoretic predicate
`CategoryTheory.Presheaf.IsSheaf` on the basis site. The extension lemma is the only part that
requires additional care. -/
recall CategoryTheory.Presheaf.IsSheaf
