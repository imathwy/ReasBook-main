import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.131.4: if the structure map `R → S` is surjective, then the module of Kähler
differentials `Ω[S⁄R]` is zero. In Lean, a module being zero is expressed as
`Subsingleton Ω[S⁄R]`, and this is exactly the canonical theorem
`KaehlerDifferential.subsingleton_of_surjective`. -/
recall KaehlerDifferential.subsingleton_of_surjective
