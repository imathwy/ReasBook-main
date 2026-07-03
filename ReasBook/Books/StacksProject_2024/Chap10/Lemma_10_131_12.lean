import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.131.12: for ring maps `R → R'` and `R → S`, with `S' = R' ⊗[R] S`, the canonical map
identifies the base change `R' ⊗[R] Ω[S⁄R]` with `Ω[S'⁄R']`. This is exactly the standard
base-change isomorphism for Kähler differentials. -/
recall KaehlerDifferential.tensorKaehlerEquivBase
