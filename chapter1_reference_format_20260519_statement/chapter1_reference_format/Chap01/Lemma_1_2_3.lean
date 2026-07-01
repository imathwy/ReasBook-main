import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 1.2.3: the textbook relation `∼` on `𝔍(ℚ)` is modeled in mathlib by the canonical setoid
`CauSeq.equiv` on `CauSeq ℚ abs`; its relation is the equivalence relation written `≈`. -/
#check (CauSeq.equiv : Setoid (CauSeq ℚ (abs : ℚ → ℚ)))
