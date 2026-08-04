import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {I : Type u} {Ω : Type v} {S : Type w}

/- Remark 9.3: writing a stochastic process as `X = (X_t)_{t ∈ I}` only emphasizes its time
evolution; formally, it is the same time-indexed family already used as the owner object for a
process. -/
#check (I → Ω → S)
