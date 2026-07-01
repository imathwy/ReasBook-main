import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe uM uN

variable {M : Type uM} {N : Type uN}

/- The canonical owner for level sets and zero sets is `Set.preimage`. -/
recall Set.preimage (Φ : M → N) (s : Set N) : Set M

variable (Φ : M → N) (c : N)

/- Definition 5.30-extra-1: a level set of a map `Φ : M → N` at a point `c : N` is the singleton
fiber `Φ ⁻¹' {c}`. In the special case `c = 0`, this is the zero set of `Φ`. -/
#check (Φ ⁻¹' {c} : Set M)

variable [Zero N]

#check (Φ ⁻¹' ({0} : Set N) : Set M)
