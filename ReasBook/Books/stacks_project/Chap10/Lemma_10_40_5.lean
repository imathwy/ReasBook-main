import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.40.5, canonical main form: more precisely, if
`I = Module.annihilator R M`, then `PrimeSpectrum.zeroLocus I = Module.support R M`. -/
recall Module.support_eq_zeroLocus

/- Source-wording consequence: if `M` is finite, then `Module.support R M` is closed. -/
recall Module.isClosed_support

end
