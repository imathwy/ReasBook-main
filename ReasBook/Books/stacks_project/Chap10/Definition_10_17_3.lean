import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

/- Definition 10.17.3: the topology on `Spec(R)` whose closed subsets are the sets `V(T)` is the
canonical Zariski topology instance `PrimeSpectrum.zariskiTopology` on `PrimeSpectrum R`; the
textbook ring statement is its special case. -/
recall PrimeSpectrum.zariskiTopology

end
