import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Remark 10.18.5 is a core/canonical recall. The primitive fiber-ring object is
`p.asIdeal.Fiber S = κ(p) ⊗[R] S`, and the source-facing fiber of `Spec S → Spec R` over `p`
is canonically homeomorphic to its prime spectrum. -/
recall PrimeSpectrum.preimageHomeomorphFiber

/- Companion derived recall: the same fiber is nonempty exactly when the primitive fiber ring
`p.asIdeal.Fiber S` is nontrivial, equivalently when `p` lies in the image of `Spec S → Spec R`.
-/
recall PrimeSpectrum.nontrivial_iff_mem_rangeComap

end
