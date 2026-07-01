import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FaithfulSMul R S] [Algebra.IsIntegral R S]

/- Lemma 10.36.17 (Stacks tag `00GQ`): if `R → S` is an integral ring extension with `R ⊂ S`,
then the induced map `Spec(S) → Spec(R)` is surjective. In mathlib this is exactly
`Algebra.IsIntegral.comap_surjective`; the inclusion hypothesis is encoded by `FaithfulSMul R S`,
which gives injectivity of `algebraMap R S`. -/
recall Algebra.IsIntegral.comap_surjective

end
