import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

namespace Ideal

-- Proof sketch: identify `V(I)` with `Spec (R ⧸ I)` via the quotient-spectrum equivalence. Since
-- `I` is pure, the quotient map `R → R ⧸ I` is flat, so `Spec (R ⧸ I) → Spec R` is generalizing by
-- `RingHom.Flat.generalizingMap_comap`. Transporting this along the quotient identification shows
-- that `V(I)` is stable under generalization.
/-- The zero locus of a pure ideal is stable under generalization in `Spec(R)`. -/
theorem stableUnderGeneralization_zeroLocus_of_pure (I : Ideal R) (hI : I.Pure) :
    StableUnderGeneralization (zeroLocus (I : Set R)) := sorry

end Ideal

-- Proof sketch: well-definedness is `Ideal.stableUnderGeneralization_zeroLocus_of_pure` together
-- with `PrimeSpectrum.isClosed_zeroLocus`. Injectivity is Lemma `10.108.3`, i.e.
-- `Ideal.zeroLocus_inj_of_pure`. For surjectivity, write a closed generalization-stable subset as
-- `V(J)` for a radical ideal `J`, then define the ideal `I = {x | ∃ y ∈ J, x = x * y}` from the
-- Stacks proof and use Lemma `10.108.2` to show `I` is pure and still satisfies `V(I) = V(J)`.
/-- Lemma 10.108.4: the rule `I ↦ V(I)` gives a bijection between pure ideals of `R` and closed
subsets of `Spec(R)` that are stable under generalization. -/
theorem pureIdeal_zeroLocus_bijective :
    Function.Bijective
      (fun I : { I : Ideal R // I.Pure } ↦
        (⟨zeroLocus (I.1 : Set R), isClosed_zeroLocus (I.1 : Set R),
          Ideal.stableUnderGeneralization_zeroLocus_of_pure I.1 I.2⟩ :
            { Z : Set (PrimeSpectrum R) // IsClosed Z ∧ StableUnderGeneralization Z })) := sorry

end
