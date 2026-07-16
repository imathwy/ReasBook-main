import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry PrimeSpectrum IsLocalRing
open scoped AlgebraicGeometry

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [IsDomain A] [IsIntegrallyClosed A]

-- Semantic recall: `lean_leansearch` surfaced the canonical affine owner `Scheme.ΓSpecIso` for
-- top sections of `Spec`, and `Chap31/Lemma_31_16_1` now provides the chapter's canonical
-- punctured-spectrum open `puncturedSpectrumOpen`.

/-- Remark 31.16.2 (1): if `(A, 𝔪)` is a Noetherian local normal domain of dimension at least
`2`, then the canonical map from `A` to the regular functions on the punctured spectrum
`U = Spec(A) \ {𝔪}` is bijective, i.e. `Γ(U, \mathcal O_U) = A` in the algebraic Hartogs
theorem form. -/
@[stacks 0BCS]
theorem bijective_algebraMap_to_localRingPuncturedSpectrumSections
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective
      (algebraMap A
        ↑((Spec.structureSheaf A).obj.obj
          (Opposite.op
            (puncturedSpectrumOpen : (Spec (CommRingCat.of A)).Opens)))) := sorry

/-- Remark 31.16.2 (2): under the same hypotheses, the punctured spectrum
`U = Spec(A) \ {𝔪}` is not affine. -/
@[stacks 0BCS]
theorem not_isAffineOpen_localRingPuncturedSpectrum
    (hdim : 2 ≤ ringKrullDim A) :
    ¬ IsAffineOpen (puncturedSpectrumOpen : (Spec (CommRingCat.of A)).Opens) := sorry

end
