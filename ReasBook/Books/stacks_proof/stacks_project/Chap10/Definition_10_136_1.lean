import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_136_1_Basic
import stacks_proof.stacks_project.Chap10.Lemma_10_135_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

/-- Helper for Chap10 Definition 10 136 1: every residue-field fiber of a local complete
intersection algebra over a field is again a local complete intersection. -/
lemma fieldFiber_isLocalCompleteIntersection [IsLocalCompleteIntersection k A]
    (p : PrimeSpectrum k) :
    IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
  -- Identify the fiber with residue-field base change and apply invariance under field extension.
  simpa [Ideal.Fiber] using
    (isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension
      (k := k) (K := p.asIdeal.ResidueField) (S := A)).mp
      (inferInstance : IsLocalCompleteIntersection k A)

-- Proof sketch: over a field every module is flat, and a local complete intersection `k`-algebra
-- is finite type by definition, hence finite presentation over the Noetherian base field `k`. The
-- only fiber of `Spec A → Spec k` is the fiber over `(0)`, which is canonically `A` itself.
/-- Chap10 Definition 10 136 1: a local complete intersection algebra over a field is syntomic. -/
theorem syntomic_of_isLocalCompleteIntersection [IsLocalCompleteIntersection k A] :
    (algebraMap k A).Syntomic := by
  refine ⟨?_, ?_, ?_⟩
  · -- Flatness of the algebra map is flatness of `A` as a module over the field `k`.
    exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_projective : Module.Flat k A)
  · -- The local-complete-intersection hypothesis supplies finite presentation of the algebra.
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · -- Reuse the original algebra structure before checking the residue-field fibers.
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap]
    intro p
    exact fieldFiber_isLocalCompleteIntersection p

end

end Algebra
