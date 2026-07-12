import Mathlib
import StacksProject_2024.Chap10.Theorem_10_95_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

-- Proof sketch: the forward implication is the standard base-change stability of
-- `Algebra.FormallySmooth`. For the converse, rewrite formal smoothness through the owner theorem
-- `Algebra.formallySmooth_iff`, descend projectivity of `Ω[S⁄R]` from the base-changed Kähler
-- module via `KaehlerDifferential.tensorKaehlerEquiv` and faithfully flat descent for projective
-- modules, and descend `Subsingleton (H1Cotangent R S)` from `Algebra.tensorH1CotangentOfFlat`
-- using `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`.
/-- Lemma 10.138.16: formal smoothness is equivalent to formal smoothness after faithfully flat
base change; in canonical tensor-product order, `R → S` is formally smooth if and only if
`R' → R' ⊗[R] S` is formally smooth. -/
@[stacks 06CM]
theorem formallySmooth_iff_formallySmooth_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FormallySmooth R S ↔ Algebra.FormallySmooth R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  constructor
  · intro h
    letI : Algebra.FormallySmooth R S := h
    infer_instance
  · intro h
    rw [Algebra.formallySmooth_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
      letI : Module.FaithfullyFlat S (S ⊗[R] R') := by infer_instance
      letI : Module.FaithfullyFlat S (R' ⊗[R] S) :=
        Module.FaithfullyFlat.of_linearEquiv S (S ⊗[R] R')
          (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
      letI : Module.Projective (R' ⊗[R] S) (Ω[R' ⊗[R] S⁄R']) := h.1
      let e := KaehlerDifferential.tensorKaehlerEquiv R R' S (R' ⊗[R] S)
      letI : Module.Projective (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[S] Ω[S⁄R]) :=
        Module.Projective.of_equiv e.symm
      exact Module.Projective.of_projective_tensorProduct_of_faithfullyFlat (R' ⊗[R] S)
    · letI : Subsingleton (Algebra.H1Cotangent R' (R' ⊗[R] S)) := h.2
      let e := Algebra.tensorH1CotangentOfFlat R S R'
      letI : Subsingleton (R' ⊗[R] Algebra.H1Cotangent R S) := e.injective.subsingleton
      simpa using
        (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
          R R').1 (show Subsingleton (R' ⊗[R] Algebra.H1Cotangent R S) from inferInstance)

end

end Algebra
