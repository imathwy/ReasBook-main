import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
- primary domain: commutative algebra of tensor-square criteria for formally unramified ring maps;
- source-facing layer: triviality of the Kähler differentials `Ω[B⁄A]` under flatness of the
  tensor-square multiplication map `lmul' A`, exactly the Stacks conclusion of Lemma `15.105.12`;
- core/canonical owners sampled for this file: `Algebra.FormallyUnramified`,
  `Algebra.formallyUnramified_iff`, `Algebra.WeaklyEtale`, `Ideal.Pure`, and
  `Ideal.isIdempotentElem_of_pure`;
- primitive data: flatness of `lmul' A`;
- derived API: the source-facing conclusion `Subsingleton Ω[B⁄A]`, and the companion bridge
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`.

The file stays source-facing: the numbered theorem concludes `Subsingleton Ω[B⁄A]`, while
formal unramifiedness is recovered only through the canonical owner
`Algebra.FormallyUnramified`.
-/

namespace Algebra.FormallyUnramified

-- Proof sketch: let `I = KaehlerDifferential.ideal A B`, the diagonal ideal in `B ⊗[A] B`.
-- Since `I = ker(B ⊗[A] B → B)` for the multiplication map, surjectivity and flatness make the
-- quotient `(B ⊗[A] B) ⧸ I` flat, so `I` is a pure ideal. Hence `I` is idempotent, and the
-- cotangent presentation `Ω[B⁄A] = I/I²` collapses to zero.
/-- Companion bridge: flatness of the tensor-square multiplication map implies that `B` is formally
unramified over `A`. -/
theorem of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    FormallyUnramified A B := by
  refine (Algebra.formallyUnramified_iff A B).2 ?_
  rw [KaehlerDifferential, Ideal.cotangent_subsingleton_iff]
  let I : Ideal (B ⊗[A] B) := KaehlerDifferential.ideal A B
  letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
  letI : Module.Flat (B ⊗[A] B) B := hflatMul
  let f : B ⊗[A] B →ₐ[B ⊗[A] B] B := { lmul' A with commutes' := fun _ ↦ rfl }
  have hsurj : Function.Surjective f := by
    intro b
    exact ⟨1 ⊗ₜ[A] b, by simp [f]⟩
  let e : (B ⊗[A] B ⧸ I) ≃ₐ[B ⊗[A] B] B :=
    by
      simpa [I, KaehlerDifferential.ideal] using
        (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  letI : I.Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  simpa [I] using Ideal.isIdempotentElem_of_pure I

end Algebra.FormallyUnramified

/-- If the tensor-square multiplication map is flat, then the module of Kähler differentials
`Ω[B⁄A]` is trivial. This is the source-facing form of Lemma `15.105.12`. -/
theorem subsingleton_kaehlerDifferential_of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Subsingleton Ω[B⁄A] :=
  (Algebra.formallyUnramified_iff A B).1 <|
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul

end
