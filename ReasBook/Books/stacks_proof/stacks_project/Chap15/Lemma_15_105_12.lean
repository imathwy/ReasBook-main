import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import stacks_proof.stacks_project.Chap15.Definition_15_105_1
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 15.105.12: tensor-square multiplication sends `1 ⊗ b` to `b`. -/
lemma tensor_square_mul_one_tmul (b : B) :
    (lmul' A) (1 ⊗ₜ[A] b) = b := by
  simp

/-- Helper for Lemma 15.105.12: every element of `B` has a tensor-square preimage under
multiplication. -/
lemma tensor_square_mul_has_preimage (b : B) :
    ∃ x : B ⊗[A] B, (lmul' A) x = b := by
  refine ⟨1 ⊗ₜ[A] b, tensor_square_mul_one_tmul (A := A) (B := B) b⟩

/-- Helper for Lemma 15.105.12: tensor-square multiplication is surjective. -/
lemma tensor_square_mul_surjective :
    Function.Surjective (lmul' A : B ⊗[A] B → B) := by
  intro b
  exact tensor_square_mul_has_preimage (A := A) (B := B) b

/-- Helper for Lemma 15.105.12: after viewing `B` as an algebra over `B ⊗[A] B` via
tensor-square multiplication, that multiplication map is the corresponding scalar map. -/
lemma tensor_square_mul_commutes :
    letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
    ∀ x : B ⊗[A] B, (lmul' A) x = algebraMap (B ⊗[A] B) B x := by
  intro x
  rfl

/-- Helper for Lemma 15.105.12: flat tensor-square multiplication makes the diagonal Kähler ideal
idempotent. -/
lemma kaehler_ideal_is_idempotent_of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    IsIdempotentElem (KaehlerDifferential.ideal A B) := by
  let I : Ideal (B ⊗[A] B) := KaehlerDifferential.ideal A B
  letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
  letI : Module.Flat (B ⊗[A] B) B := hflatMul
  let f : B ⊗[A] B →ₐ[B ⊗[A] B] B :=
    { lmul' A with commutes' := tensor_square_mul_commutes (A := A) (B := B) }
  -- The quotient by the diagonal ideal is identified with `B` through multiplication.
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨x, hx⟩ := tensor_square_mul_has_preimage (A := A) (B := B) b
    exact ⟨x, hx⟩
  have e : (B ⊗[A] B ⧸ I) ≃ₐ[B ⊗[A] B] B := by
    simpa [I, KaehlerDifferential.ideal] using
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  -- Flatness transports across the quotient equivalence, hence the ideal is pure.
  letI : I.Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  simpa [I] using Ideal.isIdempotentElem_of_pure I

-- Proof sketch: let `I = KaehlerDifferential.ideal A B`, the diagonal ideal in `B ⊗[A] B`.
-- Since `I = ker(B ⊗[A] B → B)` for the multiplication map, surjectivity and flatness make the
-- quotient `(B ⊗[A] B) ⧸ I` flat, so `I` is a pure ideal. Hence `I` is idempotent, and the
-- cotangent presentation `Ω[B⁄A] = I/I²` collapses to zero.
/-- Helper for Lemma 15.105.12: flatness of the tensor-square multiplication map implies that `B`
is formally unramified over `A`. -/
theorem of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    FormallyUnramified A B := by
  -- The formal-unramified criterion is exactly the vanishing of the cotangent module.
  refine (Algebra.formallyUnramified_iff A B).2 ?_
  rw [KaehlerDifferential, Ideal.cotangent_subsingleton_iff]
  -- The idempotence criterion is the core invariant coming from flatness of the diagonal quotient.
  exact kaehler_ideal_is_idempotent_of_tensorSquareMul_flat (A := A) (B := B) hflatMul

end Algebra.FormallyUnramified

/-- Lemma 15.105.12: if the tensor-square multiplication map is flat, then the module of Kähler
differentials `Ω[B⁄A]` is trivial. -/
@[stacks 092M]
theorem subsingleton_kaehlerDifferential_of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Subsingleton Ω[B⁄A] := by
  -- The source-facing statement is the cotangent-module half of formal unramifiedness.
  exact (Algebra.formallyUnramified_iff A B).1 <|
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul

end
