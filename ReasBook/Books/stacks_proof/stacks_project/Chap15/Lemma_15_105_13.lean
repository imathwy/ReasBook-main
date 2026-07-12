import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1
import StacksProject_2024.Chap15.Lemma_15_105_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.13:
- primary domain: finite-type and finite-presentation criteria for unramified and étale
  commutative algebra maps;
- sampled owner declarations:
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`,
  `WeaklyEtale`,
  `Algebra.Unramified`,
  `Algebra.Etale.of_formallyUnramified_of_flat`,
  `Algebra.IsWeaklyEtale`;
- best owner abstraction: this file is `bridge/view`, taking the tensor-square flatness criterion
  from Lemma `15.105.12` to the canonical owners `Algebra.Unramified` and `Algebra.Etale`;
- primitive data: flatness of the tensor-square multiplication map `lmul' A`, plus the standard
  finiteness and flatness owner assumptions;
- derived API: the source-facing conclusions that `A → B` is unramified or étale.

There is no new owner to define here: the file should reuse the canonical owner classes directly
and keep only the source-facing bridge theorems.
-/

/-- Lemma 15.105.13 (1): if the tensor-square multiplication map `B ⊗[A] B → B` is flat and
`A → B` is of finite type, then `A → B` is unramified. -/
@[stacks 0CKP]
theorem unramified_of_tensorSquareMul_flat_of_finiteType [Algebra.FiniteType A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Algebra.Unramified A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul
  exact ⟨inferInstance, inferInstance⟩

/-- Lemma 15.105.13 (2): if the tensor-square multiplication map `B ⊗[A] B → B` is flat and
`A → B` is flat of finite presentation, then `A → B` is étale. -/
@[stacks 0CKP]
theorem etale_of_tensorSquareMul_flat_of_finitePresentation_of_flat
    [Algebra.FinitePresentation A B] [Module.Flat A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Lemma 15.105.13 (3): in particular, a weakly étale ring map of finite presentation is
étale. -/
@[stacks 0CKP]
theorem etale_of_isWeaklyEtale_of_finitePresentation
    [Algebra.FinitePresentation A B] [Algebra.IsWeaklyEtale A B] :
    Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat
      ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication
  exact Algebra.Etale.of_formallyUnramified_of_flat

end
