import Mathlib
import stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x y

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N]
variable {f : M →ₗ[R] M'}

-- Proof sketch: for any `R`-module `Q`, use the tensor associativity isomorphism to identify
-- `((M ⊗[R] N) ⊗[R] Q)` with `M ⊗[R] (N ⊗[R] Q)` and similarly on the target. Under these
-- identifications, `(f.rTensor N).rTensor Q` is the tensor of `f` with `N ⊗[R] Q`, so its
-- injectivity follows from the universal injectivity of `f`.
/-- Helper for Lemma 10.82.8: the tensor associator identifies the iterated right tensor map
with tensoring `f` once by `N ⊗[R] Q`. -/
lemma rtensor_assoc_apply {Q : Type y} [AddCommGroup Q] [Module R Q]
    (x : (M ⊗[R] N) ⊗[R] Q) :
    TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) x) =
      (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q x) := by
  let lhs : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) :=
    (TensorProduct.assoc R M' N Q).toLinearMap.comp ((f.rTensor N).rTensor Q)
  let rhs : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) :=
    (f.rTensor (N ⊗[R] Q)).comp (TensorProduct.assoc R M N Q).toLinearMap
  -- Check equality of the comparison maps on pure tensors in the outer and inner tensor factors.
  have hmaps : lhs = rhs := by
    refine TensorProduct.ext_threefold ?_
    intro m n q
    rfl
  -- Evaluate the linear-map equality at `x` to obtain the desired pointwise comparison.
  have hpoint :
      lhs x = rhs x := by
    exact congrArg
      (fun φ : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) => φ x) hmaps
  simpa [lhs, rhs] using hpoint

/-- Helper for Lemma 10.82.8: after one more right tensor by a test module `Q`, the iterated
tensor map stays injective. -/
lemma injective_rtensor_rtensor_of_universallyInjective
    (hf : UniversallyInjective.{u, v, w, max x y} f) {Q : Type y}
    [AddCommGroup Q] [Module R Q] :
    Function.Injective (((f.rTensor N).rTensor Q)) := by
  intro x y hxy
  -- Transport the equality through the target associator to compare it with `f.rTensor (N ⊗[R] Q)`.
  have hxy_assoc :
      TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) x) =
        TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) y) := by
    exact congrArg (TensorProduct.assoc R M' N Q) hxy
  have hxy' :
      (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q x) =
        (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q y) := by
    rw [← rtensor_assoc_apply (f := f) (N := N) (x := x)]
    rw [← rtensor_assoc_apply (f := f) (N := N) (x := y)]
    exact hxy_assoc
  -- Apply universal injectivity to `N ⊗[R] Q` and pull the conclusion back through the source associator.
  have hTensorInjective : Function.Injective (f.rTensor (N ⊗[R] Q)) :=
    hf (N ⊗[R] Q) inferInstance inferInstance
  have hAssocEq : TensorProduct.assoc R M N Q x = TensorProduct.assoc R M N Q y :=
    hTensorInjective hxy'
  exact (TensorProduct.assoc R M N Q).injective <|
    hAssocEq

/-- Lemma 10.82.8: tensoring a universally injective `R`-linear map on the right with any
`R`-module again yields a universally injective map. -/
theorem universallyInjective_rTensor (hf : UniversallyInjective.{u, v, w, max x y} f) :
    UniversallyInjective.{u, max v x, max w x, y} (f.rTensor N) := by
  intro Q _ _
  -- Universal injectivity is tested after one more tensor factor, and the fixed-`Q` injectivity
  -- follows from the associator comparison proved above.
  exact injective_rtensor_rtensor_of_universallyInjective (f := f) (N := N) hf

end

end LinearMap
