import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PiTensorProduct

universe u v w

variable {n : ℕ} {R : Type u} [CommSemiring R]
variable {M : Fin n → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/- Lemma 10.12.4 is a `bridge/view` item. The `core/canonical` owner abstraction is the
multilinear tensor-product equivalence `PiTensorProduct.lift`; the source-facing existence and
uniqueness statement is derived from this owner together with the primitive canonical multilinear
map `PiTensorProduct.tprod R`. -/
recall PiTensorProduct.lift

/-- Companion formulation of Lemma 10.12.4: every multilinear map out of `M` factors uniquely
through the canonical multilinear map `PiTensorProduct.tprod R`. -/
theorem piTensorProduct_existsUnique_lift
    {P : Type w} [AddCommMonoid P] [Module R P] (f : MultilinearMap R M P) :
    ∃! f' : (⨂[R] i, M i) →ₗ[R] P,
      f'.compMultilinearMap (tprod R) = f := by
  refine ⟨lift f, ?_, ?_⟩
  · simpa using (lift_symm (lift f)).symm
  · intro f' hf'
    exact lift.unique' hf'
