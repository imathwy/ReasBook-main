import Mathlib
import stacks_proof.stacks_project.Chap11.Lemma_11_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra.TensorProduct Subbimodule
open scoped TensorProduct

attribute [local instance] TensorProduct.Algebra.module

universe u v w

section

variable {k : Type u} {A : Type v} {K : Type w}
variable [Field k] [Ring A] [DivisionRing K] [Algebra k A] [Algebra k K]
variable [Algebra.IsCentral k K]

/- Domain triage:
- primary domain: tensor-product base change of simple rings along a central `k`-division algebra;
- sampled owner declarations: `two_sided_submodule_eq_baseChange_comap_one_tmul`,
  `Subbimodule.toSubmodule`, `Ideal.toTwoSided`, `IsSimpleRing.of_eq_bot_or_eq_top`;
- `source-facing`: the simplicity statement for `A ⊗[k] K`;
- `core/canonical`: a two-sided ideal of `K ⊗[k] A` is the base change of its contraction along
  `includeRight : A →ₐ[k] K ⊗[k] A`, so simplicity reduces to the owner predicate on `A`.
-/

omit [Algebra.IsCentral k K] in
private theorem left_smul_eq_includeLeft_mul (a : K) (x : K ⊗[k] A) :
    a • x = ((includeLeft : K →ₐ[k] K ⊗[k] A) a) * x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b c =>
      simp [includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy, mul_add]

omit [Algebra.IsCentral k K] in
private theorem rightOp_smul_eq_mul_includeLeft (a : Kᵐᵒᵖ) (x : K ⊗[k] A) :
    a • x = x * ((includeLeft : K →ₐ[k] K ⊗[k] A) a.unop) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b c =>
      cases a
      simp [includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy, add_mul]

/-- Lemma 11.4.4: in particular, if `A` is simple, then the tensor product `A ⊗[k] K` with a
central `k`-division algebra `K` is simple. -/
@[stacks 074C]
theorem isSimpleRing_tensorProduct_of_isSimpleRing [IsSimpleRing A] :
    IsSimpleRing (A ⊗[k] K) := by
  refine IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).symm.toRingEquiv ?_
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
  let J : Ideal A := I.asIdeal.comap (includeRight : A →ₐ[k] K ⊗[k] A)
  let W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] A) :=
    Subbimodule.mk I.asIdeal.toAddSubmonoid
      (fun a {x} hx ↦ by
        rw [left_smul_eq_includeLeft_mul]
        exact I.mul_mem_left _ _ hx)
      (fun a {x} hx ↦ by
        rw [rightOp_smul_eq_mul_includeLeft]
        exact I.mul_mem_right _ _ hx)
  have hbase : ((J.restrictScalars k).baseChange K) = I.asIdeal.restrictScalars K := by
    simpa [J, W] using
      two_sided_submodule_eq_baseChange_comap_one_tmul W
  rcases IsSimpleRing.simple.eq_bot_or_eq_top J.toTwoSided with hJ | hJ
  · left
    have hJ' : J = ⊥ := by
      simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ
    have hI : I.asIdeal.restrictScalars K = ⊥ := by
      simpa [J, hJ'] using hbase.symm
    ext x
    change x ∈ I.asIdeal.restrictScalars K ↔ x ∈ (⊥ : Submodule K (K ⊗[k] A))
    simpa using Iff.of_eq (congrArg (fun S : Submodule K (K ⊗[k] A) ↦ x ∈ S) hI)
  · right
    have hJ' : J = ⊤ := by
      simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ
    have hI : I.asIdeal.restrictScalars K = ⊤ := by
      simpa [J, hJ'] using hbase.symm
    ext x
    change x ∈ I.asIdeal.restrictScalars K ↔ x ∈ (⊤ : Submodule K (K ⊗[k] A))
    simpa using Iff.of_eq (congrArg (fun S : Submodule K (K ⊗[k] A) ↦ x ∈ S) hI)

end
