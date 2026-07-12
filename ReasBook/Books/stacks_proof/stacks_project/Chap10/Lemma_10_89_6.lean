import Mathlib
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M] [MittagLeffler R M]
variable {F : Type w} [AddCommGroup F] [Module R F]

/-- Helper for Chap10 Lemma 10 89 6: the product of quotient maps over a set of submodules. -/
private def quotientProductMap {F : Type w} [AddCommGroup F] [Module R F]
    (S : Set (Submodule R F)) :
    F →ₗ[R] ∀ N : {N : Submodule R F // N ∈ S}, F ⧸ N.1 :=
  LinearMap.pi fun N ↦ N.1.mkQ

/-- Helper for Chap10 Lemma 10 89 6: the kernel of `quotientProductMap S` is `sInf S`. -/
private lemma ker_quotientProductMap_eq_sInf {F : Type w} [AddCommGroup F] [Module R F]
    (S : Set (Submodule R F)) :
    LinearMap.ker (quotientProductMap (R := R) S) = sInf S := by
  -- Membership in the kernel is pointwise vanishing in every quotient, hence membership in every
  -- submodule indexed by `S`.
  ext y
  simp [quotientProductMap, Submodule.mem_sInf, funext_iff, Submodule.Quotient.mk_eq_zero]

/-- Helper for Chap10 Lemma 10 89 6: after commuting tensor factors, the product quotient tensor
map has the expected components. -/
private lemma piRightHom_comm_quotientProductMap_rTensor {M : Type v} [AddCommGroup M]
    [Module R M] {F : Type w} [AddCommGroup F] [Module R F] (S : Set (Submodule R F))
    (x : F ⊗[R] M) :
    TensorProduct.piRightHom R R M (fun N : {N : Submodule R F // N ∈ S} ↦ F ⧸ N.1)
        ((TensorProduct.comm R (∀ N : {N : Submodule R F // N ∈ S}, F ⧸ N.1) M)
          ((quotientProductMap (R := R) S).rTensor M x)) =
      fun N : {N : Submodule R F // N ∈ S} ↦
        (TensorProduct.comm R (F ⧸ N.1) M) (N.1.mkQ.rTensor M x) := by
  -- Tensor induction reduces the component formula to pure tensors.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · ext N
    simp [quotientProductMap]
  · intro f m
    ext N
    simp [quotientProductMap, TensorProduct.piRightHom_tmul]
  · intro x₁ x₂ hx₁ hx₂
    ext N
    simp [hx₁, hx₂]

/-- Helper for Chap10 Lemma 10 89 6: quotienting by a supporting submodule kills the tensor. -/
private lemma mkQ_rTensor_eq_zero_of_mem_range_subtype {M : Type v} [AddCommGroup M]
    [Module R M] {F : Type w} [AddCommGroup F] [Module R F] {N : Submodule R F}
    {x : F ⊗[R] M} (hx : x ∈ LinearMap.range (N.subtype.rTensor M)) :
    N.mkQ.rTensor M x = 0 := by
  -- Write `x` through `N`; the quotient map vanishes on `N`.
  rcases hx with ⟨y, rfl⟩
  rw [← LinearMap.rTensor_comp_apply]
  have hcomp : N.mkQ.comp N.subtype = 0 := by
    ext z
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [hcomp, LinearMap.rTensor_zero]
  rfl

/-- Helper for Chap10 Lemma 10 89 6: every tensor is supported on a finite left submodule. -/
private lemma exists_finite_submodule_supporting_tensor {M : Type v} [AddCommGroup M]
    [Module R M] {F : Type w} [AddCommGroup F] [Module R F] (x : F ⊗[R] M) :
    ∃ N : Submodule R F, Module.Finite R N ∧
      x ∈ LinearMap.range (N.subtype.rTensor M) := by
  -- Apply mathlib's finite-submodule support theorem to the singleton containing `x`.
  obtain ⟨N, hNfin, hN⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite
      ({x} : Set (F ⊗[R] M)) (Set.finite_singleton x)
  have hxmem : x ∈ ({x} : Set (F ⊗[R] M)) := by
    simp
  exact ⟨N, hNfin, hN hxmem⟩

/-- Helper for Chap10 Lemma 10 89 6: mapping a support inside a submodule gives a support in the
ambient module. -/
private lemma range_map_submodule_rTensor_subtype {M : Type v} [AddCommGroup M] [Module R M]
    {F : Type w} [AddCommGroup F] [Module R F] {N : Submodule R F} (E : Submodule R N) :
    LinearMap.range ((E.map N.subtype).subtype.rTensor M) =
      LinearMap.range (N.subtype.rTensor M ∘ₗ E.subtype.rTensor M) := by
  -- The image submodule is linearly equivalent to `E`, so the two ranges agree after tensoring.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨z, rfl⟩
    let e : E ≃ₗ[R] E.map N.subtype :=
      Submodule.equivMapOfInjective N.subtype N.injective_subtype E
    refine ⟨(e.symm.rTensor M) z, ?_⟩
    -- Compute after transporting through the image equivalence.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [e]
    · intro z m
      simp [e]
    · intro z₁ z₂ hz₁ hz₂
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  · intro hx
    rcases hx with ⟨z, rfl⟩
    let e : E ≃ₗ[R] E.map N.subtype :=
      Submodule.equivMapOfInjective N.subtype N.injective_subtype E
    refine ⟨(e.rTensor M) z, ?_⟩
    -- Transport a tensor from `E` to its ambient image and compare the subtype maps.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [e]
    · intro z m
      simp [e]
    · intro z₁ z₂ hz₁ hz₂
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂

/-- Helper for Chap10 Lemma 10 89 6: a least supporting submodule is finite. -/
private lemma finite_of_isLeast_supporting_submodule {M : Type v} [AddCommGroup M] [Module R M]
    {F : Type w} [AddCommGroup F] [Module R F] {N : Submodule R F} {x : F ⊗[R] M}
    (hN : IsLeast {N' : Submodule R F | x ∈ LinearMap.range (N'.subtype.rTensor M)} N) :
    Module.Finite R N := by
  -- Choose a tensor over the least support mapping to the original tensor.
  rcases hN.1 with ⟨y, hy⟩
  -- Re-support that preimage on a finite submodule of `N`.
  obtain ⟨E, hEfin, hEy⟩ :=
    exists_finite_submodule_supporting_tensor (R := R) (M := M) (F := N) y
  let E' : Submodule R F := E.map N.subtype
  have hE'fin : Module.Finite R E' := by
    exact Module.Finite.equiv (Submodule.equivMapOfInjective N.subtype N.injective_subtype E)
  have hMappedSupport : x ∈ LinearMap.range (((E.map N.subtype).subtype).rTensor M) := by
    rw [range_map_submodule_rTensor_subtype (R := R) (M := M) (E := E)]
    rcases hEy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simp [LinearMap.comp_apply, hz, hy]
  have hE'support : x ∈ LinearMap.range (E'.subtype.rTensor M) := by
    simpa [E'] using hMappedSupport
  have hE'leN : E' ≤ N := by
    intro z hz
    rcases hz with ⟨e, _he, rfl⟩
    exact (e : N).2
  have hEq : E' = N := le_antisymm hE'leN (hN.2 hE'support)
  exact hEq ▸ hE'fin

/-- Helper for Chap10 Lemma 10 89 6: the quotient-product tensor map kills tensors supported by
every indexed submodule. -/
private lemma quotientProductMap_rTensor_eq_zero_of_forall_mem_range
    {M : Type v} [AddCommGroup M] [Module R M] [MittagLeffler R M]
    {F : Type w} [AddCommGroup F] [Module R F] (S : Set (Submodule R F)) {x : F ⊗[R] M}
    (hxS : ∀ N ∈ S, x ∈ LinearMap.range (N.subtype.rTensor M)) :
    (quotientProductMap (R := R) S).rTensor M x = 0 := by
  -- Use the Mittag-Leffler injectivity criterion after commuting the product tensor.
  apply (TensorProduct.comm R (∀ N : {N : Submodule R F // N ∈ S}, F ⧸ N.1) M).injective
  apply (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1
    (inferInstance : MittagLeffler R M)
      {N : Submodule R F // N ∈ S} (fun N ↦ F ⧸ N.1))
  rw [piRightHom_comm_quotientProductMap_rTensor]
  ext N
  have hzero : N.1.mkQ.rTensor M x = 0 :=
    mkQ_rTensor_eq_zero_of_mem_range_subtype (R := R) (M := M) (N := N.1) (hxS N.1 N.2)
  simp [hzero]

/-- Helper for Chap10 Lemma 10 89 6: the infimum of all supporting submodules still supports the
tensor. -/
private lemma sInf_supportingSubmodules_mem_range_rTensor (x : F ⊗[R] M) :
    x ∈ LinearMap.range (((sInf {N : Submodule R F |
      x ∈ LinearMap.range (N.subtype.rTensor M)}).subtype).rTensor M) := by
  -- The quotient product over all supports kills `x`; flatness identifies this kernel with the
  -- tensor of the intersection.
  let S : Set (Submodule R F) := {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)}
  let q : F →ₗ[R] ∀ N : {N : Submodule R F // N ∈ S}, F ⧸ N.1 :=
    quotientProductMap (R := R) S
  have hqzero : q.rTensor M x = 0 := by
    exact quotientProductMap_rTensor_eq_zero_of_forall_mem_range (R := R) (M := M) S
      (fun N hN ↦ hN)
  have hxker : x ∈ LinearMap.ker (q.rTensor M) := by
    simpa [LinearMap.mem_ker] using hqzero
  have hExact : Function.Exact ((LinearMap.ker q).subtype.rTensor M) (q.rTensor M) :=
    Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map q)
  have hxrange : x ∈ LinearMap.range ((LinearMap.ker q).subtype.rTensor M) := by
    simpa [Function.Exact.linearMap_ker_eq hExact] using hxker
  have hker : LinearMap.ker q = sInf S := by
    simpa [q] using ker_quotientProductMap_eq_sInf (R := R) S
  rw [hker] at hxrange
  simpa [S] using hxrange

-- Proof sketch: let `I` be the set of submodules `F' ≤ F` such that `x` lies in the range of
-- `F'.subtype.rTensor M`. Apply the tensor-product injectivity criterion from Proposition
-- `10.89.5` to the family of quotients `F ⧸ F'` indexed by `I`, so that `x` maps to zero in the
-- product of the quotient tensors and hence in the tensor with the product. Flatness identifies
-- the kernel of the induced map with the tensor of the intersection `sInf I`, giving the smallest
-- supporting submodule. A finite expression of `x` as a sum of pure tensors then shows this
-- smallest submodule is finitely generated, hence finite.
/-- Chap10 Lemma 10 89 6 (Lemma 10.89.6): for a flat Mittag-Leffler module `M`, every tensor
`x : F ⊗[R] M` is supported
by a smallest submodule `F' ≤ F`, and this smallest supporting submodule is finite. In Lean, the
support condition is expressed by `x ∈ LinearMap.range (F'.subtype.rTensor M)`. -/
@[stacks 0AS6]
theorem exists_smallest_finite_submodule_of_mem_tensorProduct
    (x : F ⊗[R] M) :
    ∃ F' : Submodule R F,
      IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' ∧
        Module.Finite R F' := by
  -- Take the infimum of all supports, prove it is a support, then use leastness to force
  -- finiteness.
  let S : Set (Submodule R F) :=
    {F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M)}
  let F₀ : Submodule R F := sInf S
  have hF₀mem : F₀ ∈ S := by
    simpa [F₀, S] using
      sInf_supportingSubmodules_mem_range_rTensor (R := R) (M := M) (F := F) x
  have hleast : IsLeast S F₀ := by
    refine ⟨hF₀mem, ?_⟩
    intro N hN
    exact sInf_le hN
  refine ⟨F₀, ?_, ?_⟩
  · simpa [S, F₀] using hleast
  · have hleastTarget :
        IsLeast {F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M)} F₀ := by
      simpa [S, F₀] using hleast
    exact finite_of_isLeast_supporting_submodule (R := R) (M := M) (F := F) (N := F₀)
      (x := x) hleastTarget

end

end Module
