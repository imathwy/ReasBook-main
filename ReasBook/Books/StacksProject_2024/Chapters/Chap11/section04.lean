import Mathlib
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_11_4_1 (from Chap11) -/
open scoped TensorProduct
open Algebra.TensorProduct Subalgebra

universe u v w

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {A₂ : Type w} [Ring A₂] [Algebra k A₂]

/- Domain sampling for Lemma 11.4.1.
- primary domain: tensor-product subalgebras and centralizers in `A ⊗[k] A₂`;
- inspected owner declarations:
  `Subalgebra.centralizer_coe_sup`,
  `Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct`,
  `Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct`,
  `Algebra.TensorProduct.map_range`;
- best owner abstraction: `Subalgebra.centralizer` applied to the canonical tensor-product
  subalgebra `(Algebra.TensorProduct.map B.val B₂.val).range`;
- primitive data: the subalgebras `B`, `B₂` and the owner tensor-product map;
- derived API: the one-sided centralizer computations and the `map_range` identification with the
  join of the left/right image subalgebras;
- layer classification:
  `source-facing`: the textbook centralizer statement for `B ⊗[k] B₂`;
  `core/canonical`: `Subalgebra.centralizer`;
  `bridge/view`: `Algebra.TensorProduct.map_range` and the one-sided centralizer lemmas. -/

/-- Lemma 11.4.1: for `k`-subalgebras `B ⊆ A` and `B' ⊆ A₂`, the centralizer of the tensor-product
subalgebra `B ⊗[k] B' ⊆ A ⊗[k] A₂` is the tensor product of the centralizers of `B` and `B'`. -/
-- Proof sketch: `(Algebra.TensorProduct.map B.val B₂.val).range` is the canonical tensor-product
-- subalgebra in `A ⊗[k] A₂`, and `Algebra.TensorProduct.map_range` identifies it with the
-- supremum of the left and right image subalgebras `B.map includeLeft` and
-- `B₂.map includeRight`. The one-sided owner lemmas compute the corresponding centralizers; the
-- remaining bridge identifies their intersection with the tensor product of the two centralizers,
-- for example by passing through the smaller ambient algebra `C_A(B) ⊗[k] A₂`.
theorem centralizer_tensorProduct_subalgebra_eq
    (B : Subalgebra k A) (B₂ : Subalgebra k A₂) :
    centralizer k (map B.val B₂.val).range =
      (map (centralizer k (B : Set A)).val (centralizer k (B₂ : Set A₂)).val).range := by
  let C : Subalgebra k A := centralizer k (B : Set A)
  let C₂ : Subalgebra k A₂ := centralizer k (B₂ : Set A₂)
  let ι : C ⊗[k] A₂ →ₐ[k] A ⊗[k] A₂ := map C.val (AlgHom.id k A₂)
  let S : Subalgebra k (A ⊗[k] A₂) := centralizer k (B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂))
  let T : Subalgebra k (C ⊗[k] A₂) := centralizer k (B₂.map (includeRight : A₂ →ₐ[k] C ⊗[k] A₂))
  have h_tensor :
      (map B.val B₂.val).range =
        B.map (includeLeft : A →ₐ[k] A ⊗[k] A₂) ⊔
          B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂) := by
    simpa [AlgHom.range_comp, range_val] using map_range B.val B₂.val
  have hι : Function.Injective ι := by
    change Function.Injective
      (TensorProduct.map C.val.toLinearMap (LinearMap.id : A₂ →ₗ[k] A₂))
    simpa using TensorProduct.map_injective_of_flat_flat
      C.val.toLinearMap (LinearMap.id : A₂ →ₗ[k] A₂) Subtype.val_injective
      (fun _ _ h ↦ h)
  have h_left :
      centralizer k (B.map (includeLeft : A →ₐ[k] A ⊗[k] A₂)) = ι.range := by
    simpa [C, ι, AlgHom.range_comp] using
      centralizer_coe_map_includeLeft_eq_center_tensorProduct k A A₂ B
  have h_comap : S.comap ι = T := by
    ext x
    rw [mem_comap, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx y
      rintro ⟨b, hb, rfl⟩
      apply hι
      simpa using hx (includeRight b) ⟨b, hb, rfl⟩
    · intro hx y
      rintro ⟨b, hb, rfl⟩
      simpa using congrArg ι (hx (includeRight b) ⟨b, hb, rfl⟩)
  have h_right :
      T = (map (AlgHom.id k C) C₂.val).range := by
    simpa [C₂, T] using
      centralizer_coe_map_includeRight_eq_center_tensorProduct k C A₂ B₂
  have h_map :
      ((map (AlgHom.id k C) C₂.val).range).map ι = (map C.val C₂.val).range := by
    have h_comp :
        ι.comp (map (AlgHom.id k C) C₂.val) = map C.val C₂.val := by
      simpa [ι] using (map_comp C.val (AlgHom.id k C) (AlgHom.id k A₂) C₂.val).symm
    rw [← AlgHom.range_comp]
    exact congrArg AlgHom.range h_comp
  rw [h_tensor, centralizer_coe_sup, h_left,
    show centralizer k (B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂)) = S from rfl,
    inf_comm, ← map_comap_eq ι S, h_comap, h_right, h_map]

/-! ### Lemma_11_4_2 (from Chap11) -/
universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/- Domain-style sampling for Lemma 11.4.2:
- primary domain: centers of simple finite-dimensional algebras;
- sampled owner declarations:
  `FiniteDimensional`,
  `FiniteDimensional.finiteDimensional_subalgebra`,
  `Subalgebra.center`,
  `IsSimpleRing.isField_center`;
- best owner abstraction: this item is `source-facing`, with the finiteness input carried by the
  chapter owner `FiniteDimensional k A`; the center itself is the canonical owner object
  `Subalgebra.center k A`;
- primitive data: the ambient `k`-algebra structure on `A`, together with `[FiniteDimensional k A]`
  and `[IsSimpleRing A]`;
- derived API: finite-dimensionality of the center as a subalgebra, and the field structure read
  from the simple-ring center theorem through `Subalgebra.center_toSubring`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the center of a finite simple `k`-algebra is a
  finite field extension of `k`;
- `core/canonical`: `Subalgebra.center k A`, `FiniteDimensional`, and
  `IsSimpleRing.isField_center`;
- `bridge/view`: `Subalgebra.center_toSubring`, identifying the algebra center with the ring
  center used by the owner theorem. -/

/- Owner recall for the field part of Lemma 11.4.2: the center of a simple ring is a field via
`IsSimpleRing.isField_center`; for a `k`-algebra this is read through
`Subalgebra.center_toSubring`. -/
recall IsSimpleRing.isField_center

/- The finite-dimensional part is derived, not additional center-specific structure: a subalgebra
of a finite-dimensional algebra over a field is finite-dimensional. -/
#check FiniteDimensional.finiteDimensional_subalgebra

/-- Lemma 11.4.2: if `A` is a finite simple `k`-algebra, then its center
`Subalgebra.center k A` is a finite field extension of `k`. -/
theorem center_finiteFieldExtension [FiniteDimensional k A] [IsSimpleRing A] :
    FiniteDimensional k (Subalgebra.center k A) ∧ IsField (Subalgebra.center k A) := by
  refine ⟨inferInstance, ?_⟩
  simpa [Subalgebra.center_toSubring] using IsSimpleRing.isField_center A

end

/-! ### Lemma_11_4_3 (from Chap11) -/
open LinearMap TensorProduct MulOpposite
open scoped TensorProduct

attribute [local instance] TensorProduct.Algebra.module

universe u v w

section

variable {k : Type u} {K : Type v} {V : Type w}
variable [Field k] [DivisionRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

/- Domain triage:
- primary domain: tensor products and submodules with commuting left/right scalar actions over a
  `k`-algebra `K`.
- sampled owner declarations: `Subbimodule.toSubmodule`, `Submodule.baseChange`,
  `Submodule.baseChange_eq_span`, `Submodule.map_comap_eq`.
- `source-facing`: a `k`-submodule of `V ⊗[k] K` stable under left and right multiplication on the
  `K`-factor, viewed through the canonical factor-swap `TensorProduct.comm k V K`.
- `core/canonical`: after commuting factors, a `K`-`K` subbimodule
  `W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)`.
- `bridge/view`: the corresponding `K`-submodule `Subbimodule.toSubmodule W` and its source-model
  transport back to `V ⊗[k] K`.

Primitive data vs derived API:
- primitive owner data: the ambient `K`-`K` subbimodule on `K ⊗[k] V`, and the source-facing
  `k`-submodule together with its left/right stability data;
- derived/source-facing data: the underlying left `K`-submodule, together with the corresponding
  generation/base change descriptions in the two tensor models.
-/

/-- Right multiplication on the `K`-factor of `K ⊗[k] V` is the canonical `Kᵐᵒᵖ`-action coming
from the first tensor factor. -/
@[simp] theorem op_smul_eq_rTensor_mulRight (a : K) (x : K ⊗[k] V) :
    op a • x = (((mulRight k a).rTensor V) : K ⊗[k] V →ₗ[k] K ⊗[k] V) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b v =>
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

section TwoSidedSubmodule

variable [Algebra.IsCentral k K]

/-- Lemma 11.4.3, source-facing bridge/view: for a `k`-vector space `V` and a central
`k`-division algebra `K`, a `k`-submodule of `V ⊗[k] K` stable under left and right
multiplication on the `K`-factor is obtained by transporting back the left `K`-span of the
intersection of its commuted image with `1 ⊗ V`. -/
theorem two_sided_submodule_eq_generated_by_inter_tmul_one
    (W : Submodule k (V ⊗[k] K))
    (hW_left :
      ∀ a : K,
        Set.MapsTo (((mulLeft k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    (hW_right :
      ∀ a : K,
        Set.MapsTo (((mulRight k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    :
    let W' : Submodule k (K ⊗[k] V) := W.map (TensorProduct.comm k V K).toLinearMap
    ((Submodule.span K ↑(W' ⊓ LinearMap.range (mk k K V 1))).restrictScalars k).map
      (TensorProduct.comm k K V).toLinearMap = W := by
  sorry

/-- Core/canonical bridge for Lemma 11.4.3: for a `k`-vector space `V` and a central
`k`-division algebra `K`, a two-sided `K`-submodule of `K ⊗[k] V` is the base change of its
contraction along `v ↦ 1 ⊗ v`. -/
theorem two_sided_submodule_eq_baseChange_comap_one_tmul
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    let V' := ((Subbimodule.toSubmodule W).restrictScalars k).comap
      (mk k K V 1)
    V'.baseChange K = Subbimodule.toSubmodule W := sorry

/-- Bridge/view companion to Lemma 11.4.3, in the commuted owner model `K ⊗[k] V`: for a central
`k`-division algebra `K`, a two-sided `K`-submodule is the left `K`-span of its intersection with
`1 ⊗ V`. -/
theorem two_sided_submodule_comm_eq_generated_by_inter_tmul_one
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    Submodule.span K ↑((Subbimodule.toSubmodule W).restrictScalars k ⊓
      LinearMap.range (mk k K V 1)) = Subbimodule.toSubmodule W := by
  simpa [Submodule.baseChange_eq_span, Submodule.map_comap_eq, inf_comm] using
    two_sided_submodule_eq_baseChange_comap_one_tmul W

end TwoSidedSubmodule

end

/-! ### Lemma_11_4_4 (from Chap11) -/
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

/-- If `A` is simple, then the tensor product `A ⊗[k] K` with a central `k`-division algebra `K`
is simple. -/
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

/-! ### Lemma_11_4_5 (from Chap11) -/
/- Domain-style sampling for Lemma 11.4.5:
- primary domain: Morita-theoretic and ring-theoretic invariants of full matrix rings, with the
  chapter convention that an `A`-module means a right `A`-module, modeled as a left module over
  `Aᵐᵒᵖ`;
- sampled owner declarations:
  `ModuleCat.matrixEquivalence`,
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`,
  `TwoSidedIdeal.equivMatrix`,
  `Matrix.subringCenter_eq_scalar_map`;
- best owner abstractions:
  `ModuleCat.matrixEquivalence` for the underlying Morita equivalence, transported to right
  modules by `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` along the canonical matrix-opposite
  ring equivalence `RingEquiv.mopMatrix`,
  `TwoSidedIdeal.equivMatrix` for the source-facing ideal correspondence,
  `Matrix.subringCenter_eq_scalar_map` for the center computation;
- primitive data: only the ring `R`, the size `n`, and a witness of `Fin n` when nonemptiness is
  needed to instantiate the Morita inverse and ideal correspondence;
- derived API: the textbook statements are direct views of those owner declarations and their
  canonical bridge, so this file should stay at the recall/bridge layer rather than introducing
  local wrappers.

Source/core/bridge triage:
- `source-facing`: the three textbook properties of full matrix rings listed in Lemma 11.4.5,
  where part (1) is a statement about right modules;
- `core/canonical`: `ModuleCat.matrixEquivalence`, `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`,
  `TwoSidedIdeal.equivMatrix`, and `Matrix.subringCenter_eq_scalar_map`;
- `bridge/view`: `RingEquiv.mopMatrix`, which identifies modules over
  `Matrix (Fin n) (Fin n) Rᵐᵒᵖ` with right modules over `Matrix (Fin n) (Fin n) R`, and the
  `#check` lines below exhibiting the source statements as direct uses of those owners. -/

section RightModuleEquivalence

open CategoryTheory

variable (R : Type*) [Ring R] (n : ℕ) (hn : 1 ≤ n)

/- Owner recall for Lemma 11.4.5 (1): the canonical owner abstraction is the Morita equivalence
for left modules over `Rᵐᵒᵖ`, namely `ModuleCat.matrixEquivalence`, together with the canonical
change-of-rings equivalence induced by `RingEquiv.mopMatrix`. -/
recall ModuleCat.matrixEquivalence
recall ModuleCat.restrictScalarsEquivalenceOfRingEquiv
recall RingEquiv.mopMatrix

/- Lemma 11.4.5 (1): for a possibly noncommutative ring `R` and `n ≥ 1`, the equivalence between
right `R`-modules and right `M_n(R)`-modules is obtained by applying
`ModuleCat.matrixEquivalence` to `Rᵐᵒᵖ` and then transporting across the canonical identification
`Matrix (Fin n) (Fin n) Rᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ`. -/
#check
  ((ModuleCat.matrixEquivalence Rᵐᵒᵖ (⟨0, Nat.succ_le_iff.mp hn⟩ : Fin n)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      RingEquiv.mopMatrix).symm :
      ModuleCat Rᵐᵒᵖ ≌ ModuleCat (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ)

end RightModuleEquivalence

section TwoSidedIdeals

variable (R : Type*) [Ring R] (n : ℕ) (hn : 1 ≤ n)

/- Owner recall for Lemma 11.4.5 (2): the ideal correspondence lives canonically in
`TwoSidedIdeal.equivMatrix`. -/
recall TwoSidedIdeal.equivMatrix

/- Lemma 11.4.5 (2): the correspondence between two-sided ideals of `R` and of the matrix ring
`Matrix (Fin n) (Fin n) R` is the canonical equivalence `TwoSidedIdeal.equivMatrix`; the
textbook existence statement is its surjectivity. -/
#check
  (let _ : Nonempty (Fin n) := ⟨⟨0, Nat.succ_le_iff.mp hn⟩⟩
   TwoSidedIdeal.equivMatrix :
     TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix (Fin n) (Fin n) R))

end TwoSidedIdeals

section Center

variable (R : Type*) [Ring R] (n : ℕ)

/- Owner recall for Lemma 11.4.5 (3): the center statement is exactly the matrix-center owner
theorem `Matrix.subringCenter_eq_scalar_map`. -/
recall Matrix.subringCenter_eq_scalar_map

/- Lemma 11.4.5 (3): the center of `Matrix (Fin n) (Fin n) R` is the image of the center of
`R` under the scalar-matrix embedding, which is the precise Lean form of saying that the center
of `Rₙ` equals the center of `R`. -/
#check
  (Matrix.subringCenter_eq_scalar_map R :
    Subring.center (Matrix (Fin n) (Fin n) R) = (Subring.center R).map (Matrix.scalar (Fin n)))

end Center

/-! ### Lemma_11_4_6 (from Chap11) -/
universe u v w w' w''

private noncomputable def module_double_centralizer_of_finite_end
    (A : Type v) (M : Type w) [Ring A] [IsSimpleRing A] [AddCommGroup M] [Module A M]
    [Nontrivial M] [IsSemisimpleModule A M] [Module.Finite (Module.End A M) M] :
    A ≃+* Module.End (Module.End A M) M :=
  RingEquiv.ofBijective (Module.toModuleEnd (Module.End A M) M)
    ⟨RingHom.injective _, Module.Finite.toModuleEnd_moduleEnd_surjective⟩

section SimpleAlgebra

open LinearMap

variable {k : Type u} {A : Type v}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

-- Proof sketch: apply the earlier existence result for simple submodules of the regular module of
-- a finite-dimensional algebra to the regular left `A`-module.
/- Lemma 11.4.6 (1): a finite simple `k`-algebra admits a simple left module, realized as a
simple submodule of the regular module `A`; this is exactly the earlier regular-module
specialization, with `IsSimpleRing A` supplying the needed `Nontrivial A` hypothesis. -/
recall finite_algebra_exists_simple_submodule_regular

variable {M : Type w} {N : Type w'} {P : Type w''}
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable [AddCommGroup P] [Module A P]

-- Proof sketch: identify `A` with a matrix algebra over a division ring, transport both simple
-- modules across the Morita equivalence to simple modules over that division ring, and use that a
-- simple module over a division ring is unique up to linear equivalence.
/-- Lemma 11.4.6 (2): any two simple left `A`-modules are isomorphic. -/
theorem simple_modules_unique_up_to_linear_equiv
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] :
    Nonempty (M ≃ₗ[A] N) := by
  have hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  have ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A M
  have ⟨J, ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A N
  let _ : IsSimpleModule A I := eM.isSimpleModule_iff.mp inferInstance
  let _ : IsSimpleModule A J := eN.isSimpleModule_iff.mp inferInstance
  have hJI : Nonempty (J ≃ₗ[A] I) := hA I J
  exact ⟨eM.trans hJI.some.symm |>.trans eN.symm⟩

-- Proof sketch: after identifying `A` with a matrix algebra over a division ring, transport `M`
-- and `N` across the matrix-ring equivalence; finite modules over a division ring are free of
-- finite rank, and transporting back identifies `N` with finitely many copies of the simple
-- module `M`.
/-- Lemma 11.4.6 (3): every finite left `A`-module is a finite direct sum of copies of a fixed
simple left `A`-module; here `Fin n → M` represents the finite direct sum of `n` copies of `M`. -/
theorem finite_module_equiv_pi_of_simple_module
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [Module.Finite A N] :
    ∃ n : ℕ, Nonempty (N ≃ₗ[A] (Fin n → M)) := by
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let hNM : IsIsotypicOfType A N M := fun S _ ↦ by
    let _ : IsSimpleModule A S := ‹_›
    exact simple_modules_unique_up_to_linear_equiv
  exact hNM.linearEquiv_fun

variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

-- Proof sketch: decompose both finite modules into finite direct sums of the unique simple
-- module, and compare the number of summands using the finite `k`-dimension of that simple
-- module.
/-- Lemma 11.4.6 (4): two finite left `A`-modules are isomorphic exactly when they have the same
dimension over `k`. -/
theorem finite_modules_linear_equiv_iff_finrank_eq [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := sorry

end SimpleAlgebra

section MatrixModel

open scoped Matrix.Module

variable {K : Type v} [DivisionRing K]
variable {n : ℕ}

-- Proof sketch: transport the simple left `K`-module `K` across the canonical Morita equivalence
-- between `K` and `Matrix (Fin n) (Fin n) K`.
/-- Lemma 11.4.6 (5): if `A = Matrix (Fin n) (Fin n) K` with `n ≥ 1`, then the standard module
`K^{⊕ n}`, represented in Lean as `Fin n → K`, is simple. -/
theorem matrix_simple_module (hn : 1 ≤ n) :
    IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := sorry

private noncomputable def endSelfToMatrixModuleEnd :
    Module.End K K →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]

private noncomputable def scalarToMatrixModuleEnd :
    Kᵐᵒᵖ →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEnd.comp (RingEquiv.moduleEndSelf K).toRingHom

private theorem scalarToMatrixModuleEnd_apply (x : Kᵐᵒᵖ) (v : Fin n → K) :
    scalarToMatrixModuleEnd x v = fun i ↦ v i * MulOpposite.unop x := by
  ext i
  simp [scalarToMatrixModuleEnd, endSelfToMatrixModuleEnd, LinearMap.mapMatrixModule_apply]

private noncomputable def matrixModuleEndScalar (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) : K :=
  f (Pi.single ⟨0, hn⟩ (1 : K)) ⟨0, hn⟩

private theorem matrixModuleEnd_basis_eq (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    ∀ i : Fin n,
      f (Pi.single i (1 : K)) = Pi.single i (matrixModuleEndScalar hn f) := by
  let i0 : Fin n := ⟨0, hn⟩
  have h0 : f (Pi.single i0 (1 : K)) = Pi.single i0 (matrixModuleEndScalar hn f) := by
    simpa [matrixModuleEndScalar, i0, Matrix.Module.single_smul] using
      (f.map_smul (Matrix.single i0 i0 (1 : K)) (Pi.single i0 (1 : K)))
  intro i
  simpa [i0, h0, Matrix.Module.single_smul] using
    (f.map_smul (Matrix.single i i0 (1 : K)) (Pi.single i0 (1 : K)))

private theorem scalarToMatrixModuleEnd_left_inv (hn : 1 ≤ n) (x : Kᵐᵒᵖ) :
    matrixModuleEndScalar hn (scalarToMatrixModuleEnd x) = MulOpposite.unop x := by
  simp [matrixModuleEndScalar, scalarToMatrixModuleEnd_apply]

private theorem scalarToMatrixModuleEnd_right_inv (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) = f := by
  ext v i
  have hbasis := matrixModuleEnd_basis_eq hn f
  have hv : v = ∑ j : Fin n, v j • (Pi.single j (1 : K) : Fin n → K) := by
    ext j
    simp [Pi.single_apply]
  have hfv : f v = ∑ j : Fin n, v j • f (Pi.single j (1 : K)) := by
    ext i
    rw [hv, map_sum]
    simp [Pi.single_apply, f.map_smul_of_tower]
  calc
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) v i
        = (fun j ↦ v j * matrixModuleEndScalar hn f) i := by
            simp [scalarToMatrixModuleEnd_apply]
    _ = (f v) i := by
      rw [hfv]
      simp [hbasis, Pi.single_apply]

private noncomputable def scalarToMatrixModuleEndEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  RingEquiv.ofBijective scalarToMatrixModuleEnd <| by
    constructor
    · intro x y h
      apply MulOpposite.unop_injective
      rw [← scalarToMatrixModuleEnd_left_inv hn x, ← scalarToMatrixModuleEnd_left_inv hn y, h]
    · intro f
      exact ⟨MulOpposite.op (matrixModuleEndScalar hn f), scalarToMatrixModuleEnd_right_inv hn f⟩

section

variable {k : Type u} [Field k] [Algebra k K]

private noncomputable def endSelfToMatrixModuleEndAlgHom :
    Module.End K K →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  commutes' c := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply, Algebra.algebraMap_eq_smul_one]

private noncomputable def scalarToMatrixModuleEndAlgHom :
    Kᵐᵒᵖ →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEndAlgHom.comp
    (AlgEquiv.moduleEndSelf k : Kᵐᵒᵖ ≃ₐ[k] Module.End K K).toAlgHom

private noncomputable def scalarToMatrixModuleEndAlgEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  AlgEquiv.ofBijective scalarToMatrixModuleEndAlgHom <| by
    constructor
    · intro x y h
      let φ : Kᵐᵒᵖ →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
        scalarToMatrixModuleEnd
      have h' : φ x = φ y := by
        simpa [scalarToMatrixModuleEndAlgHom, scalarToMatrixModuleEnd,
          endSelfToMatrixModuleEndAlgHom, endSelfToMatrixModuleEnd, φ] using h
      have hs : matrixModuleEndScalar hn (φ x) = matrixModuleEndScalar hn (φ y) :=
        congrArg (matrixModuleEndScalar hn) h'
      apply MulOpposite.unop_injective
      rw [← scalarToMatrixModuleEnd_left_inv hn x, ← scalarToMatrixModuleEnd_left_inv hn y]
      simpa [φ] using hs
    · intro f
      refine ⟨MulOpposite.op (matrixModuleEndScalar hn f), ?_⟩
      simpa [scalarToMatrixModuleEndAlgHom, scalarToMatrixModuleEnd,
        endSelfToMatrixModuleEndAlgHom, endSelfToMatrixModuleEnd] using
        scalarToMatrixModuleEnd_right_inv hn f

/-- Lemma 11.4.6 (6): for the standard simple module over `Matrix (Fin n) (Fin n) K`, the
endomorphism ring is `k`-algebra isomorphic to `Kᵐᵒᵖ`. -/
noncomputable def matrix_endomorphism_alg_equiv_op (hn : 1 ≤ n) :
    Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
  (scalarToMatrixModuleEndAlgEquiv hn).symm

end

end MatrixModel

section SimpleModuleEndomorphisms

open Module.End

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]

-- Proof sketch: this is Schur's lemma for a simple module: a nonzero endomorphism is injective
-- and surjective, hence invertible.
/-- Lemma 11.4.6 (7): if `M` is a simple left `A`-module, then every nonzero `A`-endomorphism of
`M` is a unit, so `Module.End A M` is a skew field. -/
theorem simple_module_endomorphism_isUnit_of_ne_zero
    {A : Type v} {M : Type w} [Ring A] [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (f : Module.End A M) (hf : f ≠ 0) :
    IsUnit f := by
  exact (Module.End.isUnit_iff f).2 (f.bijective_of_ne_zero hf)

variable [Module k M] [IsScalarTower k A M]

-- Proof sketch: reduce to the matrix-algebra description of `A` and the standard simple module,
-- where the endomorphism ring is the opposite of a finite-dimensional division algebra over `k`.
/-- Lemma 11.4.6 (8): for a simple left `A`-module `M`, the endomorphism skew field
`Module.End A M` is finite-dimensional over `k`. -/
theorem simple_module_endomorphism_finite_dimensional :
    FiniteDimensional k (Module.End A M) := sorry

private theorem simple_module_moduleFinite_over_end
    (A : Type v) (M : Type w)
    [Ring A] [IsSimpleRing A] [IsArtinianRing A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.Finite (Module.End A M) M := by
  let hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  obtain ⟨n, _, S, _hS, ⟨e⟩⟩ := hA.linearEquiv_fun
  have hSM : Nonempty (S ≃ₗ[A] M) := simple_modules_unique_up_to_linear_equiv
  let eSM : S ≃ₗ[A] M := hSM.some
  let e' : A ≃ₗ[A] Fin n → M := e.trans <| .piCongrRight fun _ ↦ eSM
  let v : Fin n → M := e' (1 : A)
  have hspan : Submodule.span (Module.End A M) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let p : A →ₗ[A] M :=
      { toFun := fun a ↦ a • x
        map_add' := fun _ _ ↦ by simp [add_smul]
        map_smul' := fun a b ↦ by simp [mul_smul] }
    let g : (Fin n → M) →ₗ[A] M := p.comp e'.symm.toLinearMap
    refine (Submodule.mem_span_range_iff_exists_fun (Module.End A M)).2 ?_
    refine ⟨fun i ↦ g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i), ?_⟩
    calc
      ∑ i, (g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i) : Module.End A M) • v i
          = ∑ i, g (Pi.single i (v i)) := by
              simp [LinearMap.comp_apply]
      _ = g (∑ i, Pi.single i (v i)) := by rw [map_sum]
      _ = g (e' (1 : A)) := by
            congr
            ext i
            simp [v]
      _ = x := by simp [g, p]
  let _ : Module.Finite (Module.End A M) (Fin n → Module.End A M) :=
    Module.Finite.of_basis (Pi.basisFun (Module.End A M) (Fin n))
  exact Module.Finite.of_surjective
    (Fintype.linearCombination (Module.End A M) v)
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination (Module.End A M) v).1
      hspan)

-- Proof sketch: this is the ring-theoretic bicommutant theorem in the simple-Artinian setting;
-- the later `k`-algebra formulation is just a thin bridge on top of this owner equivalence.
/-- Owner abstraction underlying Lemma 11.4.6 (9): for a simple left module over a simple
Artinian ring, the bicommutant recovers the original ring. -/
noncomputable def simple_module_double_centralizer [IsArtinianRing A] :
    A ≃+* Module.End (Module.End A M) M :=
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : IsSemisimpleRing A := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let _ : Module.Finite (Module.End A M) M := simple_module_moduleFinite_over_end A M
  module_double_centralizer_of_finite_end A M

-- Proof sketch: this source-facing algebra statement is the ambient `k`-linear refinement of the
-- simple-Artinian owner equivalence `simple_module_double_centralizer`.
/-- Lemma 11.4.6 (9): if `M` is a simple left `A`-module over a finite-dimensional simple
`k`-algebra `A`, then `A` identifies with the
endomorphism `k`-algebra of `M` viewed as a left `Module.End A M`-module. -/
noncomputable def simple_module_double_centralizer_algEquiv [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let e : A ≃+* Module.End (Module.End A M) M := simple_module_double_centralizer
  { __ := e
    commutes' c := by
      ext m
      simp [e, simple_module_double_centralizer, module_double_centralizer_of_finite_end,
        Algebra.algebraMap_eq_smul_one] }

private def centerToModuleEndCenter
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] :
    Subring.center R →+* Subring.center (Module.End R M) where
  toFun z := by
    let hz : (z : R) ∈ Set.center R := by
      rw [Semigroup.mem_center_iff]
      exact Subring.mem_center_iff.mp z.2
    exact ⟨Module.End.smulLeft z.1 hz, by
      change Module.End.smulLeft z.1 hz ∈ Set.center (Module.End R M)
      exact (Module.End.mem_center_iff).2 ⟨z.1, hz, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext m
    change (1 : R) • m = m
    simp
  map_mul' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) * (y : R)) • m = (x : R) • ((y : R) • m)
    simp [mul_smul]
  map_zero' := by
    apply Subtype.ext
    ext m
    change (0 : R) • m = 0
    simp
  map_add' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) + (y : R)) • m = (x : R) • m + (y : R) • m
    simp [add_smul]

private noncomputable def centerModuleEndEquiv
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    Subring.center R ≃+* Subring.center (Module.End R M) :=
  RingEquiv.ofBijective (centerToModuleEndCenter R M) <| by
    constructor
    · intro x y hxy
      apply Subtype.ext
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      exact smul_left_injective R hm <| by
        simpa using congrArg (fun f : Module.End R M ↦ f m) (congrArg Subtype.val hxy)
    · intro f
      have hf : (f : Module.End R M) ∈ Set.center (Module.End R M) := by
        rw [Semigroup.mem_center_iff]
        exact Subring.mem_center_iff.mp f.2
      rcases (Module.End.mem_center_iff).1 hf with ⟨r, hr, hfr⟩
      refine ⟨⟨r, by
        rw [Subring.mem_center_iff]
        exact Semigroup.mem_center_iff.mp hr⟩, ?_⟩
      apply Subtype.ext
      simpa [centerToModuleEndCenter] using hfr.symm

-- Proof sketch: after identifying `A` with `Module.End (Module.End A M) M`, both centers become
-- the scalar endomorphisms of the simple module, giving a canonical ring equivalence.
/-- Lemma 11.4.6 (10): the centers of `A` and `Module.End A M` are canonically ring-isomorphic. -/
noncomputable def simple_module_center_equiv
    [IsArtinianRing A] :
    Subring.center A ≃+* Subring.center (Module.End A M) := by
  classical
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : DecidableEq (Module.End A M) := Classical.decEq _
  let _ : DivisionRing (Module.End A M) := Module.End.instDivisionRing
  let e : A ≃+* Module.End (Module.End A M) M := simple_module_double_centralizer
  exact (Subring.centerCongr e).trans <|
    (centerModuleEndEquiv (Module.End A M) M).symm

-- Proof sketch: in the matrix-algebra model `A ≃ Matrix (Fin n) (Fin n) K` and
-- `Module.End A M ≃ Kᵐᵒᵖ`, so the stated formula is the usual matrix-dimension computation.
/-- Lemma 11.4.6 (11): if `M` is a simple left `A`-module and `L = Module.End A M`, then
`[A : k] [L : k] = dim_k(M)^2`. -/
theorem simple_module_finrank_formula :
    Module.finrank k A * Module.finrank k (Module.End A M) = (Module.finrank k M) ^ 2 := sorry

end SimpleModuleEndomorphisms

section FiniteModuleEndomorphisms

variable {k : Type u} {A : Type v} {M : Type w} {N : Type w'}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]
variable [AddCommGroup N] [Module A N] [Module.Finite A N]
variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

-- Proof sketch: decompose `N` as a finite direct sum of copies of the unique simple module `M`,
-- then compute endomorphisms of that finite direct sum as matrices with entries in
-- `Module.End A M`.
/-- Lemma 11.4.6 (12): for a finite left `A`-module `N`, the endomorphism ring `Module.End A N`
is `k`-algebra isomorphic to a matrix algebra over the skew field `Module.End A M`, where `M` is
any simple left `A`-module. -/
theorem finite_module_endomorphism_ring_matrix :
    ∃ n : ℕ, Nonempty (Module.End A N ≃ₐ[k] Matrix (Fin n) (Fin n) (Module.End A M)) := sorry

-- Proof sketch: identify `N` with a finite direct sum of copies of a simple module and compute
-- the bicommutant explicitly for that matrix action; nontriviality rules out the zero module,
-- where the statement would fail.
/-- Lemma 11.4.6 (13): for a nonzero finite left `A`-module `N`, the bicommutant of `N` recovers
the original algebra `A`. -/
noncomputable def finite_module_double_centralizer [Nontrivial N] :
    A ≃ₐ[k] Module.End (Module.End A N) N :=
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr (IsArtinianRing.of_finite k A)
  let _ : Module.Finite k N := Module.Finite.trans A N
  let _ : Module.Finite (Module.End A N) N :=
    Module.Finite.of_restrictScalars_finite k (Module.End A N) N
  let e : A ≃+* Module.End (Module.End A N) N := module_double_centralizer_of_finite_end A N
  { __ := e
    commutes' c := by
      ext n
      simp [e, module_double_centralizer_of_finite_end, Algebra.algebraMap_eq_smul_one] }

end FiniteModuleEndomorphisms

/-! ### Lemma_11_4_7 (from Chap11) -/
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} {A' : Type w} [Ring A] [Ring A'] [Algebra k A] [Algebra k A']
variable [IsSimpleRing A] [IsSimpleRing A']

/-- If `A` is a finite-dimensional central simple `k`-algebra and `A'` is simple over `k`, then
`A ⊗[k] A'` is simple. -/
theorem isSimpleRing_tensorProduct_of_finite_central_left_factor
    [FiniteDimensional k A] [Algebra.IsCentral k A] :
    IsSimpleRing (A ⊗[k] A') := sorry

/-- Lemma 11.4.7: if `A` and `A'` are simple `k`-algebras and one of them is finite-dimensional
and central over `k`, then the tensor product `A ⊗[k] A'` is simple. -/
-- Proof sketch: argue by cases on which factor is finite and central. In the finite central case,
-- apply the Wedderburn decomposition of that factor into a matrix algebra over a central division
-- algebra, use Lemma 11.4.4 to obtain simplicity after tensoring with the division algebra, and
-- then transport simplicity across the resulting matrix-algebra identification using Lemma 11.4.5.
theorem isSimpleRing_tensorProduct_of_finite_central_factor
    (h : (FiniteDimensional k A ∧ Algebra.IsCentral k A) ∨
      (FiniteDimensional k A' ∧ Algebra.IsCentral k A')) :
    IsSimpleRing (A ⊗[k] A') := by
  rcases h with h | h
  · letI := h.1
    letI := h.2
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  · letI := h.1
    letI := h.2
    let h' : IsSimpleRing (A' ⊗[k] A) :=
      isSimpleRing_tensorProduct_of_finite_central_left_factor
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' A).toRingEquiv h'

end

/-! ### Lemma_11_4_8 (from Chap11) -/
/- Domain-style sampling for Lemma 11.4.8:
- primary domain: finite-dimensional central simple algebras over a field and the tensor product of
  their representative algebras;
- sampled owner declarations:
  `CSA`,
  `BrauerGroup`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: this item is `source-facing`, and its public owner should be the
  representative-level object `CSA.tensorProduct`; the ambient `CSA k` structure is the
  `core/canonical` owner, while the later Brauer-group multiplication is a downstream
  `bridge/view` built from this representative tensor product;
- primitive data: only the tensor-product algebra `A ⊗[k] B` together with the canonical proofs
  that it is central and simple over `k`;
- derived API: the packaged owner `CSA.tensorProduct`, which downstream files use to define
  multiplication on Brauer classes.

The raw instances on `A ⊗[k] B` are implementation details for constructing the owner object; they
should not remain part of the public API surface. -/

open scoped TensorProduct
open Algebra Algebra.TensorProduct Subalgebra

universe u v w

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : CSA.{u, w} k)

private theorem map_bot_range_eq_includeRight_range :
    (map (⊥ : Subalgebra k A).val (AlgHom.id k B)).range =
      (includeRight : B →ₐ[k] A ⊗[k] B).range := by
  rw [Algebra.TensorProduct.map_range, AlgHom.range_comp, Subalgebra.range_val,
    Algebra.map_bot, bot_sup_eq]
  simp

private instance instIsCentralTensorProduct : Algebra.IsCentral k (A ⊗[k] B) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have hxL : x ∈ centralizer k ((includeLeft : A →ₐ[k] A ⊗[k] B).range : Set (A ⊗[k] B)) := by
      intro y hy
      exact hx y
    rw [centralizer_coe_range_includeLeft_eq_center_tensorProduct,
      Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeRight_range] at hxL
    rcases hxL with ⟨b, rfl⟩
    have hb : b ∈ center k B := by
      rw [Subalgebra.mem_center_iff]
      intro b'
      apply (includeRight : B →ₐ[k] A ⊗[k] B).injective
      simpa using hx (includeRight b')
    rw [Algebra.IsCentral.mem_center_iff] at hb
    rcases hb with ⟨r, rfl⟩
    exact ⟨r, by simp⟩

private instance instIsSimpleRingTensorProduct : IsSimpleRing (A ⊗[k] B) :=
  isSimpleRing_tensorProduct_of_finite_central_left_factor

namespace CSA

/-- Lemma 11.4.8: the tensor product of finite central simple `k`-algebras over `k`, packaged as
a canonical object of `CSA k`. -/
def tensorProduct : CSA.{u, max v w} k where
  toAlgCat := AlgCat.of k (A ⊗[k] B)

end CSA

end

/-! ### Lemma_11_4_9 (from Chap11) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, w} k)
variable (k' : Type v) [Field k'] [Algebra k k']

/-
Domain-style sampling for Lemma 11.4.9:
- primary domain: scalar extension of finite-dimensional central simple algebras along field
  extensions;
- sampled owner declarations:
  `CSA`,
  `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`,
  `Algebra.IsCentral.center_eq_bot`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: the source-facing object is the base-changed algebra
  `A.baseChange k' : CSA k'`; the tensor product `k' ⊗[k] A` is the canonical carrier, while
  centrality and simplicity are derived owner data rather than a separate wrapper;
- primitive data: a central simple algebra `A : CSA k` and a field extension `k'/k`;
- derived API: the induced `k'`-centrality and simplicity instances on `k' ⊗[k] A`, packaged by
  `CSA.mk`.

Source/core/bridge triage:
- `source-facing`: scalar extension of a central simple `k`-algebra to a `k'`-algebra;
- `core/canonical`: the owner object `CSA k'` with carrier `k' ⊗[k] A`;
- `bridge/view`: the tensor-product centralizer computation identifying the center with the image of
  the left factor. -/

private theorem map_bot_range_eq_includeLeft_range :
    (Algebra.TensorProduct.map (AlgHom.id k k') (⊥ : Subalgebra k A).val).range =
      (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
  rw [Algebra.TensorProduct.map_range]
  have hbot :
      ((includeRight : A →ₐ[k] k' ⊗[k] A).comp (⊥ : Subalgebra k A).val).range =
        (⊥ : Subalgebra k (k' ⊗[k] A)) := by
    rw [AlgHom.range_comp, Subalgebra.range_val, Algebra.map_bot]
  rw [hbot, sup_bot_eq]
  simp

private instance : Algebra.IsCentral k' (k' ⊗[k] A) := by
  refine ⟨fun x hx ↦ ?_⟩
  have hx' :
      x ∈ Subalgebra.centralizer k
        (includeRight : A →ₐ[k] k' ⊗[k] A).range := by
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y _
    exact hx y
  have hx'' :
      x ∈ (Algebra.TensorProduct.map (AlgHom.id k k') (Subalgebra.center k A).val).range := by
    rwa [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct k k' A] at hx'
  have hx''' : x ∈ (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
    rw [Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeLeft_range A k'] at hx''
    exact hx''
  rcases hx''' with ⟨y, rfl⟩
  exact Subalgebra.algebraMap_mem (⊥ : Subalgebra k' (k' ⊗[k] A)) y

private instance : IsSimpleRing (k' ⊗[k] A) := by
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A k').toRingEquiv
    isSimpleRing_tensorProduct_of_finite_central_left_factor

/-- Lemma 11.4.9: scalar extension of a finite central simple `k`-algebra along a field extension,
packaged as the canonical owner object `CSA k'`. -/
noncomputable def baseChange : CSA k' :=
  CSA.mk (AlgCat.of k' (k' ⊗[k] A))

end

end CSA

/-! ### Lemma_11_4_10 (from Chap11) -/
open scoped TensorProduct

universe u v

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/- Domain-style sampling for Lemma 11.4.10:
- primary domain: Azumaya algebras and finite-dimensional central simple algebras over a field;
- sampled owner declarations:
  `CSA`,
  `AlgHom.mulLeftRight`,
  `IsAzumaya`,
  `IsAzumaya.AlgHom.mulLeftRight_bij`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: the `core/canonical` owner is the typeclass `IsAzumaya k A`; this file
  is a `source-facing` bridge from a central simple algebra `A : CSA k` to that owner;
- primitive data: only the central simple algebra `A : CSA k`;
- derived API: the `IsAzumaya k A` instance and the source-facing theorem `CSA.isAzumaya`.

Source/core/bridge triage:
- `source-facing`: every finite central simple `k`-algebra is Azumaya over `k`;
- `core/canonical`: `IsAzumaya k A`;
- `bridge/view`: bijectivity of the canonical left-right action map `AlgHom.mulLeftRight k A`. -/

private theorem mulLeftRight_bijective :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let f : (A ⊗[k] Aᵐᵒᵖ) →ₗ[k] Module.End k A := (AlgHom.mulLeftRight k A).toLinearMap
  haveI : IsSimpleRing (A ⊗[k] Aᵐᵒᵖ) := by
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  have h_inj : Function.Injective f := by
    exact RingHom.injective (AlgHom.mulLeftRight k A).toRingHom
  have h_op : Module.finrank k Aᵐᵒᵖ = Module.finrank k A := by
    simpa using
      (LinearEquiv.finrank_eq (MulOpposite.opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ)).symm
  have h_finrank :
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ) = Module.finrank k (Module.End k A) := by
    calc
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ)
          = Module.finrank k A * Module.finrank k A := by
              rw [Module.finrank_tensorProduct, h_op]
      _ = Module.finrank k (Module.End k A) := by
            symm
            simpa using (Module.finrank_linearMap k k A A)
  have h_surj : Function.Surjective (AlgHom.mulLeftRight k A) := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp h_inj
  exact ⟨h_inj, h_surj⟩

instance instIsAzumaya : IsAzumaya k A where
  bij := mulLeftRight_bijective A

-- Proof sketch: Lemma 11.4.8 makes `A ⊗[k] Aᵐᵒᵖ` simple, so the canonical left-right action map
-- `AlgHom.mulLeftRight k A` is injective; source and target have the same `k`-dimension, hence it
-- is bijective. This is the owner-level Azumaya equivalence attached to the central simple algebra
-- `A`.
/-- Lemma 11.4.10: a finite central simple `k`-algebra is Azumaya over `k`. -/
theorem isAzumaya : IsAzumaya k A := inferInstance

end CSA
