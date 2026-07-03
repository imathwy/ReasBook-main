import Mathlib
import StacksProject_2024.Chap10.Lemma_10_133_2
import StacksProject_2024.Chap10.Lemma_10_150_8

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

/- Domain triage:
* primary domain: formally étale base change for differential operators, together with the
  resulting action of the finite-order differential-operator ring on the base-changed module;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `differential_operators_order_le`,
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`;
* best owner abstraction: the canonical owner for the extension construction is the unique
  extension theorem of Lemma `10.150.8`, while the source-facing ring
  `Diff_{S/R}(M, M)` is most naturally the subring of `Module.End R M` consisting of finite-order
  differential operators;
* primitive data: an `R`-linear map together with an order bound, and in the endomorphism case the
  finite-order carrier `{ D | ∃ k, D.IsDifferentialOperatorOfOrder S k }`;
* derived API: the canonical formally étale extension, compatibility with composition, the finite
  operator ring, and its induced action on `S' ⊗[S] M`.

Source/core/bridge triage:
* `source-facing`: Remark `10.150.9`, namely compatibility of formally étale extension with
  composition and the induced action of `Diff_{S/R}(M, M)` on `S' ⊗[S] M`;
* `core/canonical`: `differential_operators_order_le` together with
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
* `bridge/view`: the finite-order endomorphism subring and the resulting ring hom to endomorphisms
  of the base-changed module. -/

private abbrev baseChangeModuleMap
    {R S S' M : Type u}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S']
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    M →ₗ[R] S' ⊗[S] M :=
  (mk S S' S' M (1 : S')).restrictScalars R

section BoundedOperators

variable {R S S' M₁ M₂ M₃ : Type u}

section ScalarCommutatorLayer

section LinearMap

variable [Semiring R]
variable [AddCommGroup M₁] [Module R M₁] [DistribSMul S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [DistribSMul S M₂] [SMulCommClass S R M₂]

namespace LinearMap

theorem isDifferentialOperatorOfOrder_succ_of_isDifferentialOperatorOfOrder
    {D : M₁ →ₗ[R] M₂} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder S (k + 1) := by
  induction k generalizing D with
  | zero =>
      rw [isDifferentialOperatorOfOrder_succ_iff D 0]
      intro g
      rw [isDifferentialOperatorOfOrder_zero_iff]
      intro g' m
      have hg : D.scalarCommutator g = 0 := hD g
      simp [hg]
  | succ k ih =>
      rw [isDifferentialOperatorOfOrder_succ_iff D (k + 1)] at ⊢
      rw [isDifferentialOperatorOfOrder_succ_iff D k] at hD
      intro g
      exact ih (hD g)

theorem isDifferentialOperatorOfOrder_mono
    {D : M₁ →ₗ[R] M₂} {k l : ℕ} (hkl : k ≤ l)
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder S l := by
  rcases Nat.exists_eq_add_of_le hkl with ⟨m, rfl⟩
  let P : ℕ → Prop := fun n ↦
    ∀ {D : M₁ →ₗ[R] M₂},
      D.IsDifferentialOperatorOfOrder S k →
      D.IsDifferentialOperatorOfOrder S (k + n)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro D hD
        simpa using hD
    | succ n hn =>
        intro D hD
        simpa [Nat.add_assoc] using
          isDifferentialOperatorOfOrder_succ_of_isDifferentialOperatorOfOrder (hn hD)
  exact hP m hD

end LinearMap

end LinearMap

section SubtypeComposition

variable [Semiring R] [CommSemiring S]
variable [AddCommGroup M₁] [Module R M₁] [DistribSMul S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [DistribSMul S M₂] [Module S M₂]
variable [SMulCommClass S R M₂] [SMulCommClass R S M₂]
variable [AddCommGroup M₃] [Module R M₃] [Module S M₃] [DistribSMul S M₃]
variable [SMulCommClass S R M₃] [SMulCommClass R S M₃]

namespace differential_operators_order_le

/-- Composition of order-bounded differential operators raises the order by addition. -/
def comp {k₁ k₂ : ℕ}
    (D₂ : {D : M₂ →ₗ[R] M₃ // D.IsDifferentialOperatorOfOrder S k₂})
    (D₁ : {D : M₁ →ₗ[R] M₂ // D.IsDifferentialOperatorOfOrder S k₁}) :
    {D : M₁ →ₗ[R] M₃ // D.IsDifferentialOperatorOfOrder S (k₁ + k₂)} :=
  ⟨(D₂ : M₂ →ₗ[R] M₃).comp (D₁ : M₁ →ₗ[R] M₂), by
    simpa using LinearMap.isDifferentialOperatorOfOrder_comp D₁.2 D₂.2⟩

omit [CommSemiring S] [Module S M₂] [SMulCommClass R S M₂] [Module S M₃]
  [SMulCommClass R S M₃] in
@[simp] theorem coe_comp {k₁ k₂ : ℕ}
    (D₂ : {D : M₂ →ₗ[R] M₃ // D.IsDifferentialOperatorOfOrder S k₂})
    (D₁ : {D : M₁ →ₗ[R] M₂ // D.IsDifferentialOperatorOfOrder S k₁}) :
    ((_root_.differential_operators_order_le.comp D₂ D₁ :
        {D : M₁ →ₗ[R] M₃ // D.IsDifferentialOperatorOfOrder S (k₁ + k₂)}) :
      M₁ →ₗ[R] M₃) =
      (D₂ : M₂ →ₗ[R] M₃).comp (D₁ : M₁ →ₗ[R] M₂) :=
  rfl

end differential_operators_order_le

end SubtypeComposition

end ScalarCommutatorLayer

section FormallyEtaleBaseChange

variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M₁] [Module S M₁] [Module R M₁] [IsScalarTower R S M₁]
variable [AddCommGroup M₂] [Module S M₂] [Module R M₂] [IsScalarTower R S M₂]
variable [AddCommGroup M₃] [Module S M₃] [Module R M₃] [IsScalarTower R S M₃]

local notation "ι₁" => (baseChangeModuleMap : M₁ →ₗ[R] S' ⊗[S] M₁)
local notation "ι₂" => (baseChangeModuleMap : M₂ →ₗ[R] S' ⊗[S] M₂)
local notation "ι₃" => (baseChangeModuleMap : M₃ →ₗ[R] S' ⊗[S] M₃)

private theorem existsUnique_formallyEtaleBaseChangeDifferentialOperator
    [Algebra.FormallyEtale S S'] {k : ℕ}
    (D : differential_operators_order_le R S M₁ k M₂) :
    ∃! D' : (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂),
      D'.comp ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂) ∧
        D'.IsDifferentialOperatorOfOrder S' k :=
  existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale D.2

variable (S') in
/-- The canonical formally étale base-change extension of an order-`k` differential operator,
owned by the unique extension theorem of Lemma `10.150.8 (2)`. -/
noncomputable def formallyEtaleBaseChangeDifferentialOperator [Algebra.FormallyEtale S S']
    {k : ℕ} (D : differential_operators_order_le R S M₁ k M₂) :
    differential_operators_order_le R S' (S' ⊗[S] M₁) k (S' ⊗[S] M₂) :=
  let h :
      ∃! D' : (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂),
        D'.comp ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂) ∧
          D'.IsDifferentialOperatorOfOrder S' k :=
    existsUnique_formallyEtaleBaseChangeDifferentialOperator D
  ⟨Classical.choose (ExistsUnique.exists h), (Classical.choose_spec (ExistsUnique.exists h)).2⟩

variable (S') in
private theorem formallyEtaleBaseChangeDifferentialOperator_spec
    [Algebra.FormallyEtale S S'] {k : ℕ}
    (D : differential_operators_order_le R S M₁ k M₂) :
    ((formallyEtaleBaseChangeDifferentialOperator S' D :
        (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).comp
        ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂)) ∧
      (formallyEtaleBaseChangeDifferentialOperator S' D :
        (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).IsDifferentialOperatorOfOrder S' k := by
  unfold formallyEtaleBaseChangeDifferentialOperator
  simpa using
    Classical.choose_spec (ExistsUnique.exists
      (existsUnique_formallyEtaleBaseChangeDifferentialOperator D))

variable (S') in
/-- Uniqueness companion for the canonical formally étale extension of a bounded differential
operator. -/
private theorem formallyEtaleBaseChangeDifferentialOperator_unique
    [Algebra.FormallyEtale S S'] {k : ℕ}
    (D : differential_operators_order_le R S M₁ k M₂)
    (D' : (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂))
    (hD' : D'.comp ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂) ∧
      D'.IsDifferentialOperatorOfOrder S' k) :
    D' = (formallyEtaleBaseChangeDifferentialOperator S' D :
      (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)) := by
  have h :
      ∃! E : (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂),
        E.comp ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂) ∧
          E.IsDifferentialOperatorOfOrder S' k :=
    existsUnique_formallyEtaleBaseChangeDifferentialOperator D
  rcases h with ⟨E, hE, huniq⟩
  have hcanon :
      ((formallyEtaleBaseChangeDifferentialOperator
            S' D :
          (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).comp
          ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂)) ∧
      (formallyEtaleBaseChangeDifferentialOperator
          S' D :
        (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).IsDifferentialOperatorOfOrder S' k :=
    formallyEtaleBaseChangeDifferentialOperator_spec S' D
  exact (huniq D' hD').trans ((huniq _ hcanon).symm)

variable (S') in
/-- The canonical extension commutes with the scalar-extension map `M₁ → S' ⊗[S] M₁`. -/
theorem formallyEtaleBaseChangeDifferentialOperator_comp_baseChangeModuleMap
    [Algebra.FormallyEtale S S'] {k : ℕ}
    (D : differential_operators_order_le R S M₁ k M₂) :
    ((formallyEtaleBaseChangeDifferentialOperator S' D :
        (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).comp
        ι₁ = (ι₂).comp (D : M₁ →ₗ[R] M₂)) := by
  exact (formallyEtaleBaseChangeDifferentialOperator_spec S' D).1

variable (S') in
/-- The canonical extension has the same order bound as the original operator. -/
theorem formallyEtaleBaseChangeDifferentialOperator_isDifferentialOperatorOfOrder
    [Algebra.FormallyEtale S S'] {k : ℕ}
    (D : differential_operators_order_le R S M₁ k M₂) :
    (formallyEtaleBaseChangeDifferentialOperator S' D :
      (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)).IsDifferentialOperatorOfOrder S' k := by
  exact (formallyEtaleBaseChangeDifferentialOperator_spec S' D).2

variable (S') in
/-- Remark 10.150.9: formally étale base change is compatible with composition of bounded
differential operators. -/
theorem formallyEtaleBaseChangeDifferentialOperator_comp [Algebra.FormallyEtale S S']
    {k₁ k₂ : ℕ}
    (D₁ : differential_operators_order_le R S M₁ k₁ M₂)
    (D₂ : differential_operators_order_le R S M₂ k₂ M₃) :
    formallyEtaleBaseChangeDifferentialOperator S'
        (_root_.differential_operators_order_le.comp D₂ D₁) =
      _root_.differential_operators_order_le.comp
        (formallyEtaleBaseChangeDifferentialOperator S' D₂)
        (formallyEtaleBaseChangeDifferentialOperator S' D₁) := by
  apply Subtype.ext
  symm
  apply formallyEtaleBaseChangeDifferentialOperator_unique S'
    (_root_.differential_operators_order_le.comp D₂ D₁)
  constructor
  · ext m
    have h₁ :
        (formallyEtaleBaseChangeDifferentialOperator S' D₁ :
            (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)) (ι₁ m) =
          ι₂ ((D₁ : M₁ →ₗ[R] M₂) m) := by
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun
        (formallyEtaleBaseChangeDifferentialOperator_comp_baseChangeModuleMap S' D₁) m
    have h₂ :
        (formallyEtaleBaseChangeDifferentialOperator S' D₂ :
            (S' ⊗[S] M₂) →ₗ[R] (S' ⊗[S] M₃))
            (ι₂ ((D₁ : M₁ →ₗ[R] M₂) m)) =
          ι₃ ((D₂ : M₂ →ₗ[R] M₃) ((D₁ : M₁ →ₗ[R] M₂) m)) := by
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun
        (formallyEtaleBaseChangeDifferentialOperator_comp_baseChangeModuleMap S' D₂)
          ((D₁ : M₁ →ₗ[R] M₂) m)
    calc
      (formallyEtaleBaseChangeDifferentialOperator S' D₂ :
          (S' ⊗[S] M₂) →ₗ[R] (S' ⊗[S] M₃))
          ((formallyEtaleBaseChangeDifferentialOperator S' D₁ :
              (S' ⊗[S] M₁) →ₗ[R] (S' ⊗[S] M₂)) (ι₁ m))
          =
        (formallyEtaleBaseChangeDifferentialOperator S' D₂ :
          (S' ⊗[S] M₂) →ₗ[R] (S' ⊗[S] M₃))
          (ι₂ ((D₁ : M₁ →ₗ[R] M₂) m)) := by rw [h₁]
      _ = ι₃ ((D₂ : M₂ →ₗ[R] M₃) ((D₁ : M₁ →ₗ[R] M₂) m)) := h₂
      _ = ((ι₃).comp ((D₂ : M₂ →ₗ[R] M₃).comp (D₁ : M₁ →ₗ[R] M₂))) m := by rfl
  · simpa using LinearMap.isDifferentialOperatorOfOrder_comp
      (formallyEtaleBaseChangeDifferentialOperator_isDifferentialOperatorOfOrder S' D₁)
      (formallyEtaleBaseChangeDifferentialOperator_isDifferentialOperatorOfOrder S' D₂)

end FormallyEtaleBaseChange

end BoundedOperators

section FiniteOrderEndomorphisms

variable {R S S' M : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

private theorem smulLinearMap_isDifferentialOperatorOfOrder_zero (s : S) :
    (DistribSMul.toLinearMap R M s : Module.End R M).IsDifferentialOperatorOfOrder S 0 := by
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro t m
  simp [smul_smul, mul_comm]

/-- The ring `Diff_{S/R}(M, M)` of finite-order `R`-linear differential operators on `M`. -/
def finiteOrderDifferentialOperators :
    Subring (Module.End R M) where
  carrier := { D | ∃ k, D.IsDifferentialOperatorOfOrder S k }
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro g m
    simp
  one_mem' := by
    refine ⟨0, ?_⟩
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro g m
    simp
  add_mem' := by
    intro D E hD hE
    rcases hD with ⟨k, hk⟩
    rcases hE with ⟨l, hl⟩
    refine ⟨max k l, ?_⟩
    have hk' : D.IsDifferentialOperatorOfOrder S (max k l) :=
      LinearMap.isDifferentialOperatorOfOrder_mono
        (show k ≤ max k l by exact le_max_left _ _) hk
    have hl' : E.IsDifferentialOperatorOfOrder S (max k l) :=
      LinearMap.isDifferentialOperatorOfOrder_mono
        (show l ≤ max k l by exact le_max_right _ _) hl
    exact (differential_operators_order_le_submodule R S M (max k l) M).add_mem hk' hl'
  neg_mem' := by
    intro D hD
    rcases hD with ⟨k, hk⟩
    exact ⟨k, (differential_operators_order_le_submodule R S M k M).neg_mem hk⟩
  mul_mem' := by
    intro D E hD hE
    rcases hD with ⟨k, hk⟩
    rcases hE with ⟨l, hl⟩
    refine ⟨l + k, ?_⟩
    simpa using LinearMap.isDifferentialOperatorOfOrder_comp hl hk

namespace DifferentialOperators

scoped notation "Diff_{" S "⁄" R "}(" M ")" =>
  @finiteOrderDifferentialOperators R S M _ _ _ _ _ _ _

end DifferentialOperators

open scoped DifferentialOperators

namespace FiniteOrderDifferentialOperators

local notation "ι" => (baseChangeModuleMap : M →ₗ[R] S' ⊗[S] M)

/-- The ring map `S → Diff_{S/R}(M, M)`, written `S → Diff_{S⁄R}(M)`, sending `s` to
multiplication by `s`. -/
def smulRingHom : S →+* Diff_{S⁄R}(M) where
  toFun s := ⟨DistribSMul.toLinearMap R M s, ⟨0, smulLinearMap_isDifferentialOperatorOfOrder_zero
    s⟩⟩
  map_zero' := by
    apply Subtype.ext
    ext m
    simp
  map_one' := by
    apply Subtype.ext
    ext m
    simp
  map_add' := by
    intro s t
    apply Subtype.ext
    ext m
    simp [add_smul]
  map_mul' := by
    intro s t
    apply Subtype.ext
    ext m
    simp [mul_smul]

private theorem existsUnique_formallyEtaleBaseChange
    [Algebra.FormallyEtale S S']
    (D : Module.End R M)
    (hD : D ∈ Diff_{S⁄R}(M)) :
    ∃! D' : Module.End R (S' ⊗[S] M),
      D'.comp ι = (ι).comp D ∧
        D' ∈ Diff_{S'⁄R}(S' ⊗[S] M) := by
  rcases hD with ⟨k, hk⟩
  let Dk : differential_operators_order_le R S M k M := ⟨D, hk⟩
  refine ⟨formallyEtaleBaseChangeDifferentialOperator S' Dk, ?_, ?_⟩
  · exact ⟨formallyEtaleBaseChangeDifferentialOperator_comp_baseChangeModuleMap
        S' Dk, ⟨k,
      formallyEtaleBaseChangeDifferentialOperator_isDifferentialOperatorOfOrder S' Dk⟩⟩
  · intro E hE
    rcases hE.2 with ⟨l, hl⟩
    let K := max k l
    have hDk : D.IsDifferentialOperatorOfOrder S K :=
      LinearMap.isDifferentialOperatorOfOrder_mono (show k ≤ K by
        exact le_max_left _ _) hk
    let DK : differential_operators_order_le R S M K M := ⟨D, hDk⟩
    have hEK : E.IsDifferentialOperatorOfOrder S' K :=
      LinearMap.isDifferentialOperatorOfOrder_mono (show l ≤ K by
        exact le_max_right _ _) hl
    have hcanonK :
        ((formallyEtaleBaseChangeDifferentialOperator
              S' Dk :
            Module.End R (S' ⊗[S] M)).comp ι = (ι).comp D) ∧
        (formallyEtaleBaseChangeDifferentialOperator
            S' Dk :
          Module.End R (S' ⊗[S] M)).IsDifferentialOperatorOfOrder S' K := by
      refine ⟨formallyEtaleBaseChangeDifferentialOperator_comp_baseChangeModuleMap
          S' Dk, ?_⟩
      exact LinearMap.isDifferentialOperatorOfOrder_mono (show k ≤ K by
          exact le_max_left _ _)
        (formallyEtaleBaseChangeDifferentialOperator_isDifferentialOperatorOfOrder
          S' Dk)
    have hEeq :
        E = formallyEtaleBaseChangeDifferentialOperator S' DK :=
      formallyEtaleBaseChangeDifferentialOperator_unique
        S' DK E ⟨hE.1, hEK⟩
    have hcanonEq :
        (formallyEtaleBaseChangeDifferentialOperator
            S' Dk :
          Module.End R (S' ⊗[S] M)) =
        formallyEtaleBaseChangeDifferentialOperator S' DK :=
      formallyEtaleBaseChangeDifferentialOperator_unique
        S' DK (formallyEtaleBaseChangeDifferentialOperator S' Dk) hcanonK
    exact hEeq.trans hcanonEq.symm

private noncomputable def baseChanged [Algebra.FormallyEtale S S']
    (D : Diff_{S⁄R}(M)) :
    Diff_{S'⁄R}(S' ⊗[S] M) := by
  let h : ∃! D' : Module.End R (S' ⊗[S] M),
      D'.comp ι = (ι).comp (D : Module.End R M) ∧
        D' ∈ Diff_{S'⁄R}(S' ⊗[S] M) :=
    existsUnique_formallyEtaleBaseChange (D : Module.End R M) D.2
  exact ⟨Classical.choose (ExistsUnique.exists h), (Classical.choose_spec
    (ExistsUnique.exists h)).2⟩

private abbrev baseChangedEnd [Algebra.FormallyEtale S S']
    (D : Diff_{S⁄R}(M)) :
    Module.End R (S' ⊗[S] M) :=
  (baseChanged D : Diff_{S'⁄R}(S' ⊗[S] M))

private theorem baseChanged_spec [Algebra.FormallyEtale S S']
    (D : Diff_{S⁄R}(M)) :
    (baseChangedEnd D).comp ι = (ι).comp (D : Module.End R M) ∧
      baseChangedEnd D ∈ Diff_{S'⁄R}(S' ⊗[S] M) := by
  unfold baseChangedEnd baseChanged
  simpa using Classical.choose_spec
    (ExistsUnique.exists
      (existsUnique_formallyEtaleBaseChange (D : Module.End R M) D.2))

private theorem baseChanged_unique [Algebra.FormallyEtale S S']
    (D : Diff_{S⁄R}(M))
    (E : Module.End R (S' ⊗[S] M))
    (hE : E.comp ι = (ι).comp (D : Module.End R M) ∧
        E ∈ Diff_{S'⁄R}(S' ⊗[S] M)) :
    E = baseChangedEnd D := by
  have h :
      ∃! F : Module.End R (S' ⊗[S] M),
        F.comp ι = (ι).comp (D : Module.End R M) ∧
          F ∈ Diff_{S'⁄R}(S' ⊗[S] M) :=
    existsUnique_formallyEtaleBaseChange (D : Module.End R M) D.2
  rcases h with ⟨F, hF, huniq⟩
  exact (huniq E hE).trans ((huniq _ (baseChanged_spec D)).symm)

variable (S') in
/-- The canonical formally étale base-change ring hom on finite-order differential operators. -/
noncomputable def formallyEtaleBaseChange [Algebra.FormallyEtale S S'] :
    Diff_{S⁄R}(M) →+* Diff_{S'⁄R}(S' ⊗[S] M) where
  toFun D := baseChanged D
  map_zero' := by
    sorry
  map_one' := by
    sorry
  map_add' := by
    sorry
  map_mul' := by
    sorry

variable (S') in
/-- The finite-order base-change map still satisfies the defining extension square. -/
theorem formallyEtaleBaseChange_comp_baseChangeModuleMap
    [Algebra.FormallyEtale S S']
    (D : Diff_{S⁄R}(M)) :
    ((formallyEtaleBaseChange S' D : Module.End R (S' ⊗[S] M)).comp ι =
          (ι).comp (D : Module.End R M)) := by
  exact (baseChanged_spec D).1

variable (S') in
/-- Under formally étale base change, multiplication by `s : S` becomes multiplication by its
image in `S'`. -/
theorem formallyEtaleBaseChange_smulRingHom
    [Algebra.FormallyEtale S S']
    (s : S) :
    ((((formallyEtaleBaseChange S' (smulRingHom s) :
          Diff_{S'⁄R}(S' ⊗[S] M))) :
        Module.End R (S' ⊗[S] M)) =
      DistribSMul.toLinearMap R (S' ⊗[S] M) (algebraMap S S' s)) := by
  sorry

private noncomputable def toBaseChangeEnd [Algebra.FormallyEtale S S'] :
    Diff_{S⁄R}(M) →+*
      Module.End R (S' ⊗[S] M) :=
  (Diff_{S'⁄R}(S' ⊗[S] M)).subtype.comp (formallyEtaleBaseChange S')

variable (S') in
/-- Remark 10.150.9: `S' ⊗[S] M` carries the natural left action of the finite-order differential
operator ring `Diff_{S/R}(M, M)`, written `Diff_{S⁄R}(M)`. -/
noncomputable instance module [Algebra.FormallyEtale S S'] :
    Module (Diff_{S⁄R}(M)) (S' ⊗[S] M) :=
  Module.compHom (S' ⊗[S] M)
    (show Diff_{S⁄R}(M) →+* Module.End R (S' ⊗[S] M) from toBaseChangeEnd)

variable (S') in
/-- The induced action restricts along `S → Diff_{S/R}(M, M)` to the usual `S`-action on
`S' ⊗[S] M`; on the theorem surface this ring is written `Diff_{S⁄R}(M)`. -/
theorem smulRingHom_smul [Algebra.FormallyEtale S S']
    (s : S) (x : S' ⊗[S] M) :
    (smulRingHom s : Diff_{S⁄R}(M)) • x =
        (algebraMap S S' s) • x := by
  change (((((formallyEtaleBaseChange S' (smulRingHom s) :
        Diff_{S'⁄R}(S' ⊗[S] M))) :
      Module.End R (S' ⊗[S] M)) x) = _)
  rw [formallyEtaleBaseChange_smulRingHom S']
  rfl

end FiniteOrderDifferentialOperators

end FiniteOrderEndomorphisms
