import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
variable {A : Type w}

local notation "𝔪" => maximalIdeal R
local notation "k" => IsLocalRing.ResidueField R
local notation "M̄" => M ⧸ (𝔪 • (⊤ : Submodule R M))
local notation "mkQ𝔪" => Submodule.mkQ (𝔪 • (⊤ : Submodule R M))

local instance : Module k M̄ := inferInstanceAs (Module (R ⧸ 𝔪) M̄)
local instance : SMulCommClass R k M̄ := inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) M̄)
local instance : IsScalarTower R k M̄ := inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) M̄)
local instance : Module k (M →ₗ[R] M̄) := inferInstanceAs (Module (R ⧸ 𝔪) (M →ₗ[R] M̄))
local instance : SMulCommClass R k (M →ₗ[R] M̄) :=
  inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) (M →ₗ[R] M̄))
local instance : IsScalarTower R k (M →ₗ[R] M̄) :=
  inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M →ₗ[R] M̄))

-- Proof sketch: the forward implication is immediate by mapping a basis along the quotient map.
-- For the converse, Nakayama's lemma shows that lifts of a residue-field basis generate `M`.
-- Presenting `M` as a quotient of the free module on `A`, flatness keeps the kernel exact after
-- reduction modulo `maximalIdeal R`, and the quotient basis forces that kernel to vanish modulo the
-- maximal ideal. A second application of Nakayama to the kernel, using nilpotence of
-- `maximalIdeal R`, shows the generators are linearly independent.
/-
Layering for this item:
- `source-facing`: the family `x : A → M` and its reduction modulo `𝔪`;
- `core/canonical`: `Module.Basis`, `Algebra.TensorProduct.basis`,
  `IsLocalRing.linearIndependent_of_flat`, and the nilpotent Nakayama span criterion;
- `bridge/view`: the canonical comparison `((R ⧸ 𝔪) ⊗[R] M) ≃ₗ[R ⧸ 𝔪] M̄`.
-/
/-- Lemma 10.101.1: for a flat module over a local ring with nilpotent maximal ideal, a family
`x : A → M` is an `R`-basis exactly when its images in `M / maximalIdeal R • M` form a basis over
`R / maximalIdeal R`. -/
theorem basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent 𝔪)
    (x : A → M) :
    (∃ bbar : Module.Basis A k M̄, ∀ a, bbar a = mkQ𝔪 (x a)) ↔
      ∃ b : Module.Basis A R M, ∀ a, b a = x a := by
  classical
  let f : k →ₗ[k] M →ₗ[R] M̄ :=
    (LinearMap.ringLmapEquivSelf k k (M →ₗ[R] M̄)).symm mkQ𝔪
  let e₀ : (k ⊗[R] M) →ₗ[k] M̄ :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) : e₀ ((1 : k) ⊗ₜ[R] y) = mkQ𝔪 y := by
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M 𝔪).toLinearMap := by
    apply TensorProduct.ext'
    intro r y
    refine Quotient.inductionOn r ?_
    intro a
    change e₀ (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M 𝔪 (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul k a (Submodule.Quotient.mk y))
  let e : (k ⊗[R] M) ≃ₗ[k] M̄ :=
    LinearEquiv.ofBijective e₀
      ⟨by
        intro u v huv
        have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
        rw [e₀_restrictScalars] at huv'
        exact (TensorProduct.quotTensorEquivQuotSMul M 𝔪).injective huv'
      , by
        intro z
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) z
        exact ⟨(1 : k) ⊗ₜ[R] y, e₀_apply y⟩⟩
  have e_apply (y : M) : e ((1 : k) ⊗ₜ[R] y) = mkQ𝔪 y := e₀_apply y
  constructor
  · rintro ⟨bbar, hbbar⟩
    have hmkQx : mkQ𝔪 ∘ x = bbar := by
      funext a
      exact (hbbar a).symm
    have hx_tensor_li :
        LinearIndependent k (TensorProduct.mk R k M 1 ∘ x) := by
      refine ((e.toLinearMap).linearIndependent_iff (by simp)).mp ?_
      have hcomp : e ∘ TensorProduct.mk R k M 1 ∘ x = bbar := by
        funext a
        simpa [hbbar a] using e_apply (x a)
      simpa [hcomp] using bbar.linearIndependent
    have hx_li : LinearIndependent R x :=
      Module.IsLocalRing.linearIndependent_of_flat _ hx_tensor_li
    have hgen : Submodule.span R (mkQ𝔪 '' Set.range x) = ⊤ := by
      rw [← Set.range_comp, hmkQx, ← Submodule.restrictScalars_span R (R ⧸ 𝔪)
        Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff]
      exact bbar.span_eq
    have hx_span_eq :
        Submodule.span R (Set.range x) = ⊤ :=
      span_eq_top_of_quotient_span_eq_top_of_isNilpotent 𝔪 (Set.range x) hgen h_nil
    have hbij : Function.Bijective (Finsupp.linearCombination R x) := by
      refine ⟨hx_li, ?_⟩
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact hx_span_eq
    refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination R x) hbij).symm,
      ?_⟩
    intro a
    simp
  · rintro ⟨b, hb⟩
    let btensor : Module.Basis A (R ⧸ 𝔪) ((R ⧸ 𝔪) ⊗[R] M) :=
      Algebra.TensorProduct.basis (R ⧸ 𝔪) b
    refine ⟨btensor.map e, ?_⟩
    intro a
    change e (btensor a) = mkQ𝔪 (x a)
    simpa [btensor, hb a] using e_apply (x a)

end
