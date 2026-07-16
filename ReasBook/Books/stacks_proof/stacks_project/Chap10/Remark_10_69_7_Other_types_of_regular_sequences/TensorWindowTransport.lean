import stacks_proof.stacks_project.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.FinConsExteriorSplit

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degree `0`, every
tensorized Koszul complex canonically identifies with the coefficient module. -/
noncomputable def koszul_tensor_degree_zero_iso {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ} (f : Fin m → A) :
    ((HomologicalComplex.tensorObj (koszulComplexOn f)
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) ≅
      ModuleCat.of A M := by
  -- Proof comment: first collapse the tensor degree `0` term to termwise tensoring with `M`,
  -- then identify the zeroth exterior power with the tensor unit and finish with the left unitor.
  exact
    (tensor_single₀_X_iso_tensorRight (K := koszulComplexOn f) (M := M) 0) ≪≫
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin m → A)))) ≪≫
      (λ_ (ModuleCat.of A M))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): adjoining a head element does
not change the degree-`0` term of the tensorized Koszul complex. -/
noncomputable def fin_cons_tensor_degree_zero_iso_tail {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ} {r : A}
    (g : Fin (m + 1) → A) :
    ((HomologicalComplex.tensorObj (koszulComplexOn (Fin.cons r g))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) ≅
      ((HomologicalComplex.tensorObj (koszulComplexOn g)
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) := by
  -- Proof comment: both degree-`0` tensor terms identify with the same coefficient module `M`.
  exact
    (koszul_tensor_degree_zero_iso (M := M) (f := Fin.cons r g)) ≪≫
      (koszul_tensor_degree_zero_iso (M := M) (f := g)).symm

/-- Helper for Remark 10.69.7 (Other types of regular sequences): function exactness is invariant
under a commutative ladder of linear equivalences. -/
theorem functionExact_iff_of_ladder_linearEquiv {A : Type u} [CommRing A]
    {M₁ : Type u} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type u} [AddCommGroup M₂] [Module A M₂]
    {M₃ : Type u} [AddCommGroup M₃] [Module A M₃]
    {N₁ : Type u} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module A N₂]
    {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    {f₁₂ : M₁ →ₗ[A] M₂} {f₂₃ : M₂ →ₗ[A] M₃}
    {g₁₂ : N₁ →ₗ[A] N₂} {g₂₃ : N₂ →ₗ[A] N₃}
    {e₁ : M₁ ≃ₗ[A] N₁} {e₂ : M₂ ≃ₗ[A] N₂} {e₃ : M₃ ≃ₗ[A] N₃}
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Function.Exact g₁₂ g₂₃ ↔ Function.Exact f₁₂ f₂₃ := by
  -- Proof comment: this is exactly the linear-equivalence ladder criterion from the exactness
  -- API, restated with the `Function.Exact` notation used in this file.
  simpa using
    (Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) h₁₂ h₂₃)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): exactness on the source ladder
transports to exactness on the target ladder. -/
theorem functionExact_of_ladder_linearEquiv {A : Type u} [CommRing A]
    {M₁ : Type u} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type u} [AddCommGroup M₂] [Module A M₂]
    {M₃ : Type u} [AddCommGroup M₃] [Module A M₃]
    {N₁ : Type u} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module A N₂]
    {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    {f₁₂ : M₁ →ₗ[A] M₂} {f₂₃ : M₂ →ₗ[A] M₃}
    {g₁₂ : N₁ →ₗ[A] N₂} {g₂₃ : N₂ →ₗ[A] N₃}
    {e₁ : M₁ ≃ₗ[A] N₁} {e₂ : M₂ ≃ₗ[A] N₂} {e₃ : M₃ ≃ₗ[A] N₃}
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (h : Function.Exact f₁₂ f₂₃) :
    Function.Exact g₁₂ g₂₃ := by
  -- Proof comment: apply the preceding equivalence in the direction from the source exactness to
  -- the target exactness.
  exact (functionExact_iff_of_ladder_linearEquiv (A := A) h₁₂ h₂₃).2 h


end RingTheory.Sequence
