import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TensorProduct
open AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private theorem lTensor_assoc_naturality
    {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') :
    lTensor S S' (lTensor S M f) ∘ₗ (assoc R S S' S' M N).restrictScalars S =
      (assoc R S S' S' M N').restrictScalars S ∘ₗ lTensor S (S' ⊗[S] M) f := by
  ext s m n
  rfl

-- Proof sketch: for any injective `R`-linear map `N → N'`, first tensor with `M` over `R`, then
-- identify tensoring with `S' ⊗[S] M` over `R` with tensoring the resulting map with `S'` over
-- `S`; flatness of `S → S'` preserves injectivity.
/-- Lemma 10.39.9 (1), in canonical module form: if `S'` is flat over `S` and `M` is flat over
`R`, then `S' ⊗[S] M` is flat over `R`. -/
@[stacks 0584]
theorem flat_baseChange_of_flat [Module.Flat S S'] [Module.Flat R M] :
    Module.Flat R (S' ⊗[S] M) := by
  rw [Module.Flat.iff_lTensor_exact]
  intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
  have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact M h
  have hS' : Function.Exact (lTensor S S' (lTensor S M l₁₂)) (lTensor S S' (lTensor S M l₂₃)) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact S' hM
  have hBase :
      Function.Exact (lTensor S (S' ⊗[S] M) l₁₂) (lTensor S (S' ⊗[S] M) l₂₃) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (lTensor_assoc_naturality l₁₂)
      (lTensor_assoc_naturality l₂₃)).1 hS'
  simpa [coe_lTensor] using hBase

-- Proof sketch: the forward implication is `flat_baseChange_of_flat`; for the converse, test
-- `R`-flatness on injective maps, tensor the resulting kernel criterion with `S'` over `S`, and
-- use faithful flatness of `S → S'` to reflect injectivity back to the original map.
/-- Lemma 10.39.9 (2), in canonical module form: if `S'` is faithfully flat over `S`, then an
`S`-module `M` is flat over `R` if and only if its base change `S' ⊗[S] M` is flat over `R`. -/
@[stacks 0584]
theorem flat_iff_flat_baseChange_of_faithfullyFlat
    [Module.FaithfullyFlat S S'] :
    Module.Flat R M ↔ Module.Flat R (S' ⊗[S] M) := by
  constructor
  · intro
    exact flat_baseChange_of_flat
  · intro hBaseChange
    rw [Module.Flat.iff_lTensor_exact]
    intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
    have hS' : Function.Exact (lTensor S (S' ⊗[S] M) l₁₂) (lTensor S (S' ⊗[S] M) l₂₃) := by
      simpa [coe_lTensor] using Module.Flat.lTensor_exact (S' ⊗[S] M) h
    have hBase : Function.Exact (lTensor S S' (lTensor S M l₁₂)) (lTensor S S' (lTensor S M l₂₃)) :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (lTensor_assoc_naturality l₁₂)
        (lTensor_assoc_naturality l₂₃)
        hS'
    have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) :=
      Module.FaithfullyFlat.lTensor_reflects_exact S S' (lTensor S M l₁₂) (lTensor S M l₂₃)
        hBase
    simpa [coe_lTensor] using hM

end
