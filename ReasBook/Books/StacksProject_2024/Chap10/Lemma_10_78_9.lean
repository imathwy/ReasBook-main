import stacks_project.Chap10.Lemma_10_78_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped TensorProduct
open TensorProduct LinearMap

section

variable {R : Type u} [CommRing R]
variable {L : Type v} [AddCommGroup L] [Module R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module R N]

/- Domain triage:
- primary domain: tensor-Hom comparison maps for modules over a commutative ring;
- sampled owner-style declarations of the same kind:
  `TensorProduct.rTensorHomToHomRTensor`,
  `TensorProduct.rTensorHomEquivHomRTensor`,
  `Module.Projective`,
  `module_finite_projective_tfae`;
- owner abstraction: the canonical comparison map `rTensorHomToHomRTensor`, together with the
  finite-free owner equivalence `rTensorHomEquivHomRTensor`;
- primitive data: the ring `R`, the modules `L`, `M`, `N`;
- derived API: bijectivity of the canonical comparison map when `M` is finite projective.

This item is a `bridge/view` theorem. Its source-facing content is the finite-projective extension
of the finite-free owner equivalence from mathlib, and the chapter-level owner theorem
`module_finite_projective_tfae` supplies the canonical finite-free splitting used in the descent.
-/

private theorem rTensorHomToHomRTensor_lcomp
    {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
    {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] (u : M₁ →ₗ[R] M₂) :
    rTensorHomToHomRTensor (.id R) M₁ N L ∘ₗ (lcomp R N u).rTensor L =
      lcomp R (N ⊗[R] L) u ∘ₗ rTensorHomToHomRTensor (.id R) M₂ N L := by
  ext f l m
  simp [LinearMap.comp_apply]

/-- Lemma 10.78.9: if `M` is a finite projective `R`-module, then the canonical map
`Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)` is bijective. This is the source-facing finite-projective
extension of mathlib's finite-free owner equivalence `rTensorHomEquivHomRTensor`, stated directly
for the canonical comparison map `rTensorHomToHomRTensor`. -/
theorem rTensorHomToHomRTensor_bijective_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (rTensorHomToHomRTensor (.id R) M N L) := by
  have h23 :
      (Module.Finite R M ∧ Module.Projective R M) ↔
        ∃ (ι : Type (max u w)) (_ : Finite ι) (i : M →ₗ[R] (ι → R)) (s : (ι → R) →ₗ[R] M),
          s.comp i = LinearMap.id :=
    module_finite_projective_tfae.out 1 2
  rcases h23.mp ⟨inferInstance, inferInstance⟩ with ⟨ι, _instFinite, i, s, hs⟩
  let eF := rTensorHomEquivHomRTensor R (ι → R) N L
  let φM : (M →ₗ[R] N) ⊗[R] L →ₗ[R] M →ₗ[R] N ⊗[R] L :=
    rTensorHomToHomRTensor (.id R) M N L
  let ψM : (M →ₗ[R] N ⊗[R] L) →ₗ[R] (M →ₗ[R] N) ⊗[R] L :=
    (lcomp R N i).rTensor L ∘ₗ eF.symm.toLinearMap ∘ₗ lcomp R (N ⊗[R] L) s
  have eF_apply (x : ((ι → R) →ₗ[R] N) ⊗[R] L) :
      eF x = rTensorHomToHomRTensor (.id R) (ι → R) N L x := by
    change rTensorHomEquivHomRTensor R (ι → R) N L x =
      rTensorHomToHomRTensor (.id R) (ι → R) N L x
    exact rTensorHomEquivHomRTensor_apply x
  have hleft : ψM.comp φM = LinearMap.id := by
    ext f l
    dsimp [ψM, φM, eF]
    have hs_nat :
        rTensorHomToHomRTensor (.id R) (ι → R) N L ∘ₗ (lcomp R N s).rTensor L =
          lcomp R (N ⊗[R] L) s ∘ₗ rTensorHomToHomRTensor (.id R) M N L :=
      rTensorHomToHomRTensor_lcomp s
    have hs' :
        (lcomp R (N ⊗[R] L) s) ((rTensorHomToHomRTensor (.id R) M N L) (f ⊗ₜ[R] l)) =
          eF ((lcomp R N s).rTensor L (f ⊗ₜ[R] l)) := by
      simpa [eF, LinearMap.comp_apply] using
        congrArg
          (fun T ↦ T (f ⊗ₜ[R] l))
          hs_nat
    have hsi : (lcomp R N i) ((lcomp R N s) f) = f := by
      ext m
      simpa [LinearMap.lcomp_apply] using congrArg f (congrArg (fun g ↦ g m) hs)
    rw [hs', LinearEquiv.symm_apply_apply]
    simp [LinearMap.rTensor_tmul, hsi]
  have hright : φM.comp ψM = LinearMap.id := by
    ext h m
    dsimp [ψM, φM, eF]
    have hi_nat_map :
        rTensorHomToHomRTensor (.id R) M N L ∘ₗ (lcomp R N i).rTensor L =
          lcomp R (N ⊗[R] L) i ∘ₗ rTensorHomToHomRTensor (.id R) (ι → R) N L :=
      rTensorHomToHomRTensor_lcomp i
    have hi_nat :
        (rTensorHomToHomRTensor (.id R) M N L)
            ((lcomp R N i).rTensor L (eF.symm ((lcomp R (N ⊗[R] L) s) h))) =
          (lcomp R (N ⊗[R] L) i)
            ((rTensorHomToHomRTensor (.id R) (ι → R) N L)
              (eF.symm ((lcomp R (N ⊗[R] L) s) h))) := by
      simpa [LinearMap.comp_apply] using
        congrArg
          (fun T ↦ T (eF.symm ((lcomp R (N ⊗[R] L) s) h)))
          hi_nat_map
    rw [hi_nat, ← eF_apply,
      LinearEquiv.apply_symm_apply]
    simpa [LinearMap.lcomp_apply] using congrArg h (congrArg (fun g ↦ g m) hs)
  have hleft_fun : Function.LeftInverse ψM φM := fun x ↦ by
    simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T x) hleft
  have hright_fun : Function.RightInverse ψM φM := fun x ↦ by
    simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T x) hright
  change Function.Bijective φM
  exact ⟨hleft_fun.injective, hright_fun.surjective⟩

end
