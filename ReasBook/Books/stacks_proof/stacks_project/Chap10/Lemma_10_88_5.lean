import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_4
import StacksProject_2024.Chap10.Lemma_10_88_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
variable {M' : Type u} [AddCommGroup M'] [Module R M']

-- Proof sketch: combine Lemma `10.88.4`, which identifies domination with universal injectivity of
-- the pushout map, with Lemma `10.82.4`, which turns universal injectivity into splitting when the
-- cokernel is finitely presented. The pushout map splits exactly when the universal property of the
-- pushout yields a map `h : N →ₗ[R] M'` satisfying `g = h.comp f`.
/-- Lemma 10.88.5: if the cokernel `N ⧸ LinearMap.range f` is finitely presented, then `g`
dominates `f` if and only if `g` factors through `f`. -/
@[stacks 059D]
theorem dominates_iff_factorsThrough_of_finitePresentation_cokernel
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') [Module.FinitePresentation R (N ⧸ LinearMap.range f)] :
    g.Dominates f ↔ ∃ h : N →ₗ[R] M', g = h.comp f := by
  constructor
  · intro hdom
    let f₀ :
        (ModuleCat.of R M : ModuleCat R) ⟶
          (ModuleCat.of R N : ModuleCat R) :=
      ModuleCat.ofHom f
    let g₀ :
        (ModuleCat.of R M : ModuleCat R) ⟶
          (ModuleCat.of R M' : ModuleCat R) :=
      ModuleCat.ofHom g
    let P := pushout f₀ g₀
    let i : (ModuleCat.of R M' : ModuleCat R) ⟶ P :=
      show (ModuleCat.of R M' : ModuleCat R) ⟶ pushout f₀ g₀ from
        pushout.inr f₀ g₀
    let j : (ModuleCat.of R N : ModuleCat R) ⟶ P :=
      show (ModuleCat.of R N : ModuleCat R) ⟶ pushout f₀ g₀ from
        pushout.inl f₀ g₀
    let q : N →ₗ[R] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ
    let π : P ⟶ (ModuleCat.of R (N ⧸ LinearMap.range f) : ModuleCat R) :=
      pushout.desc (ModuleCat.ofHom q) 0 (by
        apply ModuleCat.hom_ext
        ext x
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).2 ⟨x, rfl⟩)
    have hiπ : i ≫ π = 0 := by
      change pushout.inr f₀ g₀ ≫ pushout.desc (ModuleCat.ofHom q) 0 _ = 0
      rw [pushout.inr_desc]
    have hjπ : j ≫ π = ModuleCat.ofHom q := by
      change pushout.inl f₀ g₀ ≫ pushout.desc (ModuleCat.ofHom q) 0 _ = ModuleCat.ofHom q
      rw [pushout.inl_desc]
    have hπ : IsColimit (CokernelCofork.ofπ π hiπ) :=
      CokernelCofork.IsColimit.ofπ π hiπ
        (fun {Z} k hk ↦ by
          have hfk : f₀ ≫ j ≫ k = 0 := by
            rw [pushout.condition_assoc]
            simpa [Category.assoc] using congrArg (fun t ↦ g₀ ≫ t) hk
          exact (ModuleCat.cokernelIsColimit f₀).desc <| CokernelCofork.ofπ (j ≫ k) hfk)
        (fun {Z} k hk ↦ by
          have hfk : f₀ ≫ j ≫ k = 0 := by
            rw [pushout.condition_assoc]
            simpa [Category.assoc] using congrArg (fun t ↦ g₀ ≫ t) hk
          apply pushout.hom_ext
          · calc
              j ≫ π ≫ (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk)
                  = (j ≫ π) ≫ (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) := by
                      simp [Category.assoc]
              _ = ModuleCat.ofHom q ≫ (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) := by
                    rw [hjπ]
              _ = j ≫ k := (ModuleCat.cokernelIsColimit f₀).fac (CokernelCofork.ofπ (j ≫ k) hfk)
                    WalkingParallelPair.one
          · have hzero :
                i ≫ π ≫ (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) = 0 := by
              change (i ≫ π) ≫ (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) = 0
              rw [hiπ]
              have hzero' :
                  (0 : ModuleCat.of R M' ⟶ ModuleCat.of R (N ⧸ LinearMap.range f)) ≫
                      (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) =
                    (0 : ModuleCat.of R M' ⟶ Z) := by
                simp
              exact hzero'
            exact hzero.trans hk.symm)
        (fun {Z} k hk m hm ↦ by
          have hfk : f₀ ≫ j ≫ k = 0 := by
            rw [pushout.condition_assoc]
            simpa [Category.assoc] using congrArg (fun t ↦ g₀ ≫ t) hk
          have hfac :=
            (ModuleCat.cokernelIsColimit f₀).fac (CokernelCofork.ofπ (j ≫ k) hfk)
              WalkingParallelPair.one
          have hq_epi : Epi (ModuleCat.ofHom q) := Cofork.IsColimit.epi (ModuleCat.cokernelIsColimit f₀)
          apply (cancel_epi (ModuleCat.ofHom q)).1
          calc
            ModuleCat.ofHom q ≫ m = j ≫ π ≫ m := by
              calc
                ModuleCat.ofHom q ≫ m = (j ≫ π) ≫ m := by rw [hjπ]
                _ = j ≫ π ≫ m := by simp [Category.assoc]
            _ = j ≫ k := by simpa [Category.assoc] using congrArg (fun t ↦ j ≫ t) hm
            _ = ModuleCat.ofHom q ≫
                  (ModuleCat.cokernelIsColimit f₀).desc (CokernelCofork.ofπ (j ≫ k) hfk) := by
                exact hfac.symm)
    let S : ShortComplex (ModuleCat R) := ShortComplex.mk i π hiπ
    have hi_universallyInjective : i.hom.UniversallyInjective := by
      simpa [i] using (dominates_iff_universallyInjective_pushout_inr f g).1 hdom
    have hi_injective : Function.Injective i.hom := by
      intro x y hxy
      have hrtensor : Function.Injective (i.hom.rTensor R) :=
        hi_universallyInjective R inferInstance inferInstance
      have hxy' :
          i.hom.rTensor R ((TensorProduct.rid R M').symm x) =
            i.hom.rTensor R ((TensorProduct.rid R M').symm y) := by
        apply (TensorProduct.rid R P).injective
        simp [TensorProduct.rid_symm_apply, LinearMap.rTensor_tmul, hxy]
      exact (TensorProduct.rid R M').symm.injective <| hrtensor hxy'
    have hπ_surjective : Function.Surjective π.hom := by
      have hπ_epi : Epi π := Cofork.IsColimit.epi hπ
      exact (ModuleCat.epi_iff_surjective _).mp hπ_epi
    have hS_exact : S.Exact := S.exact_of_g_is_cokernel hπ
    have hS_shortExact : S.ShortExact :=
      ModuleCat.shortComplex_shortExact S
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS_exact)
        hi_injective hπ_surjective
    have hS_universallyExact : S.UniversallyExact := ⟨hS_shortExact, hi_universallyInjective⟩
    obtain ⟨s⟩ :=
      CategoryTheory.ShortComplex.universallyExact_iff_split_of_finitePresentation_X₃.1
        hS_universallyExact
    let h : N →ₗ[R] M' :=
      (j ≫ s.r).hom
    refine ⟨h, ?_⟩
    simpa [g₀] using ModuleCat.hom_ext_iff.mp <| by
      calc
        g₀ = g₀ ≫ 𝟙 _ := by simp
        _ = g₀ ≫ (i ≫ s.r) := by rw [s.f_r]
        _ = g₀ ≫ i ≫ s.r := by simp
        _ = f₀ ≫ j ≫ s.r := by
          simp [i, j, ← pushout.condition_assoc]
        _ = ModuleCat.ofHom (h.comp f) := by
          rw [ModuleCat.ofHom_comp]
          simp [f₀, h]
  · rintro ⟨h, rfl⟩
    intro Q _ _
    show LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker ((h.comp f).rTensor Q)
    simpa [LinearMap.rTensor_comp] using LinearMap.ker_le_ker_comp (f.rTensor Q) (h.rTensor Q)

end

end LinearMap
