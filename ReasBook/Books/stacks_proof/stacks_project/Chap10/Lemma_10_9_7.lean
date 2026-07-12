import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

open IsLocalizedModule LinearMap LocalizedModule

variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Lemma 10.9.7: if every element of `S` acts invertibly on `N`, then precomposition with the
canonical localization map `mkLinearMap S M : M →ₗ[R] LocalizedModule S M` is a linear
equivalence `Hom_R(LocalizedModule S M, N) ≃ Hom_R(M, N)`. This is the Hom-form of the owner
universal property `IsLocalizedModule.is_universal` for `mkLinearMap S M`. -/
@[stacks 07K0]
noncomputable def localizedModuleHomLinearEquiv
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)) :
    (LocalizedModule S M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  LinearEquiv.ofBijective
    (lcomp R N (mkLinearMap S M))
    ⟨fun f _ hfg ↦
      (is_universal S (mkLinearMap S M) (f.comp (mkLinearMap S M)) hS).unique rfl hfg.symm,
      fun g ↦ (is_universal S (mkLinearMap S M) g hS).exists⟩

/-- Applying the Hom localization equivalence is precomposition with the canonical localization
map. -/
-- Proof sketch: unfold `localizedModuleHomLinearEquiv`; its underlying map is
-- `LinearMap.lcomp R N (mkLinearMap S M)`, whose value is composition with `mkLinearMap S M`.
theorem localizedModuleHomLinearEquiv_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (f : LocalizedModule S M →ₗ[R] N) :
    localizedModuleHomLinearEquiv S hS f = f.comp (mkLinearMap S M) := by
  -- Unfold the equivalence: its forward map is `LinearMap.lcomp`, so evaluation is composition.
  rfl

end
