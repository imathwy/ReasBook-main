import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The map on quotients modulo `I` induced by an `R`-linear map. -/
abbrev quotientMapByIdeal (f : M →ₗ[R] M') (I : Ideal R) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top I f)

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

private theorem quotientMapByIdeal_lTensor_naturality {I : Ideal R} (f : M →ₗ[R] M') :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul M I =
      TensorProduct.quotTensorEquivQuotSMul M' I ∘ₗ f.lTensor (R ⧸ I) := by
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

private theorem injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- A universally injective linear map stays injective after reduction modulo any ideal. -/
theorem injective_quotientMapByIdeal_of_universallyInjective (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, u} f) (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := sorry

-- Proof sketch: use Theorem 10.82.3 to reduce universal injectivity to injectivity after
-- tensoring with every finite module, choose a finite filtration with cyclic subquotients `R / I`
-- from Lemma 10.5.4, use flatness of `M'` to keep the induced filtration exact on the target
-- side, and then conclude from injectivity on each finitely generated ideal quotient together with
-- exactness of filtered colimits as in Lemma 10.8.8.
/-- Lemma 10.82.13: if `M'` is a flat `R`-module, then an `R`-linear map `M → M'` is universally
injective if and only if the induced map `M / I M → M' / I M'` is injective for every finitely
generated ideal `I` of `R`. -/
theorem universallyInjective_iff_injective_mod_finite_ideal [Module.Flat R M']
    (f : M →ₗ[R] M') :
    UniversallyInjective f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := sorry

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

-- Proof sketch: apply `universallyInjective_iff_injective_mod_finite_ideal`. For a finitely
-- generated ideal `J`, pass to the quotient local ring `A / J`; the induced map on
-- `M / J M → N / J N` has injective reduction modulo its maximal ideal by the hypothesis on
-- `u`, and flatness descends to the quotient modules, so the local criterion over `A / J`
-- upgrades that closed-fiber injectivity to injectivity modulo `J`.
/-- Over a local ring, a linear map between flat modules is universally injective as soon as its
reduction modulo the maximal ideal is injective. -/
theorem universallyInjective_of_injective_mod_maximalIdeal (u : M →ₗ[A] N)
    (hu : Function.Injective (u.quotientMapByIdeal (maximalIdeal A))) :
    UniversallyInjective.{u, v, w, u} u := by
  refine (universallyInjective_iff_injective_mod_finite_ideal u).2 ?_
  intro J hJ
  sorry

end

end

end LinearMap
