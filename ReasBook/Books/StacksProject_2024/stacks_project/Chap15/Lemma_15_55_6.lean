import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.LeftExact
import StacksProject_2024.Chap15.Definition_15_55_5

open CategoryTheory ModuleCat

universe u v

/-!
Domain-style sampling:
- primary domain: character modules as a contravariant functor on module categories;
- sampled owner declarations:
  `functor`,
  `CharacterModule.dual`,
  `LinearMap.exact_lcomp_of_exact_of_surjective`,
  `CharacterModule.dual_injective_of_surjective`,
  `CharacterModule.dual_surjective_of_injective`;
- best owner abstraction: the `source-facing` owner is the contravariant functor
  `functor : (ModuleCat R)ᵒᵖ ⥤ ModuleCat Rᵐᵒᵖ`;
- primitive data: a short exact short complex `S : ShortComplex (ModuleCat R)`;
- derived API: exactness of precomposition with a surjective linear map together with injectivity
  and surjectivity of the induced functorial maps;
- layer split: the additive exactness lemma below is an internal `bridge/view`, while
  `CharacterModule.shortExact_of_shortExact` is the `source-facing` Stacks statement.
-/

section

variable {R : Type u} [Ring R]

namespace CharacterModule

/-- Exactness of the dual maps follows from exactness of precomposition on the underlying
`ℤ`-linear maps. -/
private theorem dual_exact_of_exact_of_surjective
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hfg : Function.Exact f g)
    (hsurj : Function.Surjective g) :
    Function.Exact (dual (g.restrictScalars ℤ)) (dual (f.restrictScalars ℤ)) := by
  let D := AddCircle (1 : ℚ)
  let f' := f.restrictScalars ℤ
  let g' := g.restrictScalars ℤ
  have hExact :
      Function.Exact (LinearMap.lcomp ℤ D g') (LinearMap.lcomp ℤ D f') :=
    LinearMap.exact_lcomp_of_exact_of_surjective D hfg hsurj
  have hcomp : g'.comp f' = 0 := by
    ext x
    simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero x
  intro χ
  constructor
  · intro hχ
    have hχ' : LinearMap.lcomp ℤ D f' χ.toIntLinearMap = 0 := by
      ext x
      simpa using DFunLike.congr_fun hχ x
    rcases (hExact χ.toIntLinearMap).1 hχ' with ⟨ψ, hψ⟩
    refine ⟨ψ.toAddMonoidHom, ?_⟩
    ext x
    simpa using DFunLike.congr_fun hψ x
  · rintro ⟨ψ, rfl⟩
    ext x
    change ψ ((g'.comp f') x) = 0
    simp [hcomp]

/-- Lemma 15.55.6: if `S` is a short exact sequence of left `R`-modules, then applying the
contravariant character-module functor yields a short exact sequence of left `Rᵐᵒᵖ`-modules. -/
theorem shortExact_of_shortExact
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.op.map (functor R)).ShortExact := by
  let f := S.f.hom
  let g := S.g.hom
  have hfg : Function.Exact S.f S.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hg : Function.Surjective S.g := hS.moduleCat_surjective_g
  have hf : Function.Injective S.f := hS.moduleCat_injective_f
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact (dual (g.restrictScalars ℤ)) (dual (f.restrictScalars ℤ))
    exact dual_exact_of_exact_of_surjective f g hfg hg
  · change Function.Injective (dual (g.restrictScalars ℤ))
    exact dual_injective_of_surjective (g.restrictScalars ℤ) hg
  · change Function.Surjective (dual (f.restrictScalars ℤ))
    exact dual_surjective_of_injective (f.restrictScalars ℤ) hf

end CharacterModule

end
