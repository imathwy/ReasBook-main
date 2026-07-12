import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Lemma_10_82_7
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open LinearMap

namespace CategoryTheory
namespace ShortComplex

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat R)}

/- Domain-style sampling:
- primary domain: flatness propagation in short exact complexes of `R`-modules;
- inspected owner declarations: `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`,
  `CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃`,
  `LinearMap.lTensor_injective_of_exact_of_flat`;
- owner abstraction: `S.ShortExact` is the source-facing owner for the middle-term statement,
  while `UniversallyExact S` is only the bridge/view needed for the left-term statement;
- primitive data vs. derived API: short exactness is the primitive datum for `flat_X₂`, while
  universal exactness is derived from flatness of the cokernel and used only to recover `flat_X₁`.
  No separate equivalence wrapper between `flat_X₁` and `flat_X₂` is mathematically primitive. -/

namespace ShortExact

/-- Lemma 10.39.13 (1): in a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `R`-modules, if the
left and right terms are flat, then the middle term is flat. -/
@[stacks 00HM]
theorem flat_X₂ (hS : S.ShortExact) [Module.Flat R S.X₁] [Module.Flat R S.X₃] :
    Module.Flat R S.X₂ := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hSurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hN₁ : Function.Exact (0 : Unit →ₗ[R] TensorProduct R N S.X₁) (lTensor N S.f.hom) := by
    rw [LinearMap.exact_zero_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hSurj S.f.hom
      hS.moduleCat_injective_f hExact N
  have hN₂ : Function.Exact (lTensor N S.f.hom) (lTensor N S.g.hom) :=
    lTensor_exact N hExact hSurj
  have hP₁ : Function.Exact (0 : Unit →ₗ[R] TensorProduct R P S.X₁) (lTensor P S.f.hom) := by
    rw [LinearMap.exact_zero_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hSurj S.f.hom
      hS.moduleCat_injective_f hExact P
  exact LinearMap.injective_of_surjective_of_injective_of_injective
    (0 : Unit →ₗ[R] TensorProduct R N S.X₁) (lTensor N S.f.hom) (lTensor N S.g.hom)
    (0 : Unit →ₗ[R] TensorProduct R P S.X₁) (lTensor P S.f.hom) (lTensor P S.g.hom)
    (0 : Unit →ₗ[R] Unit) (i.rTensor S.X₁) (i.rTensor S.X₂) (i.rTensor S.X₃)
    (by ext; simp)
    (by
      ext x
      simp [LinearMap.lTensor_comp_rTensor])
    (by
      ext x
      simp [LinearMap.lTensor_comp_rTensor])
    hN₁ hN₂ hP₁
    (by
      intro u
      cases u
      exact ⟨(), rfl⟩)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)

/-- Lemma 10.39.13 (2): in a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `R`-modules, if the
middle and right terms are flat, then the left term is flat. -/
@[stacks 00HM]
theorem flat_X₁ (hS : S.ShortExact) [Module.Flat R S.X₂] [Module.Flat R S.X₃] :
    Module.Flat R S.X₁ :=
  UniversallyExact.flat_X₁ (universallyExact_of_flat_X₃ hS)

end ShortExact
end ShortComplex
end CategoryTheory
