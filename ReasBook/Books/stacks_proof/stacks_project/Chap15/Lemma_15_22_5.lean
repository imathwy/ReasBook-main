import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: torsion-free modules and exact sequences of linear maps;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Function.Exact.linearMap_ker_eq`,
  `isSMulRegular_of_range_eq_ker`,
  `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`;
- best owner abstraction: `isSMulRegular_of_range_eq_ker`;
- source-facing layer: the Stacks lemma that torsion-freeness passes to the middle term of a short
  exact sequence;
- core/canonical layer: scalar-regularity on the middle term of a left exact sequence;
- bridge/view: specialize scalar-regularity to `Module.IsTorsionFree`. The short-complex theorem
  `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact` supplies the
  chapter-level exactness bridge from `ShortExact` to `Function.Exact`, but the owner abstraction
  for this file remains the direct scalar-regularity theorem.

Primitive data for the conclusion are only the injective map `f`, the exactness relation
`Function.Exact f g`, and torsion-freeness on the end terms. The surjectivity part of short
exactness is not used by the canonical owner theorem and should not remain primitive input here.
-/

section

variable {R : Type u} [Ring R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup M''] [Module R M'']

open Module

/-- Lemma 15.22.5: if `M ⟶ M' ⟶ M''` is exact at `M'`, the first map is injective, and the end
terms are torsion free, then `M'` is torsion free. For the source short exact sequence statement,
the surjectivity of the second map is redundant for this conclusion. -/
@[stacks 0AUS]
theorem isTorsionFree_of_exact_of_injective
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    [IsTorsionFree R M] [IsTorsionFree R M''] :
    IsTorsionFree R M' where
  isSMulRegular _r hr :=
    isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm
      hr.isSMulRegular hr.isSMulRegular

end
