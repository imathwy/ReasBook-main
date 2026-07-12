import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [Ring R]
variable {M1 : Type v} [AddCommGroup M1] [Module R M1]
variable {M2 : Type w} [AddCommGroup M2] [Module R M2]
variable {M3 : Type x} [AddCommGroup M3] [Module R M3]

/- In a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M1`
and `M3` are finite, then `M2` is finite. This is exactly the canonical theorem
`Module.Finite.of_exact`. -/
recall Module.Finite.of_exact

namespace Module

-- Proof sketch: combine part (5) applied to the induced exact sequence on kernels of finite free
-- presentations with part (4), or equivalently argue via the snake lemma on a diagram of finite
-- free presentations of `M1` and `M3`.
/-- Lemma 10.5.3 (1): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M1`
and `M3` are finitely presented, then `M2` is finitely presented. -/
@[stacks 0519]
theorem finitePresentation_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M1] [Module.FinitePresentation R M3] :
    Module.FinitePresentation R M2 := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  haveI : Module.FinitePresentation R (LinearMap.ker g) := by
    exact Module.FinitePresentation.of_equiv
      ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hker.symm))
  exact Module.finitePresentation_of_ker g hg

end Module

/- In a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M2`
is finite, then `M3` is finite. This is exactly the canonical theorem
`Module.Finite.of_surjective`. -/
recall Module.Finite.of_surjective

namespace Module

-- Proof sketch: apply `Module.finitePresentation_of_surjective` to `g`; exactness identifies
-- `ker g` with `range f`, and `range f` is finitely generated because `M1` is finite.
/-- Lemma 10.5.3 (2): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M2`
is finitely presented and `M1` is finite, then `M3` is finitely presented. -/
@[stacks 0519]
theorem finitePresentation_of_surjective_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M2] [Module.Finite R M1] :
    Module.FinitePresentation R M3 := by
  rw [LinearMap.exact_iff] at hfg
  exact Module.finitePresentation_of_surjective g hg (hfg.symm ▸ Submodule.fg_range f)

end Module

namespace Module.Finite

-- Proof sketch: `Module.FinitePresentation.fg_ker` gives finite generation of `ker g` from the
-- finite presentation of `M3` and finiteness of `M2`; exactness identifies `ker g` with
-- `range f`, and injectivity of `f` transports finiteness from `range f` back to `M1`.
/-- Lemma 10.5.3 (3): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M3`
is finitely presented and `M2` is finite, then `M1` is finite. -/
@[stacks 0519]
theorem of_exact_of_finitePresentation
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M3] [Module.Finite R M2] :
    Module.Finite R M1 := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  have hrange : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_fg (hker.symm ▸ Module.FinitePresentation.fg_ker g hg)
  exact (Module.Finite.equiv_iff (LinearEquiv.ofInjective f hf)).2 hrange

end Module.Finite

end
