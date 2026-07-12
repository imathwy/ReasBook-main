import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open TensorProduct

section

variable (R : Type u) (M : Type v) (N : Type w)
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/- The finite tensor-product part of this item is the canonical mathlib instance. -/
recall Module.Finite.tensorProduct

namespace Module.FinitePresentation

/-- Helper for Lemma 10.12.14: tensoring a finitely presented module with a finite free module
stays finitely presented. -/
private lemma tensorProduct_finite_free (n : ℕ) [Module.FinitePresentation R N] :
    Module.FinitePresentation R (N ⊗[R] (Fin n → R)) := by
  -- Identify the tensor product with the finite product `Fin n → N`.
  exact Module.FinitePresentation.of_equiv
    (TensorProduct.piScalarRight R R N (Fin n)).symm

/-- Lemma 10.12.14: if `M` and `N` are finitely presented `R`-modules, then the tensor
product `M ⊗[R] N` is finitely presented over `R`. -/
@[stacks 05BS]
instance tensorProduct [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] : Module.FinitePresentation R (M ⊗[R] N) := by
  -- Follow the source proof through `N ⊗[R] M`, then commute the tensor factors at the end.
  have hNM : Module.FinitePresentation R (N ⊗[R] M) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    -- Tensor the finite free presentation source; this remains finitely presented.
    letI : Module.FinitePresentation R (N ⊗[R] (Fin n → R)) :=
      tensorProduct_finite_free (R := R) (N := N) n
    have hker_finite : Module.Finite R (LinearMap.ker f) := by
      -- The kernel of a presentation of a finitely presented module is finitely generated.
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
    have hker_fg : (LinearMap.ker (LinearMap.lTensor N f)).FG := by
      letI : Module.Finite R (LinearMap.ker f) := hker_finite
      -- Right exactness identifies the new kernel with the range of the tensored subtype map.
      have hExact : Function.Exact ((LinearMap.ker f).subtype) f :=
        LinearMap.exact_subtype_ker_map f
      have hTensorExact : Function.Exact
          (LinearMap.lTensor N (LinearMap.ker f).subtype)
          (LinearMap.lTensor N f) :=
        lTensor_exact N hExact hf
      rw [LinearMap.exact_iff] at hTensorExact
      exact hTensorExact.symm ▸ Submodule.fg_range (LinearMap.lTensor N (LinearMap.ker f).subtype)
    -- The tensor product is a quotient of the finitely presented source by a finitely generated
    -- kernel, so it is finitely presented.
    exact Module.finitePresentation_of_surjective (LinearMap.lTensor N f)
      (LinearMap.lTensor_surjective N hf) hker_fg
  -- Commute the tensor factors to recover the textbook order.
  exact Module.FinitePresentation.of_equiv (TensorProduct.comm R N M)

end Module.FinitePresentation

end
