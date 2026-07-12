import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Finsupp Submodule TensorProduct

universe u v w x y

section

variable {R : Type u} {M : Type v} {N : Type w} {I : Type x} {J : Type y}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- Proof sketch: pass to the finite family on `m.support`, swap tensor factors with
-- `TensorProduct.comm`, and apply the canonical owner theorem
-- `TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero` with the generating family `y`. The
-- resulting auxiliary elements of `M` are then expanded in the generating family `x`, producing the
-- required nested `Finsupp` coefficient matrix.
/- Layering for this item:
- `source-facing`: the finitely supported tensor relation `m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = 0`
  expressed in terms of the generating families `x` and `y`;
- `core/canonical`: `TensorProduct.VanishesTrivially` together with
  `TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero`;
- `bridge/view`: rewriting the owner witness through `m.support`, `TensorProduct.comm`, and the
  surjective linear-combination map attached to `x`.
-/
/-- Lemma 10.107.10: let `x : I → M` and `y : J → N` be generating families of the `R`-modules
`M` and `N`. For a finitely supported family `m : J →₀ M`, the tensor relation
`∑ j, m j ⊗ y j = 0` is equivalent to the existence of a finitely supported coefficient matrix
whose rows express the `m j` in terms of the generators `x i` and whose columns give relations
among the generators `y j`. -/
theorem finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix
    (x : I → M) (y : J → N) (m : J →₀ M)
    (hx : span R (Set.range x) = ⊤)
    (hy : span R (Set.range y) = ⊤) :
    (m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N)) ↔
      ∃ a : J →₀ I →₀ R,
        (∀ j, m j = linearCombination R x (a j)) ∧
          ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0 := sorry

end
