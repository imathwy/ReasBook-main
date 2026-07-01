import stacks_project.LinearAlgebra.PowerOperations

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

/- Domain triage: this file lies in multilinear algebra of symmetric and exterior powers.
The owner abstractions are the canonical comparison maps
`SymmetricPower.leftTensorMap`, `SymmetricPower.map`, `exteriorPower.leftTensorMap`, and
`exteriorPower.map` from `stacks_project.LinearAlgebra.PowerOperations`, organized around the
canonical owner `S : ShortComplex (ModuleCat R)` with `hS : S.ShortExact`. The present results are
`source-facing` exactness statements expressed directly in those owner maps, while the
tensor-presentation exact sequences from Lemma `10.13.3` remain the lower `bridge/view` layer
used to justify them. -/

section

universe u v

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: present `Sym[R]^(n + 1) M` as the quotient of the `(n + 1)`st tensor power by
-- permutation relations, use `TensorProduct.lTensor_exact` and `LinearMap.lTensor_surjective` on
-- the tensor-power presentation, and descend the resulting maps to the canonical owner maps
-- `SymmetricPower.leftTensorMap` and `SymmetricPower.map`.
/-- Lemma 10.13.2 (1), stated in degree `n + 1`: for an exact sequence `M₂ ⟶ M₁ ⟶ M ⟶ 0`,
the canonical sequence
`M₂ ⊗[R] Sym[R]^n M₁ ⟶ Sym[R]^(n + 1) M₁ ⟶ Sym[R]^(n + 1) M ⟶ 0`
is exact. -/
theorem symmetric_power_exact_of_exact (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (SymmetricPower.leftTensorMap n S.f.hom) (SymmetricPower.map (n + 1) S.g.hom) ∧
      Function.Surjective (SymmetricPower.map (n + 1) S.g.hom) := sorry

-- Proof sketch: combine `TensorProduct.lTensor_exact` and `LinearMap.lTensor_surjective` with the
-- standard exterior-power presentation by alternating tensors, then descend to the canonical owner
-- maps `exteriorPower.leftTensorMap` and `exteriorPower.map`.
/-- Lemma 10.13.2 (2), stated in degree `n + 1`: for an exact sequence `M₂ ⟶ M₁ ⟶ M ⟶ 0`,
the canonical sequence
`M₂ ⊗[R] ⋀[R]^n M₁ ⟶ ⋀[R]^(n + 1) M₁ ⟶ ⋀[R]^(n + 1) M ⟶ 0`
is exact. -/
theorem exterior_power_exact_of_exact (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (exteriorPower.leftTensorMap n S.f.hom) (exteriorPower.map (n + 1) S.g.hom) ∧
      Function.Surjective (exteriorPower.map (n + 1) S.g.hom) := sorry

end
