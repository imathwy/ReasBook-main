import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_168_9

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped TensorProduct

noncomputable section

namespace MvPolynomial

variable (n m : ℕ)

/- Domain-style sampling:
* primary domain: generic factorization maps for monic polynomials in multivariable polynomial
  rings;
* inspected owner declarations:
  - `MvPolynomial.universalFactorizationMap`
  - `MvPolynomial.universalFactorizationMap_freeMonic`
  - `MvPolynomial.finite_universalFactorizationMap`
  - `MvPolynomial.tensorEquivSum`
* best owner abstraction:
  - `source-facing`: the textbook coefficient map
    `ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`
  - `core/canonical`: `MvPolynomial.universalFactorizationMap`
  - `bridge/view`: transport of that owner across `MvPolynomial.tensorEquivSum`
* primitive vs. derived:
  - primitive data: only `n`, `m`, and the canonical owner map
  - derived API: the source-facing sum-variable realization `genericFactorizationMap` and its
    consequences below
-/
/-- The textbook coefficient map
`ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`, obtained by transporting the canonical owner
`MvPolynomial.universalFactorizationMap` across `MvPolynomial.tensorEquivSum` to the polynomial
ring with variables `Fin n ⊕ Fin m`. -/
abbrev genericFactorizationMap :
    MvPolynomial (Fin (n + m)) ℤ →ₐ[ℤ] MvPolynomial (Fin n ⊕ Fin m) ℤ :=
  (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toAlgHom.comp
    (universalFactorizationMap ℤ (n + m) n m rfl)

/-- The bridge to the canonical owner: the textbook coefficient map sends the generic monic
polynomial of degree `n + m` to the product of the two generic monic factors of degrees `n`
and `m`. -/
theorem genericFactorizationMap_freeMonic :
    (freeMonic ℤ (n + m)).map (genericFactorizationMap n m) =
      ((freeMonic ℤ n).map (rename Sum.inl).toRingHom) *
        ((freeMonic ℤ m).map (rename Sum.inr).toRingHom) := by
  sorry

-- Proof sketch: use `genericFactorizationMap_freeMonic` to identify the displayed coefficient map
-- with the canonical generic factorization map, and then transport the relative global complete
-- intersection structure across `tensorEquivSum`.
/-- Example 10.136.7: the coefficient ring map sending the coefficients of the generic monic
polynomial of degree `n + m` to the coefficients of the product of generic monic factors of
degrees `n` and `m` is a relative global complete intersection. -/
theorem genericFactorizationMap_isRelativeGlobalCompleteIntersection :
    letI := (genericFactorizationMap n m).toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection
      (MvPolynomial (Fin (n + m)) ℤ) (MvPolynomial (Fin n ⊕ Fin m) ℤ) := by
  sorry

-- Proof sketch: after identifying the displayed coefficient map with the canonical owner via
-- `genericFactorizationMap`, transport finiteness across `tensorEquivSum` and apply
-- `MvPolynomial.finite_universalFactorizationMap`.
/-- The generic factorization coefficient map is finite. -/
theorem genericFactorizationMap_finite :
    (genericFactorizationMap n m).Finite := by
  exact RingHom.Finite.comp
    (RingEquiv.finite (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingEquiv)
    (finite_universalFactorizationMap ℤ (n + m) n m rfl)

end MvPolynomial
