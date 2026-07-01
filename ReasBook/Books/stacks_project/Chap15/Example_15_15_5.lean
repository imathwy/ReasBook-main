import Mathlib
import stacks_project.Chap10.Remark_10_63_12
import stacks_project.Chap15.Definition_15_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "I∞" =>
  Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))
local notation "R∞" => infiniteSquareZeroPolynomialQuotient k
local notation "F∞" => ℕ →₀ R∞

noncomputable local instance : Module R∞ R∞ := Semiring.toModule
noncomputable local instance : Module R∞ F∞ := Finsupp.module ℕ R∞

/- Domain triage:
* primary domain: commutative algebra of local rings and weak association.
* sampled owner abstractions:
  `IsAutoAssociatedRing`,
  `isAutoAssociatedRing_iff`,
  `infiniteSquareZeroPolynomialQuotient`,
  `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv`.
* layer choice: the explicit shift map below is the `source-facing` witness, while
  `IsAutoAssociatedRing` is the chapter's `core/canonical` owner for the ring-side clause of
  Example `15.15.5`; that clause should therefore be exposed as an instance rather than a
  parallel theorem.
* primitive data: the quotient ring `R∞` and the basis prescription `e_i ↦ f_i - x_i f_{i + 1}`.
* derived API: the square-zero identities, the induced linear map `squareZeroShiftMap`, and its
  injective non-split behavior.
-/

/-- The image of the variable `X i` in the square-zero polynomial quotient. -/
abbrev squareZeroVariable (i : ℕ) : R∞ :=
  Ideal.Quotient.mk I∞ (X i : MvPolynomial ℕ k)

-- Proof sketch: each square `X i ^ 2` lies in the defining ideal `I∞`, so its image in the
-- quotient is zero.
/-- Each coordinate variable is square-zero in the quotient ring. -/
@[simp] theorem squareZeroVariable_sq_eq_zero (i : ℕ) :
    squareZeroVariable k i ^ (2 : ℕ) = 0 := sorry

private def squareZeroShiftFamily (i : ℕ) : F∞ :=
  Finsupp.single i 1 - Finsupp.single (i + 1) (squareZeroVariable k i)

/-- The map `e_i ↦ f_i - x_i f_{i + 1}` on the countable free module over the square-zero
polynomial quotient. -/
noncomputable def squareZeroShiftMap :
    F∞ →ₗ[R∞] F∞ :=
  Finsupp.linearCombination R∞ (squareZeroShiftFamily k)

-- Proof sketch: unfold `squareZeroShiftMap`, use `Finsupp.linearCombination_single`, and rewrite
-- scalar multiplication on `Finsupp.single`.
/-- On a single basis term, the shift map acts by `e_i r ↦ e_i r - e_{i+1} (x_i r)`. -/
@[simp] theorem squareZeroShiftMap_single (i : ℕ) (r : R∞) :
    squareZeroShiftMap k (Finsupp.single i r) =
      Finsupp.single i r -
        Finsupp.single (i + 1) (squareZeroVariable k i * r) := sorry

/-- Example 15.15.5 (ring side): the square-zero quotient
`k[x₀, x₁, x₂, \ldots] / (x_i^2)` is an auto-associated local ring. -/
instance :
    IsAutoAssociatedRing R∞ := by
  sorry

-- Proof sketch: prove injectivity by checking linear independence on each finite partial family
-- of images `u(e₁), ..., u(eₙ)`. To rule out a splitting, tensor with the residue field `k` to get
-- a bijection via `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv k`; a left inverse would
-- then force surjectivity, but `f₁` would require the infinite preimage
-- `e₁ + x₁ e₂ + x₁ x₂ e₃ + ⋯`, which is not finitely supported.
/-- Companion to Example 15.15.5 (module side): over the auto-associated local ring
`R = k[x₀, x₁, x₂, \ldots] / (x_i^2)`, whose residue field is canonically `k`, the map
`u(e_i) = f_i - x_i f_{i + 1}` on the free module `ℕ →₀ R` is injective but not a split
injection. -/
theorem squareZeroShiftMap_injective_not_split :
    Function.Injective (squareZeroShiftMap k) ∧
      ¬ ∃ v : F∞ →ₗ[R∞] F∞,
          v ∘ₗ squareZeroShiftMap k = LinearMap.id := sorry

end
