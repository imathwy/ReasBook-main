import stacks_project.Chap09.Definition_9_12_6
import stacks_project.Chap09.Situation_9_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open Situation_9_12_7
open scoped PolynomialSeparableDegree
open scoped Situation_9_12_7

noncomputable section

universe u v w

section

/- Domain-style sampling for Lemma 9.12.9:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra embeddings
  into algebraically closed extensions;
- sampled owner declarations:
  * `Field.finSepDegree`
  * `Field.finSepDegree_eq_of_isAlgClosed`
  * `Polynomial.natSepDegree_eq_of_isAlgClosed`
  * `embeddingTuple_bijective`
- best owner abstraction: `Field.finSepDegree F K`;
- primitive data: the finite extension `K/F`, the generator tuple `α`, and the induced tower
  stages `K[F, α; i]` with minimal polynomials `P[F, α; i]`;
- derived API: the `Nat.card` formula for `K →ₐ[F] L` after choosing an algebraic closure `L`.

Source/core/bridge triage:
- `source-facing`: the product formula for the finite separable degree `[K : F]_s`;
- `core/canonical`: `Field.finSepDegree F K`;
- `bridge/view`: the cardinality of `K →ₐ[F] L` for algebraically closed `L`.

The owner theorem should therefore avoid carrying a chosen algebraic closure as primitive data.
-/

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

-- Proof sketch: use `embeddingTuple_bijective` from Lemma 9.12.8 to identify `F`-algebra
-- embeddings `K → \overline F` with compatible tuples of roots of the successive minimal
-- polynomials, then count the roots of each polynomial in the algebraic closure by
-- `Polynomial.natSepDegree_eq_of_isAlgClosed`.
/-- Lemma 9.12.9: in Situation 9.12.7, the finite separable degree `[K : F]_s` is the product of
the separable degrees of the successive minimal polynomials `P_i`. -/
theorem finSepDegree_eq_prod_deg_s (hα : K[Fin.last n] = ⊤) :
    Field.finSepDegree F K = ∏ i : Fin n, deg_s(P[i]) := by
  rw [Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F)]
  sorry

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosure F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

attribute [local instance] IsAlgClosure.isAlgClosed

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

/-- Bridge reformulation of Lemma 9.12.9 for a chosen algebraic closure `L` of `F`. -/
theorem card_algHom_eq_prod_deg_s (hα : K[Fin.last n] = ⊤) :
    Nat.card (K →ₐ[F] L) = ∏ i : Fin n, deg_s(P[i]) := by
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K L]
  exact finSepDegree_eq_prod_deg_s F K α hα

end
