import stacks_proof.stacks_project.Chap09.Definition_9_12_6
import stacks_proof.stacks_project.Chap09.Lemma_9_12_8
import stacks_proof.stacks_project.Chap09.Situation_9_12_7
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 9.12.9: the range-product form of the first `m` separable-degree factors in
the generator tower. -/
private abbrev prefix_deg_s_prod (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.range m, if hj : j < n then deg_s(P[⟨j, hj⟩]) else 1

/-- Helper for Lemma 9.12.9: the separable degree along the tower multiplies by the next factor at
each successor stage. -/
private lemma stage_finSepDegree_succ (i : Fin n) :
    Field.finSepDegree F K[i.succ] = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) := by
  let M := IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)
  let _ : Module.Finite K[i.castSucc] K := FiniteDimensional.right F K[i.castSucc] K
  let halg : IsAlgebraic K[i.castSucc] (α i) :=
    ((Algebra.IsIntegral.of_finite K[i.castSucc] K).isIntegral (α i)).isAlgebraic
  have hstep : Field.finSepDegree K[i.castSucc] M = deg_s(P[i]) := by
    -- The simple-adjoin separable degree is the separable degree of the corresponding minpoly.
    simpa [M] using
      (IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
        (F := K[i.castSucc]) (E := K) halg)
  -- Rewrite the successor stage to the simple-adjoin stage and apply the tower law.
  rw [stage_succ_eq_adjoin F α i]
  calc
    Field.finSepDegree F M =
        Field.finSepDegree F K[i.castSucc] * Field.finSepDegree K[i.castSucc] M := by
      symm
      exact Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F K[i.castSucc] M
    _ = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) := by
      rw [hstep]

/-- Helper for Lemma 9.12.9: the separable degree of the `m`th stage is the product of the first
`m` separable-degree factors. -/
private lemma prefix_stage_finSepDegree_eq_prod_deg_s :
    ∀ m : ℕ, ∀ hm : m ≤ n,
      Field.finSepDegree F K[⟨m, Nat.lt_succ_of_le hm⟩] =
        prefix_deg_s_prod (F := F) (K := K) (α := α) m
  | 0, hm => by
      -- The zeroth stage is the base field, whose separable degree is `1`.
      have hzero : K[⟨0, Nat.lt_succ_of_le hm⟩] = (⊥ : IntermediateField F K) := by
        simpa using stage_zero_eq_bot F α
      rw [hzero]
      simp [prefix_deg_s_prod]
  | m + 1, hm => by
      let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
      -- Advance one stage using the multiplicative recursion from the simple-adjoin step.
      calc
        Field.finSepDegree F K[⟨m + 1, Nat.lt_succ_of_le hm⟩] =
            Field.finSepDegree F K[i.succ] := by
          rfl
        _ = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) :=
            stage_finSepDegree_succ (F := F) (K := K) (α := α) i
        _ = Field.finSepDegree F K[⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩] *
              deg_s(P[i]) := by
          rfl
        _ = prefix_deg_s_prod (F := F) (K := K) (α := α) m * deg_s(P[i]) := by
          rw [prefix_stage_finSepDegree_eq_prod_deg_s m (Nat.le_of_succ_le hm)]
        _ = prefix_deg_s_prod (F := F) (K := K) (α := α) (m + 1) := by
          simp [prefix_deg_s_prod, Finset.prod_range_succ, i, Nat.lt_of_succ_le hm]

/-- Helper for Lemma 9.12.9: once the final stage is all of `K`, its separable degree is the
separable degree of `K/F`. -/
private lemma last_stage_finSepDegree_eq_main_field (hα : K[Fin.last n] = ⊤) :
    Field.finSepDegree F K[Fin.last n] = Field.finSepDegree F K := by
  let _ : FiniteDimensional F K := inferInstance
  -- The top intermediate field is canonically equivalent to the ambient extension field.
  rw [hα, IntermediateField.finSepDegree_top]

/-- Lemma 9.12.9: in Situation 9.12.7, the finite separable degree `[K : F]_s` is the product of
the separable degrees of the successive minimal polynomials `P_i`. -/
@[stacks 09H8]
theorem finSepDegree_eq_prod_deg_s (hα : K[Fin.last n] = ⊤) :
    Field.finSepDegree F K = ∏ i : Fin n, deg_s(P[i]) := by
  -- Route correction: follow the source tower argument stage-by-stage via separable degrees,
  -- then rewrite the last stage to `K`.
  calc
    Field.finSepDegree F K = Field.finSepDegree F K[Fin.last n] := by
      symm
      exact last_stage_finSepDegree_eq_main_field (F := F) (K := K) (α := α) hα
    _ = prefix_deg_s_prod (F := F) (K := K) (α := α) n := by
      simpa using prefix_stage_finSepDegree_eq_prod_deg_s (F := F) (K := K) (α := α) n le_rfl
    _ = ∏ i : Fin n, deg_s(P[i]) := by
      simpa [prefix_deg_s_prod] using
        (Fin.prod_univ_eq_prod_range
          (fun j : ℕ => if hj : j < n then deg_s(P[⟨j, hj⟩]) else 1) n).symm

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
