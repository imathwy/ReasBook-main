import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_28 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.28 lies in the chapter's finite-dimensional primal-dual objective domain.

Mandatory domain-style sampling before drafting:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for the structured
  primal-dual data `Q₁`, `Q₂`, `\hat f`, `\hat φ`, and `A`;
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical primal objective
  induced by that saddle representation;
- `StructuredObjectiveModel.primalOptimalValue` and
  `StructuredObjectiveModel.adjointOptimalValue` in `Chap06/Definition_6_6`, the canonical outer
  values corresponding to the textbook symbols `f^*` and `f_*`;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the canonical dual
  objective whose outer supremum gives `f_*`.

Best owner abstraction:
- source-facing: `PrimalDualObjectiveModel`, which adds the textbook finite-dimensional ambient
  hypotheses and nonemptiness of both feasible sets to the existing Chapter 6 owner;
- core/canonical: `StructuredObjectiveModel`;
- bridge/view: the recalled inherited value API below, with later attainment lemmas recovering the
  textbook min/max formulas from the `EReal` infimum/supremum surface.

Primitive data:
- the inherited structured-objective data from `StructuredObjectiveModel`;
- nonemptiness of the primal and dual feasible sets.

Derived API:
- the inherited owner functions `objective`, `primalOptimalValue`, `adjointObjective`, and
  `adjointOptimalValue`;
- the inherited pointwise formulas `objective_apply`, `primalOptimalValue_eq_saddle_form`,
  `adjointObjective_apply`, and `adjointOptimalValue_def`.

Source/core/bridge triage:
- source-facing: `PrimalDualObjectiveModel`;
- core/canonical: `StructuredObjectiveModel`;
- bridge/view: the recalled inherited value API below.

Definition 6.28 is not a pure recall item: besides the Chapter 6 structured-objective owner, it
adds the source hypotheses that both feasible sets are nonempty and that both ambient spaces are
finite-dimensional real vector spaces. The primal and adjoint value functions themselves remain the
canonical owner API rather than a duplicate `ℝ`-valued wrapper layer.
-/

/-- Definition 6.28 [Chapter6_1.json:65]: a primal-dual objective model consists of
finite-dimensional real vector spaces `E₁` and `E₂`, nonempty bounded closed convex sets
`Q₁ ⊆ E₁` and `Q₂ ⊆ E₂`, continuous convex functions `\hat f` on `Q₁` and `\hat φ` on `Q₂`,
and a linear map `A : E₁ → E₂*`. Its primal objective, adjoint objective, primal optimal value
`f^*`, and adjoint optimal value `f_*` are the canonical Chapter 6 constructions attached to this
structured data. -/
structure PrimalDualObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    extends StructuredObjectiveModel E₁ E₂ where
  /-- The primal feasible set `Q₁` is nonempty. -/
  primalSet_nonempty : primalSet.Nonempty
  /-- The dual feasible set `Q₂` is nonempty. -/
  dualSet_nonempty : dualSet.Nonempty

namespace PrimalDualObjectiveModel

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]

/-- A primal-dual objective model inherits its underlying Chapter 6 structured objective model. -/
instance : Coe (PrimalDualObjectiveModel E₁ E₂) (StructuredObjectiveModel E₁ E₂) where
  coe problem := problem.toStructuredObjectiveModel

section

/- The primal objective of Definition 6.28 is the inherited Chapter 6 owner function. -/
recall StructuredObjectiveModel.objective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal

/- The primal optimal value `f^*` is the inherited outer infimum of the primal objective. -/
recall StructuredObjectiveModel.primalOptimalValue
    (problem : StructuredObjectiveModel E₁ E₂) : EReal

/- The adjoint objective `φ` of Definition 6.28 is the inherited Chapter 6 dual objective. -/
recall StructuredObjectiveModel.adjointObjective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.dualSet → EReal

/- The adjoint optimal value `f_*` is the inherited outer supremum of the adjoint objective. -/
recall StructuredObjectiveModel.adjointOptimalValue
    (problem : StructuredObjectiveModel E₁ E₂) : EReal

/- The textbook saddle formula for the primal objective is the inherited owner theorem. -/
recall StructuredObjectiveModel.objective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

/- The textbook outer primal value is the inherited infimum of the saddle-form objective. -/
recall StructuredObjectiveModel.primalOptimalValue_eq_saddle_form
    (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalOptimalValue =
      sInf (Set.range fun x : problem.primalSet ↦
        sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)))

/- The textbook formula for the adjoint objective is the inherited owner theorem. -/
recall StructuredObjectiveModel.adjointObjective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (u : problem.dualSet) :
    problem.adjointObjective u =
      sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal))

/- The adjoint optimal value is the inherited outer supremum of the adjoint objective. -/
recall StructuredObjectiveModel.adjointOptimalValue_def
    (problem : StructuredObjectiveModel E₁ E₂) :
    problem.adjointOptimalValue = sSup (Set.range problem.adjointObjective)

end

end PrimalDualObjectiveModel

end

/-! ### Proposition_6_28 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped StandardSimplex

section

variable (n : ℕ) (m : ℕ+)

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 6.28 lies in the finite simplex / entropy-smoothed primal-dual gap domain.

Sampled owner declarations:
* `maxTypeObjective` in `Chap02/Lemma_2_18`, the canonical finite-family maximum owner;
* `Δ[m]` in `Chap06/Definition_6_11`, the Chapter 6 simplex surface for the dual feasible set;
* `normalizedEntropyProxFunction` and `sSup_range_normalizedEntropyProxFunction_eq_log` in
  `Chap06/Definition_6_14` and `Chap06/Lemma_6_3`, the entropy prox owner and its budget
  `D₂ = log m`;
* `scheme_6_2_37_primal_dual_gap_le_rate` in `Chap06/Theorem_6_2_4`, the generic Chapter 6
  `(6.2.37)` gap-rate theorem.

Best owner abstraction:
* source-facing: the explicit strongly convex max-affine primal objective and its associated dual
  objective on the simplex;
* core/canonical: `maxTypeObjective` for the finite maximum and the Chapter 6 simplex owner
  `Δ[m]`;
* bridge/view: the specialization of the generic `(6.2.37)` rate theorem to the entropy budget
  `log m` and the operator-norm formula `‖A‖_{1,2} = max_j ‖g_j‖`.

Primitive data:
* the affine data `f`, `g`, and `points`;
* the explicit primal objective and associated dual objective;
* the scalar operator norm `‖A‖_{1,2}` written directly as `max_j ‖g_j‖`.

Derived API:
* the coordinate expansion of the primal objective;
* the explicit formula for the dual objective;
* the Chapter 6 gap-rate specialization stated in the main theorem below.
-/

/-- The strongly convex max-affine objective
`x ↦ (1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)` from Proposition 6.28. -/
def strongly_convex_max_affine_objective
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) : E → ℝ :=
  fun x ↦
    (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
      maxTypeObjective (fun j : Fin (m : ℕ) ↦ fun y : E ↦ f j + inner ℝ (g j) (y - points j)) x

-- Proof sketch: unfold `strongly_convex_max_affine_objective` and then expand the finite maximum
-- by `maxTypeObjective_apply`.
/-- Evaluating `strongly_convex_max_affine_objective` gives the textbook formula
`(1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)`. -/
theorem strongly_convex_max_affine_objective_apply
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) (x : E) :
    strongly_convex_max_affine_objective n m f g points x =
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m : ℕ) ↦ f j + inner ℝ (g j) (x - points j)) := sorry

/-- The scalar operator norm `‖A‖_{1,2}` from Proposition 6.28, which in the Euclidean primal
geometry equals `max_j ‖g_j‖`. -/
def strongly_convex_max_affine_operator_norm_12
    (g : Fin (m : ℕ) → E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m : ℕ) ↦ ‖g j‖)

-- Proof sketch: unfold `strongly_convex_max_affine_operator_norm_12`; the displayed finite
-- maximum is the defining formula.
/-- Expanding `strongly_convex_max_affine_operator_norm_12` gives `max_j ‖g_j‖`. -/
theorem strongly_convex_max_affine_operator_norm_12_def
    (g : Fin (m : ℕ) → E) :
    strongly_convex_max_affine_operator_norm_12 n m g =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m : ℕ) ↦ ‖g j‖) := sorry

/-- The associated dual objective
`u ↦ -(1 / 2) ‖Aᵀ u‖^2 - ⟨b, u⟩`, where
`Aᵀ u = ∑_j u_j g_j` and `b_j = ⟪g_j, x_j⟫ - f_j`. -/
def strongly_convex_max_affine_dual_objective
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) : Δ[m] → ℝ :=
  fun u ↦
    -((1 / 2 : ℝ) * ‖∑ j : Fin (m : ℕ), u j • g j‖ ^ (2 : ℕ)) -
      ∑ j : Fin (m : ℕ), u j * (inner ℝ (g j) (points j) - f j)

-- Proof sketch: unfold `strongly_convex_max_affine_dual_objective`; the displayed formula is the
-- defining expression for the associated dual objective.
/-- Evaluating `strongly_convex_max_affine_dual_objective` recovers the formula
`-(1 / 2) ‖∑_j u_j g_j‖^2 - ∑_j u_j (⟪g_j, x_j⟫ - f_j)`. -/
theorem strongly_convex_max_affine_dual_objective_apply
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    strongly_convex_max_affine_dual_objective n m f g points u =
      -((1 / 2 : ℝ) * ‖∑ j : Fin (m : ℕ), u j • g j‖ ^ (2 : ℕ)) -
        ∑ j : Fin (m : ℕ), u j * (inner ℝ (g j) (points j) - f j) := sorry

-- Proof sketch: specialize the Chapter 6 rate theorem for scheme `(6.2.37)` to the objective
-- `strongly_convex_max_affine_objective n m f g points`, the associated dual objective
-- `strongly_convex_max_affine_dual_objective n m f g points`, the entropy budget
-- `D₂ = log m`, and the smoothness constant
-- `L₂(φ) = (strongly_convex_max_affine_operator_norm_12 n m g)^2`.
/-- Proposition 6.28 [Chapter6_2.json:92]: for the objective
`x ↦ (1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)` and the associated dual objective
`u ↦ -(1 / 2) ‖∑_j u_j g_j‖^2 - ∑_j u_j (⟪g_j, x_j⟫ - f_j)`, if the averaged iterates of
scheme `(6.2.37)` satisfy the entropy-smoothed lower approximation with budget `μ log m` and the
stagewise excessive-gap inequality at
`μ₂,k = 4 ‖A‖_{1,2}^2 / ((k + 1) (k + 2))`, then
`f(x̄_k) - φ(ū_k) ≤ 4 log m · ‖A‖_{1,2}^2 / ((k + 1) (k + 2))`. -/
theorem strongly_convex_max_affine_primal_dual_gap_le_entropy_rate
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E)
    (fμ₂ : ℝ → E → ℝ) (barx : ℕ → E) (baru : ℕ → Δ[m])
    (happrox :
      ∀ μ x,
        strongly_convex_max_affine_objective n m f g points x - μ * Real.log (m : ℝ) ≤
          fμ₂ μ x)
    (hscheme :
      ∀ k : ℕ,
        fμ₂
            ((4 * (strongly_convex_max_affine_operator_norm_12 n m g) ^ (2 : ℕ)) /
              (((k : ℝ) + 1) * ((k : ℝ) + 2)))
            (barx k) ≤
          strongly_convex_max_affine_dual_objective n m f g points (baru k))
    (k : ℕ) :
    strongly_convex_max_affine_objective n m f g points (barx k) -
        strongly_convex_max_affine_dual_objective n m f g points (baru k) ≤
      (4 * Real.log (m : ℝ) * (strongly_convex_max_affine_operator_norm_12 n m g) ^ (2 : ℕ)) /
        (((k : ℝ) + 1) * ((k : ℝ) + 2)) := sorry

end
