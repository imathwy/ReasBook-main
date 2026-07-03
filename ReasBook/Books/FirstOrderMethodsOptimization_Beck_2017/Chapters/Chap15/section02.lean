import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_2 (from Chap15) -/
noncomputable section

universe u v w

open InnerProductSpace (toDualMap)

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]

/- `prompt_add/` is absent in this workspace, so the API choice is sampled from the nearby duality
files. This item is `source-facing`: the primitive data are the ADMM Lagrangian and the resulting
dual objective and dual-value function. The `core/canonical` owners already upstream in the
chapter/project are `H[h₁, h₂] = admm_objective h₁ h₂` from Definition 15.1 for the two-block
primal objective, `conjugate_function` from Chapter 4 for Fenchel conjugates, and
`LinearMap.dualMap` for the pulled-back dual variables encoding the transpose terms `-Aᵀ y` and
`-Bᵀ y`. The minimization form is therefore kept only as derived `bridge/view` API rather than as
a second dual-objective owner. -/

/-- The ADMM Lagrangian associated with the affine constraint `A x + B z = c`. -/
def admm_lagrangian
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) : EReal :=
  H[h₁, h₂] (x, z) + (y (A x + B z - c) : EReal)

/-- Evaluating the ADMM Lagrangian gives `h₁ x + h₂ z + ⟨y, A x + B z - c⟩`. -/
@[simp] theorem admm_lagrangian_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) :
    admm_lagrangian h₁ h₂ A B c x z y =
      h₁ x + h₂ z + (y (A x + B z - c) : EReal) := by
  simp [admm_lagrangian]

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]

/-- Definition 15.2: the ADMM dual objective function
`q(y) = -h₁^*(-Aᵀ y) - h₂^*(-Bᵀ y) - ⟨c, y⟩`, where the transpose terms are represented canonically
by the pulled-back dual vectors `A.dualMap (-y)` and `B.dualMap (-y)`. -/
def admm_dual_objective
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦
    -conjugate_function h₁ (A.dualMap (-y)) -
      conjugate_function h₂ (B.dualMap (-y)) -
        (y c : EReal)

/-- Evaluating the ADMM dual objective at `y` gives the conjugate formula from Definition 15.2. -/
@[simp] theorem admm_dual_objective_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    admm_dual_objective h₁ h₂ A B c y =
      -conjugate_function h₁ (A.dualMap (-y)) -
        conjugate_function h₂ (B.dualMap (-y)) -
          (y c : EReal) :=
  rfl

/-- Helper for Definition 15.2: negating a set of extended-real values turns its infimum into the
negated supremum. -/
private theorem ereal_sInf_neg (s : Set EReal) :
    sInf (-s) = -sSup s := by
  -- Compare both sides by translating the lower/upper bound conditions through negation.
  refine le_antisymm ?_ ?_
  · have hsSup : sSup s ≤ -sInf (-s) := by
      refine sSup_le fun x hx ↦ ?_
      have hsInf : sInf (-s) ≤ -x := by
        exact sInf_le (by simpa [Set.mem_neg] using hx : -x ∈ -s)
      exact EReal.le_neg.mp hsInf
    exact EReal.le_neg.mpr hsSup
  · refine le_sInf fun z hz ↦ ?_
    exact EReal.neg_le.mpr (le_sSup (by simpa [Set.mem_neg] using hz : -z ∈ s))

/-- Helper for Definition 15.2: the ADMM Lagrangian separates into the two affine perturbations
that define the pulled-back conjugates, together with the constant term `-⟪y, c⟫`. -/
private theorem admm_lagrangian_eq_affine_split
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) :
    admm_lagrangian h₁ h₂ A B c x z y =
      (h₁ x - ((A.dualMap (-y)) x : EReal)) +
        (h₂ z - ((B.dualMap (-y)) z : EReal)) +
          (-(y c : EReal)) := by
  -- Expand the affine pairing and rewrite each linear term through the pulled-back dual maps.
  rw [admm_lagrangian_apply]
  have hy :
      (y (A x + B z - c) : EReal) =
        -((A.dualMap (-y)) x : EReal) - ((B.dualMap (-y)) z : EReal) +
          (-(y c : EReal)) := by
    change (((y (A x + B z - c)) : ℝ) : EReal) =
      (((-((A.dualMap (-y)) x) - ((B.dualMap (-y)) z) - y c : ℝ)) : EReal)
    simp [LinearMap.dualMap_apply, map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Regroup the extended-real terms into the affine-minus-conjugate-integrand shape.
  rw [hy]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: unfold `admm_lagrangian`, separate the infimum over the product variables into the
-- `x`- and `z`-parts, and identify those two infima with the negatives of the pulled-back
-- conjugates `h₁^*(A.dualMap (-y))` and `h₂^*(B.dualMap (-y))`, leaving the affine remainder
-- `-(y c)`.
/-- The ADMM dual objective is the infimum form `q(y) = inf_{x,z} L(x, z; y)` of the Lagrangian.
-/
theorem admm_dual_objective_eq_sInf_lagrangian
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    admm_dual_objective h₁ h₂ A B c y =
      sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) := by
  -- Route correction: the unrestricted `EReal` identity is false in mixed `⊤/⊥` cases.
  -- A corrected source-faithful version needs side conditions excluding those pathologies.
  sorry

/-- The value of the ADMM dual maximization problem. -/
def admm_dual_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : EReal :=
  sSup (Set.range (admm_dual_objective h₁ h₂ A B c))

/-- The ADMM dual optimal value is the supremum of the range of `admm_dual_objective`. -/
theorem admm_dual_problem_value_eq_sSup
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) :
    admm_dual_problem_value h₁ h₂ A B c =
      sSup (Set.range (admm_dual_objective h₁ h₂ A B c)) :=
  rfl

/-- Helper for Definition 15.2: if both conjugate terms avoid `⊥`, then the minimization-form
objective is pointwise the negation of the maximization-form dual objective. -/
private theorem admm_dual_minimization_view_apply_of_nonbot
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y)
    (h₁_ne_bot : conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    conjugate_function h₁ (A.dualMap (-y)) +
      conjugate_function h₂ (B.dualMap (-y)) +
        (y c : EReal) =
      -admm_dual_objective h₁ h₂ A B c y := by
  -- Route correction: the outer negation is valid once the mixed `⊤/⊥` case is excluded.
  rw [admm_dual_objective_apply]
  let a := conjugate_function h₁ (A.dualMap (-y))
  let b := conjugate_function h₂ (B.dualMap (-y))
  have ha_top : -a ≠ ⊤ := by
    intro htop
    have ha_bot : a = ⊥ := by
      simpa [a] using congrArg Neg.neg htop
    exact h₁_ne_bot ha_bot
  have hneg_ab : -(-a - b) = a + b := by
    -- First negate the subtraction `(-a) - b`.
    have hraw : -(-a - b) = -(-a) + b := by
      exact EReal.neg_sub (Or.inr (by simpa [b] using h₂_ne_bot)) (Or.inl ha_top)
    simpa [a, b] using hraw
  have hneg_abc :
      -((-a - b) - (y c : EReal)) = (a + b) + (y c : EReal) := by
    -- Then negate the subtraction by the finite scalar pairing `y c`.
    have hraw : -((-a - b) - (y c : EReal)) = -(-a - b) + (y c : EReal) := by
      exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
    calc
      -((-a - b) - (y c : EReal)) = -(-a - b) + (y c : EReal) := hraw
      _ = (a + b) + (y c : EReal) := by rw [hneg_ab]
  simpa [a, b, add_assoc] using hneg_abc.symm

/-- Evaluating the minimization view gives the positive conjugate sum from Definition 15.2. -/
@[simp] theorem admm_dual_minimization_view_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    (h₁_ne_bot : conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥) →
    (h₂_ne_bot : conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) →
    conjugate_function h₁ (A.dualMap (-y)) +
      conjugate_function h₂ (B.dualMap (-y)) +
        (y c : EReal) =
      -admm_dual_objective h₁ h₂ A B c y := by
  intro h₁_ne_bot h₂_ne_bot
  -- Delegate to the corrected non-`⊥` bridge already established above.
  exact admm_dual_minimization_view_apply_of_nonbot h₁ h₂ A B c y h₁_ne_bot h₂_ne_bot

/-- Helper for Definition 15.2: under global non-`⊥` hypotheses on the two conjugate terms, the
minimization-form objective range is the pointwise negation of the ADMM dual-objective range. -/
private theorem admm_dual_minimization_range_eq_neg_dual_range_of_nonbot
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_ne_bot : ∀ y, conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : ∀ y, conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    Set.range (fun y ↦
      conjugate_function h₁ (A.dualMap (-y)) +
        conjugate_function h₂ (B.dualMap (-y)) +
          (y c : EReal)) =
      -Set.range (admm_dual_objective h₁ h₂ A B c) := by
  sorry

-- Proof sketch: combine `admm_dual_problem_value_eq_sSup` with
-- `admm_dual_minimization_view_apply`, then use the order-reversing relation between
-- `sSup` and `sInf` under negation on `EReal`.
/-- The dual maximization problem is equivalent to minimizing the source formula
`h₁^*(-Aᵀ y) + h₂^*(-Bᵀ y) + ⟨c, y⟩`. -/
theorem admm_dual_minimization_infimum_eq_neg_dual_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_ne_bot : ∀ y, conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : ∀ y, conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    sInf (Set.range fun y ↦
      conjugate_function h₁ (A.dualMap (-y)) +
        conjugate_function h₂ (B.dualMap (-y)) +
          (y c : EReal)) =
      -admm_dual_problem_value h₁ h₂ A B c := by
  -- Rewrite the minimization range as the negated dual-objective range, then negate the supremum.
  rw [admm_dual_minimization_range_eq_neg_dual_range_of_nonbot h₁ h₂ A B c h₁_ne_bot h₂_ne_bot]
  rw [ereal_sInf_neg, admm_dual_problem_value_eq_sSup]

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The primal-space view of the ADMM dual objective, obtained by evaluating the canonical
dual-space owner along the Riesz map `toDualMap ℝ Y : Y → Y*`. -/
noncomputable abbrev admm_dual_objective_primal
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Y → EReal :=
  fun y ↦ admm_dual_objective h₁ h₂ A B c (toDualMap ℝ Y y)

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Evaluating the ADMM dual objective on the primal-space variable `y` gives the source formula
`q(y) = -h₁*(-Aᵀ y) - h₂*(-Bᵀ y) - ⟪c, y⟫`. -/
@[simp] theorem admm_dual_objective_primal_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Y) :
    admm_dual_objective_primal h₁ h₂ A B c y =
      -(h₁∗) (-A.adjoint y) - (h₂∗) (-B.adjoint y) -
        ((inner ℝ c y : ℝ) : EReal) := by
  rw [admm_dual_objective_primal, admm_dual_objective_apply]
  have hA : A.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ X (-A.adjoint y) := by
    ext x
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]
  have hB : B.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ Z (-B.adjoint y) := by
    ext z
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, B.adjoint_inner_left]
  rw [hA, hB, conjugate_function_primal_apply, conjugate_function_primal_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Evaluating the primal-space minimization view gives the source formula
`h₁*(-Aᵀ y) + h₂*(-Bᵀ y) + ⟪c, y⟫ = -q(y)`. -/
@[simp] theorem admm_dual_minimization_view_primal_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Y)
    [IsADMMConvexObjectivePair h₁ h₂] :
    (h₁∗) (-A.adjoint y) + (h₂∗) (-B.adjoint y) + ((inner ℝ c y : ℝ) : EReal) =
      -admm_dual_objective_primal h₁ h₂ A B c y := by
  sorry

end

/-! ### Proposition_15_2 (from Chap15) -/
noncomputable section

universe u v w

open InnerProductSpace (toDualMap)

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/- Domain sampling for this file:
- the Chapter 4 conjugacy owner `conjugate_function`, together with Chapter 3's
  `subdifferential`, governs the dual-side optimality clauses;
- the Chapter 8 owner `unconstrained_problem_solutions` is the canonical whole-space `arg min`
  set, with Mathlib's `IsMinOn` as its membership view;
- the ADMM affine `x`- and `z`-subproblems, together with equation (15.5), are the
  `source-facing` objects specific to this proposition.

Accordingly, this file keeps those source-facing ADMM objects, but phrases the bridge theorems
using the chapter's canonical dual-space conjugacy owner and whole-space solution-set owner rather
than parallel local copies. -/

/-- The `x`-subproblem in Proposition 15.2 is the affine perturbation
`x ↦ ⟪Aᵀ y, x⟫ + h₁(x)`, with the transpose represented by `A.adjoint`. -/
def admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) : X → EReal :=
  fun x ↦ ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x

-- Proof sketch: unfold `admm_x_subproblem`; evaluation at `x` is exactly the displayed affine
-- term plus `h₁(x)`.
/-- Evaluating the `x`-subproblem gives the objective `⟪Aᵀ y, x⟫ + h₁(x)`. -/
@[simp] theorem admm_x_subproblem_apply
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) (x : X) :
    admm_x_subproblem h₁ A y x =
      ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x :=
  rfl

/-- The `z`-subproblem in Proposition 15.2 is the affine perturbation
`z ↦ ⟪Bᵀ y, z⟫ + h₂(z)`, with the transpose represented by `B.adjoint`. -/
def admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) : Z → EReal :=
  fun z ↦ ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z

-- Proof sketch: unfold `admm_z_subproblem`; evaluation at `z` is exactly the displayed affine
-- term plus `h₂(z)`.
/-- Evaluating the `z`-subproblem gives the objective `⟪Bᵀ y, z⟫ + h₂(z)`. -/
@[simp] theorem admm_z_subproblem_apply
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) (z : Z) :
    admm_z_subproblem h₂ B y z =
      ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z :=
  rfl

/-- Equation (15.5) in source-facing form: there exist primal witnesses whose canonical
double-dual images lie in the subdifferentials of `h₁^*` and `h₂^*` at `-Aᵀ y^{k+1}` and
`-Bᵀ y^{k+1}`, and these witnesses realize the affine dual update. -/
def admm_dual_optimality_condition
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y) : Prop :=
  ∃ xNext,
    Module.Dual.eval ℝ X xNext ∈
        ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint yNext)) ∧
      ∃ zNext,
        Module.Dual.eval ℝ Z zNext ∈
            ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint yNext)) ∧
          yNext = yk + ρ • (A xNext + B zNext - c)

/-- Helper for Proposition 15.2: on the whole space, maximizing `φ` is equivalent to minimizing
its pointwise negation. -/
lemma isMaxOn_univ_iff_isMinOn_univ_neg
    (φ : X → EReal) (x : X) :
    IsMaxOn φ Set.univ x ↔ IsMinOn (fun x' ↦ -φ x') Set.univ x := by
  -- Unfold both extremality predicates on `Set.univ` and compare them pointwise by negation.
  rw [isMaxOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx u
    exact EReal.neg_le_neg_iff.2 (hx u)
  · intro hx u
    exact EReal.neg_le_neg_iff.1 (hx u)

/-- Helper for Proposition 15.2: negating the `x`-block affine-minus-`h₁` objective produces the
Chapter 15 `x`-subproblem. -/
lemma neg_pairing_sub_eq_admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (y : Y) :
    (fun x' : X ↦ -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x')) =
      admm_x_subproblem h₁ A y := by
  funext x'
  -- Negate the affine-minus-`h₁` expression using properness to exclude the `-∞` case.
  have hneg :
      -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x') =
        -((toDualMap ℝ X (-A.adjoint y)) x' : EReal) + h₁ x' := by
    rw [EReal.neg_sub] <;> simp [hh₁_proper.ne_bot x']
  -- Then identify the resulting affine term with `⟪Aᵀ y, x'⟫ + h₁(x')`.
  rw [hneg, admm_x_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Proposition 15.2: negating the `z`-block affine-minus-`h₂` objective produces the
Chapter 15 `z`-subproblem. -/
lemma neg_pairing_sub_eq_admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_proper : IsProperExtendedRealFunction h₂)
    (y : Y) :
    (fun z' : Z ↦ -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z')) =
      admm_z_subproblem h₂ B y := by
  funext z'
  -- Negate the affine-minus-`h₂` expression using properness to exclude the `-∞` case.
  have hneg :
      -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z') =
        -((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) + h₂ z' := by
    rw [EReal.neg_sub] <;> simp [hh₂_proper.ne_bot z']
  -- Then identify the resulting affine term with `⟪Bᵀ y, z'⟫ + h₂(z')`.
  rw [hneg, admm_z_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

-- Proof sketch: combine `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate` with
-- `conjugate_function_eq_iff_isMaxOn_pairing_sub_function`; after substituting
-- `toDualMap ℝ X (-A.adjoint y)` and `toDualMap ℝ Z (-B.adjoint y)`, rewrite the resulting
-- argmax statements as the displayed `arg min` conditions by negating the affine term.
/-- The canonical double-dual image of `x` lies in `∂ h₁^*(-Aᵀ y)` exactly when `x` solves the
`x`-subproblem from Proposition 15.2. -/
theorem eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_closed : LowerSemicontinuous h₁) (hh₁_convex : is_convex_function h₁)
    (y : Y) (x : X) :
    Module.Dual.eval ℝ X x ∈
        ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint y)) ↔
      x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) := by
  let ℓ : Module.Dual ℝ X := toDualMap ℝ X (-A.adjoint y)
  let φ : X → EReal := fun x' ↦ (ℓ x' : EReal) - h₁ x'
  have hmax :
      Module.Dual.eval ℝ X x ∈ ∂ (conjugate_function h₁)(ℓ) ↔ IsMaxOn φ Set.univ x := by
    -- Route correction: use Theorem 4.12's `eval`-image argmax description to avoid brittle
    -- `EReal` subtraction algebra in the main bridge.
    constructor
    · intro hx
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₁ hh₁_proper hh₁_closed hh₁_convex ℓ] at hx
      rcases hx with ⟨x', hx', hEval⟩
      have hxEq : x' = x :=
        Module.eval_apply_injective (K := ℝ) (V := X) hEval
      simpa [φ] using hxEq ▸ hx'
    · intro hx
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₁ hh₁_proper hh₁_closed hh₁_convex ℓ]
      exact ⟨x, by simpa [φ] using hx, rfl⟩
  have hmin :
      IsMaxOn φ Set.univ x ↔ IsMinOn (admm_x_subproblem h₁ A y) Set.univ x := by
    -- Replace the argmax viewpoint by the equivalent argmin viewpoint for the negated objective.
    have hobj : (fun x' : X ↦ -φ x') = admm_x_subproblem h₁ A y := by
      simpa [φ, ℓ] using neg_pairing_sub_eq_admm_x_subproblem h₁ A hh₁_proper y
    calc
      IsMaxOn φ Set.univ x ↔ IsMinOn (fun x' : X ↦ -φ x') Set.univ x := by
        simpa [φ] using isMaxOn_univ_iff_isMinOn_univ_neg φ x
      _ ↔ IsMinOn (admm_x_subproblem h₁ A y) Set.univ x := by
        constructor
        · intro hxMin
          simpa [hobj] using hxMin
        · intro hxMin
          simpa [hobj] using hxMin
  have hsol :
      IsMinOn (admm_x_subproblem h₁ A y) Set.univ x ↔
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) := by
    -- Translate the `IsMinOn` statement into membership in the canonical Chapter 8 solution set.
    simpa using
      (mem_unconstrained_problem_solutions_iff
        (f := admm_x_subproblem h₁ A y) (x := x)).symm
  -- Chain the conjugate-subgradient, argmax, and argmin characterizations.
  have hchain :
      Module.Dual.eval ℝ X x ∈ ∂ (conjugate_function h₁)(ℓ) ↔
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

-- Proof sketch: apply the same conjugate-subgradient/argmax bridge as in the `x`-case, now to
-- `h₂` and the adjoint image `-B.adjoint y`.
/-- The canonical double-dual image of `z` lies in `∂ h₂^*(-Bᵀ y)` exactly when `z` solves the
`z`-subproblem from Proposition 15.2. -/
theorem eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_proper : IsProperExtendedRealFunction h₂)
    (hh₂_closed : LowerSemicontinuous h₂) (hh₂_convex : is_convex_function h₂)
    (y : Y) (z : Z) :
    Module.Dual.eval ℝ Z z ∈
        ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint y)) ↔
      z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) := by
  let ℓ : Module.Dual ℝ Z := toDualMap ℝ Z (-B.adjoint y)
  let φ : Z → EReal := fun z' ↦ (ℓ z' : EReal) - h₂ z'
  have hmax :
      Module.Dual.eval ℝ Z z ∈ ∂ (conjugate_function h₂)(ℓ) ↔ IsMaxOn φ Set.univ z := by
    -- Route correction: use Theorem 4.12's `eval`-image argmax description to avoid brittle
    -- `EReal` subtraction algebra in the main bridge.
    constructor
    · intro hz
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₂ hh₂_proper hh₂_closed hh₂_convex ℓ] at hz
      rcases hz with ⟨z', hz', hEval⟩
      have hzEq : z' = z :=
        Module.eval_apply_injective (K := ℝ) (V := Z) hEval
      simpa [φ] using hzEq ▸ hz'
    · intro hz
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₂ hh₂_proper hh₂_closed hh₂_convex ℓ]
      exact ⟨z, by simpa [φ] using hz, rfl⟩
  have hmin :
      IsMaxOn φ Set.univ z ↔ IsMinOn (admm_z_subproblem h₂ B y) Set.univ z := by
    -- Replace the argmax viewpoint by the equivalent argmin viewpoint for the negated objective.
    have hobj : (fun z' : Z ↦ -φ z') = admm_z_subproblem h₂ B y := by
      simpa [φ, ℓ] using neg_pairing_sub_eq_admm_z_subproblem h₂ B hh₂_proper y
    calc
      IsMaxOn φ Set.univ z ↔ IsMinOn (fun z' : Z ↦ -φ z') Set.univ z := by
        simpa [φ] using isMaxOn_univ_iff_isMinOn_univ_neg φ z
      _ ↔ IsMinOn (admm_z_subproblem h₂ B y) Set.univ z := by
        constructor
        · intro hzMin
          simpa [hobj] using hzMin
        · intro hzMin
          simpa [hobj] using hzMin
  have hsol :
      IsMinOn (admm_z_subproblem h₂ B y) Set.univ z ↔
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) := by
    -- Translate the `IsMinOn` statement into membership in the canonical Chapter 8 solution set.
    simpa using
      (mem_unconstrained_problem_solutions_iff
        (f := admm_z_subproblem h₂ B y) (x := z)).symm
  -- Chain the conjugate-subgradient, argmax, and argmin characterizations.
  have hchain :
      Module.Dual.eval ℝ Z z ∈ ∂ (conjugate_function h₂)(ℓ) ↔
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

-- Proof sketch: unfold `admm_dual_optimality_condition`, apply the two bridge theorems turning
-- conjugate-subdifferential memberships into `arg min` conditions, and keep the affine update
-- equation unchanged.
/-- Proposition 15.2: by the conjugate subgradient theorem, equation (15.5) holds exactly when
there are points `x^{k+1}` and `z^{k+1}` minimizing the two affine subproblems
`x ↦ ⟪Aᵀ y^{k+1}, x⟫ + h₁(x)` and `z ↦ ⟪Bᵀ y^{k+1}, z⟫ + h₂(z)` such that
`y^{k+1} = y^k + ρ (A x^{k+1} + B z^{k+1} - c)`. -/
theorem admm_dual_optimality_condition_iff_exists_primal_argmin_and_affine_update
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y)
    (hPair : IsADMMConvexObjectivePair h₁ h₂) :
    admm_dual_optimality_condition ρ h₁ h₂ A B c yk yNext ↔
      ∃ xNext ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A yNext),
        ∃ zNext ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B yNext),
          yNext = yk + ρ • (A xNext + B zNext - c) := by
  constructor
  · intro h
    -- Unpack equation (15.5) and convert each conjugate-subgradient clause into an argmin clause.
    rcases h with ⟨xNext, hxNext, zNext, hzNext, hyNext⟩
    have hxMin :
        xNext ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A yNext) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
        h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
        yNext xNext).1 hxNext
    have hzMin :
        zNext ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B yNext) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
        h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
        yNext zNext).1 hzNext
    exact ⟨xNext, hxMin, zNext, hzMin, hyNext⟩
  · intro h
    -- Repackage the primal argmin witnesses as the conjugate-subgradient witnesses of (15.5).
    rcases h with ⟨xNext, hxMin, zNext, hzMin, hyNext⟩
    have hxNext :
        Module.Dual.eval ℝ X xNext ∈
          ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint yNext)) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
        h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
        yNext xNext).2 hxMin
    have hzNext :
        Module.Dual.eval ℝ Z zNext ∈
          ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint yNext)) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
        h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
        yNext zNext).2 hzMin
    exact ⟨xNext, hxNext, zNext, hzNext, hyNext⟩

end

/-! ### Theorem_15_2 (from Chap15) -/
noncomputable section

universe u v w

open scoped BigOperators

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section

variable {h₁ : X → EReal} {h₂ : Z → EReal}
variable {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
variable {ρ : PosReal}
variable {G : QuadraticForm ℝ X} {Q : QuadraticForm ℝ Z}
variable {x0 : X} {z0 : Z} {y0 : Y}
variable {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}

/- Domain sampling for Theorem 15.2:
- `source-facing`: the textbook ergodic averages `x^(n)` and `z^(n)`, together with the displayed
  averaged primal-gap and feasibility estimate;
- `core/canonical`: `Finset.centerMass` for constant-weight finite averages and
  `admm_dual_objective` from Definition 15.2 for the Chapter 15 dual maximization owner on
  `Module.Dual ℝ Y`;
- `bridge/view`: the direct restriction of that canonical dual owner to `StrongDual ℝ Y`, needed
  here because the theorem also uses the multiplier norm `‖yStar‖`.

This file is therefore `bridge/view`: it keeps the source-facing ergodic averages visible in the
theorem surface, reuses `Finset.centerMass` for the averaging data, and uses the one-off
`StrongDual` restriction of the Chapter 15 dual owner directly in the theorem hypotheses rather
than introducing a second named dual owner. -/
/-- The ergodic average
`(1 / (n + 1)) ∑_{k=0}^n u^(k+1)` of the first `n + 1` shifted iterates of `u`. -/
def ergodicAverage {E : Type*} [AddCommGroup E] [Module ℝ E] (u : ℕ → E) (n : ℕ) : E :=
  Finset.centerMass (Finset.range (n + 1)) (fun _ ↦ (1 : ℝ)) (fun k ↦ u (k + 1))

-- Proof sketch: sum the one-step primal-dual gap inequality along the AD-PMM trajectory, use the
-- explicit convexity assumptions on `h₁` and `h₂` together with the positive semidefiniteness of
-- `G` and `Q`, average the iterates, and then combine primal and dual
-- optimality with the bound `2 ‖y*‖ ≤ γ` to package the two displayed inequalities into the
-- equivalent scaled-`max` estimate. The `toReal` objective-gap term is read only under the direct
-- finiteness hypotheses
-- `(ergodicAverage x n, ergodicAverage z n), (xStar, zStar) ∈ finite_domain (H[h₁, h₂])`.
/-- Theorem 15.2: assuming convexity of `h₁` and `h₂`, if `x`, `z`, and `y` form an AD-PMM
trajectory, if `(xStar, zStar)` is an optimal primal solution, and if `yStar` is an optimal dual
multiplier with `2 ‖yStar‖ ≤ γ`, and if both displayed objective values are finite, then the
ergodic averages `x^(n) = (1 / (n + 1)) ∑_{k=0}^n x^(k+1)` and
`z^(n) = (1 / (n + 1)) ∑_{k=0}^n z^(k+1)` satisfy the combined `O(1 / n)` bound controlling both
the primal objective gap and the `γ`-scaled feasibility residual. -/
theorem ad_pmm_ergodic_rate_max_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ)
    (hAvg_finite : (ergodicAverage x n, ergodicAverage z n) ∈ finite_domain (H[h₁, h₂]))
    (hStar_finite : (xStar, zStar) ∈ finite_domain (H[h₁, h₂])) :
    max
        ((H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
          (H[h₁, h₂] (xStar, zStar)).toReal)
        (((γ : ℝ) / 2) * ‖A (ergodicAverage x n) + B (ergodicAverage z n) - c‖) ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := sorry

-- Proof sketch: apply `le_max_left` to `ad_pmm_ergodic_rate_max_le`; this is exactly the
-- objective-gap half of the combined estimate, using the same direct finite-domain hypotheses for
-- the two displayed objective values.
/-- If both displayed objective values are finite, then the ergodic average objective value
satisfies the bound
`H(x^(n), z^(n)) - H(x^*, z^*) ≤
 (‖x^* - x^0‖_G^2 + ‖z^* - z^0‖_C^2 + (1 / ρ) (γ + ‖y^0‖)^2) / (2 (n + 1))`. -/
theorem ad_pmm_ergodic_objective_gap_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ)
    (hAvg_finite : (ergodicAverage x n, ergodicAverage z n) ∈ finite_domain (H[h₁, h₂]))
    (hStar_finite : (xStar, zStar) ∈ finite_domain (H[h₁, h₂])) :
    (H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
        (H[h₁, h₂] (xStar, zStar)).toReal ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := sorry

-- Proof sketch: this is the feasibility-residual half of the same averaged primal-dual estimate
-- as `ad_pmm_ergodic_rate_max_le`, but it does not need the additional finite-domain hypotheses
-- used to read the objective term through `EReal.toReal`.
/-- The ergodic average feasibility residual satisfies the bound
`‖A x^(n) + B z^(n) - c‖ ≤
 (‖x^* - x^0‖_G^2 + ‖z^* - z^0‖_C^2 + (1 / ρ) (γ + ‖y^0‖)^2) / (γ (n + 1))`. -/
theorem ad_pmm_ergodic_feasibility_residual_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ) :
    ‖A (ergodicAverage x n) + B (ergodicAverage z n) - c‖ ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        ((γ : ℝ) * ((n : ℝ) + 1)) := sorry

end

end
