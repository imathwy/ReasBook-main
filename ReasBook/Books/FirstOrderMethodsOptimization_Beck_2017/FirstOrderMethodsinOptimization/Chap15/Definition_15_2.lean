import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

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
