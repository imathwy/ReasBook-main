import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Proposition_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped FirstOrderSubdifferential

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/- Proposition 15.3 is a `bridge/view` item. The `core/canonical` owner remains Chapter 3's
`extendedRealSubdifferential`; `euclideanSubdifferential` is only its finite-dimensional vector-side view; and
the `source-facing` Chapter 15 data are the ADMM affine subproblem objectives and the dual
optimality condition from equation (15.5), reused from their canonical owner in Proposition 15.2.
The only extra hypothesis needed for the individual argmin/subgradient equivalences is nonempty
`effective_domain`, excluding the degenerate `⊤` case in Fermat's criterion. -/

recall euclideanSubdifferential
recall mem_euclideanSubdifferential_iff
recall isMinOn_univ_iff_zero_mem_subdifferential

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Proposition 15.3: zero is a subgradient of the affine perturbation
`u ↦ ⟪a, u⟫ + h(u)` at `x` exactly when `-a` belongs to the Euclidean extendedRealSubdifferential of `h`
at `x`. -/
theorem zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
    (h : E → EReal) (a x : E) :
    (0 : Module.Dual ℝ E) ∈
        extendedRealSubdifferential (fun u ↦ ((inner ℝ a u : ℝ) : EReal) + h u) x ↔
      -a ∈ euclideanSubdifferential h x := by
  let perturbation : E → EReal := fun u ↦ ((inner ℝ a u : ℝ) : EReal) + h u
  have perturbation_mem_effective_domain_iff (u : E) :
      u ∈ effective_domain perturbation ↔ u ∈ effective_domain h := by
    constructor
    · intro hu
      have hu_ne_top : h u ≠ ⊤ := by
        intro hhu_top
        have hsum_top : perturbation u = ⊤ := by
          simp [perturbation, hhu_top, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]
        exact hu.ne hsum_top
      exact lt_top_iff_ne_top.mpr hu_ne_top
    · intro hu
      have hu_lt_top : h u < ⊤ := hu
      simpa [perturbation, effective_domain] using
        EReal.add_lt_top (EReal.coe_ne_top (inner ℝ a u)) hu_lt_top.ne
  -- Rewrite both sides to the owner subgradient inequalities before comparing the affine terms.
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · rintro ⟨hx, hzero⟩
    refine ⟨?_, ?_⟩
    · -- The linear perturbation is everywhere finite, so it does not change the effective domain.
      exact (perturbation_mem_effective_domain_iff x).1 hx
    · -- Move the affine inner-product term to the right-hand side of the subgradient inequality.
      intro y hy
      have hy_perturbation : y ∈ effective_domain perturbation :=
        (perturbation_mem_effective_domain_iff y).2 hy
      have haux :
          h x + ((inner ℝ a x : ℝ) : EReal) ≤ h y + ((inner ℝ a y : ℝ) : EReal) := by
        simpa [perturbation, add_assoc, add_left_comm, add_comm, ge_iff_le] using
          hzero y hy_perturbation
      have hstep :
          h x ≤ h y + ((inner ℝ a (y - x) : ℝ) : EReal) := by
        have hsub :
            h x ≤ (h y + ((inner ℝ a y : ℝ) : EReal)) - ((inner ℝ a x : ℝ) : EReal) := by
          exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
            (.inl (EReal.coe_ne_top _))).2 (by
              simpa [add_assoc, add_left_comm, add_comm] using haux)
        have hinner :
            -(((inner ℝ a x : ℝ) : EReal)) + ((inner ℝ a y : ℝ) : EReal) =
              ((inner ℝ a (y - x) : ℝ) : EReal) := by
          calc
            -(((inner ℝ a x : ℝ) : EReal)) + ((inner ℝ a y : ℝ) : EReal) =
                (((-inner ℝ a x : ℝ) + inner ℝ a y : ℝ) : EReal) := by
                  rw [← EReal.coe_neg, EReal.coe_add]
            _ = ((inner ℝ a (y - x) : ℝ) : EReal) := by
                  congr
                  rw [inner_sub_right]
                  ring
        simpa [sub_eq_add_neg, hinner, add_assoc, add_left_comm, add_comm] using hsub
      have hsub :
          h x - ((inner ℝ a (y - x) : ℝ) : EReal) ≤ h y :=
        EReal.sub_le_of_le_add' (by simpa [add_comm, add_left_comm, add_assoc] using hstep)
      simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply, sub_eq_add_neg, inner_neg_left]
        using hsub
  · rintro ⟨hx, hsubgrad⟩
    refine ⟨?_, ?_⟩
    · -- The same effective-domain simplification works in the reverse direction.
      exact (perturbation_mem_effective_domain_iff x).2 hx
    · -- Reinsert the affine term to recover zero-subgradient membership for the perturbation.
      intro y hy
      have hy_h : y ∈ effective_domain h := (perturbation_mem_effective_domain_iff y).1 hy
      have hsub :
          h x - ((inner ℝ a (y - x) : ℝ) : EReal) ≤ h y := by
        simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply, sub_eq_add_neg, inner_neg_left]
          using hsubgrad y hy_h
      have hstep : h x ≤ h y + ((inner ℝ a (y - x) : ℝ) : EReal) := by
        exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
          (.inl (EReal.coe_ne_top _))).1 hsub
      have haux :
          h x + ((inner ℝ a x : ℝ) : EReal) ≤ h y + ((inner ℝ a y : ℝ) : EReal) := by
        have hbase :
            h x + ((inner ℝ a x : ℝ) : EReal) ≤
              (h y + ((inner ℝ a (y - x) : ℝ) : EReal)) + ((inner ℝ a x : ℝ) : EReal) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hstep (((inner ℝ a x : ℝ) : EReal))
        have hinner :
            ((inner ℝ a (y - x) : ℝ) : EReal) + ((inner ℝ a x : ℝ) : EReal) =
              ((inner ℝ a y : ℝ) : EReal) := by
          calc
            ((inner ℝ a (y - x) : ℝ) : EReal) + ((inner ℝ a x : ℝ) : EReal) =
                (((inner ℝ a (y - x) : ℝ) + inner ℝ a x : ℝ) : EReal) := by
                  rw [EReal.coe_add]
            _ = ((inner ℝ a y : ℝ) : EReal) := by
                  congr
                  rw [inner_sub_right]
                  ring
        calc
          h x + ((inner ℝ a x : ℝ) : EReal) ≤
              (h y + ((inner ℝ a (y - x) : ℝ) : EReal)) + ((inner ℝ a x : ℝ) : EReal) := hbase
          _ = h y + ((inner ℝ a y : ℝ) : EReal) := by
            rw [add_assoc, hinner]
      simpa [perturbation, add_assoc, add_left_comm, add_comm, ge_iff_le] using haux

end

section

variable {X : Type u} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- Proof sketch: apply Fermat's criterion to the affine perturbation
-- `x ↦ ⟪Aᵀ y, x⟫ + h₁(x)` and use the affine-linear extendedRealSubdifferential rule to move the linear term
-- to the other side, yielding the Euclidean/vector-side Chapter 3 condition
-- `-A.adjoint y ∈ euclideanSubdifferential h₁ x`.
/-- A point minimizes the `x`-subproblem from Proposition 15.2 exactly when `-Aᵀ y` belongs to
the Euclidean Chapter 3 extendedRealSubdifferential of `h₁` at that point. -/
theorem mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_dom : (effective_domain h₁).Nonempty)
    (y : Y) (x : X) :
    x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) ↔
      -A.adjoint y ∈ euclideanSubdifferential h₁ x := by
  obtain ⟨x₀, hx₀⟩ := hh₁_dom
  have hhx_dom : (effective_domain (admm_x_subproblem h₁ A y)).Nonempty := by
    refine ⟨x₀, ?_⟩
    simpa [admm_x_subproblem_apply, effective_domain] using
      EReal.add_lt_top (EReal.coe_ne_top (inner ℝ (A.adjoint y) x₀)) hx₀.ne
  -- Rewrite the unconstrained minimizer clause as Fermat's zero-subgradient condition.
  rw [mem_unconstrained_problem_solutions_iff]
  rw [isMinOn_univ_iff_zero_mem_subdifferential (f := admm_x_subproblem h₁ A y) hhx_dom]
  -- Then normalize the affine perturbation to the Euclidean/vector-side subgradient statement.
  simpa [admm_x_subproblem_apply] using
    (zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
      h₁ (A.adjoint y) x)

end

section

variable {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- Proof sketch: apply the same Fermat-plus-affine-perturbation argument to the `z`-subproblem
-- `z ↦ ⟪Bᵀ y, z⟫ + h₂(z)`, again stated through the Euclidean bridge owner.
/-- A point minimizes the `z`-subproblem from Proposition 15.2 exactly when `-Bᵀ y` belongs to
the Euclidean Chapter 3 extendedRealSubdifferential of `h₂` at that point. -/
theorem mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_dom : (effective_domain h₂).Nonempty)
    (y : Y) (z : Z) :
    z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) ↔
      -B.adjoint y ∈ euclideanSubdifferential h₂ z := by
  obtain ⟨z₀, hz₀⟩ := hh₂_dom
  have hhz_dom : (effective_domain (admm_z_subproblem h₂ B y)).Nonempty := by
    refine ⟨z₀, ?_⟩
    simpa [admm_z_subproblem_apply, effective_domain] using
      EReal.add_lt_top (EReal.coe_ne_top (inner ℝ (B.adjoint y) z₀)) hz₀.ne
  -- The `z`-subproblem is the same Fermat-plus-affine-perturbation argument as the `x`-case.
  rw [mem_unconstrained_problem_solutions_iff]
  rw [isMinOn_univ_iff_zero_mem_subdifferential (f := admm_z_subproblem h₂ B y) hhz_dom]
  simpa [admm_z_subproblem_apply] using
    (zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
      h₂ (B.adjoint y) z)

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- Proof sketch: start from Proposition 15.2, which rewrites equation (15.5) as the existence of
-- primal witnesses solving the `x`- and `z`-subproblems together with the affine update (15.6).
-- Then replace each `arg min` clause by the corresponding extendedRealSubdifferential condition using the two
-- preceding bridge lemmas.
/-- Proposition 15.3: under the Chapter 15 proper/closed/convex hypotheses on `h₁` and `h₂`,
equation (15.5) is equivalent to the existence of primal witnesses `x^(k+1)` and `z^(k+1)`
satisfying the affine update (15.6) and the extendedRealSubdifferential optimality conditions corresponding to
(15.7) and (15.8). -/
theorem admm_dual_optimality_condition_iff_exists_primal_subgradient_and_affine_update
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y)
    (hPair : IsADMMConvexObjectivePair h₁ h₂) :
    admm_dual_optimality_condition ρ h₁ h₂ A B c yk yNext ↔
      ∃ xNext zNext,
        -A.adjoint yNext ∈ euclideanSubdifferential h₁ xNext ∧
          -B.adjoint yNext ∈ euclideanSubdifferential h₂ zNext ∧
            yNext = yk + ρ • (A xNext + B zNext - c) := by
  let hh₁_dom : (effective_domain h₁).Nonempty :=
    hPair.toIsProperExtendedRealFunction.effective_domain_nonempty
  let hh₂_dom : (effective_domain h₂).Nonempty :=
    hPair.h₂_proper.effective_domain_nonempty
  constructor
  · rintro ⟨xNext, hxDual, zNext, hzDual, hyNext⟩
    -- Convert the two conjugate-subgradient witnesses into primal argmin witnesses, then into
    -- the Euclidean subgradient conditions (15.7) and (15.8).
    refine ⟨xNext, zNext, ?_, ?_, hyNext⟩
    · exact
        (mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₁ A hh₁_dom yNext xNext).1
          ((eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
            h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
            yNext xNext).1 hxDual)
    · exact
        (mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₂ B hh₂_dom yNext zNext).1
          ((eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
            h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
            yNext zNext).1 hzDual)
  · rintro ⟨xNext, zNext, hxNext, hzNext, hyNext⟩
    -- Reverse the two bridges to recover the source-facing dual optimality condition (15.5).
    refine ⟨xNext, ?_, zNext, ?_, hyNext⟩
    · exact
        (eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
          h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
          yNext xNext).2
          ((mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
            h₁ A hh₁_dom yNext xNext).2 hxNext)
    · exact
        (eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
          h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
          yNext zNext).2
          ((mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
            h₂ B hh₂_dom yNext zNext).2 hzNext)

end
