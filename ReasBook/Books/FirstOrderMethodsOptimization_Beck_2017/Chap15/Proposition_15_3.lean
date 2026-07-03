import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/- Proposition 15.3 is a `bridge/view` item. The `core/canonical` owner remains Chapter 3's
`subdifferential`; `euclideanSubdifferential` is only its finite-dimensional vector-side view; and
the `source-facing` Chapter 15 data are the ADMM affine subproblem objectives and the dual
optimality condition from equation (15.5). The imported Proposition 15.2 module is currently not
available as a stable dependency in this workspace, so this file reintroduces only the minimal
earlier API needed to carry out the same source-faithful proof route for Proposition 15.3. The
only extra hypothesis needed for the individual argmin/subgradient equivalences is nonempty
`effective_domain`, excluding the degenerate `⊤` case in Fermat's criterion. -/

recall euclideanSubdifferential
recall mem_euclideanSubdifferential_iff
recall isMinOn_univ_iff_zero_mem_subdifferential

end

section

open InnerProductSpace (toDualMap)

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Helper for Proposition 15.3: the Chapter 15 `x`-subproblem is the affine perturbation
`x ↦ ⟪Aᵀ y, x⟫ + h₁(x)`. -/
def admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) : X → EReal :=
  fun x ↦ ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x

/-- Helper for Proposition 15.3: evaluating the `x`-subproblem gives the displayed affine
objective. -/
@[simp] theorem admm_x_subproblem_apply
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) (x : X) :
    admm_x_subproblem h₁ A y x =
      ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x :=
  rfl

/-- Helper for Proposition 15.3: the Chapter 15 `z`-subproblem is the affine perturbation
`z ↦ ⟪Bᵀ y, z⟫ + h₂(z)`. -/
def admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) : Z → EReal :=
  fun z ↦ ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z

/-- Helper for Proposition 15.3: evaluating the `z`-subproblem gives the displayed affine
objective. -/
@[simp] theorem admm_z_subproblem_apply
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) (z : Z) :
    admm_z_subproblem h₂ B y z =
      ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z :=
  rfl

/-- Helper for Proposition 15.3: equation (15.5) is represented by the existence of primal
witnesses whose evaluation functionals lie in the conjugate subdifferentials at
`-Aᵀ y^{k+1}` and `-Bᵀ y^{k+1}`, together with the affine update. -/
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

/-- Helper for Proposition 15.3: maximizing an objective on the whole space is equivalent to
minimizing its pointwise negation. -/
lemma isMaxOn_univ_iff_isMinOn_univ_neg
    (φ : X → EReal) (x : X) :
    IsMaxOn φ Set.univ x ↔ IsMinOn (fun x' ↦ -φ x') Set.univ x := by
  -- Unfold both whole-space extremality predicates and compare them by pointwise negation.
  rw [isMaxOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx u
    exact EReal.neg_le_neg_iff.2 (hx u)
  · intro hx u
    exact EReal.neg_le_neg_iff.1 (hx u)

/-- Helper for Proposition 15.3: negating the affine-minus-`h₁` conjugate objective yields the
Chapter 15 `x`-subproblem. -/
lemma neg_pairing_sub_eq_admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (y : Y) :
    (fun x' : X ↦ -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x')) =
      admm_x_subproblem h₁ A y := by
  funext x'
  -- Properness rules out the `-∞` case, so the negated subtraction is the expected sum.
  have hneg :
      -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x') =
        -((toDualMap ℝ X (-A.adjoint y)) x' : EReal) + h₁ x' := by
    rw [EReal.neg_sub] <;> simp [hh₁_proper.ne_bot x']
  -- Identify the resulting affine term with the adjoint inner product.
  rw [hneg, admm_x_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Proposition 15.3: negating the affine-minus-`h₂` conjugate objective yields the
Chapter 15 `z`-subproblem. -/
lemma neg_pairing_sub_eq_admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_proper : IsProperExtendedRealFunction h₂)
    (y : Y) :
    (fun z' : Z ↦ -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z')) =
      admm_z_subproblem h₂ B y := by
  funext z'
  -- Properness rules out the `-∞` case, so the negated subtraction is the expected sum.
  have hneg :
      -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z') =
        -((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) + h₂ z' := by
    rw [EReal.neg_sub] <;> simp [hh₂_proper.ne_bot z']
  -- Identify the resulting affine term with the adjoint inner product.
  rw [hneg, admm_z_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Proposition 15.3: conjugate-subgradient membership for `f*` is exactly the
argmax condition for the affine-minus-`f` objective. -/
lemma eval_mem_conjugate_subdifferential_iff_isMaxOn_affine_minus
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (y : Module.Dual ℝ E) (x : E) :
    Module.Dual.eval ℝ E x ∈ subdifferential (conjugate_function f) y ↔
      IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := by
  -- Route correction: Theorem 4.12 already packages the conjugate-side argmax description, so
  -- we use it directly instead of rebuilding Fenchel--Young subtraction identities by hand.
  constructor
  · intro hx
    rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
      f hf_proper hf_closed hf_convex y] at hx
    rcases hx with ⟨x', hx', hEval⟩
    have hxEq : x' = x :=
      Module.eval_apply_injective (K := ℝ) (V := E) hEval
    simpa using hxEq ▸ hx'
  · intro hx
    rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
      f hf_proper hf_closed hf_convex y]
    exact ⟨x, hx, rfl⟩

/-- Helper for Proposition 15.3: a conjugate-side subgradient witness for `h₁` at `-Aᵀ y` is
equivalent to solving the `x`-subproblem. -/
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
      Module.Dual.eval ℝ X x ∈ subdifferential (conjugate_function h₁) ℓ ↔
        IsMaxOn φ Set.univ x := by
    -- First express conjugate-subgradient membership through the canonical argmax description.
    simpa [φ] using
      (eval_mem_conjugate_subdifferential_iff_isMaxOn_affine_minus
        h₁ hh₁_proper hh₁_closed hh₁_convex ℓ x)
  have hmin :
      IsMaxOn φ Set.univ x ↔ IsMinOn (admm_x_subproblem h₁ A y) Set.univ x := by
    -- Then negate the objective and rewrite it to the ADMM `x`-subproblem.
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
    -- Finally pass from `IsMinOn` to the Chapter 8 solution-set owner.
    simpa using
      (mem_unconstrained_problem_solutions_iff
        (f := admm_x_subproblem h₁ A y) (x := x)).symm
  -- Chaining the three equivalences gives the desired source-faithful bridge.
  have hchain :
      Module.Dual.eval ℝ X x ∈ subdifferential (conjugate_function h₁) ℓ ↔
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

/-- Helper for Proposition 15.3: a conjugate-side subgradient witness for `h₂` at `-Bᵀ y` is
equivalent to solving the `z`-subproblem. -/
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
      Module.Dual.eval ℝ Z z ∈ subdifferential (conjugate_function h₂) ℓ ↔
        IsMaxOn φ Set.univ z := by
    -- First express conjugate-subgradient membership through the canonical argmax description.
    simpa [φ] using
      (eval_mem_conjugate_subdifferential_iff_isMaxOn_affine_minus
        h₂ hh₂_proper hh₂_closed hh₂_convex ℓ z)
  have hmin :
      IsMaxOn φ Set.univ z ↔ IsMinOn (admm_z_subproblem h₂ B y) Set.univ z := by
    -- Then negate the objective and rewrite it to the ADMM `z`-subproblem.
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
    -- Finally pass from `IsMinOn` to the Chapter 8 solution-set owner.
    simpa using
      (mem_unconstrained_problem_solutions_iff
        (f := admm_z_subproblem h₂ B y) (x := z)).symm
  -- Chaining the three equivalences gives the desired source-faithful bridge.
  have hchain :
      Module.Dual.eval ℝ Z z ∈ subdifferential (conjugate_function h₂) ℓ ↔
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Proposition 15.3: zero is a subgradient of the affine perturbation
`u ↦ ⟪a, u⟫ + h(u)` at `x` exactly when `-a` belongs to the Euclidean subdifferential of `h`
at `x`. -/
theorem zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
    (h : E → EReal) (a x : E) :
    (0 : Module.Dual ℝ E) ∈
        subdifferential (fun u ↦ ((inner ℝ a u : ℝ) : EReal) + h u) x ↔
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
-- `x ↦ ⟪Aᵀ y, x⟫ + h₁(x)` and use the affine-linear subdifferential rule to move the linear term
-- to the other side, yielding the Euclidean/vector-side Chapter 3 condition
-- `-A.adjoint y ∈ euclideanSubdifferential h₁ x`.
/-- A point minimizes the `x`-subproblem from Proposition 15.2 exactly when `-Aᵀ y` belongs to
the Euclidean Chapter 3 subdifferential of `h₁` at that point. -/
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
the Euclidean Chapter 3 subdifferential of `h₂` at that point. -/
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
-- Then replace each `arg min` clause by the corresponding subdifferential condition using the two
-- preceding bridge lemmas.
/-- Proposition 15.3: under the Chapter 15 proper/closed/convex hypotheses on `h₁` and `h₂`,
equation (15.5) is equivalent to the existence of primal witnesses `x^(k+1)` and `z^(k+1)`
satisfying the affine update (15.6) and the subdifferential optimality conditions corresponding to
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
