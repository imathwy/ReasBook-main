import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

noncomputable section

universe u

open scoped BigOperators Matrix Rockafellar

section

variable {m s : ℕ}
variable (n : Fin s → ℕ)

local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The ambient product space of block variables in the separable program. -/
abbrev BlockSpace (n : Fin s → ℕ) :=
  ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k))

/-- The coupling map `x ↦ ∑ₖ Aₖ xₖ` for the separable equality-constrained problem. -/
def couplingSum
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) :
    BlockSpace n → U :=
  fun x ↦ ∑ k, Matrix.toEuclideanLin (A k) (x k)

-- Proof sketch: unfold `couplingSum`; the `i`-th coordinate is the displayed finite sum of the
-- `i`-th coordinates of the block images `(A k) *ᵥ (x k)`.
/-- The `i`-th coordinate of `couplingSum A x` is the sum of the `i`-th coordinates of the block
images `(Aₖ xₖ)`. -/
theorem couplingSum_apply
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (x : BlockSpace n) (i : Fin m) :
    couplingSum n A x i = ∑ k, (((A k) *ᵥ (x k)) i) := sorry

/-- The separable objective `x ↦ f₀₁(x₁) + ⋯ + f₀s(x_s)`. -/
def separableObjective
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal) :
    BlockSpace n → EReal :=
  fun x ↦ ∑ k, f₀ k (x k)

-- Proof sketch: unfold `separableObjective`; evaluation at `x` is definitionally the displayed
-- finite sum of the block objectives.
/-- Evaluating `separableObjective f₀` at `x` gives the sum of the block objective values
`∑ₖ f₀ₖ(xₖ)`. -/
theorem separableObjective_apply
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (x : BlockSpace n) :
    separableObjective n f₀ x = ∑ k, f₀ k (x k) := sorry

/-- The `i`-th equality-constraint function for the associated separable program, namely
`x ↦ (∑ₖ (Aₖ xₖ)ᵢ) - aᵢ`. -/
def couplingEqualityFunction
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U) (i : Fin m) :
    BlockSpace n → EReal :=
  fun x ↦ (((couplingSum n A x i) - a i : ℝ) : EReal)

-- Proof sketch: unfold `couplingEqualityFunction`; the value at `x` is definitionally the
-- displayed coordinate residual `((∑ₖ (Aₖ xₖ)ᵢ) - aᵢ : ℝ)`.
/-- Evaluating `couplingEqualityFunction A a i` at `x` gives the `i`-th residual of the coupling
constraint `∑ₖ Aₖ xₖ = a`. -/
theorem couplingEqualityFunction_apply
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U) (i : Fin m)
    (x : BlockSpace n) :
    couplingEqualityFunction n A a i x = (((couplingSum n A x i) - a i : ℝ) : EReal) := sorry

/-- The block objective `hₖ` obtained by adding to `f₀ₖ` the linear term defined by the
multiplier vector `ν`. -/
def componentLagrangianObjective
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (ν : Fin m → ℝ) (k : Fin s) :
    EuclideanSpace ℝ (Fin (n k)) → EReal :=
  fun xk ↦ f₀ k xk + ∑ i, (ν i : EReal) * (((A k) *ᵥ xk) i)

-- Proof sketch: unfold `componentLagrangianObjective`; evaluating at `xₖ` gives the objective
-- value `f₀ₖ(xₖ)` plus the multiplier-weighted linear form `∑ᵢ νᵢ (Aₖ xₖ)ᵢ`.
/-- Evaluating `componentLagrangianObjective f₀ A ν k` at `xₖ` gives the textbook function
`hₖ(xₖ) = f₀ₖ(xₖ) + ∑ᵢ νᵢ (Aₖ xₖ)ᵢ`. -/
theorem componentLagrangianObjective_apply
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (ν : Fin m → ℝ) (k : Fin s)
    (xk : EuclideanSpace ℝ (Fin (n k))) :
    componentLagrangianObjective n f₀ A ν k xk =
      f₀ k xk + ∑ i, (ν i : EReal) * (((A k) *ᵥ xk) i) := sorry

/-- The minimum set `Dₖ` of the independent problem associated with the block objective `hₖ`. -/
def componentMinimizerSet
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (ν : Fin m → ℝ) (k : Fin s) :
    Set (EuclideanSpace ℝ (Fin (n k))) :=
  minimumSet (componentLagrangianObjective n f₀ A ν k)

-- Proof sketch: unfold `componentMinimizerSet`; membership is exactly the statement that the
-- block objective `hₖ` attains its minimum over the whole block space at `xₖ`.
/-- Membership in `componentMinimizerSet f₀ A ν k` means that `xₖ` minimizes `hₖ` on its whole
ambient block space. -/
theorem mem_componentMinimizerSet
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (ν : Fin m → ℝ) (k : Fin s)
    (xk : EuclideanSpace ℝ (Fin (n k))) :
    xk ∈ componentMinimizerSet n f₀ A ν k ↔
      xk ∈ minimumSet (componentLagrangianObjective n f₀ A ν k) := by
  rfl

-- Proof sketch: `separableObjective n f₀` is the finite sum of the convex block objectives
-- `f₀ k`. Viewing the sum on the subtype `Set.univ` changes only the domain representation, so the
-- ambient convexity data assemble into the convexity field required by
-- `OrdinaryConvexProgram`.
/-- The whole-space separable objective supplies the convexity field for the associated ordinary
convex program. -/
theorem separableEqualityProgram_objective_convexOn
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ) :
    ConvexOn ℝ (Set.univ : Set (BlockSpace n))
      (extendZero (fun x : (Set.univ : Set (BlockSpace n)) ↦ separableObjective n f₀ x.1)) := sorry

-- Proof sketch: for each coordinate `i`, `couplingEqualityFunction A a i` is the coercion to
-- `EReal` of an affine real-valued map `x ↦ (∑ₖ (Aₖ xₖ)ᵢ) - aᵢ`. Restricting that affine map to the
-- subtype `Set.univ` and then extending back by `extendZero` preserves the same whole-space
-- affine owner needed by `OrdinaryConvexProgram`.
/-- Each coordinate residual of the coupling equation is affine on the ambient block space. -/
theorem separableEqualityProgram_equality_affOn
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U) (i : Fin m) :
    affOn[ℝ]
      (extendZero
        (fun x : (Set.univ : Set (BlockSpace n)) ↦ couplingEqualityFunction n A a i x.1),
        (Set.univ : Set (BlockSpace n))) :=
  sorry

/-- The ordinary convex program corresponding to the separable equality-constrained problem. Its
constraint set is all block vectors, it has no inequality constraints, and its equality
constraints are the coordinate equations of `∑ₖ Aₖ xₖ = a`. -/
def separableEqualityProgram
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ) :
    OrdinaryConvexProgram ℝ (BlockSpace n) EReal 0 m :=
  { constraintSet := Set.univ
    objective := fun x ↦ separableObjective n f₀ x.1
    objective_convexOn := separableEqualityProgram_objective_convexOn n f₀ hf₀_convex
    inequality := Fin.elim0
    inequality_convexOn := fun i ↦ Fin.elim0 i
    equality := fun i x ↦ couplingEqualityFunction n A a i x.1
    equality_affOn := fun i ↦ separableEqualityProgram_equality_affOn n A a i }
-- Proof sketch: use the Kuhn--Tucker hypothesis to place the weighted objective in the proper
-- source setting. Then unfold the weighted objective minimizer set of the associated ordinary
-- convex program as the chapter owner `minimumSet` and expand its weighted objective with no
-- inequality block. The resulting
-- function is the sum over `k` of the independent objectives
-- `componentLagrangianObjective n f₀ A ν k`, up to the additive constant `-∑ᵢ νᵢ aᵢ`, which does
-- not affect minimizers. Therefore a block vector minimizes the global weighted objective exactly
-- when each block belongs to the corresponding minimum set `Dₖ`.
/-- Under the Kuhn--Tucker hypothesis, minimizing the weighted objective attached to the
associated ordinary convex program is equivalent to minimizing each independent block objective
`hₖ`. -/
theorem mem_minimumSet_weightedObjective_iff_forall_mem_componentMinimizerSet
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ)
    (ν : Fin m → ℝ)
    (hν :
      (separableEqualityProgram n f₀ A a hf₀_convex).IsKuhnTuckerVector Fin.elim0 ν)
    (x : BlockSpace n) :
    x ∈ minimumSet
          ((separableEqualityProgram n f₀ A a hf₀_convex).weightedObjective Fin.elim0 ν) ↔
      ∀ k : Fin s, x k ∈ componentMinimizerSet n f₀ A ν k := sorry

-- Proof sketch: apply Theorem 6.28.1 to the associated ordinary convex program
-- `separableEqualityProgram n f₀ A a hf₀_convex` and the Kuhn--Tucker vector `ν`. In the present
-- pure-equality situation there is no inequality block, so the complementary conditions reduce to
-- the single feasibility equation `couplingSum n A x = a`. Then rewrite the weighted-objective
-- minimizer condition by
-- `mem_minimumSet_weightedObjective_iff_forall_mem_componentMinimizerSet` to obtain the
-- componentwise conditions `x k ∈ Dₖ`.
/-- Theorem 6.28.7: if `ν` is a Kuhn--Tucker vector for the ordinary convex program associated to
the separable problem with objective `∑ₖ f₀ₖ(xₖ)` and constraint `∑ₖ Aₖ xₖ = a`, then the optimal
solutions are exactly the feasible block vectors whose `k`-th component lies in the minimum set
`Dₖ` of the independent objective `hₖ`. -/
theorem optimalSolutionSet_eq_componentMinimizerSet_and_couplingSum_eq
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ)
    (ν : Fin m → ℝ)
    (hν :
      (separableEqualityProgram n f₀ A a hf₀_convex).IsKuhnTuckerVector Fin.elim0 ν) :
    (separableEqualityProgram n f₀ A a hf₀_convex).optimalSolutionSet =
      {x | (∀ k : Fin s, x k ∈ componentMinimizerSet n f₀ A ν k) ∧ couplingSum n A x = a} := sorry

end
