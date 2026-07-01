import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

noncomputable section

open scoped BigOperators Matrix Rockafellar

namespace Matrix

/-- The Euclidean adjoint linear map of a real matrix, implemented by transpose on coordinates. -/
abbrev euclideanAdjoint {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n :=
  Matrix.toEuclideanLin Aᵀ

end Matrix

section

variable {m s : ℕ}
variable (n : Fin s → ℕ)

local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The ambient product space of block variables in the separable equality program. -/
abbrev SeparableEqualityBlockSpace (n : Fin s → ℕ) :=
  ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k))

/-- The coupling map `x ↦ ∑ₖ Aₖ xₖ` for the separable equality-constrained problem. -/
def separableEqualityCouplingSum
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) :
    SeparableEqualityBlockSpace n → U :=
  fun x ↦ ∑ k, Matrix.toEuclideanLin (A k) (x k)

/-- The separable objective `x ↦ f₀₁(x₁) + ⋯ + f₀s(x_s)`. -/
def separableEqualityObjective
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal) :
    SeparableEqualityBlockSpace n → EReal :=
  fun x ↦ ∑ k, f₀ k (x k)

/-- The `i`-th equality-constraint function for the associated separable program, namely
`x ↦ (∑ₖ (Aₖ xₖ)ᵢ) - aᵢ`. -/
def separableEqualityConstraintFunction
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U) (i : Fin m) :
    SeparableEqualityBlockSpace n → EReal :=
  fun x ↦ (((separableEqualityCouplingSum n A x i) - a i : ℝ) : EReal)

-- Proof sketch: `separableEqualityObjective n f₀` is the finite sum of the convex block
-- objectives
-- `f₀ k`. Viewing the sum on the subtype `Set.univ` changes only the domain representation, so the
-- ambient convexity data assemble into the convexity field required by
-- `OrdinaryConvexProgram`.
/-- The whole-space separable objective supplies the convexity field for the associated ordinary
convex program. -/
theorem separableEqualityOrdinaryProgram_objective_convexOn
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ) :
    ConvexOn ℝ (Set.univ : Set (SeparableEqualityBlockSpace n))
      (extendZero
        (fun x : (Set.univ : Set (SeparableEqualityBlockSpace n)) ↦
          separableEqualityObjective n f₀ x.1)) := sorry

-- Proof sketch: for each coordinate `i`, `separableEqualityConstraintFunction A a i` is the
-- coercion to
-- `EReal` of an affine real-valued map `x ↦ (∑ₖ (Aₖ xₖ)ᵢ) - aᵢ`. Restricting that affine map to the
-- subtype `Set.univ` and then extending back by `extendZero` preserves the same whole-space
-- affine owner needed by `OrdinaryConvexProgram`.
/-- Each coordinate residual of the coupling equation is affine on the ambient block space. -/
theorem separableEqualityOrdinaryProgram_equality_affOn
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U) (i : Fin m) :
    affOn[ℝ]
      (extendZero
        (fun x : (Set.univ : Set (SeparableEqualityBlockSpace n)) ↦
          separableEqualityConstraintFunction n A a i x.1),
        (Set.univ : Set (SeparableEqualityBlockSpace n))) := sorry

/-- The ordinary convex program corresponding to the separable equality-constrained problem. Its
constraint set is all block vectors, it has no inequality constraints, and its equality
constraints are the coordinate equations of `∑ₖ Aₖ xₖ = a`. -/
def separableEqualityOrdinaryProgram
    (f₀ : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U)
    (hf₀_convex : ∀ k : Fin s, (f₀ k).IsConvex ℝ) :
    OrdinaryConvexProgram ℝ (SeparableEqualityBlockSpace n) EReal 0 m :=
  { constraintSet := Set.univ
    objective := fun x ↦ separableEqualityObjective n f₀ x.1
    objective_convexOn := separableEqualityOrdinaryProgram_objective_convexOn n f₀ hf₀_convex
    inequality := Fin.elim0
    inequality_convexOn := fun i ↦ Fin.elim0 i
    equality := fun i x ↦ separableEqualityConstraintFunction n A a i x.1
    equality_affOn := fun i ↦ separableEqualityOrdinaryProgram_equality_affOn n A a i }

/-- The separable Lagrangian `L(u*, x)` from the equality-constrained block program, written in
the source form `-<a, u*> + sum_k (f0_k(x_k) + <x_k, A_k^* u*>)`. -/
def separableLagrangian
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) (uStar : U) (x : SeparableEqualityBlockSpace n) : EReal :=
  -⟪a, uStar⟫ₚ + ∑ k, (f0 k (x k) + ⟪x k, Matrix.euclideanAdjoint (A k) uStar⟫ₚ)

/-- The dual objective `g(u*) = -<a, u*> - sum_k f0_k^*(-A_k^* u*)` for the same separable
program. -/
def separableDualObjective
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) (uStar : U) : EReal :=
  -⟪a, uStar⟫ₚ -
    ∑ k, ((f0 k)⋆) (-(Matrix.euclideanAdjoint (A k) uStar))

/-- The convex function `w(u*) = -g(u*) = <a, u*> + sum_k f0_k^*(-A_k^* u*)` whose minimizers are
the Kuhn--Tucker vectors in this separable example. -/
def separableDualCost
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) (uStar : U) : EReal :=
  ⟪a, uStar⟫ₚ +
    ∑ k, ((f0 k)⋆) (-(Matrix.euclideanAdjoint (A k) uStar))

-- Proof sketch: expand the blockwise Lagrangian, then separate the infimum over the product space
-- into the sum of independent blockwise infima. For each block, rewrite that infimum by the
-- defining `-f^*` identity for the Fenchel conjugate evaluated at `-A_k^* u*`.
/-- The dual objective is the infimum of the separable Lagrangian over all block variables. -/
theorem separableDualObjective_eq_iInf_separableLagrangian
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) (uStar : U) :
    separableDualObjective n f0 A a uStar =
      ⨅ x : SeparableEqualityBlockSpace n, separableLagrangian n f0 A a uStar x := sorry

-- Proof sketch: unfold `separableDualObjective` and `separableDualCost`; the displayed formulas
-- differ only by an overall sign.
/-- The minimization cost `w` is the pointwise negative of the dual objective `g`. -/
theorem separableDualCost_eq_neg_separableDualObjective
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) (uStar : U) :
    separableDualCost n f0 A a uStar = -separableDualObjective n f0 A a uStar := sorry

-- Proof sketch: each conjugate term `x ↦ (f0_k)^*(x)` is convex by the Chapter 12 conjugacy
-- owner theorem, precomposing with the linear map `u* ↦ -A_k^* u*` preserves convexity, and
-- finite sums together with the linear pairing term `<a, u*>` remain convex.
/-- The source dual cost `w(u*) = <a, u*> + sum_k f0_k^*(-A_k^* u*)` is convex on `R^m`. -/
theorem separableDualCost_isConvex
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : U) :
    (separableDualCost n f0 A a).IsConvex ℝ := sorry

-- Proof sketch: specialize the Section 28 characterization of Kuhn--Tucker vectors as dual
-- maximizers to the separable equality program from Theorem 6.28.7. Then rewrite the specialized
-- dual objective by `separableDualObjective_eq_iInf_separableLagrangian` and pass from maximizers
-- of `g` to minimizers of `w = -g` using `separableDualCost_eq_neg_separableDualObjective`.
/-- Theorem 6.28.8: for the separable equality-constrained program with objective
`sum_k f0_k(x_k)` and constraint `sum_k A_k x_k = a`, a multiplier vector `u*` is a
Kuhn--Tucker vector exactly when it minimizes the convex function
`w(u*) = <a, u*> + f0_1^*(-A_1^* u*) + ... + f0_s^*(-A_s^* u*)` on `R^m`. -/
theorem isKuhnTuckerVector_iff_isMinOn_separableDualCost
    (f0 : ∀ k : Fin s, EuclideanSpace ℝ (Fin (n k)) → EReal)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ) (a : U)
    (hf0_convex : ∀ k : Fin s, (f0 k).IsConvex ℝ)
    (uStar : U) :
    (separableEqualityOrdinaryProgram n f0 A a hf0_convex).IsKuhnTuckerVector Fin.elim0 uStar ↔
      IsMinOn (separableDualCost n f0 A a) Set.univ uStar := sorry

end
