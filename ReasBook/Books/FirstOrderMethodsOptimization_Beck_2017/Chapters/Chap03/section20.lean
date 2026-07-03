import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_20 (from Chap03) -/
universe u

section

variable {E : Type u} {m : ℕ}

/-
Definition 3.20 is `source-facing`. The ambient domain is finite-family inequality-constrained
optimization, and the owner abstractions for later KKT/Fritz-John developments are the chapter
feasible-set owner `inequality_feasible_set` together with the strict feasible set cut out by the
same constraint family. The primitive data are only the constraint family `g`; Slater's condition
is derived from the strict feasible-set owner as its nonemptiness. -/

/-- The strict feasible set of the inequality-constrained problem cut out by the family `g`. -/
def strict_inequality_feasible_set (g : Fin m → E → ℝ) : Set E :=
  {x | ∀ i, g i x < 0}

variable {g : Fin m → E → ℝ}

/-- Membership in `strict_inequality_feasible_set g` means satisfying every inequality
constraint strictly. -/
@[simp] theorem mem_strict_inequality_feasible_set {x : E} :
    x ∈ strict_inequality_feasible_set g ↔ ∀ i, g i x < 0 :=
  Iff.rfl

/-- Every strict feasible point is feasible for the inequality-constrained problem. -/
theorem strict_inequality_feasible_set_subset_inequality_feasible_set :
    strict_inequality_feasible_set g ⊆ inequality_feasible_set g := fun _ hx i ↦
  le_of_lt (hx i)

/-- Definition 3.20: Slater's condition for the inequality-constrained problem with constraint
family `g` means that there exists a point strictly satisfying every inequality `g_i(x) < 0`. -/
def slaters_condition (g : Fin m → E → ℝ) : Prop :=
  (strict_inequality_feasible_set g).Nonempty

/-- Slater's condition holds exactly when some point satisfies every inequality constraint
strictly. -/
@[simp] theorem slaters_condition_iff (g : Fin m → E → ℝ) :
    slaters_condition g ↔ ∃ x : E, ∀ i : Fin m, g i x < 0 :=
  Iff.rfl

end

/-! ### Proposition_3_20 (from Chap03) -/
section

open InnerProductSpace
open Metric

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.20 is a `bridge/view` item in the chapter real-valued subdifferential API. Its
core owner abstraction is the canonical `subdifferentialAt` from Theorem 3.4, and its Euclidean
bridge/view owner is `euclideanSubdifferentialAt`. The affine pullback step is governed upstream
by the source-facing owner theorem `subdifferential_precompose_affineMap_eq` from
Theorem 3.19, while the concrete norm-side case split already belongs to Proposition 3.15. The
primitive data here are just the affine map `y ↦ A y + b` and the owner Euclidean-norm
subdifferential; the transpose-image and piecewise singleton/ball formulas are derived API. -/

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_l2_norm_eq_piecewise

-- Proof sketch: apply the affine chain rule to `g(z) = ‖z‖`, so the dual subgradients pull back
-- along `A` by the owner theorem on `subdifferential`, then transport that canonical dual pullback
-- through the chapter bridges `strongDualSubdifferential` and `euclideanSubdifferentialAt`. In
-- Euclidean coordinates the pullback is represented by applying `Aᵀ`, and `toDualMap` converts
-- the dual-valued statement into the vector-valued image formula.
/-- Pulling back the Euclidean norm subdifferential along the affine map `y ↦ A y + b` gives the
vector-form chain-rule description `Aᵀ ∂‖·‖(A x + b)`. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun z : Em ↦ ‖z‖) (A.toEuclideanLin x + b) := sorry

-- Proof sketch: first rewrite the affine subdifferential through the transpose-image formula
-- above. Then specialize Proposition 3.15 at the residual vector `A.toEuclideanLin x + b`; the
-- zero case gives the transpose image of the closed unit ball, and the nonzero case gives the
-- transpose of the singleton containing the normalized residual.
/-- Proposition 3.20: for `f(x) = ‖A x + b‖₂` on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing `Aᵀ ((A x + b) / ‖A x + b‖₂)` when
`A x + b ≠ 0`, and it is the image of the closed Euclidean unit ball under `Aᵀ` when
`A x + b = 0`. This is the concrete specialization of
`euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm` using the
norm formula from Proposition 3.15. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      if A.toEuclideanLin x + b = 0 then
        A.transpose.toEuclideanLin '' closedBall (0 : Em) 1
      else
        {A.transpose.toEuclideanLin
          (‖A.toEuclideanLin x + b‖⁻¹ • (A.toEuclideanLin x + b))} := sorry

end

/-! ### Theorem_3_20 (from Chap03) -/
section

open Set

/-
Theorem 3.20 lives at the one-variable calculus owner layer. Its main statement is already the
canonical mathlib chain rule `HasDerivAt.comp_hasDerivWithinAt`; the textbook right-endpoint
formula for `derivWithin` is only a thin `bridge/view` consequence of that owner theorem together
with `HasDerivWithinAt.derivWithin` and `uniqueDiffWithinAt_Ici`.
-/
recall HasDerivAt.comp_hasDerivWithinAt
recall HasDerivWithinAt.derivWithin
recall uniqueDiffWithinAt_Ici

/-- Right-derivative formula companion to the canonical chain rule at a left endpoint. -/
theorem derivWithin_comp_right_endpoint {f g : ℝ → ℝ} {a f' g' : ℝ}
    (hf : HasDerivWithinAt f f' (Ici a) a) (hg : HasDerivAt g g' (f a)) :
    derivWithin (g ∘ f) (Ici a) a = g' * f' :=
  (hg.comp_hasDerivWithinAt a hf).derivWithin (uniqueDiffWithinAt_Ici a)

end
