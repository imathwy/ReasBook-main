import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- The Fenchel conjugate, viewed on the continuous dual via the canonical coercion
`StrongDual ℝ E → Module.Dual ℝ E`, written directly using the supremum formula. -/
noncomputable def conjugate_function_strongDual {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → EReal) : StrongDual ℝ E → EReal :=
  fun y ↦ sSup (Set.range fun x : E ↦ (y x : EReal) - f x)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.26 is `source-facing` and splits into atomic clauses: source part (a), then the
finiteness and smoothness consequences comprising source part (b). Domain sampling identifies the
owner-level ingredients as the Fenchel conjugate formula, Definition 5.1's `is_l_smooth_on`, and
mathlib's canonical `StrongConvexOn` on the finite-valued domain of an extended-real-valued
function. In this item file, only the thin bridge from the algebraic dual to the continuous dual
`StrongDual ℝ E` is added so the source statement lives on the dual normed space without changing
the owner-level mathematics. -/

-- Proof sketch: transport the `1 / σ`-smoothness hypothesis through the Chapter 5 equivalence
-- between convex smoothness and gradient cocoercivity, then apply the conjugate subgradient
-- correspondence to convert cocoercivity of `f` into strong monotonicity of `∂f*`. Finally use
-- the Chapter 5 strong-convexity characterization to identify that strong monotonicity with
-- `σ`-strong convexity of the conjugate on its finite-valued domain in the continuous dual.
/-- Theorem 5.26 (1): source part (a). If a convex real-valued function on `E` is globally
`1 / σ`-smooth, then its Fenchel conjugate is `σ`-strongly convex on its finite-valued domain in
the continuous dual space, with respect to the ambient dual norm. -/
theorem strongConvexOn_toReal_conjugate_function_of_convex_is_l_smooth
    (σ : ℝ) (hσ : 0 < σ) (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_diff : ∀ x, DifferentiableAt ℝ f x)
    (hf_fderiv_lipschitz :
      LipschitzOnWith (Real.toNNReal (1 / σ)) (fderiv ℝ f) Set.univ) :
    StrongConvexOn
      ({y : StrongDual ℝ E |
          conjugate_function_strongDual (fun x : E ↦ (f x : EReal)) y < ⊤} :
        Set (StrongDual ℝ E))
      σ
      (fun y : StrongDual ℝ E ↦
        (conjugate_function_strongDual (fun x : E ↦ (f x : EReal)) y).toReal) := sorry

-- Proof sketch: strong convexity together with properness and lower semicontinuity yields a
-- unique primal maximizer in the Fenchel conjugate formula at each dual point, so the conjugate
-- never takes either infinite value on the continuous dual.
/-- Theorem 5.26 (2): source part (b), finiteness clause. If a proper closed extended-real-valued
function is `σ`-strongly convex, then its Fenchel conjugate is finite everywhere on the
continuous dual. -/
theorem conjugate_function_finite_of_proper_closed_strongConvexOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (h_ne_bot : ∀ x, f x ≠ ⊥)
    (hdom : ({x : E | f x < ⊤} : Set E).Nonempty) (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn ({x : E | f x < ⊤} : Set E) σ (fun x ↦ (f x).toReal)) :
    ∀ y : StrongDual ℝ E,
      conjugate_function_strongDual f y ≠ ⊥ ∧ conjugate_function_strongDual f y < ⊤ := sorry

-- Proof sketch: after `conjugate_function_finite_of_proper_closed_strongConvexOn`, the conjugate
-- is real-valued on all of `StrongDual ℝ E`. Transfer strong monotonicity of the extendedRealSubdifferential
-- across the Fenchel correspondence and apply the Chapter 5 smoothness characterization to obtain
-- global `1 / σ`-smoothness of the real-valued conjugate.
/-- Theorem 5.26 (3): source part (b), smoothness clause. If a proper closed extended-real-valued
function is `σ`-strongly convex, then the real-valued Fenchel conjugate is globally
`1 / σ`-smooth on the continuous dual. -/
theorem is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (h_ne_bot : ∀ x, f x ≠ ⊥)
    (hdom : ({x : E | f x < ⊤} : Set E).Nonempty) (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn ({x : E | f x < ⊤} : Set E) σ (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal)
      Set.univ
      (Real.toNNReal (1 / σ)) := sorry

end
