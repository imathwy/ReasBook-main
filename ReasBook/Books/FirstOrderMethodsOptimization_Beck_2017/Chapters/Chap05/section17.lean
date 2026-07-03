import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_17 (from Chap05) -/
noncomputable section

universe u

/-- The effective domain of an extended-real-valued function is the set where the value is finite.
-/
def effective_domain {E : Type u} (f : E → EReal) : Set E := {x | f x < ⊤}

/-- A proper extended-real-valued function never takes the value `-∞` and has nonempty effective
domain. -/
class IsProperExtendedRealFunction {E : Type u} (f : E → EReal) : Prop where
  ne_bot : ∀ x, f x ≠ ⊥
  effective_domain_nonempty : (effective_domain f).Nonempty

/-- An extended-real-valued function is convex when its real epigraph is convex. -/
def is_convex_function {E : Type u} [AddCommMonoid E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The infimal convolution is the pointwise infimum of translated sums. -/
noncomputable def infimal_convolution {E : Type u} [AddCommGroup E]
    (h1 h2 : E → EReal) : E → EReal :=
  fun x ↦ ⨅ u : E, h1 u + h2 (x - u)

/-- The Fenchel conjugate of an extended-real-valued function on the algebraic dual. -/
noncomputable def conjugate_function {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup (Set.range fun x : E ↦ (y x : EReal) - f x)

/-- A real-valued function is `L`-smooth on `D` when it is differentiable there and its Fréchet
derivative is `L`-Lipschitz on `D`. -/
def is_l_smooth_on {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : Set E) (L : NNReal) : Prop :=
  (∀ x ∈ D, DifferentiableAt ℝ f x) ∧ LipschitzOnWith L (fderiv ℝ f) D

/-- The Fenchel conjugate, viewed on the continuous dual through the canonical coercion to the
algebraic dual. -/
noncomputable def conjugate_function_strongDual {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → EReal) : StrongDual ℝ E → EReal :=
  fun y ↦ sSup (Set.range fun x : E ↦ (y x : EReal) - f x)

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.17 is `source-facing` in the infimal-convolution smoothing calculus. The owner
abstractions already present in the project are:
- `IsProperExtendedRealFunction`, `is_convex_function`, and `infimal_convolution` for the primal
  extended-real objects;
- `conjugate_function` for the algebraic-dual Fenchel conjugate appearing in the exact formula;
- `conjugate_function_strongDual` and `is_l_smooth_on` for the normed dual/smoothness bridge.

The item splits naturally into two atomic clauses: the exact conjugacy identity for `f □ ω`, then
the smoothness consequence under strong convexity of the conjugate kernel. The second clause is
stated on the continuous dual, since that is the existing normed owner for strong convexity in the
repo. -/

-- Proof sketch: use the conjugacy formula `(f □ ω)^* = f^* + ω^*`, obtained from the infimal
-- convolution theorem together with the no-`⊥` part of properness, and then apply the closed
-- convex biconjugation theorem to `f □ ω`. The canonical bidual equivalence `Module.evalEquiv ℝ E`
-- identifies the primal space with the bidual, yielding the source formula
-- `f □ ω = (f^* + ω^*)^*`.
/-- Proposition 5.17 (1): if `f` and `ω` are proper closed convex extended-real-valued functions,
then their infimal convolution equals the primal-side conjugate of the sum of the conjugates. This
is the owner-level rendering of the textbook identity
`f \square ω = (f^* + ω^*)^*`, with the bidual conjugate transported back to `E` by the canonical
equivalence `Module.evalEquiv ℝ E`. -/
theorem proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω) :
    infimal_convolution f ω =
      conjugate_function (conjugate_function f + conjugate_function ω) ∘ Module.evalEquiv ℝ E :=
  sorry

-- Proof sketch: the strong-convexity hypothesis on `ω^*`, expressed in the repo's normed-dual API
-- via `conjugate_function_strongDual`, makes `f^* + ω^*` strongly convex after adding the proper
-- closed convex conjugate `f^*`. Apply the conjugate smoothness correspondence to that summed dual
-- function and then transport the resulting smoothness statement back to the primal infimal
-- convolution using clause (1).
/-- Proposition 5.17 (2): if `f` and `ω` are proper closed convex extended-real-valued functions
and the continuous-dual Fenchel conjugate `ω^*` is `(1 / L)`-strongly convex, then the real-valued
infimal convolution `x ↦ ((f \square ω) x).toReal` is globally `L`-smooth. This is the canonical
continuous-dual formulation of the textbook clause that `ω^*` being `(1 / L)`-strongly convex,
equivalently `ω` being `L`-smooth, implies `f \square ω` is `L`-smooth. -/
theorem infimal_convolution_toReal_is_l_smooth_of_conjugate_strongConvex
    (f ω : E → EReal) (L : NNReal) (hL_pos : 0 < L) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (hω_star_strong :
      StrongConvexOn
        ({y : StrongDual ℝ E | conjugate_function_strongDual ω y < ⊤} : Set (StrongDual ℝ E))
        (1 / (L : ℝ))
        (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual ω y).toReal)) :
    is_l_smooth_on (fun x ↦ (infimal_convolution f ω x).toReal) Set.univ L := sorry

end

/-! ### Theorem_5_17 (from Chap05) -/
universe u

/-- The effective domain of an extended-real-valued function is the set of points where the
function is finite above. -/
def effective_domain {E : Type u} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- An extended-real-valued function is convex when its real epigraph is a convex subset of
`E × ℝ`. -/
def is_convex_function {E : Type u} [AddCommMonoid E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- A source-facing strong-convexity predicate for extended-real-valued functions: the function
never takes the value `-∞`, its effective domain is convex, and it satisfies the quadratic Jensen
inequality on that domain. -/
class is_strongly_convex_function {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The effective domain of a strongly convex function is convex. -/
  convex_effective_domain : Convex ℝ (effective_domain f)
  /-- The defining quadratic Jensen inequality along segments in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 5.17 is a `bridge/view` item: it compares the source-facing strong-convexity owner
`is_strongly_convex_function` from Definition 5.16 with the source-facing convexity owner
`is_convex_function` from Definition 2.6, using Definition 2.7's segment formulation after
subtracting the quadratic function `x ↦ (σ / 2) ‖x‖²`. The Euclidean-space hypothesis is
formalized by `InnerProductSpace ℝ E`, which is exactly the structure needed for the quadratic
norm identity underlying this equivalence. -/

-- Proof sketch: rewrite convexity of the shifted function by its segment inequality, expand the
-- shifted function along a segment, and use the inner-product identity
-- `‖t • x + (1 - t) • y‖² - t * ‖x‖² - (1 - t) * ‖y‖² = -t * (1 - t) * ‖x - y‖²` to convert the
-- convexity inequality into the defining segment inequality from `is_strongly_convex_function`.
/-- Theorem 5.17: on a Euclidean space, for `σ > 0`, an extended-real-valued function is
`σ`-strongly convex if and only if subtracting `(σ / 2) ‖x‖²` yields a convex
extended-real-valued function. -/
theorem is_strongly_convex_function_iff_sub_half_sigma_norm_sq_is_convex
    (f : E → EReal) (σ : ℝ) :
    is_strongly_convex_function f σ ↔
      is_convex_function
        (fun x ↦ f x - ((((σ / 2) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) := sorry

end
