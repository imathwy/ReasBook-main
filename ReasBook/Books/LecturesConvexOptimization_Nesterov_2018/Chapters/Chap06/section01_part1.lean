import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_1 (from Chap06) -/
noncomputable section

open Module

universe u

/- Definition 6.1 lies in the chapter's Fenchel-conjugacy domain.

Relevant owner-style declarations sampled before refinement:
- `Dual ℝ E`, the canonical algebraic-dual owner notation for real linear functionals;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing inner-product-space bridge built
  from this owner by evaluation along `innerₗ`;
- `fenchelSmoothApproximation` in `Definition_6_2`, the immediate Chapter 6 downstream owner that
  consumes `fenchelConjugate` directly.

Best owner abstraction:
- core/canonical: `fenchelConjugate`;
- bridge/view: later specializations from `Dual ℝ E` to inner-product or continuous-dual surfaces.

Primitive data:
- `f : E → EReal`.

Derived API:
- `fenchelConjugate_apply`.

Source/core/bridge triage:
- core/canonical: the dual-space Fenchel supremum owner itself.

This file is the owner, not a bridge. The conjugate formula only needs the primitive module
structure needed to evaluate linear functionals, so the old `AddCommGroup` header was stronger
than necessary; the refined owner now lives over `AddCommMonoid E` and leaves stronger ambient
structures to downstream bridge files.
-/
variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Definition 6.1: the Fenchel conjugate of an extended-real function is the pointwise supremum
of the affine functionals `x ↦ ⟪s, x⟫ - f x`; for a proper convex function, this is the textbook
Fenchel conjugate. -/
def fenchelConjugate (f : E → EReal) : Dual ℝ E → EReal :=
  fun s ↦ ⨆ x : E, (s x : EReal) - f x

/-- Evaluating the Fenchel conjugate recovers its defining supremum formula. -/
@[simp] theorem fenchelConjugate_apply (f : E → EReal) (s : Dual ℝ E) :
    fenchelConjugate f s = ⨆ x : E, (s x : EReal) - f x :=
  rfl

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous-dual Fenchel conjugate of a real-valued function, obtained by evaluating the
core owner `fenchelConjugate` on `StrongDual ℝ E`. -/
abbrev strongFenchelConjugate (f : E → ℝ) : StrongDual ℝ E → EReal :=
  fun s ↦ fenchelConjugate (fun x ↦ (f x : EReal)) s

/-- Evaluating the continuous-dual Fenchel conjugate recovers the defining supremum formula. -/
@[simp] theorem strongFenchelConjugate_apply (f : E → ℝ) (s : StrongDual ℝ E) :
    strongFenchelConjugate f s = ⨆ x : E, (s x : EReal) - (f x : EReal) :=
  fenchelConjugate_apply (fun x ↦ (f x : EReal)) s

/-! ### Example_6_1_1 (from Chap06) -/
noncomputable section

open scoped BigOperators ConvexAnalysis

universe u v

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.1.1 lies in the finite max-type / simplex-duality domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `StdSimplex` and its weight coordinates in the chapter's finite convex-combination layer;
- the chapter's Fenchel-duality bridge `fenchelDual` in `Chap03/Definition_3_1_2_1`.

Best owner abstraction:
- source-facing: the finite max-absolute affine objective attached to a family `(a_j, b_j)`;
- core/canonical: `maxTypeObjective` together with `StdSimplex`;
- bridge/view: the `ℓ₁`-ball and signed-simplex multiplier representations of the same function.

Primitive data:
- a finite family `a : ι → E`;
- offsets `b : ι → ℝ`.

Derived API:
- the source-facing owner `piecewiseLinearObjective a b`;
- its direct finite-maximum formula;
- the `ℓ₁`-ball representation;
- the signed-simplex representation from the end of the example.

This file keeps the public owner at the actual source-facing absolute-value function
`x ↦ max_j |⟪a_j, x⟫ - b_j|`, and records the multiplier representations as separate theorem
statements rather than replacing that function by a surrogate package. -/

/-- The max-absolute affine objective attached to the finite family
`x ↦ ⟪a_j, x⟫ - b_j`. -/
def piecewiseLinearObjective (a : ι → E) (b : ι → ℝ) : E → ℝ :=
  maxTypeObjective fun j x ↦ |inner ℝ (a j) x - b j|

-- Proof sketch: unfold `piecewiseLinearObjective` through the owner
-- `maxTypeObjective`.
/-- Evaluating the max-absolute affine objective gives the finite maximum of the absolute affine
pieces. -/
theorem piecewiseLinearObjective_apply (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x - b j|) := sorry

-- Proof sketch: use the scalar identity
-- `|t| = sup {u * t | |u| ≤ 1}`, then combine the coordinate multipliers into a single point of
-- the `ℓ₁` ball in `ι → ℝ`.
/-- The max-absolute affine objective is the supremum of the corresponding linear functional over
the `ℓ₁` unit ball of coefficient vectors. -/
theorem piecewiseLinearObjective_eq_sSup_l1Ball
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        ((fun u : ι → ℝ ↦ ∑ j, u j * (inner ℝ (a j) x - b j)) ''
          {u : ι → ℝ | ∑ j, |u j| ≤ 1}) := sorry

-- Proof sketch: split each signed coefficient `u j` as a difference of nonnegative parts
-- `u₁ j - u₂ j`, normalize them to total mass `1`, and identify those nonnegative parts with a
-- simplex point on the signed index set `ι ⊕ ι`.
/-- Example 6.1.1 [Chapter6_1.json:13]: the max-absolute affine objective admits the signed-simplex
representation
`f(x) = sup_{u ∈ Δ(ι ⊕ ι)} ∑_j (u(inl j) - u(inr j)) (⟪a_j, x⟫ - b_j)`. -/
theorem piecewiseLinearObjective_eq_simplexSup
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
          ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) *
            (inner ℝ (a j) x - b j)) := sorry

end

/-! ### Lemma_6_1 (from Chap06) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

/- Lemma 6.1 lies in the chapter's Fenchel-biconjugacy domain.

Primary domain:
- Fenchel duality for `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `dom` and `withTopToEReal` from `Chap03/Definition_3_3`, the chapter owners for the
  finite-value domain and the canonical codomain bridge to `EReal`;
- `ClosedConvexFunction` from `Chap03/Definition_3_1_1_5`, the chapter owner for proper
  closed-convex `WithTop`-valued functions;
- `fenchelDual` with the notation `f⋆` from `Chap03/Definition_3_1_2_1`, the source-facing
  Fenchel-conjugate owner;
- `fenchelBidual` with the notation `f⋆⋆` from `Chap03/Theorem_3_1_5_2`, the canonical
  source-facing biconjugate owner.

Best owner abstraction:
- source-facing theorem: the Fenchel-Moreau equality for a proper closed convex function;
- core/canonical owner: `fenchelBidual`;
- bridge/view: the explicit supremum formula obtained from `fenchelBidual` by the
  `dom (f⋆)`-restriction bridge under `hproper`;
- Euclidean `ℝⁿ` is only a specialization layer, already handled separately by chapter recall
  files such as `Theorem_3_20`.

Primitive data:
- `f : E → WithTop ℝ`;
- properness as `(dom f).Nonempty`;
- closed convexity as `ClosedConvexFunction f`.

Derived API:
- the owner-level equality `(f⋆⋆) x = withTopToEReal (f x)`;
- the explicit source-facing supremum formula obtained by restricting the owner-level supremum to
  `dom (f⋆)` under `hproper`.

Source/core/bridge triage:
- source-facing: Lemma 6.1's equality between `f` and its Fenchel biconjugate;
- core/canonical: `fenchelBidual`;
- bridge/view: the theorem `fenchelMoreau_eq_sSup_inner_sub_fenchelDual` below, which uses the
  `dom (f⋆)`-restriction bridge from `Theorem_3_1_5_2`.

The previous file rebuilt local owners for the effective domain, closed-convexity, conjugate, and
biconjugate integrand. Those notions already live upstream on the canonical chapter surfaces
`dom`, `ClosedConvexFunction`, `f⋆`, and `f⋆⋆`, so this file keeps only the source-facing theorem
layer and derives the displayed supremum formula from the canonical owner `fenchelBidual` through
the domain-restriction bridge justified by `hproper`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ClosedConvexFunction

/-- Lemma 6.1, owner form: a proper closed convex function agrees with its Fenchel bidual. -/
-- Proof sketch: this is the Fenchel-Moreau theorem on the chapter owner surface `f⋆⋆`; the
-- nonempty-domain hypothesis is the source-facing properness assumption under which the bidual
-- recovers the original function.
theorem fenchelBidual_eq_of_dom_nonempty
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty) (x : E) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  sorry

end ClosedConvexFunction

/-- Lemma 6.1, source-facing form: a proper closed convex function equals the supremum of the
affine terms `⟪s, x⟫ - f_*(s)` over `dom f_*`. -/
theorem fenchelMoreau_eq_sSup_inner_sub_fenchelDual
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty) (x : E) :
    withTopToEReal (f x) =
      sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
  calc
    withTopToEReal (f x) = (f⋆⋆) x := (hf.fenchelBidual_eq_of_dom_nonempty hdom x).symm
    _ = sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) :=
      fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty hdom x

end

/-! ### Proposition_6_1 (from Chap06) -/
noncomputable section

open Metric
open scoped ConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 6.1 lies in the chapter's Fenchel-conjugacy / dual-norm domain.

Primary domain:
- growth bounds for the continuous-dual effective domain of a Fenchel conjugate.

Sampled owner-style declarations:
- `fenchelConjugate` in `Definition_6_1`, the chapter owner for conjugates on `Module.Dual ℝ E`;
- `fenchelConjugate_apply` in `Definition_6_1`, the owner evaluation theorem;
- `strongFenchelConjugate` in `Definition_6_1`, the continuous-dual bridge owner used in Chapter 6
  normed-space statements;
- `extendedRealEffectiveDomain` / the notation `dom` in `Definition_3_1_1_2`, the chapter owner
  for finite-value domains of `EReal`-valued functions;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the nearby bridge/view pattern that specializes
  the same owner surface instead of rebuilding it.

Best owner abstraction:
- `strongFenchelConjugate` together with `dom`.

Primitive data:
- `f : E → ℝ`.

Derived API:
- the closed-ball containment and boundedness consequences for the continuous-dual effective
  domain of `strongFenchelConjugate`.

Source/core/bridge triage:
- source-facing: Proposition 6.1's boundedness statement for the continuous-dual finite-value
  domain of the conjugate of a real-valued function;
- core/canonical: `fenchelConjugate` and `dom`;
- bridge/view: `strongFenchelConjugate`.

This file therefore uses the reusable Chapter 6 bridge owner `strongFenchelConjugate` instead of
repeating a theorem-local `StrongDual` lambda for the continuous-dual restriction of
`fenchelConjugate`. The previous local `convexConjugate` definition duplicated the owner
`fenchelConjugate`, the previous local domain alias duplicated the chapter owner `dom`, and the
previous specialized membership wrapper duplicated `mem_extendedRealEffectiveDomain_iff`; all
three are removed here. The linear-growth conclusion itself does not use convexity,
finite-dimensionality, or a separate `0 ≤ L` witness, so the theorem surface is reduced to the
actual primitive data: a nonnegative radius `L : NNReal` and the growth bound.
-/

/-- Proposition 6.1: if a real-valued function is bounded above by `f 0 + L ‖x‖`, then the
finite-value domain of its Fenchel conjugate on the continuous dual is contained in the closed
dual ball of radius `L`. -/
-- Proof sketch: if `‖s‖ > L`, choose `u` in the unit ball with `s u > L`; then along the ray
-- `t • u` the maximand `s (t • u) - f (t • u)` is bounded below by
-- `t * (s u - L) - f 0`, which diverges to `+∞`, so `s` cannot lie in the finite-value domain.
theorem dom_fenchelConjugate_subset_closedBall_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    dom (strongFenchelConjugate f) ⊆ closedBall 0 L := sorry

/-- The finite-value domain of the conjugate is bounded under the same upper linear-growth
hypothesis. -/
-- Proof sketch: apply the closed-ball containment theorem and `Metric.isBounded_closedBall`.
theorem dom_fenchelConjugate_bounded_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    Bornology.IsBounded (dom (strongFenchelConjugate f)) := sorry

end

/-! ### Remark_6_1_1 (from Chap06) -/
noncomputable section

universe u

/- Remark 6.1.1 lies in the accelerated-prefix-convexity / Euclidean prox-function domain.

Sampled owner-style declarations:
- `bounded_union_of_prefix_convex_hull_sequences` in `Proposition_6_8`, the chapter owner of the
  boundedness conclusion once prefix convex-hull membership is known;
- `bounded_union_of_prefix_convex_hull_sequences_of_isBounded` in `Proposition_6_8`, the same
  owner factored through boundedness of `Set.range v`;
- `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  centered quadratic penalty;
- `quadraticallyRegularizedObjective_apply` in `Chap01/Definition_1_4_17`, the companion bridge
  back to the textbook formula.

Best owner abstractions:
- source-facing: the update-rule consequences placing `x_k` and `y_k` in the convex hull of the
  prefix `v₀, …, v_k`, and the Euclidean-prox radius estimate used in the remark;
- core/canonical: `bounded_union_of_prefix_convex_hull_sequences` for boundedness and
  `quadraticallyRegularizedObjective` for the quadratic penalty;
- bridge/view: the source-facing shorthand `quadraticDistanceTo` and the prefix-membership lemmas
  that feed Proposition 6.8.

Primitive data:
- the iterate families `v`, `x`, `y` together with the source update identities;
- the seminorm owner `p` and center `x0` for the generic quadratic prox term;
- the Euclidean prox center `x0` and comparison point `xStar`.

Derived API:
- the generic seminorm-centered quadratic prox owner `Seminorm.quadraticDistanceTo`;
- prefix convex-hull membership of `x_k` and `y_k`;
- boundedness of the union of the three ranges via Proposition 6.8;
- the Euclidean radius estimate derived from the chapter's quadratic-regularization owner.

The Euclidean prox formula is now routed through the generic seminorm-centered quadratic owner
`Seminorm.quadraticDistanceTo`. The source-facing shorthand `quadraticDistanceTo` is retained
because it materially shortens the Euclidean theorem surface, but it is only the
`normSeminorm` specialization of that owner. -/

section PrefixConvexHull

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: argue by induction on `k`. The base case is `x₀ = v₀`, so `x₀` belongs to the
-- convex hull of the singleton prefix. For the step, use `x_succ_eq` to write `x_{k+1}` as a
-- convex combination of `x_k` and `v_{k+1}`, then enlarge the prefix from `v₀, ..., v_k` to
-- `v₀, ..., v_{k+1}`.
/-- The iterates `x_k` of the composite fast gradient method lie in the convex hull of the prefix
`v₀, ..., v_k` once the initialization satisfies `x₀ = v₀`. -/
theorem x_mem_prefix_convexHull_of_update
    (x v : ℕ → E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1)) :
    ∀ k : ℕ, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)) := sorry

-- Proof sketch: use `y_eq` to write `y_k` as a convex combination of `x_k` and `v_k`, then apply
-- `x_mem_prefix_convexHull` and the fact that `v_k` itself belongs to the same finite prefix hull.
/-- Every interpolation point `y_k` lies in the convex hull of the prefix `v₀, ..., v_k`. -/
theorem y_mem_prefix_convexHull_of_update
    (x y v : ℕ → E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1))
    (hy : ∀ k : ℕ,
      y k = (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v k) :
    ∀ k : ℕ, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)) := sorry

-- Proof sketch: derive the prefix convex-hull membership of `x_k` and `y_k` from the update
-- rules, then apply Proposition 6.8 to the resulting source-facing hypotheses.
/-- Remark 6.1.1: if method `(6.1.19)` starts from `x₀ = v₀`, then the update relations place
`x_k` and `y_k` in the convex hull of `v₀, ..., v_k`; if moreover
`‖v_k - x^*‖² ≤ 2 D` for all `k ≥ 0`, where `D` is the source scalar `d(x^*)`, then the iterates
`v_k`, `x_k`, and `y_k` form a bounded family. -/
theorem bounded_iterates_of_sqDist_bound
    (D : ℝ) (x y v : ℕ → E) (xStar : E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1))
    (hy : ∀ k : ℕ,
      y k = (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v k)
    (hv : ∀ k : ℕ, ‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * D) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := by
  refine bounded_union_of_prefix_convex_hull_sequences xStar D v x y ?_ ?_ ?_
  · exact x_mem_prefix_convexHull_of_update x v hx0 hxsucc
  · exact y_mem_prefix_convexHull_of_update x y v hx0 hxsucc hy
  · simpa using hv

end PrefixConvexHull

namespace Seminorm

section QuadraticDistance

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The quadratic prox function centered at `x₀` attached to the seminorm `p`. -/
def quadraticDistanceTo (p : Seminorm ℝ E) (x0 : E) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * p (x - x0) ^ (2 : ℕ)

/-- Evaluating `p.quadraticDistanceTo x₀` recovers the centered quadratic formula
`(1 / 2) p(x - x₀)^2`. -/
@[simp] theorem quadraticDistanceTo_apply
    (p : Seminorm ℝ E) (x0 x : E) :
    p.quadraticDistanceTo x0 x = (1 / 2 : ℝ) * p (x - x0) ^ (2 : ℕ) :=
  rfl

end QuadraticDistance

end Seminorm

section QuadraticDistance

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euclidean prox function centered at `x₀`, realized as the zero-objective specialization
of the seminorm-centered quadratic prox owner for the ambient norm. -/
abbrev quadraticDistanceTo (x0 : E) : E → ℝ :=
  (normSeminorm ℝ E).quadraticDistanceTo x0

/-- Evaluating `quadraticDistanceTo x₀` recovers the textbook formula
`(1 / 2) ‖x - x₀‖²`. -/
@[simp] theorem quadraticDistanceTo_apply (x0 x : E) :
    quadraticDistanceTo x0 x = (1 / 2 : ℝ) * ‖x - x0‖ ^ (2 : ℕ) := by
  simp [quadraticDistanceTo, Seminorm.quadraticDistanceTo]

-- Proof sketch: rewrite the prox function using `hprox`, then apply
-- `two_mul_quadraticDistanceTo`, identify `‖xStar - x0‖` with `‖x0 - xStar‖`, and then take
-- square roots on both sides of the resulting nonnegative inequality.
/-- Doubling `quadraticDistanceTo x₀ x` recovers the squared Euclidean distance `‖x - x₀‖²`. -/
theorem two_mul_quadraticDistanceTo (x0 x : E) :
    2 * quadraticDistanceTo x0 x = ‖x - x0‖ ^ (2 : ℕ) := sorry

-- Proof sketch: rewrite `2 * quadraticDistanceTo x0 xStar` as `‖xStar - x0‖²`, use symmetry of
-- the norm, and pass from the squared-distance bound to the norm bound.
/-- In the Euclidean prox choice `d(x) = (1 / 2) ‖x - x₀‖²`, the estimate
`‖v_k - x^*‖² ≤ 2 d(x^*)` yields the explicit radius bound `‖v_k - x^*‖ ≤ ‖x₀ - x^*‖`. -/
theorem euclidean_prox_radius_bound
    (x0 xStar : E) (v : ℕ → E)
    (hv : ∀ k : ℕ, ‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * quadraticDistanceTo x0 xStar) (k : ℕ) :
    ‖v k - xStar‖ ≤ ‖x0 - xStar‖ := sorry

end QuadraticDistance

end

/-! ### Text_6_1_1_Black_Box_Complexity_Barrier (from Chap06) -/
/- Domain note: this item lies in the chapter's nonsmooth first-order black-box complexity domain.

Mandatory domain-style sampling before refinement:
- `exists_problem_with_nonsmooth_firstOrder_lower_bound` in `Chap03/Theorem_3_2_1`, the chapter's
  canonical owner theorem for the nonsmooth black-box lower bound;
- `Theorem_3_39`, the earlier chapter recall that already records this owner theorem as the
  textbook barrier and explicitly notes that separate positivity guards on `R, M : NNReal` are
  redundant;
- `f_k` in `Chap03/Definition_3_35`, the source-facing Nemirovski hard-instance family;
- `f_k_minimizer` in `Chap03/Proposition_3_30`, the canonical minimizer attached to that explicit
  witness family.

Best owner abstraction:
- source-facing: Text 6.1.1 as the black-box `O(1 / ε^2)` barrier statement;
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`;
- bridge/view: the explicit Nemirovski witness family `f_k` with `f_k_minimizer`, which explains
  how the owner theorem can be realized but should not replace the owner surface here.

Primitive data on the owner surface:
- the dimension `n`;
- the starting point `x₀`;
- the radius and Lipschitz parameters `R M : NNReal`;
- the iteration index `k` with `k + 1 ≤ n`.

Derived API:
- existence of a hard instance `f` with chosen minimizer `xStar` in `𝒫(x₀, R, M)`;
- the lower bound for every first-order oracle satisfying the prefix-support-growth condition and
  every iterate sequence satisfying the linear-span condition for that oracle.

This Chapter 6 text item is therefore a direct recall of the canonical Chapter 3 owner theorem.
The explicit hard family `f_k` remains upstream as an auxiliary witness layer rather than the main
public declaration here.
-/

/- Text 6.1.1-Black-Box Complexity Barrier: the Chapter 3 black-box lower-bound theorem gives the
canonical `O(1 / ε^2)` oracle-complexity barrier for span-based nonsmooth convex minimization
under the resisting-oracle prefix-support-growth hypothesis, and the Nemirovski hard family `f_k`
explains this barrier constructively through explicit simple witness problems. -/
recall exists_problem_with_nonsmooth_firstOrder_lower_bound

/-! ### Text_6_1_1_Complexity_Insight (from Chap06) -/
noncomputable section

/- Text 6.1.1-Complexity Insight lies in the chapter's scalar oracle-complexity scaling domain.

Owner-style declarations sampled before refining:
* `sqrt_rate_complexity_bound` in `Chap01/Definition_1_2_5`, the earlier project owner for turning
  a square-root rate estimate into an explicit complexity threshold;
* `constantStepSchemeIII_objective_gap_le_geometric_rate` in `Chap02/Theorem_2_46`, the chapter
  accelerated-gradient owner carrying the canonical square-root rate factor on the method side;
* mathlib `Real.sqrt_le_sqrt` and `mul_le_mul_of_nonneg_left`, the canonical scalar-order tools
  governing the proof of the present rescaling lemma.

Best owner abstraction:
* source-facing: the displayed `ε⁻¹` oracle bound for the smoothed surrogate complexity estimate;
* core/canonical: the scalar comparison
  `L_μ / ε ≤ (C_L / c_μ) / ε^2` together with monotonicity of `Real.sqrt`;
* bridge/view: this theorem, which isolates the scalar oracle-count algebra from the surrounding
  smoothing and optimization statements.

Primitive data:
* the positive scale parameters `ε` and `cμ`;
* the fast-gradient prefactor `CF`;
* the smoothing-scale inequality `cμ * ε ≤ μ`;
* the Lipschitz-growth bound `Lμ ≤ CL / μ`;
* the input oracle-count estimate `(N : ℝ) ≤ CF * sqrt (Lμ / ε)`.

Derived API:
* the explicit inverse-`ε` oracle-count bound
  `(N : ℝ) ≤ (CF * Real.sqrt (CL / cμ)) / ε`.

This file is therefore kept at the scalar bridge layer. The nearby bundled Chapter 6 smoothing
theorem should reuse this atomic lemma for its oracle-count conclusion instead of carrying a
parallel local copy of the same algebra.
-/

/-- Text 6.1.1-Complexity Insight: if the smoothed surrogate has gradient Lipschitz constant
`L_μ` with `L_μ ≤ C_L / μ`, the smoothing parameter is chosen on the scale `μ ≳ ε`, and a fast
gradient method reaches an `ε`-approximation within `C_F * √(L_μ / ε)` oracle calls, then the
number of oracle calls is bounded by a constant multiple of `ε⁻¹`. -/
-- Proof sketch: if `Lμ / ε ≤ 0`, then the oracle estimate forces `N = 0`, so the conclusion is
-- immediate. Otherwise `Lμ ≥ 0`; the lower bound `cμ * ε ≤ μ` and positivity of `ε` imply
-- `μ > 0`, hence `L_μ / ε ≤ (C_L / c_μ) / ε^2`. Taking square roots and multiplying by the
-- fast-gradient prefactor `C_F` gives the displayed `1 / ε` oracle-complexity bound.
theorem fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation
    {ε μ Lμ CL CF cμ : ℝ} (hε : 0 < ε) (hcμ : 0 < cμ) (hCF : 0 ≤ CF)
    (hμ : cμ * ε ≤ μ) (hLμ : Lμ ≤ CL / μ) {N : ℕ}
    (hN : (N : ℝ) ≤ CF * Real.sqrt (Lμ / ε)) :
    (N : ℝ) ≤ (CF * Real.sqrt (CL / cμ)) / ε := by
  by_cases hLμε_nonneg : 0 ≤ Lμ / ε
  · have hμ_pos : 0 < μ := lt_of_lt_of_le (mul_pos hcμ hε) hμ
    have hLμ_nonneg : 0 ≤ Lμ := by
      have hscaled : 0 ≤ (Lμ / ε) * ε := mul_nonneg hLμε_nonneg hε.le
      simpa [div_eq_mul_inv, mul_assoc, hε.ne'] using hscaled
    have hμLμ_le : μ * Lμ ≤ CL := by
      have hscaled := mul_le_mul_of_nonneg_right hLμ hμ_pos.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hμ_pos.ne'] using hscaled
    have hCL : 0 ≤ CL := le_trans (mul_nonneg hμ_pos.le hLμ_nonneg) hμLμ_le
    have hLμ_le : Lμ ≤ CL / (cμ * ε) := by
      refine (le_div_iff₀ (mul_pos hcμ hε)).2 ?_
      have hscaled := mul_le_mul_of_nonneg_right hμ hLμ_nonneg
      exact (le_trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled) hμLμ_le)
    have hratio : Lμ / ε ≤ (CL / cμ) / ε ^ (2 : ℕ) := by
      have hdiv := div_le_div_of_nonneg_right hLμ_le hε.le
      simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hCLcμ : 0 ≤ CL / cμ := div_nonneg hCL hcμ.le
    have hsqrt_split : Real.sqrt ((CL / cμ) / ε ^ (2 : ℕ)) = Real.sqrt (CL / cμ) / ε := by
      rw [Real.sqrt_div hCLcμ, Real.sqrt_sq_eq_abs, abs_of_pos hε]
    calc
      (N : ℝ) ≤ CF * Real.sqrt (Lμ / ε) := hN
      _ ≤ CF * Real.sqrt ((CL / cμ) / ε ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) hCF
      _ = (CF * Real.sqrt (CL / cμ)) / ε := by
        rw [hsqrt_split]
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]
  · have hN_zero : (N : ℝ) ≤ 0 := by
      simpa [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hLμε_nonneg)] using hN
    have hrhs_nonneg : 0 ≤ (CF * Real.sqrt (CL / cμ)) / ε := by
      exact div_nonneg (mul_nonneg hCF (Real.sqrt_nonneg _)) hε.le
    exact le_trans hN_zero hrhs_nonneg

end

/-! ### Text_6_1_1_Conjugate_Closedness_and_Domain_Nonemptiness (from Chap06) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-conjugacy / effective-epigraph domain.

Primary domain:
- the source-facing Fenchel dual `f⋆`, its effective domain `dom (f⋆)`, and its effective
  epigraph `effectiveEpigraph (f⋆)` on a real inner-product space.

Mandatory domain-style sampling before refinement:
- `fenchelDual` and the notation `f⋆` in `Chap03/Definition_3_1_2_1`, the source-facing Fenchel
  dual owner on real inner-product spaces;
- `subdifferential` and the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `effectiveEpigraph` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter
  owners for the `EReal` effective epigraph and finite real part;
- `subdifferential_subset_dom_fenchelDual` in `Chap03/Theorem_3_1_5_2`, the canonical
  subdifferential-to-dual-domain bridge already used downstream in later Fenchel files.

Best owner abstraction:
- core/canonical: the chapter owner stack `f⋆`, `dom (f⋆)`, and `effectiveEpigraph (f⋆)`;
- bridge/view: `IsClosed (effectiveEpigraph (f⋆))`, `Convex ℝ (effectiveEpigraph (f⋆))`, and the
  domain corollary derived from `subdifferential_subset_dom_fenchelDual`.

Primitive data:
- `f : E → WithTop ℝ`;
- the point `x : E` for the subdifferential-domain inclusion.

Derived API in this file:
- the source-facing theorem that `effectiveEpigraph (f⋆)` is closed and convex;
- the domain nonemptiness corollary from a nonempty subdifferential.

Source/core/bridge triage:
- source-facing: the textbook claims about the effective epigraph of the Fenchel dual and the
  finiteness of the dual at subgradients;
- core/canonical: `f⋆`, `dom (f⋆)`, and the chapter owner stack around `effectiveEpigraph`;
- bridge/view: `effectiveEpigraph (f⋆)` and the subdifferential-domain inclusion.

The previous version kept an extra local companion for the owner-level convexity surface of `f⋆`.
That surface already belongs upstream in the Chapter 3 Fenchel stack, so this file now keeps only
the source-facing closed-convex epigraph statement together with the domain consequence needed in
later Chapter 5/6 Fenchel files.
-/

-- Proof sketch: a Fenchel conjugate is convex on its effective domain, and Theorem 3.1.1.2
-- converts that owner-level convexity into convexity of the effective epigraph; closedness is the
-- standard epigraph closedness property of conjugates.
/-- Text 6.1.1-Conjugate Closedness and Domain Nonemptiness: the Fenchel dual has a closed and
convex effective epigraph. The domain nonemptiness consequence is recorded separately below. -/
theorem fenchelDual_effectiveEpigraph_closed_convex
    (f : E → WithTop ℝ) :
    IsClosed (effectiveEpigraph (f⋆)) ∧
      Convex ℝ (effectiveEpigraph (f⋆)) := sorry

-- The owner-level `ConvexOn` surface for `f⋆` is already the canonical Chapter 3 API, so this
-- file does not keep a second local theorem for it.

-- Proof sketch: choose `g ∈ ∂ f(x)` from the nonempty subdifferential and apply the inclusion
-- theorem above.
/-- If some subdifferential of `f` is nonempty, then the effective domain of the Fenchel dual is
nonempty. -/
theorem dom_fenchelDual_nonempty_of_subdifferential_nonempty
    {f : E → WithTop ℝ} {x : E} (hsub : (∂ f(x)).Nonempty) :
    (dom (f⋆)).Nonempty := sorry

end

/-! ### Text_6_1_1_Smoothing_Approximation_Error (from Chap06) -/
noncomputable section

open Module
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped ConvexAnalysis BInducedNorm

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-smoothing / dual-norm domain.

Relevant sampled declarations in this domain:
- `fenchelSmoothApproximation` in `Chap06/Definition_6_2`, the chapter owner for the quadratically
  regularized Fenchel supremum;
- `fenchelSmoothApproximation_apply` in `Chap06/Definition_6_2`, the owner evaluation theorem;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the canonical dual object feeding the smoothing
  construction;
- `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the finite-value domain of an
  `EReal`-valued function.

Best owner abstraction:
- source-facing: the approximation-error bound for `fenchelSmoothApproximation`;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: its zero-penalty specialization, which is exactly the unsmoothed Fenchel supremum
  model used in the textbook statement.

Primitive data:
- `B : BilinForm ℝ E` with positive-definiteness;
- `f : E → EReal`;
- the smoothing parameter `μ`, the radius bound `L`, and the dual-domain bound `hdual`.

Derived API:
- the zero-penalty expansion `fenchelSmoothApproximation_zero_apply`;
- the owner-level comparison with the zero-penalty specialization
  `fenchelSmoothApproximation_zero_bounds`;
- the source-facing approximation-error theorem below.

Source/core/bridge triage:
- source-facing: the error estimate itself;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: the theorem identifying the unsmoothed Fenchel supremum with the `μ = 0`
  specialization of that owner, and the source-facing bridge from that owner-level comparison back
  to `f x`.

This item does not introduce a second unsmoothed owner. The previous local
`fenchelApproximationMaximand` / `fenchelApproximation` pair duplicated the Chapter 6 owner
`fenchelSmoothApproximation`; the unsmoothed model is only the zero-penalty specialization of that
owner, so this file now exposes it only as a bridge theorem.
-/

/-- Setting the smoothing parameter to `0` recovers the unsmoothed Fenchel supremum model. -/
@[simp] theorem fenchelSmoothApproximation_zero_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (x : E) :
    fenchelSmoothApproximation B f 0 x =
      sSup ((fun s : Dual ℝ E ↦ (s x : EReal) - fenchelConjugate f s) ''
        dom (fenchelConjugate f)) := by
  simp [fenchelSmoothApproximation, fenchelSmoothApproximationMaximand]

-- Proof sketch: the upper bound follows because the smoothed maximand is obtained from the
-- unsmoothed one by subtracting the nonnegative penalty `(μ / 2) ‖s‖[B,*]^2`.
-- For the lower bound, use the domain estimate `‖s‖[B,*] ≤ L` on every dual point
-- contributing to the
-- supremum, so the penalization removes at most `(μ * L^2) / 2` from the Fenchel representation
-- of `f`.
/-- Under the dual-domain radius bound `‖s‖[B,*] ≤ L`, the zero-penalty specialization dominates
every smoothed value and differs from it by at most `((μ * L^2) / 2 : NNReal)`. This is the
owner-level smoothing comparison, before identifying the zero-penalty value with `f x`. -/
theorem fenchelSmoothApproximation_zero_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L) :
    fenchelSmoothApproximation B f 0 x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        fenchelSmoothApproximation B f 0 x - ((μ * L ^ 2) / 2 : NNReal) := sorry

-- Proof sketch: apply the owner-level comparison `fenchelSmoothApproximation_zero_bounds` and
-- rewrite its zero-penalty endpoint with the source-facing representation hypothesis `hf`.
/-- Text 6.1.1-Smoothing Approximation Error: if `f` is represented by the Fenchel supremum model
associated to its Fenchel conjugate at `x`, equivalently by the zero-penalty specialization of
`fenchelSmoothApproximation` at that point, and every `s ∈ dom (fenchelConjugate f)` satisfies
the dual estimate
`‖s‖[B,*] ≤ L`, then the smoothed approximation `f_μ` lies between `f` and
`f - (μ * L^2) / 2` on the canonical `EReal` surface. -/
theorem fenchelSmoothApproximation_error_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hf : f x = fenchelSmoothApproximation B f 0 x)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L)
    :
    f x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        f x - ((μ * L ^ 2) / 2 : NNReal) := by
  simpa [hf] using fenchelSmoothApproximation_zero_bounds B f x hdual

end

/-! ### Text_6_1_1_Structure_Helps_Beyond_Black_Box (from Chap06) -/
universe u

section

variable {E : Type u}

/- Text 6.1.1 lies in the chapter's surrogate-smoothing / oracle-complexity bridge domain.

Sampled owner-style declarations:
* `IsApproximateSolution` in `Chap03/Definition_3_34`, the chapter's source-facing owner for an
  `ε`-accurate unconstrained solution relative to a chosen minimizer `xStar`;
* `isApproximateSolution_iff_isApproximateMinimizer` in `Chap03/Definition_3_34`, the canonical
  bridge from that source-facing owner to the Chapter 1 approximate-minimizer API on
  `SetConstrainedMinimizationProblem.unconstrained f`;
* mathlib `IsMinOn`, the canonical owner of exact minimizers on `Set.univ`;
* `fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation` in
  `Text_6_1_1_Complexity_Insight`, the Chapter 6 owner for the scalar `ε⁻¹` oracle bound.

Best owner abstraction:
* source-facing: the statement that a structured smoothing scheme yields a genuine Chapter 3
  `IsApproximateSolution f xStar ε x` once `xStar` is fixed as an exact minimizer of `f`, together
  with an explicit oracle bound;
* core/canonical: `IsApproximateSolution`, the surrogate minimizer owner
  `IsMinOn fμ Set.univ xμStar`, and the imported scalar oracle-complexity theorem;
* bridge/view: the transfer from surrogate suboptimality to the raw objective-gap inequality
  `f x - f xStar ≤ ε`, and then from that inequality to the Chapter 3 approximate-solution owner
  via an exact minimizer of `f`.

Primitive data:
* the surrogate minimizer witness `hxμStar : IsMinOn fμ Set.univ xμStar`;
* the lower and upper approximation inequalities relating `f` and `fμ`;
* the surrogate suboptimality estimate at `x`;
* the scale choice `cμ * ε ≤ μ`, the Lipschitz-growth bound `Lμ ≤ CL / μ`, and the input oracle
  estimate.

Derived API:
* the raw suboptimality estimate `f x - f xStar ≤ ε` against an arbitrary comparison point;
* `IsApproximateSolution f xStar ε x` once `xStar` is also assumed to be an exact minimizer of
  `f`;
* the explicit inverse-`ε` oracle bound from the imported scalar owner theorem.

The file therefore stays at the bridge layer: it does not introduce a parallel smoothing package,
and it keeps only the primitive assumptions actually needed to derive the raw suboptimality,
approximate-solution, and complexity conclusions.
-/

-- Proof sketch: compare the original objective and the smoothed surrogate at `x` and at a
-- comparison point `xStar`. The lower approximation bound gives
-- `f x ≤ fμ x + ε / 2`, the surrogate suboptimality gives
-- `fμ x ≤ fμ xμStar + ε / 2`, the minimizer property of `xμStar` and the upper approximation bound
-- give `fμ xμStar ≤ fμ xStar ≤ f xStar`, and rearranging yields the raw objective-gap estimate
-- `f x - f xStar ≤ ε`.
/-- If the smoothed surrogate approximates the original objective within `ε / 2` from below and
never exceeds it, then an `ε / 2`-accurate point for the surrogate relative to an exact smoothed
minimizer has original objective value at most `ε` above any chosen comparison point `xStar`. -/
theorem sub_le_epsilon_of_smoothedObjective_suboptimality
    {f fμ : E → ℝ} {x xStar xμStar : E} {ε : ℝ}
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2) :
    f x - f xStar ≤ ε := by
  have hxμStar_le : fμ xμStar ≤ fμ xStar := (isMinOn_univ_iff.mp hxμStar) xStar
  linarith [happrox_lower x, hstructured_step, hxμStar_le, happrox_upper xStar]

-- Proof sketch: first derive the raw objective-gap estimate from
-- `sub_le_epsilon_of_smoothedObjective_suboptimality`, then use the exact minimizer hypothesis on
-- `xStar` to convert that inequality to the genuine Chapter 3 approximate-solution owner.
/-- If `xStar` is an exact minimizer of `f`, the smoothed-surrogate suboptimality estimate above
upgrades to the genuine Chapter 3 statement that `x` is an `ε`-approximate solution of `f`
relative to `xStar`. -/
theorem isApproximateSolution_of_smoothedObjective_suboptimality
    {f fμ : E → ℝ} {x xStar xμStar : E} {ε : ℝ}
    (hxStar : IsMinOn f Set.univ xStar)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2) :
    IsApproximateSolution f xStar ε x := by
  rw [isApproximateSolution_iff_isApproximateMinimizer hxStar]
  exact
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).2
      (sub_le_epsilon_of_smoothedObjective_suboptimality
        hxμStar happrox_lower happrox_upper hstructured_step)

-- Proof sketch: the approximation assumptions transfer `ε / 2` surrogate accuracy to the Chapter
-- 6 raw objective-gap estimate by `sub_le_epsilon_of_smoothedObjective_suboptimality`. For
-- the oracle bound, combine
-- `Lμ ≤ CL / μ` with the scale choice `μ ≥ cμ * ε` and positivity of `ε` to get
-- `Lμ / (ε / 2) ≤ (2 * CL / cμ) / ε^2`; taking square roots and multiplying by `CF` yields the
-- displayed `1 / ε` estimate.
/-- Text 6.1.1-Structure Helps Beyond Black-Box: once an objective admits a structured smoothing
scheme whose surrogate `f_μ` lies between `f` and `f + ε / 2`, whose gradient Lipschitz constant
satisfies `L_μ ≤ C_L / μ`, and whose smoothing parameter is chosen on the scale `μ ≳ ε`, any
fast-gradient method that solves the surrogate to accuracy `ε / 2` produces a point whose
original objective value is at most `ε` above any chosen comparison point `xStar`, with oracle
complexity bounded by a constant multiple of `ε⁻¹`. -/
theorem structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound
    {f fμ : E → ℝ} {x xStar xμStar : E}
    {ε μ Lμ CL CF cμ : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hcμ : 0 < cμ)
    (hCF : 0 ≤ CF)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hμ : cμ * ε ≤ μ)
    (hLμ : Lμ ≤ CL / μ)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2)
    (horacle : (N : ℝ) ≤ CF * Real.sqrt (Lμ / (ε / 2))) :
    f x - f xStar ≤ ε ∧
      (N : ℝ) ≤ (CF * Real.sqrt (2 * CL / cμ)) / ε := by
  refine ⟨?_, ?_⟩
  · exact
      sub_le_epsilon_of_smoothedObjective_suboptimality hxμStar
        happrox_lower happrox_upper hstructured_step
  · have horacle' : (N : ℝ) ≤ CF * Real.sqrt ((2 * Lμ) / ε) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      have hrewrite : Lμ / (ε / 2) = (2 * Lμ) / ε := by
        field_simp [hε_ne]
      simpa [hrewrite] using horacle
    have hLμ' : 2 * Lμ ≤ (2 * CL) / μ := by
      have hscaled := mul_le_mul_of_nonneg_left hLμ (show 0 ≤ (2 : ℝ) by positivity)
      simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation
        hε hcμ hCF hμ hLμ' horacle'

-- Proof sketch: combine the raw objective-gap theorem
-- `structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound` with the exact
-- minimizer bridge for `IsApproximateSolution`.
/-- Text 6.1.1-Structure Helps Beyond Black-Box: if `xStar` is an exact minimizer of `f`, then
structured smoothing turns the surrogate `ε / 2`-accuracy guarantee into the genuine Chapter 3
statement `IsApproximateSolution f xStar ε x`, while keeping the oracle complexity bounded by a
constant multiple of `ε⁻¹`. -/
theorem structured_smoothing_yields_approximateSolution_with_inv_epsilon_oracle_bound
    {f fμ : E → ℝ} {x xStar xμStar : E}
    {ε μ Lμ CL CF cμ : ℝ} {N : ℕ}
    (hxStar : IsMinOn f Set.univ xStar)
    (hε : 0 < ε)
    (hcμ : 0 < cμ)
    (hCF : 0 ≤ CF)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hμ : cμ * ε ≤ μ)
    (hLμ : Lμ ≤ CL / μ)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2)
    (horacle : (N : ℝ) ≤ CF * Real.sqrt (Lμ / (ε / 2))) :
    IsApproximateSolution f xStar ε x ∧
      (N : ℝ) ≤ (CF * Real.sqrt (2 * CL / cμ)) / ε := by
  rcases structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound
      hε hcμ hCF hxμStar happrox_lower happrox_upper hμ hLμ hstructured_step horacle with
    ⟨hsub, horacle_bound⟩
  refine ⟨?_, horacle_bound⟩
  rw [isApproximateSolution_iff_isApproximateMinimizer hxStar]
  exact
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).2 hsub

end

/-! ### Theorem_6_1 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 6.1 lies in the chapter's prox-smoothed maximization domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter owner of the regularized-max
  smoothing formula;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the canonical argmax-set owner for the
  textbook maximizer `u_μ(x)`;
- `smoothedPrimalObjective_apply` in `Definition_6_30`, the source-facing supremum formula for the
  smoothed objective;
- `smoothed_maximizer_unique` in `Proposition_6_6`, the chapter uniqueness theorem showing that
  convexity of `phiHat` together with strong convexity of `d2` is the actual structural input for
  uniqueness of the maximizer.

Best owner abstraction:
- source-facing: the prox-smoothed objective `smoothedPrimalObjective A Q 0 phiHat d2 μ` and its
  differentiability properties;
- core/canonical: `smoothedPrimalObjective` together with the pointwise argmax owner
  `smoothedPrimalObjectiveArgmax`;
- bridge/view: a choice `uMu : E₁ → E₂` recorded only through the membership hypothesis
  `uMu x ∈ smoothedPrimalObjectiveArgmax ... x`, used only when the selected maximizer itself
  appears in the conclusion.

Primitive data:
- the linear map `A`, feasible set `Q`, nonsmooth term `phiHat`, prox term `d2`, and smoothing
  parameter `μ`;
- existence of points in the canonical argmax set;
- when needed for derivative-identification statements, a pointwise choice `uMu` of elements of the
  canonical argmax set.

Derived API:
- evaluation of the smoothed supremum at an argmax point;
- convexity and continuous differentiability of the smoothed objective from canonical argmax
  existence;
- derivative identification and Lipschitz control from a chosen argmax selection.

Source/core/bridge triage:
- source-facing: Theorem 6.1's four properties of the prox-smoothed objective;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`;
- bridge/view: a selected map `uMu` into the argmax set.

The previous version introduced a parallel public predicate
`IsSmoothedObjectiveMaximizerSelection` and carried stronger ambient hypotheses than the owner
surface needs. This file now uses the canonical argmax owner directly and keeps only the convexity
and strong-convexity hypotheses that match the uniqueness/smoothness mechanism. -/

/-- Any point of `smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x` realizes the supremum defining
the smoothed objective at `x`. -/
-- Proof sketch: the argmax property makes `u` an upper bound for the image of the penalized
-- maximand on `Q`, and evaluating at `u` gives the matching lower bound.
theorem smoothedPrimalObjectiveArgmax.value_eq
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q : Set E₂} {phiHat d2 : E₂ → ℝ} {μ : ℝ}
    {x : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    smoothedPrimalObjective A Q 0 phiHat d2 μ x =
      smoothedPrimalObjectiveMaximand A phiHat d2 μ x u := sorry

/-- Theorem 6.1 (1): the prox-smoothed dual supremum is convex on all of `E₁`. -/
-- Proof sketch: each map `x ↦ A x u - phiHat u - μ * d2 u` is affine in `x`, so the supremum
-- over `u ∈ Q` is convex.
theorem smoothedObjective_convex
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q : Set E₂) (phiHat d2 : E₂ → ℝ) (μ : ℝ) :
    ConvexOn ℝ Set.univ (smoothedPrimalObjective A Q 0 phiHat d2 μ) := sorry

/-
Theorem 6.1 splits into four atomic declarations: if `phiHat` is convex on `Q`, `d2` is `C¹` and
`1`-strongly convex on `Q`, and the canonical argmax set is nonempty at each `x`, then the
smoothed objective is convex and continuously differentiable. When a selected maximizer
`uMu x ∈ smoothedPrimalObjectiveArgmax ... x` is also fixed, the derivative is `A.flip (uMu x)` at
each `x`, and this derivative map is Lipschitz with constant `(1 / μ) * ‖A‖^2`.
-/
section Theorem61

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (Q : Set E₂) (phiHat d2 : E₂ → ℝ) {μ : ℝ}
  (uMu : E₁ → E₂)

/-- Theorem 6.1 (2): under the smoothing hypotheses, the smoothed objective is continuously
differentiable. -/
-- Proof sketch: apply Danskin's theorem to the supremum formula, using convexity of `phiHat`,
-- strong convexity of `d2`, and the nonemptiness of the canonical argmax set to obtain the unique
-- maximizer at each `x`.
theorem smoothedObjective_contDiff
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax : ∀ x, (smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x).Nonempty) :
    ContDiff ℝ 1 (smoothedPrimalObjective A Q 0 phiHat d2 μ) := sorry

/-- Theorem 6.1 (3): under the smoothing hypotheses, the derivative of the smoothed objective at
`x` is `A.flip (uMu x)`. -/
-- Proof sketch: combine the unique-maximizer form of Danskin's theorem with the canonical pairing
-- identity `(A.flip u) x = A x u`.
theorem smoothedObjective_hasFDerivAt
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ y, uMu y ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ y)
    (x : E₁) :
    HasFDerivAt (smoothedPrimalObjective A Q 0 phiHat d2 μ) (A.flip (uMu x)) x := sorry

/-- Theorem 6.1 (4): under the smoothing hypotheses, the derivative selection
`x ↦ A.flip (uMu x)` is Lipschitz with constant `(1 / μ) * ‖A‖^2`. -/
-- Proof sketch: compare the optimality conditions at two points, use monotonicity of the convex
-- part together with convexity of `phiHat` and the `1`-strong convexity of `d2`, and bound the
-- adjoint difference by
-- `‖A‖^2 / μ`.
theorem smoothedObjective_gradient_lipschitz
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    LipschitzWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) (fun x ↦ A.flip (uMu x)) := sorry

end Theorem61

end

/-! ### Example_6_1_2 (from Chap06) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]

/- Example 6.1.2 lies in the chapter's prox-function / prox-center quadratic-growth domain.

Primary domain:
- prox-functions and normalized prox-centers on real normed spaces

Sampled owner declarations:
- `IsProxFunction` in `Definition_6_31`, the chapter owner for prox-function data
- `IsProxCenter` in `Definition_6_31`, the chapter owner for normalized prox-center data
- `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Definition_2_14`, the
  canonical quadratic-growth theorem behind the chapter specialization
- `prox_center_quadratic_lower_bound` in `Proposition_6_5`, the exact chapter-level owner theorem
  for this lower bound

Best owner abstraction:
- source-facing: the quadratic lower bound at a normalized prox-center
- core/canonical: `IsProxFunction p Q d`, `IsProxCenter Q d x₀`, and
  `prox_center_quadratic_lower_bound`
- bridge/view: the source's differentiability wording is auxiliary here and does not enter the
  owner theorem, since the lower-bound proof uses only strong convexity, minimality, and the
  normalization `d x₀ = 0`

Primitive data:
- the feasible set `Q`
- the prox-function owner `hd : IsProxFunction p Q d`
- the normalized prox-center owner `hx₀ : IsProxCenter Q d x₀`
- the comparison point `u ∈ Q`

Derived API:
- `hd.strongConvexOnWith`
- `hx₀.mem`, `hx₀.isMinOn`, and `hx₀.value_eq_zero`
- the quadratic lower bound itself

This file therefore does not keep a second local theorem with the same mathematical content under
raw `DifferentiableOn` / `StrongConvexOn` / `IsMinOn` hypotheses. The exact owner theorem already
exists upstream in `Proposition_6_5`, so Example 6.1.2 should be a direct recall surface. -/

section

variable {Q : Set E} {d : E → ℝ} {x₀ u : E}

/- Example 6.1.2: a normalized prox-center of a prox-function on `Q` gives the quadratic lower
bound `d u ≥ (1 / 2) p(u - x₀)^2` at every feasible point `u ∈ Q`. -/
recall prox_center_quadratic_lower_bound
    (hd : IsProxFunction p Q d)
    (hx₀ : IsProxCenter Q d x₀)
    (hu : u ∈ Q) :
    d u ≥ (1 / 2 : ℝ) * (p (u - x₀)) ^ (2 : ℕ)

end

/-! ### Remark_6_1_2 (from Chap06) -/
/- Remark 6.1.2 lies in the chapter's primal-dual weak-duality / no-gap closure domain.

Primary domain:
- order-theoretic closure of the primal/adjoint bounds `f^* ≤ f_*` and `f_* ≤ f^*`

Sampled owner-style declarations:
- `StructuredObjectiveModel.weakDuality` in `Chap06/Proposition_6_4`, the chapter owner theorem
  supplying the weak-duality bound `f_* ≤ f^*`
- `LagrangianProblem.noDualityGap_of_primalOptimalValue_le_dualOptimalValue` in
  `Chap06/Proposition_6_12`, the chapter-level owner-pattern that packages a reverse bound with
  the relevant weak-duality theorem
- `le_antisymm`, the canonical order owner that turns opposite inequalities into equality
- the linear-order instance on `ℝ`, which specializes `le_antisymm` to scalar primal/adjoint
  values with no extra wrapper data

Best owner abstraction:
- source-facing: the no-duality-gap conclusion from the reverse inequality `(6.1.28)`
- core/canonical: `le_antisymm`
- bridge/view: the specialization of `le_antisymm` to the scalar primal and adjoint optimal
  values, with the weak-duality side supplied upstream by `StructuredObjectiveModel.weakDuality`

Primitive data:
- two scalar values `primalOptimalValue adjointOptimalValue : ℝ`
- the opposite inequalities between them

Derived API:
- the equality `primalOptimalValue = adjointOptimalValue`

Source/core/bridge triage:
- source-facing: no duality gap for the primal-dual pair once `(6.1.28)` gives the reverse bound
- core/canonical: `le_antisymm`
- bridge/view: interpreting the two scalar inequalities as the primal/adjoint value bounds

This item adds no new mathematical owner beyond antisymmetry in a linear order. Keeping a local
theorem named for primal and adjoint values would duplicate the canonical owner with an exact
interface shell, so the file is refined to a pure recall surface. -/

/- Remark 6.1.2 uses the canonical antisymmetry owner directly. -/
recall le_antisymm {α : Type*} [PartialOrder α] {a b : α} : a ≤ b → b ≤ a → a = b

example {primalOptimalValue adjointOptimalValue : ℝ}
    (hgap : primalOptimalValue ≤ adjointOptimalValue)
    (hweak : adjointOptimalValue ≤ primalOptimalValue) :
    primalOptimalValue = adjointOptimalValue :=
  le_antisymm hgap hweak

/-! ### Text_6_1_2_Adjoint_Problem_Tractability_Caveat (from Chap06) -/
noncomputable section

universe u v

open scoped ConstrainedArgmin

/- Text 6.1.2 lies in the chapter's structured saddle-value / constrained-argmin domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the chapter owner for
  the adjoint value function on `Q₂`, canonically valued in `EReal`;
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the canonical saddle
  slice whose infimum defines the adjoint objective;
- `constrainedArgmin` with notation `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project owner
  for minimizers over a feasible set;
- `cubicRegularizationValue_eq_of_mem_argmin` in `Chap04/Definition_4_1_3`, a chapter-level
  attained-infimum bridge stated directly from `argmin` membership instead of a selector package.

Source/core/bridge triage:
- source-facing: for a fixed `u ∈ Q₂`, evaluating `φ(u)` requires solving the inner minimization
  problem on `Q₁`;
- core/canonical: `problem.adjointObjective u`, `problem.saddleFunction x u`, and
  `argmin[problem.primalSet]
    (fun x ↦ (problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u : EReal))`;
- bridge/view: an attained-inner-minimum theorem identifying `problem.adjointObjective u` with the
  saddle value at a pointwise argmin.

Primitive data:
- `problem : StructuredObjectiveModel E₁ E₂`;
- `u : problem.dualSet`;
- `x : problem.primalSet`;
- the minimizer witness
  `IsMinOn
    (fun y : E₁ ↦
      (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
    problem.primalSet x`.

Derived API:
- the induced equality `problem.adjointObjective u = problem.saddleFunction x u`;
- the expanded textbook formula as a thin `EReal` companion;
- the `argmin`-surface corollary for a primal feasible point whose ambient representative lies in
  the canonical argmin set.

The previous version used the later specialized owner `PrimalDualObjectiveModel`. This refinement
moves Text 6.1.2 down to the chapter's canonical owner `StructuredObjectiveModel`, keeps the main
bridge directly on `adjointObjective`, `saddleFunction`, and `argmin`, and leaves the expanded
formula as a thin companion in the chapter's `EReal` encoding.
-/

namespace StructuredObjectiveModel

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Text 6.1.2-Adjoint Problem Tractability Caveat: for a fixed `u ∈ Q₂`, any point of the
fixed-`u` saddle slice `x ↦ Ψ(x, u)` over `Q₁` evaluates the adjoint objective `φ(u)` via the
chapter's `EReal` owner. -/
theorem adjointObjective_eq_saddleFunction_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    problem.adjointObjective u = (problem.saddleFunction x u : EReal) := by
  rw [isMinOn_iff] at hx
  have hsaddleLeast :
      IsLeast
        (Set.range fun y : problem.primalSet ↦ (problem.saddleFunction y u : EReal))
        (problem.saddleFunction x u : EReal) := by
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (hx y y.property).trans_eq <| by simp [saddleFunction]
  rw [problem.adjointObjective_apply]
  exact hsaddleLeast.csInf_eq

/-- A primal feasible point whose ambient representative belongs to the canonical argmin set of
the fixed-`u` saddle slice evaluates the adjoint objective `φ(u)` via the chapter's `EReal`
owner. -/
theorem adjointObjective_eq_saddleFunction_of_mem_argmin
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : (x : E₁) ∈
      argmin[problem.primalSet]
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))) :
    problem.adjointObjective u = (problem.saddleFunction x u : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨_, hx_min⟩
  exact adjointObjective_eq_saddleFunction_of_isMinOn <| by
    simpa using hx_min

/-- Expanding `adjointObjective_eq_saddleFunction_of_isMinOn` yields the textbook formula
`φ(u) = -\hat φ(u) + (\langle A x, u \rangle + \hat f(x))` as a thin companion in the chapter's
`EReal` encoding. -/
theorem adjointObjective_eq_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    problem.adjointObjective u =
      ((-problem.dualPenalty u + (problem.linearMap x u + problem.smoothPart x)) : EReal) := by
  simpa [saddleFunction, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    adjointObjective_eq_saddleFunction_of_isMinOn hx

/-- Expanding `adjointObjective_eq_saddleFunction_of_mem_argmin` yields the textbook formula
`φ(u) = -\hat φ(u) + (\langle A x, u \rangle + \hat f(x))` for any ambient-space argmin point. -/
theorem adjointObjective_eq_of_mem_argmin
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : E₁}
    (hx : x ∈
      argmin[problem.primalSet]
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))) :
    problem.adjointObjective u =
      ((-problem.dualPenalty u + (problem.linearMap x u + problem.smoothPart x)) : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  let x' : problem.primalSet := ⟨x, hx_mem⟩
  have hx'_min :
      IsMinOn
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
        problem.primalSet x' := by
    simpa [x'] using hx_min
  simpa [saddleFunction, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    adjointObjective_eq_saddleFunction_of_isMinOn hx'_min

end StructuredObjectiveModel

end

/-! ### Text_6_1_2_Nonunique_Structured_Representation (from Chap06) -/
noncomputable section

open scoped ConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Text 6.1.2 lies in the chapter's Fenchel-conjugacy / structured-objective bridge domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.objective` and `StructuredObjectiveModel.objective_apply` in
  `Chap06/Definition_6_6`, the canonical owner of Chapter 6 structured objectives;
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the chapter owner
  for the dual objective on `StrongDual ℝ E`;
- `strongFenchelConjugate` in `Chap06/Definition_6_1`, the reusable continuous-dual bridge owner
  for real-valued objectives on normed spaces;
- `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical finite-domain /
  finite-real-part bridge for the dual objective;
- `NormedSpace.inclusionInDoubleDual`, the canonical evaluation map `x ↦ (s ↦ s x)`.

Best owner abstraction:
- source-facing: the claim that the Fenchel-conjugate formula gives a structured representation of
  the objective;
- core/canonical: `StructuredObjectiveModel.objective`;
- bridge/view: the specialization with `smoothPart = 0`,
  `linearMap = NormedSpace.inclusionInDoubleDual ℝ E`,
  `dualSet = dom (strongFenchelConjugate f)`, and
  `dualPenalty = extendedRealRealPart (strongFenchelConjugate f)`.

Primitive data:
- the real-valued objective `f : E → ℝ`;
- a structured model `problem : StructuredObjectiveModel E (StrongDual ℝ E)`;
- a primal point `x : problem.primalSet`.

Derived API:
- the explicit Fenchel-conjugate expansion of `problem.objective x` under the bridge hypotheses;
- the source-facing equality `problem.objective x = f x` when the Fenchel formula represents `f`
  at `x`.

Source/core/bridge triage:
- source-facing: the representation of `f` by the Fenchel formula;
- core/canonical: `StructuredObjectiveModel.objective`;
- bridge/view: the theorems below identifying that owner objective with the Fenchel formula.

The previous file introduced a second root owner `fenchelDualRepresentation` and weakened the
statement to an arbitrary dual penalty `fStar`. This refinement deletes that duplicate owner,
keeps the actual Fenchel-conjugate data on the theorem surface through the reusable bridge owner
`strongFenchelConjugate`, and states Text 6.1.2 as a bridge from those canonical data to the
existing Chapter 6 structured-objective owner.
-/

/- The canonical double-dual inclusion is the structured linear term used in the Fenchel
representation. -/
recall NormedSpace.inclusionInDoubleDual

namespace StructuredObjectiveModel

variable (f : E → ℝ)

/-- Text 6.1.2, bridge form: if a structured model uses zero smooth part, the canonical
double-dual inclusion, and the actual Fenchel conjugate data of `f`, then its owner objective is
exactly the Fenchel-conjugate representation formula. -/
theorem objective_eq_fenchelConjugate_representation
    (problem : StructuredObjectiveModel E (StrongDual ℝ E))
    (x : problem.primalSet)
    (hsmooth : problem.smoothPart = 0)
    (hdualSet : problem.dualSet = dom (strongFenchelConjugate f))
    (hlinear : problem.linearMap = NormedSpace.inclusionInDoubleDual ℝ E)
    (hdualPenalty : problem.dualPenalty = extendedRealRealPart (strongFenchelConjugate f)) :
    problem.objective x =
      sSup
        ((fun s : StrongDual ℝ E ↦
            ((NormedSpace.inclusionInDoubleDual ℝ E x s -
                extendedRealRealPart (strongFenchelConjugate f) s : ℝ) :
              EReal)) ''
          dom (strongFenchelConjugate f)) := by
  rw [problem.objective_apply]
  have hrange :
      Set.range (fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)) =
        ((fun s : StrongDual ℝ E ↦
            ((problem.smoothPart x + problem.linearMap x s - problem.dualPenalty s : ℝ) :
              EReal)) ''
          problem.dualSet) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [hrange, hdualSet]
  simp [hsmooth, hlinear, hdualPenalty]

/-- Text 6.1.2-Nonunique Structured Representation: whenever the Fenchel-conjugate formula
represents the objective `f` at `x`, the same value is the canonical Chapter 6 objective of any
structured model carrying exactly that Fenchel data. -/
theorem objective_eq_of_eq_fenchelConjugate_representation
    (problem : StructuredObjectiveModel E (StrongDual ℝ E))
    (x : problem.primalSet)
    (hsmooth : problem.smoothPart = 0)
    (hdualSet : problem.dualSet = dom (strongFenchelConjugate f))
    (hlinear : problem.linearMap = NormedSpace.inclusionInDoubleDual ℝ E)
    (hdualPenalty : problem.dualPenalty = extendedRealRealPart (strongFenchelConjugate f))
    (hf :
      ((f x : ℝ) : EReal) =
        sSup
          ((fun s : StrongDual ℝ E ↦
              ((NormedSpace.inclusionInDoubleDual ℝ E x s -
                  extendedRealRealPart (strongFenchelConjugate f) s : ℝ) :
                EReal)) ''
            dom (strongFenchelConjugate f))) :
    problem.objective x = (f x : EReal) := by
  rw [objective_eq_fenchelConjugate_representation f problem x hsmooth hdualSet hlinear
    hdualPenalty]
  exact hf.symm

end StructuredObjectiveModel

end

/-! ### Example_6_1_3 (from Chap06) -/
/- Example 6.1.3 lies in the chapter's explicit-model smoothing / within-set differential-calculus
domain.

Primary domain:
- within-set differentiability and gradient Lipschitzness for the explicit-model smoothed
  objective, with the textbook `ℝⁿ` / `ℝᵐ` presentation obtained by specializing the ambient
  spaces to `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`

Sampled owner-style declarations:
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter owner of the smoothed
  explicit-model objective;
- `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Proposition_6_10`, the canonical derivative/Lipschitz theorem for that owner;
- mathlib `HasFDerivWithinAt`, the pointwise within-set derivative owner;
- mathlib `LipschitzOnWith`, the canonical owner of the set-restricted Lipschitz bound.

Best owner abstraction:
- source-facing: the explicit-model smoothed objective from Definition 6.9;
- core/canonical: `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`;
- bridge/view: the Euclidean specialization of that theorem to the textbook finite-dimensional
  spaces.

Primitive data:
- the feasible set `Q₁`, model term `hatf`, smoothing term `fμ`, and their chosen derivative
  fields;
- the within-set derivative hypotheses;
- the Lipschitz constants `M` and `Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))`.

Derived API:
- the derivative selection of the smoothed objective;
- the Lipschitz estimate for the summed derivative field.

Source/core/bridge triage:
- source-facing: the explicit-model smoothing example stated in equation `(6.1.26)`;
- core/canonical: `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`;
- bridge/view: the Euclidean textbook specialization.

The previous file introduced a Euclidean-specialized theorem shell whose proof was a single
`simpa` from the Chapter 6 owner theorem, together with a one-off abbreviation for the displayed
constant `L_μ = M + (1 / μ) ‖A‖²`. Neither declaration carried new mathematical content or owned
primitive data, so this refinement removes that parallel API and keeps Example 6.1.3 as a direct
recall of the canonical chapter theorem. -/

/- Example 6.1.3 is the Euclidean specialization of the chapter owner theorem
`explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`. -/
recall explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn
