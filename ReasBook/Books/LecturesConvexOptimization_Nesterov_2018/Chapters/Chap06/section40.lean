import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_40 (from Chap06) -/
noncomputable section

universe u

/- Definition 6.40 lies in the chapter's adjoint-gradient / feasible argmax-selection domain.

Sampled owner-style declarations:
- mathlib `gradient`, the canonical ambient owner for the quadratic model's first-order term;
- mathlib `IsMaxOn`, the canonical feasible-set owner for pointwise maximizers;
- Chapter 6 `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the nearby project pattern for
  encoding a selected feasible maximizer by an argmax-set owner rather than by a second wrapper
  structure.

Best owner abstraction:
- source-facing: a feasible-set endomorphism `V : Q₂ → Q₂` selecting, for each feasible base
  point `u`, a maximizer of the displayed quadratic model on `Q₂`;
- core/canonical: `adjointGradientArgmax Q₂ φ Lphi u`, built from `IsMaxOn`;
- bridge/view: `IsAdjointGradientMappingOn Q₂ φ Lphi V`, the pointwise membership condition in
  that canonical argmax owner.

Primitive data:
- the feasible set `Q₂`;
- the scalar field `φ : E₂ → ℝ`;
- the curvature parameter `Lphi`;
- the feasible-set endomorphism `V : Q₂ → Q₂`.

Derived API:
- the pointwise quadratic maximand `adjointGradientMaximand φ Lphi u`;
- its feasible argmax set `adjointGradientArgmax Q₂ φ Lphi u`;
- the adjoint-gradient mapping predicate `IsAdjointGradientMappingOn Q₂ φ Lphi V`.

Source/core/bridge triage:
- source-facing: Definition 6.40's adjoint gradient mapping `V`;
- core/canonical: `adjointGradientArgmax`;
- bridge/view: `IsAdjointGradientMappingOn`.

This item is not a pure recall in the current project, because the expected owner did not yet
exist. The repair therefore introduces the minimal source-facing owner layer directly, using the
canonical feasible-maximizer predicate `IsMaxOn` and the same argmax-set design already used in
Chapter 6 for selected maximizers.
-/

section

variable {E₂ : Type u}
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The quadratic maximand
`v ↦ ⟪∇φ(u), v - u⟫ - (L₂(φ) / 2) ‖v - u‖²`
used in the adjoint-gradient update at the base point `u`. -/
def adjointGradientMaximand
    (φ : E₂ → ℝ) (Lphi : ℝ) (u : E₂) : E₂ → ℝ :=
  fun v ↦ inner ℝ (gradient φ u) (v - u) - (Lphi / 2) * ‖v - u‖ ^ (2 : ℕ)

/-- The feasible argmax set of the adjoint-gradient quadratic model at `u`. -/
abbrev adjointGradientArgmax
    (Q₂ : Set E₂) (φ : E₂ → ℝ) (Lphi : ℝ) (u : E₂) : Set E₂ :=
  {v | v ∈ Q₂ ∧ IsMaxOn (adjointGradientMaximand φ Lphi u) Q₂ v}

-- Proof sketch: unfold `adjointGradientArgmax`; membership is definitionally feasibility together
-- with the `IsMaxOn` condition for the quadratic maximand.
/-- A point belongs to `adjointGradientArgmax Q₂ φ Lphi u` exactly when it lies in `Q₂` and
maximizes the adjoint-gradient quadratic model on `Q₂`. -/
@[simp] theorem mem_adjointGradientArgmax_iff
    (Q₂ : Set E₂) (φ : E₂ → ℝ) (Lphi : ℝ) (u v : E₂) :
    v ∈ adjointGradientArgmax Q₂ φ Lphi u ↔
      v ∈ Q₂ ∧ IsMaxOn (adjointGradientMaximand φ Lphi u) Q₂ v := sorry

/-- Definition 6.40 [Chapter6_1.json:93]: an adjoint gradient mapping on `Q₂` is a feasible-set
endomorphism `V : Q₂ → Q₂` such that for every `u ∈ Q₂`, the point `V(u)` belongs to the
feasible argmax set of
`v ↦ ⟪∇φ(u), v - u⟫ - (L₂(φ) / 2) ‖v - u‖²` on `Q₂`. -/
abbrev IsAdjointGradientMappingOn
    (Q₂ : Set E₂) (φ : E₂ → ℝ) (Lphi : ℝ) (V : Q₂ → Q₂) : Prop :=
  ∀ u : Q₂, (V u : E₂) ∈ adjointGradientArgmax Q₂ φ Lphi (u : E₂)

-- Proof sketch: rewrite each pointwise argmax-membership condition with
-- `mem_adjointGradientArgmax_iff`; feasibility of `V u` is automatic from the codomain `Q₂`,
-- leaving exactly the `IsMaxOn` clause.
/-- An endomorphism of `Q₂` is an adjoint gradient mapping exactly when it sends each feasible
base point to a maximizer of the corresponding quadratic model on `Q₂`. -/
@[simp] theorem isAdjointGradientMappingOn_iff
    (Q₂ : Set E₂) (φ : E₂ → ℝ) (Lphi : ℝ) (V : Q₂ → Q₂) :
    IsAdjointGradientMappingOn Q₂ φ Lphi V ↔
      ∀ u : Q₂, IsMaxOn (adjointGradientMaximand φ Lphi (u : E₂)) Q₂ (V u : E₂) := sorry

-- Proof sketch: apply the forward direction of `isAdjointGradientMappingOn_iff` to the given
-- feasible base point `u`.
/-- If `V` is an adjoint gradient mapping on `Q₂`, then for every feasible base point `u`, the
selected point `V(u)` maximizes the corresponding adjoint-gradient quadratic model on `Q₂`. -/
theorem isAdjointGradientMappingOn_isMaxOn
    {Q₂ : Set E₂} {φ : E₂ → ℝ} {Lphi : ℝ} {V : Q₂ → Q₂}
    (hV : IsAdjointGradientMappingOn Q₂ φ Lphi V) (u : Q₂) :
    IsMaxOn (adjointGradientMaximand φ Lphi (u : E₂)) Q₂ (V u : E₂) := sorry

end

/-! ### Proposition_6_40 (from Chap06) -/
noncomputable section

universe u

/-
Proposition 6.40 lies in the second-order Hölder upper-model domain on real normed spaces.

Sampled owner-style declarations:
- mathlib `HolderOnWith`, the canonical on-set owner for Hölder continuity of a map;
- mathlib `DifferentiableOn`, the canonical on-set owner for Fréchet differentiability;
- mathlib `UniqueDiffOn`, the canonical hypothesis ensuring that higher within derivatives are
  intrinsic on a feasible set;
- mathlib `iteratedFDerivWithin`, the canonical higher-order owner for within-set Fréchet
  derivatives;
- Chapter 6 `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the first-order
  chapter owner for Hölder regularity of the canonical within derivative on a convex feasible set;
- mathlib `contDiffOn_succ_iff_fderivWithin`, the owner equivalence showing that on a
  `UniqueDiffOn` set the canonical higher differential layer is organized around `fderivWithin`;
- mathlib `iteratedFDerivWithin_two_apply'`, the bridge identifying the second iterated within
  derivative with the nested `fderivWithin` formula on uniquely differentiable sets.

Source/core/bridge triage:
- source-facing: Proposition 6.40's quadratic upper model under Hölder continuity of the second
  derivative;
- core/canonical: `DifferentiableOn ℝ f Q`, `DifferentiableOn ℝ (fderivWithin ℝ f Q) Q`, and
  `HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q`;
- bridge/view: the pointwise quadratic-model inequality below.

Primitive data:
- the feasible set `Q`, objective `f`, Hölder exponent `v`, and Hölder constant `H`;
- convexity of `Q`;
- unique differentiability of `Q`, making the within-derivative layers intrinsic;
- differentiability on `Q` of `f` and of its canonical within derivative;
- Hölder continuity on `Q` of the canonical iterated within second-derivative map.

Derived API:
- the quadratic upper-model inequality below.

The previous file used ambient derivatives `fderiv ℝ f` and `fderiv ℝ (fderiv ℝ f)` on an
arbitrary convex set `Q`, which over-specialized the statement to neighborhood differentiability
at boundary points. This refinement keeps the source-facing proposition but moves its primitive
data to the canonical within-set layer: `fderivWithin` for first-derivative existence and
`iteratedFDerivWithin ℝ 2 f Q` for the public second-derivative owner. Because higher within
derivatives are only intrinsic on uniquely differentiable sets, the public API now records
`UniqueDiffOn ℝ Q` explicitly instead of treating convexity alone as sufficient. The nested
`fderivWithin` formula survives only as an internal bridge via
`iteratedFDerivWithin_two_apply'`. This matches the Chapter 6 owner style on feasible sets while
remaining faithful for lower-dimensional convex sets, and removes the redundant positivity guard
on `v`. -/

/-- Proposition 6.40: if the canonical iterated within second Fréchet derivative of `f` is
`v`-Hölder on the convex set `Q`, then `f` admits the quadratic upper model with Hölder
remainder `H * ‖y - x‖^(2 + v) / ((1 + v) * (2 + v))`. -/
-- Proof sketch: restrict `f` to the line segment `t ↦ x + t • (y - x)`, apply the
-- one-dimensional second-order Taylor formula with integral remainder, and bound the remainder
-- using the Hölder estimate on `iteratedFDerivWithin ℝ 2 f Q`; when one needs the nested
-- derivative formula inside the proof, recover it from `iteratedFDerivWithin_two_apply'`
-- together with `UniqueDiffOn ℝ Q` and convexity of `Q`.
theorem holder_hessian_upper_model
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf : DifferentiableOn ℝ f Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + fderivWithin ℝ f Q x (y - x) +
        (1 / 2 : ℝ) * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
          (H : ℝ) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) /
            ((1 + (v : ℝ)) * (2 + (v : ℝ))) := sorry
