import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
