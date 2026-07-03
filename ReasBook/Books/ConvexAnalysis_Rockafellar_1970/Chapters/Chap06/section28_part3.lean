import Mathlib
import Mathlib.Order.Filter.Extr
import Mathlib.Order.SaddlePoint
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_28_7 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.7 introduces the notion of a saddle point of the Lagrangian
  `L u⋆ x`, with maximization in the dual variable `u⋆` and minimization in the primal variable
  `x`.
- `core/canonical`: mathlib already owns the ambient notion as `_root_.IsSaddlePointOn X Y f a b`.
- `bridge/view`: the source writes kernels as `K u v` with maximization in `u` and minimization in
  `v`, so this file exposes a source-ordered owner
  `Bifunction.IsSaddlePointOn C D K u v := _root_.IsSaddlePointOn D C (Function.swap K) v u`.
- owner policy: expose the source-facing bridge API and avoid a second public layer that merely
  repeats swapped raw-owner statements.

Domain-style sampling used here:
- `_root_.IsSaddlePointOn` from `Mathlib.Order.SaddlePoint`;
- `isMinOn_iff` from `Mathlib.Order.Filter.Extr`;
- `isMaxOn_iff` from `Mathlib.Order.Filter.Extr`;

Primitive data vs derived API:
- primitive owner data: the domain sets `C`, `D`, the bifunction `K`, and the candidate pair
  `(u, v)`;
- source-facing owner: `Bifunction.IsSaddlePointOn C D K u v`;
- canonical bridge owner: `_root_.IsSaddlePointOn D C (Function.swap K) v u`;
- primitive bridge API: the full source-order two-variable inequality
  `∀ u' ∈ C, ∀ v' ∈ D, K u' v ≤ K u v'`;
- derived API: source-order one-sided inequalities and `IsMaxOn`/`IsMinOn` reformulations.
-/

universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w} [Preorder β]

namespace Bifunction

/-- Definition 6.28.7, source-ordered owner: `u` is maximized on `C`, `v` is minimized on `D`,
for a kernel written as `K u v`. -/
def IsSaddlePointOn (C : Set E) (D : Set F) (K : E → F → β) (u : E) (v : F) : Prop :=
  _root_.IsSaddlePointOn D C (Function.swap K) v u

/-- Whole-space specialization of `Bifunction.IsSaddlePointOn`. -/
abbrev IsSaddlePoint (K : E → F → β) (u : E) (v : F) : Prop :=
  IsSaddlePointOn Set.univ Set.univ K u v

/-- Primitive source-order inequality characterization:
`(u, v)` is a source-ordered saddle point on `C × D` iff every rectangle-corner inequality
`K u' v ≤ K u v'` holds for `u' ∈ C`, `v' ∈ D`. -/
theorem isSaddlePointOn_iff_forall
    {C : Set E} {D : Set F} {K : E → F → β} {u : E} {v : F} :
    IsSaddlePointOn C D K u v ↔
      ∀ u' ∈ C, ∀ v' ∈ D, K u' v ≤ K u v' := by
  constructor
  · intro h u' hu' v' hv'
    exact h v' hv' u' hu'
  · intro h v' hv' u' hu'
    exact h u' hu' v' hv'

/-- Primitive whole-space source-order inequality characterization of Definition 6.28.7. -/
theorem isSaddlePoint_iff_forall
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      ∀ u' : E, ∀ v' : F, K u' v ≤ K u v' := by
  simpa [IsSaddlePoint] using
    (isSaddlePointOn_iff_forall
      (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (K := K) (u := u) (v := v))

-- Proof sketch: expand the swapped canonical owner at `x = v` and `y = u`, obtaining the two
-- source-order one-sided inequalities; conversely compose those inequalities by transitivity.
/-- One-sided source-order inequality characterization of `Bifunction.IsSaddlePointOn` on `C × D`,
derived from `isSaddlePointOn_iff_forall` under membership of the distinguished pair. -/
theorem isSaddlePointOn_iff_source_order
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      (∀ u' ∈ C, K u' v ≤ K u v) ∧
      ∀ v' ∈ D, K u v ≤ K u v' := by
  constructor
  · intro h
    rcases (isSaddlePointOn_iff_forall (C := C) (D := D) (K := K) (u := u) (v := v)).1 h with hrect
    refine ⟨?_, ?_⟩
    · intro u' hu'
      exact hrect u' hu' v hv
    · intro v' hv'
      exact hrect u hu v' hv'
  · intro h v' hv' u' hu'
    exact le_trans (h.1 u' hu') (h.2 v' hv')

/-- Extrema reformulation of `isSaddlePointOn_iff_source_order`. -/
theorem isSaddlePointOn_iff_isMaxOn_isMinOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      IsMaxOn (fun u' : E ↦ K u' v) C u ∧
      IsMinOn (fun v' : F ↦ K u v') D v := by
  simpa [isMaxOn_iff, isMinOn_iff] using
    (isSaddlePointOn_iff_source_order (C := C) (D := D) (K := K) (u := u) (v := v) hu hv)

/-- Extrema reformulation of `isSaddlePointOn_iff_source_order` with `(IsMinOn, IsMaxOn)` order. -/
theorem isSaddlePointOn_iff_isMinOn_isMaxOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      IsMinOn (fun v' : F ↦ K u v') D v ∧
      IsMaxOn (fun u' : E ↦ K u' v) C u := by
  simpa [and_comm] using
    (isSaddlePointOn_iff_isMaxOn_isMinOn (C := C) (D := D) (K := K) (u := u) (v := v) hu hv)

/-- Whole-space source-order inequality characterization of Definition 6.28.7. -/
theorem isSaddlePoint_iff_source_order
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      (∀ u' : E, K u' v ≤ K u v) ∧
      ∀ v' : F, K u v ≤ K u v' := by
  constructor
  · intro h
    rcases (isSaddlePoint_iff_forall (K := K) (u := u) (v := v)).1 h with hrect
    refine ⟨?_, ?_⟩
    · intro u'
      exact hrect u' v
    · intro v'
      exact hrect u v'
  · intro h
    exact (isSaddlePoint_iff_forall (K := K) (u := u) (v := v)).2
      (fun u' v' ↦ le_trans (h.1 u') (h.2 v'))

/-- Whole-space extrema reformulation of Definition 6.28.7. -/
theorem isSaddlePoint_iff_isMaxOn_isMinOn
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      IsMaxOn (fun u' : E ↦ K u' v) (Set.univ : Set E) u ∧
      IsMinOn (fun v' : F ↦ K u v') (Set.univ : Set F) v := by
  simpa [IsSaddlePoint] using
    (isSaddlePointOn_iff_isMaxOn_isMinOn
      (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (K := K) (u := u) (v := v) (by simp) (by simp))

end Bifunction

end

/-! ### Theorem_6_28_7 (from Chap06) -/
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

/-! ### Corollary_6_28_8 (from Chap06) -/
noncomputable section

open scoped BigOperators Rockafellar

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.8 computes the one-multiplier Lagrangian and dual objective for
  the separable simplex program from the Section 28 setup, then rewrites the Kuhn--Tucker
  coefficient condition as minimization of `-g`.
- `core/canonical`: the existing owner abstractions needed here are the Chapter 12 conjugate
  notation `(·)⋆`, finite sums over `Fin n`, and the extrema owners `IsMaxOn` and `IsMinOn`.
- `bridge/view`: the source variables `x = (ξ₁, …, ξₙ)` and `v₁*` are represented directly as
  `x : Fin n → 𝕜` and `v : 𝕜`, and the coordinate interaction term is stated through the pairing
  owner `⟪·, ·⟫ₚ` instead of a concrete scalar-product model.

Domain-style sampling used here:
- the conjugate owner `(·)⋆` from `Chap03.Defn_12_2`;
- the simplex-coordinate owners from `Definition_6_28_11`;
- `IsMaxOn` / `IsMinOn` from mathlib's extrema API;
- the project-wide Chapter 1 extended codomain surface `WithBotTop 𝕜`.

Primitive data vs derived API:
- primitive source data: the scalar family `f₀ : Fin n → 𝕜 → WithBotTop 𝕜`;
- primitive owners: `standardSimplexCoordinateLagrangian`,
  `standardSimplexCoordinateDualObjective`, and `standardSimplexCoordinateDualCost`;
- derived API: the pointwise source formula for the Lagrangian, the coordinatewise-infimum
  formula for the dual objective, and the maximizer/minimizer bridge.

Layer target: `source-facing`. This item is a direct computation for the special one-equality
problem, so it is formalized directly in terms of the scalar coordinate family and the canonical
conjugate owner, without introducing a separate program package.
-/

section

variable {n : ℕ}
variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [HasPairing 𝕜 𝕜 𝕜]

/-- The specialized Lagrangian for the one-equality separable simplex program with scalar
coordinate branches `f₀ₖ`. -/
def standardSimplexCoordinateLagrangian
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) (x : Fin n → 𝕜) : WithBotTop 𝕜 :=
  (-v : WithBotTop 𝕜) + ∑ k, (f₀ k (x k) - ⟪x k, -v⟫ₚ)

-- Proof sketch: unfold `standardSimplexCoordinateLagrangian`; the displayed formula is exactly
-- its defining separable sum.
/-- Evaluating the specialized simplex Lagrangian gives the source coordinate formula. -/
theorem standardSimplexCoordinateLagrangian_apply
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) (x : Fin n → 𝕜) :
    standardSimplexCoordinateLagrangian f₀ v x =
      (-v : WithBotTop 𝕜) + ∑ k, (f₀ k (x k) - ⟪x k, -v⟫ₚ) := sorry

end

section

variable {n : ℕ}
variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [HasPairing 𝕜 𝕜 𝕜]

/-- The dual objective `g(v) = -v - ∑ₖ f₀ₖ⋆(-v)` attached to the same one-multiplier simplex
program. -/
def standardSimplexCoordinateDualObjective
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) : WithBotTop 𝕜 :=
  (-v : WithBotTop 𝕜) - ∑ k, (f₀ k)⋆ (-v)

/-- The negated dual objective `-g` from the final clause of Corollary 6.28.8. -/
def standardSimplexCoordinateDualCost
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) : WithBotTop 𝕜 :=
  (v : WithBotTop 𝕜) + ∑ k, (f₀ k)⋆ (-v)

-- Proof sketch: for each coordinate `k`, use the defining relation between the conjugate and the
-- negative infimum at `-v`; summing the coordinate identities yields the displayed source formula
-- for the dual objective.
/-- The dual objective also has the source coordinatewise-infimum formula. -/
theorem standardSimplexCoordinateDualObjective_apply_eq_iInf
    [IsOrderedAddMonoid 𝕜]
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) :
    standardSimplexCoordinateDualObjective f₀ v =
      (-v : WithBotTop 𝕜) +
        ∑ k, (⨅ ξ : 𝕜, f₀ k ξ - ⟪ξ, -v⟫ₚ) := sorry

-- Proof sketch: unfold `standardSimplexCoordinateDualCost` and
-- `standardSimplexCoordinateDualObjective`; pointwise, the former is exactly the negative of the
-- latter.
/-- The dual cost is the pointwise negative of the dual objective. -/
theorem standardSimplexCoordinateDualCost_eq_neg_dualObjective
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) :
    standardSimplexCoordinateDualCost f₀ = fun v ↦ -standardSimplexCoordinateDualObjective f₀ v :=
  sorry

-- Proof sketch: maximizing `g` is equivalent to minimizing `-g`; then identify `-g`
-- with `standardSimplexCoordinateDualCost` using
-- `standardSimplexCoordinateDualCost_eq_neg_dualObjective`.
/-- Corollary 6.28.8: for the one-multiplier separable simplex program with coordinate branches
`f₀ₖ`, a scalar `λ₁` maximizes the dual objective `g(v) = -v - ∑ₖ f₀ₖ⋆(-v)` exactly when it
minimizes the equivalent source quantity `v + ∑ₖ f₀ₖ⋆(-v)`, which is the minimization criterion
corresponding to the Kuhn--Tucker coefficient condition for `(P)`. -/
theorem isMaxOn_standardSimplexCoordinateDualObjective_iff_isMinOn_standardSimplexCoordinateDualCost
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (lam₁ : 𝕜) :
    IsMaxOn (standardSimplexCoordinateDualObjective f₀) Set.univ lam₁ ↔
      IsMinOn (standardSimplexCoordinateDualCost f₀) Set.univ lam₁ := sorry

end

end Function

/-! ### Definition_6_28_8 (from Chap06) -/
noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

namespace Function

section

variable {E : Type u} {ι : Type v} {α β : Type*}
variable [LE β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.8 rewrites a finite inequality-constrained problem with
  objective in `α` and constraints in an ordered zero type `β` as one `WithTopBot α`-valued
  objective obtained by adjoining the indicator of the common feasible set cut out by the
  inequalities.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.toWithTopBotOn` for extension by `+∞` outside a feasible set and
  `weakConvexInequalitySolutionSetOn` for the canonical feasible set of a finite weak
  convex-inequality subsystem with zero right-hand-side bounds.
- `bridge/view`: the source formula `f₀.toWithTopBot + δ[α](· | C)` is the Chapter 1 bridge for
  `Function.toWithTopBotOn f₀ C`, and the finite subsystem indexed by `s : Finset ι` is
  equivalently the textbook set `{x | ∀ i ∈ s, f i x ≤ 0}`.

Domain-style sampling used here:
- `Function.toWithTopBotOn` and `Function.toWithTopBotOn_eq_add_indicator` from
  `Chap01.Remark_4_4_5`;
- `indicator` / `δ[α](· | C)` from `Chap01.Defintion_4_8_1`;
- `weakConvexInequalitySolutionSetOn` and `mem_weakConvexInequalitySolutionSetOn` from
  `Chap04.Text_21_0_1`.

Primitive data vs derived API:
- primitive data: an `α`-valued objective `f₀`, a finite index set `s`, and `β`-valued
  constraint functions `f i`;
- canonical owner surface:
  `Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`;
- derived API: the source formula via direct reuse of
  `Function.toWithTopBotOn_eq_add_indicator`, the pointwise branch formula, and the
  empty-family specialization.

Layer target: `source-facing` through the existing `core/canonical` owner. Definition 6.28.8 is
not a second root declaration; it is this concrete use of `Function.toWithTopBotOn` on the
Chapter 4 finite feasible-set owner.
-/

/- Definition 6.28.8: the constrained objective is the canonical extension
`Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`,
equivalently `f₀.toWithTopBot + δ[α](· | {x | ∀ i ∈ s, f i x ≤ 0})`. -/
recall Function.toWithTopBotOn

section

variable [Zero β]

recall weakConvexInequalitySolutionSetOn

/-- Primitive owner spelling of Definition 6.28.8 on the Chapter 4 finite weak feasible-set
owner, with no additive codomain assumptions. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      (weakConvexInequalitySolutionSetOn s f).piecewise f₀.toWithTopBot ⊤ :=
  rfl

/-- Source-set spelling of the primitive owner for Definition 6.28.8:
`{x | ∀ i ∈ s, f i x ≤ 0}.piecewise f₀.toWithTopBot ⊤`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      ({x : E | ∀ i ∈ s, f i x ≤ 0}).piecewise f₀.toWithTopBot ⊤ := by
  simpa [weakConvexInequalitySolutionSetOn_eq_setOf] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise
      (f₀ := f₀) (s := s) (f := f)

/-- On the finite weak feasible-set owner, the constrained objective agrees with `f₀` on feasible
points. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_of_mem
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) {x : E}
    (hx : x ∈ weakConvexInequalitySolutionSetOn s f) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x = f₀.toWithTopBot x := by
  simpa using Function.toWithTopBotOn_of_mem f₀ (weakConvexInequalitySolutionSetOn s f) hx

/-- Outside the finite weak feasible-set owner, the constrained objective is `+∞`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_of_notMem
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) {x : E}
    (hx : x ∉ weakConvexInequalitySolutionSetOn s f) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x = (⊤ : WithTopBot α) := by
  simpa using Function.toWithTopBotOn_of_notMem f₀ (weakConvexInequalitySolutionSetOn s f) hx

/-- Pointwise owner form of Definition 6.28.8, phrased at the canonical feasible-set owner
layer. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) (x : E) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x =
      if x ∈ weakConvexInequalitySolutionSetOn s f then f₀.toWithTopBot x else ⊤ := by
  by_cases hx : x ∈ weakConvexInequalitySolutionSetOn s f
  · simp [hx]
  · simp [hx]

/-- Source-set spelling of the pointwise form of Definition 6.28.8:
`if (∀ i ∈ s, f i x ≤ 0) then f₀.toWithTopBot x else ⊤`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) (x : E) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x =
      if ∀ i ∈ s, f i x ≤ 0 then f₀.toWithTopBot x else ⊤ := by
  simpa [mem_weakConvexInequalitySolutionSetOn] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply
      (f₀ := f₀) (s := s) (f := f) (x := x)

/-- With no inequality constraints, Definition 6.28.8 reduces to the ambient codomain lift of the
objective. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_empty
    (f₀ : E → α) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn (∅ : Finset ι) f) =
      f₀.toWithTopBot := by
  ext x
  simp [Function.toWithTopBotOn]

end

section

variable [AddZeroClass α] [Zero β]

/-- Owner-to-source bridge for Definition 6.28.8 on the Chapter 4 finite weak feasible-set
owner. -/
theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      f₀.toWithTopBot + (δ(· | weakConvexInequalitySolutionSetOn s f)) := by
  simpa using
    Function.toWithTopBotOn_eq_add_indicator f₀ (weakConvexInequalitySolutionSetOn s f)

/-- Source-set spelling of Definition 6.28.8:
`f₀.toWithTopBot + δ[α](· | {x | ∀ i ∈ s, f i x ≤ 0})`. -/
theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      f₀.toWithTopBot + (δ(· | {x : E | ∀ i ∈ s, f i x ≤ 0})) := by
  simpa [weakConvexInequalitySolutionSetOn_eq_setOf] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator
      (f₀ := f₀) (s := s) (f := f)

end

end

end Function

/-! ### Theorem_6_28_8 (from Chap06) -/
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

/-! ### Definition_6_28_9 (from Chap06) -/
universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w} [Preorder β]

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.9 specializes the saddle-point notion to a Lagrangian
  `L u⋆ x`, with the dual variable `u⋆` maximized over the multiplier set `Eᵣ` and the primal
  variable `x` minimized over the feasible set `C`.
- `core/canonical`: Chapter 6 now uses the source-ordered owner
  `Bifunction.IsSaddlePointOn C D K u v`.
- `bridge/view`: this source owner is definitionally
  `_root_.IsSaddlePointOn D C (Function.swap K) v u`; swapped-kernel views remain available
  from `Chap06.Definition_6_28_7` when needed.

Domain-style sampling used here:
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_forall` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_source_order` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_isMaxOn_isMinOn` from `Chap06.Definition_6_28_7`.

Primitive data vs derived API:
- primitive owner data: the primal domain `C`, the dual domain `Eᵣ`, the Lagrangian `L`, and the
  candidate pair `(u⋆, x)`;
- source-facing owner API: the Chapter 6 owner `Bifunction.IsSaddlePointOn Er C L u⋆ x`;
- derived source-facing API: the Lagrangian specialization obtained by instantiating that bridge at
  `K = L`.

Layer target: a `source-facing` owner surface for Definition 6.28.9.
-/

/-- Definition 6.28.9: a pair `(u⋆, x)` with `x ∈ C` and `u⋆ ∈ Eᵣ` is a saddle point of the
Lagrangian `L` exactly when, on the primal feasible set `C` and the dual multiplier set `Eᵣ`,
the dual variable `u⋆` is a maximizer of `L · x` and the primal variable `x` is a minimizer of
`L u⋆ ·`. -/
theorem lagrangian_mem_iff_isMaxOn_isMinOn
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    (uStar ∈ Er ∧ x ∈ C ∧ IsSaddlePointOn Er C L uStar x) ↔
      uStar ∈ Er ∧ x ∈ C ∧
        IsMaxOn (L · x) Er uStar ∧
        IsMinOn (L uStar) C x := by
  constructor
  · rintro ⟨huStar, hx, hsaddle⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_isMaxOn_isMinOn
          (C := Er) (D := C) (K := L) huStar hx).1 hsaddle⟩
  · rintro ⟨huStar, hx, hmaxmin⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_isMaxOn_isMinOn
          (C := Er) (D := C) (K := L) huStar hx).2 hmaxmin⟩

/-- Membership-hypothesis formulation of Definition 6.28.9 in extrema-owner form. -/
theorem lagrangian_iff
    {C : Set E} {Er : Set F} {L : F → E → β}
    {uStar : F} (huStar : uStar ∈ Er) {x : E} (hx : x ∈ C) :
    IsSaddlePointOn Er C L uStar x ↔
      IsMaxOn (L · x) Er uStar ∧
      IsMinOn (L uStar) C x := by
  simpa using
    (isSaddlePointOn_iff_isMaxOn_isMinOn
      (C := Er) (D := C) (K := L) huStar hx)

/-- Primitive rectangle-corner inequality form of Definition 6.28.9, with no distinguished-point
membership assumptions. -/
theorem lagrangian_iff_forall_rect
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    IsSaddlePointOn Er C L uStar x ↔
      ∀ u ∈ Er, ∀ y ∈ C, L u x ≤ L uStar y := by
  simpa using
    (isSaddlePointOn_iff_forall (C := Er) (D := C) (K := L) (u := uStar) (v := x))

/-- One-sided source-order inequality form of Definition 6.28.9 under distinguished-point
membership assumptions. -/
theorem lagrangian_mem_iff_source_order
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    (uStar ∈ Er ∧ x ∈ C ∧ IsSaddlePointOn Er C L uStar x) ↔
      uStar ∈ Er ∧ x ∈ C ∧
        (∀ u ∈ Er, L u x ≤ L uStar x) ∧
        (∀ y ∈ C, L uStar x ≤ L uStar y) := by
  constructor
  · rintro ⟨huStar, hx, hsaddle⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_source_order
          (C := Er) (D := C) (K := L) huStar hx).1 hsaddle⟩
  · rintro ⟨huStar, hx, horder⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_source_order
          (C := Er) (D := C) (K := L) huStar hx).2 horder⟩

/-- Membership-hypothesis formulation of Definition 6.28.9 in one-sided source-order form. -/
theorem lagrangian_iff_forall
    {C : Set E} {Er : Set F} {L : F → E → β}
    {uStar : F} (huStar : uStar ∈ Er) {x : E} (hx : x ∈ C) :
    IsSaddlePointOn Er C L uStar x ↔
      (∀ u ∈ Er, L u x ≤ L uStar x) ∧
      (∀ y ∈ C, L uStar x ≤ L uStar y) := by
  simpa using
    (isSaddlePointOn_iff_source_order
      (C := Er) (D := C) (K := L) huStar hx)

/-- Universe-domain specialization of `lagrangian_iff`, eliminating proof-only membership
arguments from the theorem surface. -/
theorem lagrangian_univ_iff
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      IsMaxOn (L · x) (Set.univ : Set F) uStar ∧
      IsMinOn (L uStar) (Set.univ : Set E) x := by
  simpa using (isSaddlePoint_iff_isMaxOn_isMinOn (K := L) (u := uStar) (v := x))

/-- Primitive rectangle-corner inequality form of `lagrangian_univ_iff`. -/
theorem lagrangian_univ_iff_forall_rect
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      (∀ u : F, ∀ y : E, L u x ≤ L uStar y) := by
  simpa using (isSaddlePoint_iff_forall (K := L) (u := uStar) (v := x))

/-- Raw pointwise inequality form of `lagrangian_univ_iff`. -/
theorem lagrangian_univ_iff_forall
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      (∀ u : F, L u x ≤ L uStar x) ∧
      (∀ y : E, L uStar x ≤ L uStar y) := by
  simpa using (isSaddlePoint_iff_source_order (K := L) (u := uStar) (v := x))

end Bifunction

end

/-! ### Definition_6_28_10 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.10 introduces the simplex-constrained separable minimization
  problem with objective `q₁(ξ₁) + ⋯ + qₙ(ξₙ)` and constraints `ξ ≥ 0`, `∑ ξᵢ = 1`.
- `core/canonical`: the owner abstractions are mathlib's feasible set `stdSimplex 𝕜 ι`,
  the project's coordinate-sum owner `separableCoordinateSum`, and mathlib's extrema owner
  `IsMinOn` on the ambient feasible set `stdSimplex 𝕜 ι`.
- `bridge/view`: the source optimization problem is owned by the minimizer predicate
  `IsStdSimplexSeparableMinimizer q x`; the minimizer set
  `stdSimplexSeparableMinimumSet q` is the derived set-level view.

Domain-style sampling used here:
- `stdSimplex` from mathlib's simplex API;
- `separableCoordinateSum` from `Chap03.Text_16_0_4`;
- `separableCoordinateSum_apply` from the same owner file;
- `isMinOn_iff` from mathlib's extrema API.

Primitive data vs derived API:
- primitive source data: the family of scalar functions `q : ι → 𝕜 → α`;
- primitive owners: the ambient feasible-owner predicate
  `IsStdSimplexSeparableMinimizer q x`, plus the intrinsic objective owner
  `stdSimplexSeparableObjective q : stdSimplex 𝕜 ι → α` as a bridge view;
- derived API: the minimizer set `stdSimplexSeparableMinimumSet q` and the textbook
  sum-inequality criterion.

Layer target: `bridge/view`, centered on the canonical ambient feasible-owner layer:
`x ∈ stdSimplex 𝕜 ι ∧ IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x`,
with a bridge to the intrinsic subtype objective owner.
-/

open scoped BigOperators

universe u v

section

variable {𝕜 : Type u} {α : Type v} {ι : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [Fintype ι]
variable [AddCommMonoid α]

variable (q : ι → 𝕜 → α)

/-- The separable objective `ξ ↦ ∑ i, qᵢ(ξᵢ)` restricted to the intrinsic feasible owner
`stdSimplex 𝕜 ι`. -/
def stdSimplexSeparableObjective (q : ι → 𝕜 → α) : stdSimplex 𝕜 ι → α :=
  fun ξ ↦ separableCoordinateSum q ξ

@[simp] theorem stdSimplexSeparableObjective_apply
    (ξ : stdSimplex 𝕜 ι) :
    stdSimplexSeparableObjective q ξ = ∑ i, q i (ξ i) :=
  rfl

variable [Preorder α]
variable (x : ι → 𝕜)

/-- Definition 6.28.10: `x` solves the simplex-constrained separable minimization problem
for the coordinate family `q` exactly when `x` is feasible for the canonical simplex owner and
minimizes the canonical separable objective owner on that feasible set. The owner is index-generic
over a finite type `ι`; the textbook `n`-coordinate form is the specialization `ι = Fin n`. -/
def IsStdSimplexSeparableMinimizer : Prop :=
  x ∈ stdSimplex 𝕜 ι ∧
    IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x

/-- Set-level view of Definition 6.28.10: all simplex-feasible minimizers of the separable
objective with coordinate family `q`. -/
def stdSimplexSeparableMinimumSet : Set (ι → 𝕜) :=
  {x | IsStdSimplexSeparableMinimizer q x}

namespace IsStdSimplexSeparableMinimizer

theorem iff :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplex 𝕜 ι ∧
        IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x :=
  Iff.rfl

/-- Intrinsic-subtype bridge: the ambient feasible-owner predicate of Definition 6.28.10 is
equivalent to minimizing the restricted objective on the simplex subtype. -/
theorem iff_subtype :
    IsStdSimplexSeparableMinimizer q x ↔
      ∃ hx : x ∈ stdSimplex 𝕜 ι,
        IsMinOn (stdSimplexSeparableObjective q) Set.univ ⟨x, hx⟩ := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_univ_iff]
    intro y
    simpa [stdSimplexSeparableObjective_apply] using
      (isMinOn_iff.mp hmin) y.1 y.2
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    simpa [stdSimplexSeparableObjective_apply] using
      (isMinOn_univ_iff.mp hmin) ⟨y, hy⟩

theorem iff_mem :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplexSeparableMinimumSet q := by
  rfl

/-- Definition 6.28.10 in the textbook coordinate-sum spelling: the source criterion is
feasibility in the standard simplex together with the pointwise inequality
`∑ i, q i (x i) ≤ ∑ i, q i (y i)` against every feasible `y`. -/
theorem iff_sum :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplex 𝕜 ι ∧
        ∀ y ∈ stdSimplex 𝕜 ι, ∑ i, q i (x i) ≤ ∑ i, q i (y i) := by
  constructor
  · rintro ⟨hxmem, hmin⟩
    refine ⟨hxmem, ?_⟩
    simpa [isMinOn_iff, separableCoordinateSum_apply] using hmin
  · rintro ⟨hxmem, hsum⟩
    refine ⟨hxmem, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    simpa [separableCoordinateSum_apply] using hsum y hy

end IsStdSimplexSeparableMinimizer

namespace stdSimplexSeparableMinimumSet

variable {q}

theorem mem_iff {x : ι → 𝕜} :
    x ∈ stdSimplexSeparableMinimumSet q ↔
      IsStdSimplexSeparableMinimizer q x :=
  Iff.rfl

/-- Textbook coordinate-sum spelling of membership in `stdSimplexSeparableMinimumSet q`. -/
theorem mem_iff_sum {x : ι → 𝕜} :
    x ∈ stdSimplexSeparableMinimumSet q ↔
      x ∈ stdSimplex 𝕜 ι ∧
        ∀ y ∈ stdSimplex 𝕜 ι, ∑ i, q i (x i) ≤ ∑ i, q i (y i) := by
  simpa [mem_iff] using
    (IsStdSimplexSeparableMinimizer.iff_sum (q := q) (x := x))

end stdSimplexSeparableMinimumSet

end

/-! ### Definition_6_28_11 (from Chap06) -/
noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.11 rewrites the standard-simplex problem from
  Definition 6.28.10 into the scalar coordinate families `f_{0k}` and `f_{1k}`.
- `core/canonical`: the project already owns extension by `+∞` outside a set as
  `Function.toWithBotTopOn`.
- `bridge/view`: the branch formula for `f_{0k}` is exactly the canonical extension of `q k`
  from the nonnegative half-line `Set.Ici 0`, so this file should use that owner directly rather
  than keep a parallel alias. The source-facing family `f_{1k}` is the identity on every
  coordinate except one distinguished index, where the affine shift by `1` appears.

Domain-style sampling used here:
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `Function.toWithBotTopOn_of_mem`;
- `Function.toWithBotTopOn_of_notMem`;
- `IsStdSimplexSeparableMinimizer.iff_sum` from `Definition_6_28_10`, which already keeps the
  simplex problem itself on the canonical owners `stdSimplex` and `separableCoordinateSum`;
- `Function.separableCoordinateSum` from `Chap03.Text_16_0_4`, which already treats a
  separable optimization problem through a family of scalar coordinate branches.

Primitive data vs derived API:
- primitive source data: an index family `q : ι → α → β`;
- core owner for `f_{0k}`: use the family `fun k ↦ Function.toWithBotTopOn (q k) (Set.Ici 0)`
  directly, with branch formulas inherited from
  `Function.toWithBotTopOn_of_mem` and `Function.toWithBotTopOn_of_notMem`;
- source-facing specialization kept in this file:
  `Function.standardSimplexCoordinateConstraint`;
- derived API local to this file: branch formulas for the distinguished-index family `f_{1k}`.

Layer target:
- the `f_{0k}` clause is `core/canonical` recall of `Function.toWithBotTopOn`;
- the `f_{1k}` clause is `source-facing`, with the branch owner implemented directly via the
  canonical `Set.piecewise` interface.
-/

namespace Function

section Objective

variable {ι : Type*}
variable [Preorder α] [Zero α]

variable (q : ι → α → β)

/- Definition 6.28.11 (`f_{0k}`): the simplex objective branches are the coordinatewise canonical
extension owner `Function.toWithBotTopOn (q k) (Set.Ici 0)`. Use
`Function.toWithBotTopOn_of_mem` and `Function.toWithBotTopOn_of_notMem` for the source branch
formulas on nonnegative and negative inputs. -/
@[simp] theorem toWithBotTopOn_Ici_zero_of_nonneg
    (k : ι) {ξ : α} (hξ : 0 ≤ ξ) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = q k ξ := by
  simpa using Function.toWithBotTopOn_of_mem (q k) (Set.Ici (0 : α)) hξ

@[simp] theorem toWithBotTopOn_Ici_zero_of_not_nonneg
    (k : ι) {ξ : α} (hξ : ¬ 0 ≤ ξ) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = (⊤ : WithBotTop β) := by
  simpa using Function.toWithBotTopOn_of_notMem (q k) (Set.Ici (0 : α)) hξ

@[simp] theorem toWithBotTopOn_Ici_zero_of_lt_zero
    (k : ι) {ξ : α} (hξ : ξ < 0) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = (⊤ : WithBotTop β) := by
  exact toWithBotTopOn_Ici_zero_of_not_nonneg (q := q) (k := k) (ξ := ξ) (not_le_of_gt hξ)

end Objective

section Constraint

variable {ι : Type*}
variable [One α] [Sub α]

/-- The family `f_{1k}` encoding one affine simplex constraint branch:
every coordinate branch is the identity except at a distinguished index `k0`, where `1` is
subtracted. The textbook "last-coordinate" form is recovered by specializing to `ι = Fin n` and
choosing the distinguished terminal coordinate. -/
def standardSimplexCoordinateConstraint (k0 : ι) : ι → α → α :=
  ({k0} : Set ι).piecewise
    (fun _ ξ ↦ ξ - 1)
    (fun _ ↦ id)

/-- Branch formula for `f_{1k}`: `k0` uses `ξ - 1`, all other coordinates use `ξ`. -/
@[simp] theorem standardSimplexCoordinateConstraint_apply
    (k0 k : ι) (ξ : α) :
    standardSimplexCoordinateConstraint k0 k ξ = if k = k0 then ξ - 1 else ξ := by
  by_cases hk : k = k0 <;> simp [standardSimplexCoordinateConstraint, hk]

/-- Away from `k0`, `standardSimplexCoordinateConstraint k0` is the identity map. -/
@[simp] theorem standardSimplexCoordinateConstraint_of_ne
    (k0 k : ι) (ξ : α) (hk : k ≠ k0) :
    standardSimplexCoordinateConstraint k0 k ξ = ξ := by
  simp [standardSimplexCoordinateConstraint, hk]

/-- At `k0`, `standardSimplexCoordinateConstraint k0` is `ξ - 1`. -/
@[simp] theorem standardSimplexCoordinateConstraint_of_eq
    (k0 k : ι) (ξ : α) (hk : k = k0) :
    standardSimplexCoordinateConstraint k0 k ξ = ξ - 1 := by
  simp [standardSimplexCoordinateConstraint, hk]

end Constraint

end Function

end

/-! ### Definition_6_28_12 (from Chap06) -/
noncomputable section

universe u v w

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.12 writes the Fenchel conjugate by its pointwise supremum
  formula and, in the chapter codomain layer, by the equivalent negative-infimum formula.
- `core/canonical`: these are already owned by `convexConjugate` and its canonical bridge theorem
  family from `Chap03.Defn_12_2`, at the primitive pairing and codomain abstraction layers.
- `bridge/view`: this file is a recap/reuse surface only; it should reuse those owners directly
  instead of adding alias theorem names.

Abstraction checks:
- no over-concrete `ℝ`/`EReal` lock-in is needed;
- the generic codomain layer remains `SupSet` + subtraction + pairing;
- the chapter-specific codomain bridge remains the existing `WithTopBot α` theorem;
- no extra wrapper owner/API is introduced.
-/

/- Definition 6.28.12: the Fenchel conjugate owner is exactly the existing canonical declaration. -/
recall convexConjugate

/- Canonical source-facing supremum formula for `f⋆`. -/
recall convexConjugate_eq_iSup_pairing_sub

/- Chapter-facing `WithTopBot α` bridge to the equivalent negative-infimum formula. -/
recall convexConjugate_eq_neg_iInf_sub_pairing
