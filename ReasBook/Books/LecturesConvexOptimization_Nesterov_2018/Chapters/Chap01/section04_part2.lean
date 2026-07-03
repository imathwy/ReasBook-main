import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.MonotoneConvergence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_4_10 (from Items/Chap01) -/
noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 1.4.10 lies in the tangent-direction geometry of differentiable level sets.

Relevant owner-style declarations sampled before refinement:
* `posTangentConeAt`, the mathlib tangent-cone owner underlying this domain;
* `tangentDirectionsToLevelSet`, the chapter source-facing owner for unit tangent directions to a
  level set;
* `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`, the normalized-secant
  bridge from the textbook formulation to that owner;
* `inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet`, the upstream owner theorem proving
  orthogonality of tangent directions to the gradient.

Source/core/bridge triage:
* source-facing: tangent directions to the level set through `xbar`;
* core/canonical: `posTangentConeAt (f ⁻¹' {f xbar}) xbar`, surfaced in this chapter through
  `tangentDirectionsToLevelSet f xbar`;
* bridge/view: `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`, which keeps
  the textbook secant-limit formulation as a companion characterization.

Primitive data:
* `f : E → ℝ`, `xbar : E`, `s : E`;
* differentiability of `f` at `xbar`;
* owner-level membership `s ∈ tangentDirectionsToLevelSet f xbar`.

Derived API:
* the secant-limit existence criterion from Definition 1.4.9;
* orthogonality to the gradient from the upstream owner theorem.

The previous version duplicated that bridge on the theorem surface by taking existential secant
data as primitive input. This refinement removes the duplicate wheel and keeps the numbered item
as direct recall of the chapter owner theorem; the secant-limit formulation remains available via
Definition 1.4.9.
-/

/- Lemma 1.4.10: if `f` is differentiable at `xbar`, then every tangent direction to the level
set of `f` at `xbar` is orthogonal to the gradient at `xbar`. -/
recall inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    (hs : s ∈ tangentDirectionsToLevelSet f xbar) :
    inner ℝ (∇ f xbar) s = 0

/-! ### Definition_1_4_11 (from Chap01) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- 
Definition 1.4.11 is source-facing in first-order differential calculus over real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `HasDerivWithinAt`
- `HasLineDerivAt`
- `HasLineDerivWithinAt`
- `HasFDerivAt.hasLineDerivAt`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`

Primitive data:
- `f`, `xBar`, `s`, and the derivative value `Δ`

Derived API:
- ambient differentiability of `f` at `xBar` gives the line-derivative owner
  `HasLineDerivAt ℝ f (fderiv ℝ f xBar s) xBar s`;
- restricting that ambient derivative at `0` to `Set.Ici 0` yields the textbook one-sided
  directional derivative along the ray.

Source/core/bridge triage:
- source-facing: the right derivative of the directional slice along the ray
  `α ↦ f (xBar + α • s)`
- core/canonical: `HasDerivWithinAt` on that scalar slice over `Set.Ici 0`
- bridge/view: the differentiability bridge through `HasLineDerivAt`

The ambient space is generalized from `ℝⁿ` to an arbitrary real normed space because no Euclidean
coordinates or finite-dimensional structure enter the owner notion or the bridge theorem. The
scalar field remains `ℝ` because the source notion is explicitly the one-sided derivative for
`α ↓ 0` on `Set.Ici 0`.
-/
recall HasDerivWithinAt
recall HasLineDerivAt
recall HasLineDerivWithinAt
recall HasFDerivAt.hasLineDerivAt

section

variable {f : E → ℝ} {xBar s : E} {Δ : ℝ}

/- Definition 1.4.11: the directional derivative of `f` at `xBar` along `s` is the right
derivative at `0` of the directional slice `α ↦ f (xBar + α • s)`. In Lean the source-facing
owner is the canonical one-variable derivative statement on `Set.Ici 0`. -/
#check (
  HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0
)

/-- A differentiable function has the expected one-sided derivative along every ray. -/
-- Proof sketch: `hf` gives the Fréchet derivative of `f` at `xBar`, and mathlib's owner line
-- derivative API specializes this derivative to the line `α ↦ xBar + α • s`. Restricting the
-- resulting derivative at `0` to `Set.Ici 0` gives the desired one-sided derivative.
theorem hasDerivWithinAt_directionalSlice_of_differentiableAt
    (hf : DifferentiableAt ℝ f xBar) :
    HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) (fderiv ℝ f xBar s) (Set.Ici (0 : ℝ)) 0 := by
  simpa [HasLineDerivAt] using (hf.hasFDerivAt.hasLineDerivAt s).hasDerivWithinAt

end

/-! ### Definition_1_4_11 (from Items/Chap01) -/
noncomputable section

universe u

/-
Definition 1.4.11 is source-facing in first-order differential calculus over real normed spaces.

Relevant owner-style declarations sampled before drafting:
- `HasDerivWithinAt`
- `HasLineDerivAt`
- `HasDerivAt.hasDerivWithinAt`
- `HasFDerivAt.hasLineDerivAt`
- `hasDerivWithinAt_directionalSlice_of_differentiableAt` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_11.lean`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`

Primitive data:
- `f`, `xBar`, `s`, and the derivative value `Δ`

Derived API:
- differentiability of `f` at `xBar` gives the ambient line-derivative statement
- restricting that two-sided statement to `Set.Ici 0` yields the textbook one-sided directional
  derivative along the ray

Source/core/bridge triage:
- source-facing: the right derivative of the directional slice along the ray
  `α ↦ xBar + α • s`
- core/canonical: `HasDerivWithinAt` on that scalar slice over `Set.Ici 0`
- bridge/view: the differentiability bridge through `HasLineDerivAt`

The ambient space is generalized from `ℝⁿ` to an arbitrary real normed space because no Euclidean
coordinates or finite-dimensional structure enter the owner notion or the bridge theorem. The
scalar field remains `ℝ` because the source definition is the one-sided derivative for `α ↓ 0`
along the real ray.

The source-facing owner already exists canonically in mathlib, and the chapter file already owns
the thin differentiability bridge. This item therefore exposes the owner expression directly and
recalls the companion bridge instead of keeping a duplicate local theorem body. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {xBar s : E} {Δ : ℝ}

/-
Definition 1.4.11: the directional derivative of `f` at `xBar` along `s` is the right derivative
at `0` of the directional slice `α ↦ f (xBar + α • s)`. In Lean the source-facing owner is the
canonical one-variable derivative statement on `Set.Ici 0`.
-/
#check (
  HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0
)

/-
A differentiable real-valued function has the expected one-sided derivative along every ray; this
is the chapter's thin bridge from ambient differentiability to the source-facing owner.
-/
recall hasDerivWithinAt_directionalSlice_of_differentiableAt
    {f : E → ℝ} {xBar s : E} (hf : DifferentiableAt ℝ f xBar) :
    HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) (fderiv ℝ f xBar s) (Set.Ici (0 : ℝ)) 0

end

/-! ### Proposition_1_4_12 (from Chap01) -/
open scoped Gradient
open NormedSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "S" => Metric.sphere (0 : E) 1

/-
Proposition 1.4.12 is `source-facing` in first-order smooth optimization.

Primary domain:
* directional derivatives on a real Hilbert space, minimized over the unit sphere.

Sampled owner-style declarations:
* `HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`
* `lineDeriv ℝ f xBar s`
* `DifferentiableAt.lineDeriv_eq_fderiv`
* `inner_gradient_left`
* `IsMinOn`

Owner abstraction:
* the directional-derivative owner `lineDeriv ℝ f xBar`
* represented, under differentiability, by the gradient vector `∇ f xBar`

Primitive data:
* a differentiable function `f`
* a base point `xBar`

Derived API:
* the lower bound for `lineDeriv ℝ f xBar` on the unit sphere
* the attained value at `-normalize (∇ f xBar)`
* the source-facing minimizer statement on the unit sphere

Source/core/bridge triage:
* source-facing: minimizing the directional derivative over unit directions
* core/canonical: `lineDeriv ℝ f xBar`, `gradient`, `normalize`, `Metric.sphere`, and `IsMinOn`
* bridge/view: `DifferentiableAt.lineDeriv_eq_fderiv` and `inner_gradient_left`

Definition 1.4.11 already fixed the chapter owner for directional derivatives. This file therefore
keeps `lineDeriv` on the public theorem surface and uses `fderiv ℝ f xBar s` only through the
canonical differentiability bridge, not as a second owner for the same notion.
-/

/-- Helper for Proposition 1.4.12: the normalized negative gradient is a unit direction whenever
the gradient is nonzero. -/
-- Proof sketch: rewrite membership in the unit sphere as a norm-one condition and apply
-- `norm_normalize` to `∇ f xBar`, then simplify the minus sign with `norm_neg`.
private lemma neg_normalize_gradient_mem_unitSphere
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    -normalize (∇ f xBar) ∈ S := by
  -- Turn unit-sphere membership into the scalar norm condition.
  rw [mem_sphere_zero_iff_norm]
  -- The minus sign does not change the norm, and `normalize` has norm one off the origin.
  simpa [norm_neg] using norm_normalize hgrad

/-- Helper for Proposition 1.4.12: along every unit direction, the directional derivative is
bounded below by the negative gradient norm. -/
-- Proof sketch: rewrite `lineDeriv` as `fderiv` using `DifferentiableAt.lineDeriv_eq_fderiv`,
-- then identify `fderiv` with the gradient pairing via `inner_gradient_left`. Turn `s ∈ S` into
-- `‖s‖ = 1` and apply the Cauchy-Schwarz bound `abs_real_inner_le_norm`.
theorem lineDeriv_ge_neg_norm_of_mem_unitSphere
    {f : E → ℝ} {xBar s : E} (hf : DifferentiableAt ℝ f xBar) (hs : s ∈ S) :
    lineDeriv ℝ f xBar s ≥ -‖∇ f xBar‖ := by
  have hlineDeriv :
      fderiv ℝ f xBar s = inner ℝ (∇ f xBar) s := by
    -- Replace the Fréchet derivative by pairing with the gradient.
    symm
    simpa using (inner_gradient_left (y := s) hf)
  have hbound : -(‖∇ f xBar‖ * ‖s‖) ≤ inner ℝ (∇ f xBar) s := by
    -- Cauchy-Schwarz bounds the real inner product from below by the negative product of norms.
    exact neg_le_of_abs_le (by
      simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f xBar) s)
  -- Once `s` is on the unit sphere, its norm simplifies to `1`.
  rw [hf.lineDeriv_eq_fderiv, hlineDeriv]
  rw [mem_sphere_zero_iff_norm] at hs
  simpa [hs] using hbound

/-- Helper for Proposition 1.4.12: the directional derivative at the normalized negative gradient
equals the negative gradient norm when the gradient is nonzero. -/
-- Proof sketch: first derive `DifferentiableAt ℝ f xBar` from `hgrad` by contraposing
-- `gradient_eq_zero_of_not_differentiableAt`. Then rewrite `lineDeriv` as `fderiv`, identify
-- `fderiv` with the gradient pairing, and simplify the resulting inner product against
-- `-normalize (∇ f xBar)` using `norm_normalize`.
theorem lineDeriv_neg_normalize_gradient_eq_neg_norm
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    lineDeriv ℝ f xBar (-normalize (∇ f xBar)) = -‖∇ f xBar‖ := by
  have hdiff : DifferentiableAt ℝ f xBar := by
    -- A nonzero totalized gradient forces genuine differentiability at `xBar`.
    by_contra hnot_diff
    have hzero : ∇ f xBar = 0 := by
      simpa using gradient_eq_zero_of_not_differentiableAt hnot_diff
    exact hgrad hzero
  have hlineDeriv :
      fderiv ℝ f xBar (-normalize (∇ f xBar)) =
        inner ℝ (∇ f xBar) (-normalize (∇ f xBar)) := by
    -- Rewrite the Fréchet derivative through the gradient pairing.
    symm
    simpa using (inner_gradient_left (y := -normalize (∇ f xBar)) hdiff)
  have hnorm_ne : ‖∇ f xBar‖ ≠ 0 := norm_ne_zero_iff.mpr hgrad
  rw [hdiff.lineDeriv_eq_fderiv, hlineDeriv]
  calc
    inner ℝ (∇ f xBar) (-normalize (∇ f xBar)) =
        -inner ℝ (∇ f xBar) (normalize (∇ f xBar)) := by
      -- Move the sign out of the inner product.
      rw [inner_neg_right]
    _ = -(‖∇ f xBar‖ ^ (2 : ℕ) / ‖∇ f xBar‖) := by
      -- Expand `normalize` once and evaluate the self-inner product as a norm square.
      rw [NormedSpace.normalize, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hnorm_ne]
    _ = -‖∇ f xBar‖ := by
      -- Cancel one copy of the nonzero norm in the quotient.
      field_simp [hnorm_ne]

/-- Proposition 1.4.12: if the gradient at `xBar` is nonzero, then the minimum directional
derivative on the unit sphere is attained at the normalized negative gradient direction.
Concretely, `-normalize (∇ f xBar)` lies on the unit sphere and minimizes `lineDeriv ℝ f xBar`
there. The companion lemmas
`lineDeriv_ge_neg_norm_of_mem_unitSphere` and
`lineDeriv_neg_normalize_gradient_eq_neg_norm` isolate the lower-bound and value computations. -/
-- Proof sketch: first derive `DifferentiableAt ℝ f xBar` from `hgrad` using
-- `gradient_eq_zero_of_not_differentiableAt`. The nonzero-gradient hypothesis then puts
-- `-normalize (∇ f xBar)` on the unit sphere by `norm_normalize`. The value clause is
-- `lineDeriv_neg_normalize_gradient_eq_neg_norm`. For minimality, combine that equality with
-- `lineDeriv_ge_neg_norm_of_mem_unitSphere` and rewrite the result using `isMinOn_iff`.
theorem lineDeriv_isMinOn_unitSphere_at_neg_normalize_gradient
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    -normalize (∇ f xBar) ∈ S ∧
      IsMinOn (lineDeriv ℝ f xBar) S (-normalize (∇ f xBar)) := by
  have hdiff : DifferentiableAt ℝ f xBar := by
    -- The minimizer formula only makes sense in the differentiable regime.
    by_contra hnot_diff
    have hzero : ∇ f xBar = 0 := by
      simpa using gradient_eq_zero_of_not_differentiableAt hnot_diff
    exact hgrad hzero
  constructor
  · -- The candidate direction is feasible on the unit sphere.
    exact neg_normalize_gradient_mem_unitSphere hgrad
  · rw [isMinOn_iff]
    intro s hs
    -- The candidate value is exactly `-‖∇ f xBar‖`, and every other unit direction is above it.
    rw [lineDeriv_neg_normalize_gradient_eq_neg_norm hgrad]
    exact lineDeriv_ge_neg_norm_of_mem_unitSphere hdiff hs

end

/-! ### Theorem_1_4_13 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

/- 
Theorem 1.4.13 lies in first-order differential calculus and stationarity for local minimizers.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`, the chapter's owner predicate for stationarity
* `DifferentiableAt.hasGradientAt`, which supplies the canonical gradient witness
* `gradient_eq_zero_of_not_differentiableAt`, which totalizes the gradient off the differentiable
  locus
* `IsLocalMin.fderiv_eq_zero`, mathlib's Fermat theorem for local minima

Best owner abstraction:
* `HasGradientAt f 0 xStar`

Primitive data:
* the function `f`
* the point `xStar`
* local or global minimality at `xStar`

Derived API:
* the stationary-point equality for local and global minimizers
* the global-minimizer specialization below
* the differentiable `HasGradientAt` bridge theorems below

Source/core/bridge triage:
* source-facing: Theorem 1.4.13's stationary-point conclusion
* core/canonical: `HasGradientAt f 0 xStar`
* bridge/view: the thin differentiable `HasGradientAt` companion deduced from
  `IsLocalMin.fderiv_eq_zero` and `DifferentiableAt.hasGradientAt`

The source statement is about `f : ℝⁿ → ℝ`, but the mathematical content uses only the ambient
real inner-product-space structure needed for the canonical gradient owner. The refined file keeps
the same semantics while dropping the unnecessary concrete `EuclideanSpace ℝ (Fin n)` model layer.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: if `f` is differentiable at `xStar`, apply Fermat's theorem
-- `IsLocalMin.fderiv_eq_zero` and recover the gradient from `hf.hasGradientAt`; otherwise the
-- totalized gradient already vanishes by `gradient_eq_zero_of_not_differentiableAt`.
/-- Theorem 1.4.13: a local minimizer of a real-valued function on a real inner-product space has
vanishing totalized gradient. -/
theorem isLocalMin_gradient_eq_zero
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 := by
  by_cases hf : DifferentiableAt ℝ f xStar
  · have hstationary : HasGradientAt f 0 xStar := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa [IsLocalMin.fderiv_eq_zero hmin] using hf.hasFDerivAt
    exact hstationary.gradient
  · simpa using gradient_eq_zero_of_not_differentiableAt hf

/-- Companion bridge: a differentiable local minimizer carries the canonical zero-gradient owner
`HasGradientAt f 0 xStar`. -/
theorem isLocalMin_hasGradientAt_zero_of_differentiableAt
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) (hf : DifferentiableAt ℝ f xStar) :
    HasGradientAt f 0 xStar := by
  convert hf.hasGradientAt using 1
  exact (isLocalMin_gradient_eq_zero hmin).symm

-- Proof sketch: convert `IsMinOn f Set.univ xStar` to a local minimum using
-- `IsMinOn.isLocalMin`, then invoke Theorem 1.4.13 at the minimizer.
/-- A global minimizer on `Set.univ` has vanishing totalized gradient. -/
theorem isMinOn_gradient_eq_zero
    {f : E → ℝ} {xStar : E} (hmin : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact isLocalMin_gradient_eq_zero (hmin.isLocalMin (by simp))

/-- Companion bridge: a global minimizer on `Set.univ` carries the canonical stationary witness as
soon as `f` is differentiable at that minimizer. -/
theorem isMinOn_hasGradientAt_zero_of_differentiableAt
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hmin : IsMinOn f Set.univ xStar) :
    HasGradientAt f 0 xStar := by
  convert hf.hasGradientAt using 1
  exact (isMinOn_gradient_eq_zero hmin).symm

end

/-! ### Theorem_1_4_13 (from Items/Chap01) -/
/- Theorem 1.4.13 lies in first-order differential calculus and stationarity for local minimizers
on real inner-product spaces.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`, the canonical owner for stationarity of a differentiable scalar objective;
* `DifferentiableAt.hasGradientAt`, the bridge from differentiability to gradient data;
* `IsLocalMin.fderiv_eq_zero`, mathlib's Fermat theorem for local minima;
* `gradient_eq_zero_of_not_differentiableAt`, which explains why the source-facing equality has no
  differentiability binder;
* `isLocalMin_gradient_eq_zero` in `Chap01/Theorem_1_4_13`, the chapter source-facing theorem for
  this exact statement.

Source/core/bridge triage:
* source-facing: the textbook conclusion `∇ f(xStar) = 0`;
* core/canonical: the stationary witness `HasGradientAt f 0 xStar`;
* bridge/view: the companion owner theorem `isLocalMin_hasGradientAt_zero_of_differentiableAt`.

The previous item file duplicated the chapter theorem with the same public interface and no new
primitive data. This refinement removes that duplicate wheel and keeps the item as a pure recall
surface. -/

recall isLocalMin_gradient_eq_zero

/-! ### Theorem_1_4_14 (from Chap01) -/
open Matrix
open scoped Gradient

noncomputable section

/- 
Theorem 1.4.14 lives in smooth equality-constrained optimization.

Relevant owner declarations sampled before refinement:
* `IsLocalMinOn.hasFDerivWithinAt_eq_zero`
* `mem_posTangentConeAt_of_segment_subset`
* `LinearMap.orthogonal_ker`
* `DifferentiableAt.hasGradientAt`
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

Best owner abstraction:
* the linear constraint map `L : E →ₗ[ℝ] F`

Primitive data:
* `f`, `L`, `b`, `xStar`
* pointwise differentiability of `f` at `xStar`
* feasibility `L xStar = b`
* local minimality of `f` on the affine level set

Derived API:
* the canonical range statement `∇ f xStar ∈ L.adjoint.range`
* the matrix-source bridge witness `λStar` with `∇ f xStar = Aᵀ.toEuclideanLin λStar`

Source/core/bridge triage:
* source-facing: existence of a Lagrange multiplier for the linear equality constraint in the
  textbook transpose form
* core/canonical: a real finite-dimensional inner-product-space map `L` together with
  `LinearMap.orthogonal_ker`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

The proof only uses differentiability at the minimizing point, so the refined API exposes
`DifferentiableAt ℝ f xStar` instead of a stronger global differentiability assumption. In
finite-dimensional real inner-product spaces the adjoint-range identity
`L.kerᗮ = L.adjoint.range` makes the usual surjectivity hypothesis for the constraint map
redundant, so the refined theorem omits that binder.
-/

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- If `xStar` is a local minimizer of a function on the linear level set `{x | L x = b}` and `f`
is differentiable at `xStar`, then the gradient at `xStar` belongs to the adjoint range of the
constraint map. -/
-- Proof sketch: every vector `h ∈ ker L` and its negative remain feasible along a
-- whole segment through `xStar`, so local minimality forces `Df(xStar) h = 0`. Hence
-- `∇ f xStar` is orthogonal to `ker L`, and `LinearMap.orthogonal_ker` rewrites
-- this orthogonality condition as membership in the adjoint range.
theorem gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet
    (f : E → ℝ) (L : E →ₗ[ℝ] F) (b : F)
    {xStar : E} (hf : DifferentiableAt ℝ f xStar) (hxStar : L xStar = b)
    (hmin : IsLocalMinOn f {x | L x = b} xStar) :
    ∇ f xStar ∈ L.adjoint.range := by
  let constraintSet : Set E := {x | L x = b}
  have hxConstraint : xStar ∈ constraintSet := by
    simpa [constraintSet] using hxStar
  have hminConstraint : IsLocalMinOn f constraintSet xStar := by
    simpa [constraintSet] using hmin
  have hconstraint_convex : Convex ℝ constraintSet :=
    (convex_singleton b).linear_preimage L
  have hgrad_orthogonal : ∇ f xStar ∈ L.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro h hh
    have hxPlus : xStar + h ∈ constraintSet := by
      simpa [constraintSet, hh, hxStar]
    have hxMinus : xStar + -h ∈ constraintSet := by
      simpa [constraintSet, hh, hxStar]
    have hpos : h ∈ posTangentConeAt constraintSet xStar := by
      exact mem_posTangentConeAt_of_segment_subset
        (hconstraint_convex.segment_subset hxConstraint hxPlus)
    have hneg : -h ∈ posTangentConeAt constraintSet xStar := by
      exact mem_posTangentConeAt_of_segment_subset
        (hconstraint_convex.segment_subset hxConstraint hxMinus)
    have hderiv : fderiv ℝ f xStar h = 0 :=
      hminConstraint.hasFDerivWithinAt_eq_zero hf.hasFDerivAt.hasFDerivWithinAt hpos hneg
    simpa [hf.hasGradientAt.fderiv_apply] using hderiv
  rwa [LinearMap.orthogonal_ker] at hgrad_orthogonal

end

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- Theorem 1.4.14: if `xStar` is a local minimizer of a function `f : ℝⁿ → ℝ`
on the linear level set `{x | A.toEuclideanLin x = b}` and `f` is differentiable at `xStar`,
then there is a multiplier `λStar ∈ ℝᵐ` such that
`∇ f xStar = Aᵀ.toEuclideanLin λStar`. -/
theorem exists_lagrangeMultiplier_of_isLocalMinOn_linearLevelSet
    (f : E → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Λ)
    {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hxStar : A.toEuclideanLin xStar = b)
    (hmin : IsLocalMinOn f {x | A.toEuclideanLin x = b} xStar) :
    ∃ lamStar : Λ, ∇ f xStar = Aᵀ.toEuclideanLin lamStar := by
  rcases
      gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet
        f A.toEuclideanLin b hf hxStar hmin with
    ⟨lamStar, hlamStar⟩
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  refine ⟨lamStar, ?_⟩
  simpa [hAdj] using hlamStar.symm

end

/-! ### Definition_1_4_15 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {xBar : E}

/-
Primary domain: first-order differential calculus on real Hilbert spaces.

Source/core/bridge triage:
* source-facing item: the stationary-point condition at `xBar`
* core/canonical owner abstraction: `HasGradientAt f 0 xBar`
* bridge/view: the derived reformulation
  `DifferentiableAt ℝ f xBar ∧ ∇ f xBar = 0`

Relevant owner declarations sampled before refining:
* `HasGradientAt`
* `DifferentiableAt.hasGradientAt`
* `HasGradientAt.differentiableAt`
* `HasGradientAt.gradient`

Primitive data:
* the owner predicate `HasGradientAt f g xBar`

Derived API:
* differentiability at `xBar`
* identification of the canonical gradient with the witness `g`

The source specializes this owner to `f : ℝⁿ → ℝ`, but no Euclidean coordinates or
finite-dimensional structure are used in the owner itself. Definition 1.4.15 is therefore a
recall item: a stationary point of `f` at `xBar` is exactly the specialized owner condition
`HasGradientAt f 0 xBar`.
-/

/- Definition 1.4.15: for a differentiable real-valued function, a point is stationary exactly
when it satisfies the canonical zero-gradient owner condition `HasGradientAt f 0 xBar`. -/
#check HasGradientAt f 0 xBar

-- Proof sketch: use `hf.hasGradientAt` to identify the canonical gradient witness at `xBar` with
-- `∇ f xBar`; then `HasGradientAt.gradient` turns `HasGradientAt f 0 xBar` into the zero-gradient
-- equation, and conversely `hf.hasGradientAt` rewrites `∇ f xBar = 0` back to the stationary
-- owner condition.
/-- Under differentiability at `xBar`, the canonical stationary-point owner is equivalent to the
textbook equation `∇ f xBar = 0`. -/
theorem hasGradientAt_zero_iff_gradient_eq_zero (hf : DifferentiableAt ℝ f xBar) :
    HasGradientAt f 0 xBar ↔ ∇ f xBar = 0 := by
  constructor
  · intro h
    simpa using h.gradient
  · intro h
    convert hf.hasGradientAt using 1
    exact h.symm

end

/-! ### Definition_1_4_16 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/- Definition 1.4.16 lies in the second-order differential-calculus domain on Euclidean space.

Source/core/bridge triage:
* source-facing: the Hessian matrix of `f : ℝⁿ → ℝ` at `xBar`
* core/canonical: the derivative of the gradient map, viewed as a continuous linear endomorphism
* bridge/view: the standard-basis matrix of that endomorphism

Sampled owner-style declarations:
* `gradient`
* `fderiv`
* `LinearMap.toMatrixOrthonormal`
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`

The file therefore keeps the intrinsic operator owner `hessian f x` and exposes the textbook
matrix as its standard Euclidean matrix view. -/

/-- The Hessian of `f` at `x`, viewed intrinsically as the derivative of the gradient map. -/
abbrev hessian (f : X → ℝ) (x : X) : X →L[ℝ] X :=
  fderiv ℝ (∇ f) x

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Definition 1.4.16: if `f : ℝⁿ → ℝ`, the Hessian of `f` at `x` is the matrix of the
derivative of the gradient map in the standard orthonormal basis of `ℝⁿ`. -/
abbrev hessianMatrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrixOrthonormal e (hessian f x)

@[inherit_doc hessianMatrix]
scoped[Gradient] notation "∇²" => hessianMatrix

-- Proof sketch: unfold `hessianMatrix` and apply the entrywise formula for
-- `LinearMap.toMatrixOrthonormal` in the standard orthonormal basis.
/-- The `(i,j)` entry of the Hessian matrix is the inner product of the `i`th standard basis
vector with the Hessian operator applied to the `j`th standard basis vector. -/
theorem hessianMatrix_apply (f : E → ℝ) (x : E) (i j : Fin n) :
    ∇² f x i j = inner ℝ (e i) (hessian f x (e j)) := by
  simpa [hessianMatrix] using
    (LinearMap.toMatrixOrthonormal_apply_apply e (hessian f x) i j)

/-- Helper for Definition 1.4.16: the `i`th coordinate of the Euclidean gradient is the inner
product with the `i`th standard basis vector. -/
lemma gradient_coordinate_eq_inner_basis (f : E → ℝ) (i : Fin n) :
    (fun y : E ↦ ((∇ f) y) i) = fun y : E ↦ inner ℝ (e i) ((∇ f) y) := by
  -- The Euclidean orthonormal basis recovers coordinates by inner product.
  funext y
  simpa using (EuclideanSpace.basisFun_inner (x := ((∇ f) y)) (i := i)).symm

/-- Helper for Definition 1.4.16: the derivative of a gradient coordinate is obtained by composing
the Hessian operator with the corresponding coordinate functional. -/
lemma hasFDerivAt_gradient_coordinate
    (f : E → ℝ) (x : E) (i : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    HasFDerivAt (fun y : E ↦ ((∇ f) y) i) (((innerSL ℝ) (e i)).comp (hessian f x)) x := by
  -- Rewrite the coordinate map in the standard inner-product form.
  rw [gradient_coordinate_eq_inner_basis (f := f) (i := i)]
  -- The chain rule differentiates the fixed coordinate functional after the gradient.
  simpa [hessian, Function.comp, innerSL_apply_apply] using
    (((innerSL ℝ) (e i)).hasFDerivAt.comp x hgrad.hasFDerivAt)

/-- Helper for Definition 1.4.16: evaluating the derivative of the `i`th gradient coordinate on
the `j`th standard basis vector gives the corresponding Hessian inner-product entry. -/
lemma fderiv_gradient_coordinate_apply_basis
    (f : E → ℝ) (x : E) (i j : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    fderiv ℝ (fun y : E ↦ ((∇ f) y) i) x (e j) = inner ℝ (e i) (hessian f x (e j)) := by
  -- Replace the Fréchet derivative by the chain-rule derivative from the previous lemma.
  rw [(hasFDerivAt_gradient_coordinate (f := f) (x := x) (i := i) hgrad).fderiv]
  -- Evaluating the composed coordinate functional gives the advertised inner product.
  rfl

-- Proof sketch: combine `hessianMatrix_apply` with the coordinate formula for the gradient and
-- differentiate the `i`th gradient coordinate in the `j`th basis direction.
/-- Under differentiability of the gradient at `x`, the `(i,j)` entry of the Hessian matrix is
the derivative of the `i`th gradient coordinate in the `j`th standard basis direction, i.e. the
textbook second partial derivative. -/
theorem hessianMatrix_apply_eq_fderiv_gradient_coordinate
    (f : E → ℝ) (x : E) (i j : Fin n) (hgrad : DifferentiableAt ℝ (∇ f) x) :
    ∇² f x i j = fderiv ℝ (fun y : E ↦ ((∇ f) y) i) x (e j) := by
  -- First read the matrix entry through the intrinsic Hessian operator.
  rw [hessianMatrix_apply]
  -- Then identify the directional derivative of the gradient coordinate with the same quantity.
  rw [fderiv_gradient_coordinate_apply_basis (f := f) (x := x) (i := i) (j := j) hgrad]

-- Proof sketch: rewrite `∇² f x` as `LinearMap.toMatrixOrthonormal e (hessian f x)` and apply
-- `Matrix.toEuclideanLin_eq_toLin_orthonormal`.
/-- Turning the Hessian matrix back into its Euclidean linear action recovers the intrinsic
Hessian operator. -/
theorem hessianMatrix_toEuclideanLin (f : E → ℝ) (x : E) :
    (∇² f x).toEuclideanLin = hessian f x := by
  rw [hessianMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

end

/-! ### Definition_1_4_16 (from Items/Chap01) -/
open scoped Gradient

noncomputable section

universe u

/- Definition 1.4.16 lies in second-order differential calculus on finite-dimensional Euclidean
space.

Relevant owner-style declarations sampled before refining:
* `hessian` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_16.lean`, the chapter owner for the intrinsic
  Hessian operator `fderiv ℝ (∇ f) x`
* `hessianMatrix` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_16.lean`, the source-facing matrix view in
  the standard Euclidean basis
* `LinearMap.toMatrixOrthonormal`, the canonical matrix presentation of a Euclidean endomorphism
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`, the inverse bridge back to the intrinsic operator

Best owner abstraction:
* core/canonical owner: `hessian`

Primitive data:
* a real-valued function `f`
* a base point `x`

Derived API:
* the Euclidean matrix view `hessianMatrix f x`
* the notation surface `∇² f x`
* the entrywise coordinate formula `hessianMatrix_apply`
* the second-partial bridge `hessianMatrix_apply_eq_fderiv_gradient_coordinate`
* the reconstruction bridge `hessianMatrix_toEuclideanLin`

Source/core/bridge triage:
* source-facing: the textbook Hessian matrix on `ℝⁿ`
* core/canonical: the intrinsic Hessian operator `hessian f x`
* bridge/view: `hessianMatrix`, `hessianMatrix_apply`,
  `hessianMatrix_apply_eq_fderiv_gradient_coordinate`, and
  `hessianMatrix_toEuclideanLin`

The exact owner and bridge declarations already exist in the chapter file, so this item is
refined to a recall surface instead of reintroducing parallel local Hessian definitions.
-/

/- The intrinsic Hessian operator is the chapter owner for the derivative of the gradient map. -/
recall hessian {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : X → ℝ) (x : X) : X →L[ℝ] X

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.4.16: on `ℝⁿ`, the textbook Hessian matrix is the standard-basis matrix of the
intrinsic Hessian operator. -/
recall hessianMatrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ

variable (f : E → ℝ) (x : E)

/- The `Gradient`-scope notation `∇² f x` is the source-facing surface for `hessianMatrix f x`. -/
#check ∇² f x

/- The entries of `∇² f x` are obtained by pairing the intrinsic Hessian operator with the
standard basis vectors. -/
recall hessianMatrix_apply

/- Under first- and second-order differentiability, each matrix entry is the directional
derivative of the corresponding gradient coordinate, i.e. the textbook second partial
derivative. -/
recall hessianMatrix_apply_eq_fderiv_gradient_coordinate

/- Converting the Hessian matrix back to a Euclidean linear map recovers the intrinsic Hessian
operator. -/
recall hessianMatrix_toEuclideanLin

end

/-! ### Definition_1_4_17 (from Chap01) -/
noncomputable section

universe u

open scoped Gradient

section TaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.4.17 lies in the second-order local Taylor-model domain for smooth optimization.

Primary domain:
* second-order local models on real Hilbert spaces

Relevant owner-style declarations sampled before refining:
* `HasGradientAt` in mathlib, the owner for genuine first-order differential data
* `HasFDerivAt` in mathlib, the owner for genuine second-order differential data of the gradient
* `hessian` in `Definition_1_4_16`, the intrinsic operator-valued Hessian owner
* `hessianMatrix` in `Definition_1_4_16`, the Euclidean matrix view of that intrinsic Hessian

Source/core/bridge triage:
* source-facing/core: `secondOrderTaylorModelAt f x`
* bridge/view: the evaluation formula `secondOrderTaylorModelAt_apply`
* bridge/view: the Euclidean matrix rewrite
  `secondOrderTaylorModelAt_apply_hessianMatrix`

Primitive data:
* the function `f`
* the base point `x`

Derived API:
* pointwise evaluation of the quadratic model at `y`
* the `ℝⁿ` matrix realization via `∇² f x`

The public owner for this numbered item is therefore the second-order Taylor model itself. The
first-order Taylor model and the generic quadratic regularization operator live in the auxiliary
module `Chap01/FirstOrderTaylorModel`. -/

/-- Definition 1.4.17: the second-order Taylor model of `f` at `x`. -/
def secondOrderTaylorModelAt (f : E → ℝ) (x : E) : E → ℝ :=
  fun y ↦
    f x +
      inner ℝ (∇ f x) (y - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x)

/-- Evaluating `secondOrderTaylorModelAt f x` recovers the displayed quadratic formula. -/
@[simp] theorem secondOrderTaylorModelAt_apply (f : E → ℝ) (x y : E) :
    secondOrderTaylorModelAt f x y =
      f x +
        inner ℝ (∇ f x) (y - x) +
          (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) :=
  rfl

section EuclideanSpace

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin n)

/-- On `ℝⁿ`, the quadratic Taylor model can be rewritten using the Hessian matrix `∇² f x`
acting on the displacement `y - x`. -/
theorem secondOrderTaylorModelAt_apply_hessianMatrix
    (f : F → ℝ) (x y : F) :
    secondOrderTaylorModelAt f x y =
      f x +
        inner ℝ (∇ f x) (y - x) +
          (1 / 2 : ℝ) * inner ℝ ((∇² f x).toEuclideanLin (y - x)) (y - x) := by
  rw [secondOrderTaylorModelAt_apply]
  have hlin :
      (∇² f x).toEuclideanLin (y - x) = hessian f x (y - x) := by
    simpa using
      congrArg (fun T : F →ₗ[ℝ] F ↦ T (y - x)) (hessianMatrix_toEuclideanLin f x)
  rw [← hlin]

end EuclideanSpace

end TaylorModel

/-! ### Definition_1_4_18 (from Chap01) -/
open scoped ComplexOrder MatrixOrder

/- Definition 1.4.18 is a source-facing recall of positive semidefinite and positive definite real
square matrices, implemented by the generic matrix-positivity owners below and specialized in the
textbook to `ℝ`.

Primary domain:
- matrix positivity and the Loewner order on matrices over `ℝ` or `ℂ`.

Sampled owner-style declarations:
- `Matrix.PosSemidef`
- `Matrix.PosDef`
- `Matrix.nonneg_iff_posSemidef`
- `Matrix.isStrictlyPositive_iff_posDef`

Best owner abstraction:
- the canonical matrix-positivity owners `Matrix.PosSemidef` and `Matrix.PosDef`

Primitive data:
- a square matrix `B`

Derived API:
- the order-notation bridges `Matrix.nonneg_iff_posSemidef`
- the strict-positivity bridge `Matrix.isStrictlyPositive_iff_posDef`

Source/core/bridge triage:
- source-facing: the textbook notions `B ≥ 0` and the positive-definite shorthand `B > 0` for
  real square matrices
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`
- bridge/view: `Matrix.nonneg_iff_posSemidef` and the canonical strict-positivity bridge
  `Matrix.isStrictlyPositive_iff_posDef`

This file therefore recalls the owner predicates directly, keeping the order-notation lemmas only
as companion bridges for the textbook notation `B ≥ 0` and the positive-definite shorthand
`B > 0`; in mathlib, the latter is bridged by `IsStrictlyPositive B ↔ B.PosDef`, not by the plain
strict order relation `0 < B`.
-/

recall Matrix.PosSemidef
    {n : Type*} {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (B : Matrix n n R) :
    Prop

recall Matrix.PosDef
    {n : Type*} {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (B : Matrix n n R) :
    Prop

recall Matrix.nonneg_iff_posSemidef
    {𝕜 : Type*} {n : Type*} [RCLike 𝕜] {B : Matrix n n 𝕜} :
    0 ≤ B ↔ B.PosSemidef

recall Matrix.isStrictlyPositive_iff_posDef
    {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {B : Matrix n n 𝕜} :
    IsStrictlyPositive B ↔ B.PosDef

/-! ### Definition_1_4_18 (from Items/Chap01) -/
open scoped MatrixOrder

/- Definition 1.4.18 is a source-facing recall of positive semidefinite and positive definite real
square matrices, implemented by the generic matrix-positivity owners below and specialized here to
the textbook setting over `ℝ`.

Primary domain:
- matrix positivity and the induced order on real matrices.

Sampled owner-style declarations:
- `Matrix.PosSemidef`
- `Matrix.PosDef`
- `Matrix.nonneg_iff_posSemidef`
- `Matrix.isStrictlyPositive_iff_posDef`

Best owner abstraction:
- the canonical matrix-positivity owners `Matrix.PosSemidef` and `Matrix.PosDef`

Primitive data:
- a square matrix `B`

Derived API:
- the order-notation bridges `Matrix.nonneg_iff_posSemidef`
- the strict-order bridge `Matrix.isStrictlyPositive_iff_posDef`

Source/core/bridge triage:
- source-facing: the textbook notions `B ≥ 0` and `B > 0` for real square matrices
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`
- bridge/view: `Matrix.nonneg_iff_posSemidef` and `Matrix.isStrictlyPositive_iff_posDef`

This file therefore recalls the owner predicates directly, keeping the order-notation lemmas only
as companion bridges for the textbook notation `B ≥ 0` and `B > 0`.
-/

section

variable {n : Type*} (B : Matrix n n ℝ)

/- Definition 1.4.18: the textbook notation `B ≥ 0` for a symmetric real matrix means that `B`
is positive semidefinite; the canonical owner notion is `Matrix.PosSemidef`. -/
#check (B.PosSemidef : Prop)

/- Positive definiteness is the corresponding canonical matrix-positivity notion. -/
#check (B.PosDef : Prop)

/- The matrix-order notation `0 ≤ B` is exactly positive semidefiniteness. -/
#check (Matrix.nonneg_iff_posSemidef : 0 ≤ B ↔ B.PosSemidef)

end

section

variable {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)

/- In the textbook real-matrix setting, the canonical strict-positivity predicate is exactly
positive definiteness. -/
#check (Matrix.isStrictlyPositive_iff_posDef : IsStrictlyPositive B ↔ B.PosDef)

end

/-! ### Theorem_1_4_19 (from Chap01) -/
open InnerProductSpace
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.4.19 is source-facing at the Euclidean matrix view of the Hessian from
`Definition_1_4_16`, but its canonical operator owner is already intrinsic to real Hilbert spaces.

Sampled owner-style declarations:
* `hessian` from `Definition_1_4_16`
* `ContDiffAt.isSymmSndFDerivAt`
* `ContinuousLinearMap.IsSymmetric`
* `hessianMatrix` and `Matrix.IsSymm`

Core owner abstraction:
* `(hessian f x).IsSymmetric`

Bridge/view API:
* the Euclidean-coordinate Hessian matrix
-/

private theorem inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt
    {f : E → ℝ} {x v w : E} (hf : ContDiffAt ℝ 2 f x) :
    inner ℝ v (fderiv ℝ (∇ f) x w) = fderiv ℝ (fderiv ℝ f) x w v := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hgrad : fderiv ℝ (∇ f) x = D.comp (fderiv ℝ (fderiv ℝ f) x) := by
    simpa [D, gradient] using fderiv_comp x D.differentiableAt hfdiff
  have hdual (φ : StrongDual ℝ E) (v : E) : inner ℝ v (D φ) = φ v := by
    dsimp [D]
    rw [real_inner_comm]
    change ((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φ)) v = φ v
    simp
  calc
    inner ℝ v (fderiv ℝ (∇ f) x w) = inner ℝ v (D ((fderiv ℝ (fderiv ℝ f) x) w)) := by
      rw [hgrad]
      simp [D]
    _ = (fderiv ℝ (fderiv ℝ f) x w) v := hdual _ _

/-- Under a `C²` hypothesis, the intrinsic Hessian operator `hessian f x` is symmetric. -/
theorem fderiv_gradient_isSymmetric_of_contDiffAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    (hessian f x).IsSymmetric := by
  have hsymm := hf.isSymmSndFDerivAt (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  intro v w
  calc
    inner ℝ (hessian f x v) w = inner ℝ w (hessian f x v) := by
      rw [real_inner_comm]
    _ = fderiv ℝ (fderiv ℝ f) x v w := inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt hf
    _ = fderiv ℝ (fderiv ℝ f) x w v := hsymm.eq _ _
    _ = inner ℝ v (hessian f x w) :=
      (inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt hf).symm

section

variable {n : ℕ}

local notation "EFin" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Theorem 1.4.19: if `f : ℝⁿ → ℝ` is twice continuously differentiable at `x`, then the Hessian
matrix of `f` at `x` is symmetric. -/
theorem hessianMatrix_isSymm_of_contDiffAt {f : EFin → ℝ} {x : EFin}
    (hf : ContDiffAt ℝ 2 f x) :
    (∇² f x).IsSymm := by
  have hH := fderiv_gradient_isSymmetric_of_contDiffAt hf
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  calc
    ∇² f x j i = inner ℝ (hessian f x (e i)) (e j) := by
          rw [hessianMatrix_apply, real_inner_comm]
    _ = inner ℝ (e i) (hessian f x (e j)) := hH _ _
    _ = ∇² f x i j := by
          rw [hessianMatrix_apply]

end

end

/-! ### Theorem_1_4_20 (from Chap01) -/
open scoped Gradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.4.20 is a source-facing item in second-order smooth optimization.

Relevant owner declarations sampled before refinement:
* `hessian` from `Definition_1_4_16`
* `isLocalMin_hasGradientAt_zero_of_differentiableAt` from `Theorem_1_4_13`
* `gradient_eq_zero_of_not_differentiableAt`
* `fderiv_gradient_isSymmetric_of_contDiffAt` from `Theorem_1_4_19`
* `ContinuousLinearMap.isPositive_iff`

Best owner abstractions:
* source-facing: the Hessian quadratic-form condition
  `∀ s, 0 ≤ inner ℝ (hessian f xStar s) s`
* bridge/view: the positive-operator conclusion
  `ContinuousLinearMap.IsPositive (hessian f xStar)` under `ContDiffAt ℝ 2 f xStar`

Primitive data:
* `f`
* `xStar`
* local minimality of `f` at `xStar`
* differentiability of `f` at `xStar`
* differentiability of `∇ f` at `xStar`

Derived API:
* vanishing gradient at `xStar`
* nonnegativity of the Hessian quadratic form at `xStar`
* positivity of the Hessian operator at `xStar` once Hessian symmetry is supplied canonically by
  `ContDiffAt.isSymmSndFDerivAt`

Source/core/bridge triage:
* source-facing: the combined first- and second-order necessary conditions
* core/canonical: `∇ f xStar = 0` together with the directional inequality
  `∀ s, 0 ≤ inner ℝ (hessian f xStar s) s`
* bridge/view: the `C²` upgrade to `ContinuousLinearMap.IsPositive`; Euclidean matrix
  restatements belong in separate Hessian-matrix view files

The public API therefore keeps the source-facing quadratic-form theorem as the main entry. The
positive-operator statement is retained only as the thin `C²` bridge that reuses the canonical
second-derivative symmetry owner instead of routing through a separate Euclidean coordinate view. -/

-- Helper for Theorem 1.4.20: restricting `f` to an affine line through `xStar`
-- preserves local minimality at the origin.
omit [CompleteSpace E] in
private lemma line_restriction_isLocalMin
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) (s : E) :
    IsLocalMin (fun t : ℝ ↦ f (xStar + t • s)) 0 := by
  let g : ℝ → E := fun t ↦ xStar + t • s
  have hmin' : IsLocalMin f (g 0) := by
    dsimp [g]
    simpa using hmin
  have hcont : ContinuousAt g 0 := by
    simpa [g] using
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
        ContinuousAt (fun t : ℝ ↦ xStar + t • s) 0)
  -- Compose the local minimum with the continuous affine line parameterization.
  simpa [g] using hmin'.comp_continuous hcont

-- Helper for Theorem 1.4.20: the derivative of the line restriction at `t` is the line
-- derivative of `f` at the translated base point.
omit [CompleteSpace E] in
private lemma line_restriction_deriv_eq_lineDeriv
    {f : E → ℝ} {xStar s : E} (t : ℝ) :
    deriv (fun u : ℝ ↦ f (xStar + u • s)) t = lineDeriv ℝ f (xStar + t • s) s := by
  -- Shift the affine parameter so the derivative at `t` becomes a line derivative at the origin.
  rw [lineDeriv]
  nth_rewrite 1 [← zero_add t]
  rw [← deriv_comp_add_const (fun u : ℝ ↦ f (xStar + u • s)) t 0]
  congr with u
  simp [add_smul, add_assoc, add_comm (u • s)]

/-- Helper for Theorem 1.4.20: differentiating the directional gradient along a line recovers the
Hessian quadratic form in that direction. -/
private lemma directional_gradient_deriv_eq_hessian_quadratic
    {f : E → ℝ} {xStar : E} (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (s : E) :
    HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f (xStar + t • s)) s)
      (inner ℝ ((fderiv ℝ (∇ f) xStar) s) s) 0 := by
  have hLine : HasDerivAt (fun t : ℝ ↦ ∇ f (xStar + t • s))
      ((fderiv ℝ (∇ f) xStar) s) 0 := by
    -- Differentiate the gradient field along the affine line.
    simpa using (hgradDiff.hasFDerivAt.hasLineDerivAt s)
  have hs : HasDerivAt (fun _ : ℝ ↦ s) 0 0 := hasDerivAt_const 0 s
  -- Pair the differentiated gradient with the fixed direction `s`.
  simpa using hLine.inner ℝ hs

/-- Helper for Theorem 1.4.20: at points where `f` is differentiable, the derivative of the line
restriction agrees with the directional pairing of the gradient. -/
private lemma line_restriction_deriv_eq_directional_gradient
    {f : E → ℝ} {xStar s : E} {t : ℝ}
    (hdiff : DifferentiableAt ℝ f (xStar + t • s)) :
    deriv (fun u : ℝ ↦ f (xStar + u • s)) t = inner ℝ (∇ f (xStar + t • s)) s := by
  -- Rewrite the line derivative at time `t` using differentiability of `f` at the translated
  -- base point.
  rw [line_restriction_deriv_eq_lineDeriv t]
  rw [hdiff.lineDeriv_eq_fderiv]
  symm
  simpa using (inner_gradient_left hdiff)

/-- Helper for Theorem 1.4.20: if a scalar function is constant on a neighborhood of the origin,
then every interior derivative in that neighborhood vanishes. -/
private lemma deriv_zero_of_locally_constant_near_zero
    {φ : ℝ → ℝ} {ε t : ℝ} (ht : |t| < ε)
    (hconst : ∀ u, |u| < ε → φ u = φ 0) : HasDerivAt φ 0 t := by
  have hδ : 0 < ε - |t| := sub_pos.mpr ht
  have heq : φ =ᶠ[nhds t] fun _ ↦ φ 0 := by
    -- Shrink the original neighborhood of constancy so it becomes a neighborhood of `t`.
    refine Metric.mem_nhds_iff.mpr ?_
    refine ⟨ε - |t|, hδ, ?_⟩
    intro u hu
    have hu' : |u| < ε := by
      have hut' : |u - t| < ε - |t| := by
        simpa [Real.dist_eq] using hu
      have habs : |u| ≤ |u - t| + |t| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (abs_sub_le u t 0)
      linarith
    exact hconst u hu'
  -- Replace `φ` by the locally equal constant function.
  exact ((heq.hasDerivAt_iff).2 (hasDerivAt_const t (φ 0)))

/-- Helper for Theorem 1.4.20: every directional Hessian quadratic form is nonnegative at a local
minimizer. -/
private lemma directional_quadratic_nonneg_of_isLocalMin
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (hmin : IsLocalMin f xStar) (s : E) :
    0 ≤ inner ℝ ((fderiv ℝ (∇ f) xStar) s) s := by
  let φ : ℝ → ℝ := fun t ↦ f (xStar + t • s)
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (xStar + t • s)) s
  have hφmin : IsLocalMin φ 0 := by
    -- Restrict the multivariate local minimum to the affine line through `xStar` in direction `s`.
    simpa [φ] using line_restriction_isLocalMin hmin s
  have hgrad0 : ∇ f xStar = 0 :=
    isLocalMin_gradient_eq_zero hmin
  have hψderiv : HasDerivAt ψ (inner ℝ ((fderiv ℝ (∇ f) xStar) s) s) 0 := by
    -- The derivative of the directional gradient at the origin is the Hessian quadratic form.
    simpa [ψ] using directional_gradient_deriv_eq_hessian_quadratic hgradDiff s
  have hψ0 : ψ 0 = 0 := by
    simp [ψ, hgrad0]
  by_contra hneg
  have hψright : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ψ t < 0 := by
    have hsign : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        SignType.sign (ψ t) = SignType.sign (0 - t) :=
      (eventually_nhdsWithin_sign_eq_of_deriv_neg
        (by simpa [hψderiv.deriv] using hneg) hψ0).filter_mono inf_le_left
    -- A negative derivative at `0` forces the directional gradient to be negative on the right.
    filter_upwards [hsign, self_mem_nhdsWithin] with t ht hpos
    have hsignneg : SignType.sign (ψ t) = -1 := by
      calc
        SignType.sign (ψ t) = SignType.sign (0 - t) := ht
        _ = -1 := by
          apply sign_eq_neg_one_iff.mpr
          have htpos : 0 < t := hpos
          linarith
    exact sign_eq_neg_one_iff.mp hsignneg
  have hψleft : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), 0 < ψ t := by
    have hsign : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0),
        SignType.sign (ψ t) = SignType.sign (0 - t) :=
      (eventually_nhdsWithin_sign_eq_of_deriv_neg
        (by simpa [hψderiv.deriv] using hneg) hψ0).filter_mono inf_le_left
    -- The same derivative information makes the directional gradient positive on the left.
    filter_upwards [hsign, self_mem_nhdsWithin] with t ht hneg_t
    have hsignpos : SignType.sign (ψ t) = 1 := by
      calc
        SignType.sign (ψ t) = SignType.sign (0 - t) := ht
        _ = 1 := by
          apply sign_eq_one_iff.mpr
          have htneg : t < 0 := hneg_t
          linarith
    exact sign_eq_one_iff.mp hsignpos
  have hφcont : ContinuousAt φ 0 := by
    let g : ℝ → E := fun t ↦ xStar + t • s
    have hline : ContinuousAt g 0 := by
      simpa [g] using
        ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
          ContinuousAt (fun t : ℝ ↦ xStar + t • s) 0)
    have hcont_f : ContinuousAt f (g 0) := by
      dsimp [g]
      simpa using hf.continuousAt
    -- Continuity of `f` at `xStar` gives continuity of the restricted scalar function at `0`.
    simpa [φ, g] using hcont_f.comp hline
  have hfdiff_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      DifferentiableAt ℝ f (xStar + t • s) := by
    -- On the right, a nonzero directional gradient forces `∇ f` to be nonzero, hence `f` is
    -- genuinely differentiable there because the totalized gradient vanishes at non-differentiable
    -- points.
    filter_upwards [hψright] with t ht
    have hgrad_ne : ∇ f (xStar + t • s) ≠ 0 := by
      intro hzero
      have : ψ t = 0 := by
        simp [ψ, hzero]
      exact ht.ne this
    by_contra hdiff
    exact hgrad_ne (by simpa using gradient_eq_zero_of_not_differentiableAt hdiff)
  have hfdiff_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0),
      DifferentiableAt ℝ f (xStar + t • s) := by
    -- The same argument works on the left.
    filter_upwards [hψleft] with t ht
    have hgrad_ne : ∇ f (xStar + t • s) ≠ 0 := by
      intro hzero
      have : ψ t = 0 := by
        simp [ψ, hzero]
      exact ht.ne' this
    by_contra hdiff
    exact hgrad_ne (by simpa using gradient_eq_zero_of_not_differentiableAt hdiff)
  have hφdiff_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), DifferentiableAt ℝ φ t := by
    filter_upwards [hfdiff_right] with t hdiff_f
    have hline : DifferentiableAt ℝ (fun u : ℝ ↦ xStar + u • s) t :=
      (differentiableAt_id.smul_const s).const_add xStar
    -- Compose the affine line with the differentiability of `f`.
    simpa [φ] using hdiff_f.comp t hline
  have hφdiff_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), DifferentiableAt ℝ φ t := by
    filter_upwards [hfdiff_left] with t hdiff_f
    have hline : DifferentiableAt ℝ (fun u : ℝ ↦ xStar + u • s) t :=
      (differentiableAt_id.smul_const s).const_add xStar
    -- Compose the affine line with the differentiability of `f`.
    simpa [φ] using hdiff_f.comp t hline
  have hderiv_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), deriv φ t < 0 := by
    -- On the right, the derivative of the restricted function is exactly the negative directional
    -- gradient.
    filter_upwards [hψright, hfdiff_right] with t ht hdiff
    rw [line_restriction_deriv_eq_directional_gradient hdiff]
    simpa [φ, ψ] using ht
  have hderiv_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), 0 < deriv φ t := by
    -- On the left, the derivative of the restricted function is positive.
    filter_upwards [hψleft, hfdiff_left] with t ht hdiff
    rw [line_restriction_deriv_eq_directional_gradient hdiff]
    simpa [φ, ψ] using ht
  have hφmax : IsLocalMax φ 0 := by
    -- These one-sided derivative signs force a local maximum of the restricted function at `0`.
    refine isLocalMax_of_deriv' hφcont hφdiff_left hφdiff_right ?_ ?_
    · exact hderiv_left.mono fun _ ht ↦ le_of_lt ht
    · exact hderiv_right.mono fun _ ht ↦ le_of_lt ht
  have hconst_event : ∀ᶠ t in nhds (0 : ℝ), φ t = φ 0 := by
    -- Having both a local minimum and a local maximum makes the line restriction locally constant.
    filter_upwards [hφmin, hφmax] with t htmin htmax
    exact le_antisymm htmax htmin
  obtain ⟨ε, hε, hconst⟩ : ∃ ε > 0, ∀ t, |t| < ε → φ t = φ 0 := by
    rcases Metric.mem_nhds_iff.mp hconst_event with ⟨ε, hε, hεmem⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    exact hεmem (by simpa [Metric.ball, Real.dist_eq] using ht)
  obtain ⟨δ, hδ, hδprop⟩ : ∃ δ > 0, ∀ t, t ∈ Set.Ioo (0 : ℝ) δ → deriv φ t < 0 := by
    rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hderiv_right with ⟨δ, hδ, hδprop⟩
    exact ⟨δ, hδ, fun t ht ↦ hδprop ht⟩
  let t0 : ℝ := min ε δ / 2
  have ht0_pos : 0 < t0 := by
    positivity
  have ht0_lt_ε : |t0| < ε := by
    have ht0_lt : t0 < ε := by
      have hmin_pos : 0 < min ε δ := lt_min hε hδ
      have : min ε δ / 2 < min ε δ := by
        nlinarith
      exact this.trans_le (min_le_left _ _)
    simpa [t0, abs_of_pos ht0_pos] using ht0_lt
  have ht0_mem : t0 ∈ Set.Ioo (0 : ℝ) δ := by
    refine ⟨ht0_pos, ?_⟩
    have hmin_pos : 0 < min ε δ := lt_min hε hδ
    have : min ε δ / 2 < min ε δ := by
      nlinarith
    exact this.trans_le (min_le_right _ _)
  have hderiv_zero : deriv φ t0 = 0 := by
    -- A function constant near `0` is constant near `t0`, so its derivative at `t0` vanishes.
    exact (deriv_zero_of_locally_constant_near_zero ht0_lt_ε hconst).deriv
  have hderiv_neg : deriv φ t0 < 0 := hδprop t0 ht0_mem
  exact hderiv_neg.ne' hderiv_zero.symm

/-- Theorem 1.4.20: if a real-valued function on a real complete inner product space is
differentiable at `xStar` and the gradient map `∇ f` is differentiable at `xStar`, then every
local minimizer `xStar` has vanishing gradient and nonnegative Hessian quadratic form in every
direction at `xStar`. -/
-- Proof sketch: combine Fermat's theorem for the gradient with the line-restriction argument
-- proving nonnegativity of every directional Hessian quadratic form.
theorem isLocalMin_gradient_eq_zero_and_hessian_quadratic_nonneg
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 ∧ ∀ s : E, 0 ≤ inner ℝ (hessian f xStar s) s := by
  refine ⟨isLocalMin_gradient_eq_zero hmin, ?_⟩
  intro s
  simpa [hessian] using directional_quadratic_nonneg_of_isLocalMin hf hgradDiff hmin s

/-- Companion bridge: under the chapter's canonical `C²` owner assumption, the source-facing
quadratic-form condition from Theorem 1.4.20 upgrades to positivity of the Hessian operator. -/
theorem isLocalMin_gradient_eq_zero_and_hessian_isPositive
    {f : E → ℝ} {xStar : E} (hf : ContDiffAt ℝ 2 f xStar) (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 ∧ ContinuousLinearMap.IsPositive (hessian f xStar) := by
  have hdiff : DifferentiableAt ℝ f xStar :=
    hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hgradDiff : DifferentiableAt ℝ (∇ f) xStar := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) xStar :=
      hfderiv.differentiableAt one_ne_zero
    simpa [gradient] using
      (((InnerProductSpace.toDual ℝ E).symm).comp_differentiableAt_iff).2 hfdiff
  have hsymm : (hessian f xStar).IsSymmetric :=
    fderiv_gradient_isSymmetric_of_contDiffAt hf
  rcases isLocalMin_gradient_eq_zero_and_hessian_quadratic_nonneg hdiff hgradDiff hmin with
    ⟨hgrad, hquad⟩
  exact ⟨hgrad, (ContinuousLinearMap.isPositive_iff _).2 ⟨hsymm, hquad⟩⟩

end
