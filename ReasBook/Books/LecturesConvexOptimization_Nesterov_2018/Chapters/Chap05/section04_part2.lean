import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_4_3_2 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 5.4.3.2 lies in the Chapter 5 logarithmic-homogeneity / self-concordant-barrier domain.

Sampled owner declarations in this domain:
* `IsLogarithmicallyHomogeneousOnWith` in `Definition_5_4_3_3`, the source-facing owner for the
  logarithmic scaling law on a cone interior;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for `ν`-self-
  concordant barriers on a domain;
* mathlib `ConvexCone.Salient`, the canonical owner for the source's "no straight lines" / no
  nontrivial lineality condition on a cone;
* `HasPositiveDefiniteHessianOn` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  Chapter 5 owner and bridge for pointwise Hessian nondegeneracy on a domain;
* `hessian` in `Chap01/Definition_1_4_16` and `ContinuousLinearMap.inverse`, the canonical
  operator-level Hessian and inverse-Hessian surface.

Best owner abstraction:
* source-facing: the six logarithmic-homogeneity identities and their barrier consequence under
  the full logarithmic-homogeneity / barrier / salience hypotheses;
* core/canonical: `HasPositiveDefiniteHessianOn (interior (K : Set E)) F` together with the
  operator owner `hessian F x`, and the cone owner `K.Salient`;
* bridge/view: the textbook "no straight lines" phrasing
  `∀ u, u ∈ K → -u ∈ K → u = 0`, the determinant-nonzero consequence, and the inverse-Hessian
  pairing formula.

Primitive data:
* a cone owner `K : ConvexCone ℝ E`;
* logarithmic homogeneity of `F` on `K`;
* a self-concordant barrier hypothesis on `interior K`;
* the salience condition on `K`.

Derived API:
* pointwise positive-definite Hessian on `interior K` under the full barrier hypotheses;
* Hessian nondegeneracy at each interior point;
* the canonical inverse-Hessian expression `((hessian F x).inverse ...)`.

This refinement keeps the textbook source-facing statements, deletes the unused local salience
repackaging, and keeps the supporting Hessian-nondegeneracy bridge on the chapter owner
`HasPositiveDefiniteHessianOn`. The bridge now carries the closed logarithmic-homogeneity
hypothesis actually needed to match the cone geometry used later in the file, while the main
gradient/Hessian identities continue to use the canonical cone owner `K.Salient` together with the
canonical `hessian` / inverse surface instead of raw `fderiv` terms. -/

section BarrierCone

variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

variable [CompleteSpace E]

-- Proof sketch: use the closed logarithmically-homogeneous cone data carried by `hFlog`
-- together with salience to rule out the flat directions that obstruct strict Hessian
-- positivity, and read the result on `interior K` through the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
positive-definite Hessian on that interior domain. -/
theorem hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient) :
    HasPositiveDefiniteHessianOn (interior (K : Set E)) F := by
  sorry

end BarrierCone

section BarrierCone

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance barrierConeFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: apply the owner bridge
-- `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` to the positive-definite Hessian
-- owner supplied by `hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
nondegenerate Hessian at every interior point. -/
theorem hessian_det_ne_zero_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    (hessian F x).det ≠ 0 := by
  letI : HasPositiveDefiniteHessianOn (interior (K : Set E)) F :=
    hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient hFlog hbarrier hK
  exact HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx

end BarrierCone

section LogarithmicHomogeneity

variable [CompleteSpace E]
variable {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ}

-- Proof sketch: differentiate the logarithmic scaling identity
-- `F (τ • x) = F x - ν log τ` with respect to `x`; the chain rule contributes the factor `τ` on
-- the left, and rearranging gives the `τ⁻¹` scaling of the gradient.
/-- Lemma 5.4.3.2 (1): logarithmic homogeneity rescales the gradient by `τ⁻¹`. -/
theorem gradient_pos_smul_eq_inv_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    ∇ F (τ • x) = (1 / τ) • ∇ F x := sorry

-- Proof sketch: differentiate the gradient scaling identity once more with respect to `x`; the
-- chain rule introduces a second factor of `τ`, yielding the `τ⁻²` scaling of the Hessian map.
/-- Lemma 5.4.3.2 (2): logarithmic homogeneity rescales the Hessian by `τ⁻²`. -/
theorem hessian_pos_smul_eq_inv_sq_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    hessian F (τ • x) = (1 / τ ^ (2 : ℕ)) • hessian F x := sorry

-- Proof sketch: differentiate the logarithmic scaling identity with respect to the scalar `τ`
-- along the ray `τ ↦ τ • x`, and then evaluate at `τ = 1`.
/-- Lemma 5.4.3.2 (3): the gradient pairing with the base point equals `-ν`. -/
theorem inner_gradient_self_eq_neg_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) x = -ν := sorry

-- Proof sketch: differentiate the scalar identity `⟪∇ F(x), x⟫ = -ν` in an arbitrary direction
-- `h`; symmetry of the Hessian then identifies the resulting linear functional with
-- `h ↦ ⟪h, ∇²F(x) x + ∇F(x)⟫`.
/-- Lemma 5.4.3.2 (4): applying the Hessian at `x` to `x` gives `-∇ F(x)`. -/
theorem hessian_apply_self_eq_neg_gradient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    hessian F x x = -∇ F x := sorry

-- Proof sketch: pair the identity `∇²F(x) x = -∇F(x)` with `x`, then substitute
-- `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (5): the Hessian quadratic form of `x` at `x` equals `ν`. -/
theorem inner_hessian_apply_self_self_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (hessian F x x) x = ν := sorry

end LogarithmicHomogeneity

section InverseHessian

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance inverseHessianFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: the logarithmically homogeneous salient-cone barrier hypothesis gives the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`, so the Hessian at `x` has its canonical inverse
-- `(hessian F x).inverse`. Solve `∇²F(x) x = -∇F(x)` for `x` using that inverse, then substitute
-- the result into `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (6): the inverse-Hessian pairing of the gradient with itself equals `ν`. -/
theorem inner_gradient_inverseHessian_gradient_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) = (ν : ℝ) := sorry

end InverseHessian

end

/-! ### Lemma_5_4_3_3 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 5.4.3.3 lies in the Chapter 5 cone-barrier domain.

Sampled owner-style declarations in this domain:
* mathlib `ConvexCone ℝ (E × ℝ)`, the canonical owner for cone domains in the intrinsic ambient
  product space;
* project `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs,
  which realizes the second-order cone as the epigraph of `x ↦ ‖x‖`;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, the canonical `L²` product owner for
  the ambient inner-product geometry of the barrier statement;
* project `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, which already
  states a Chapter 5 logarithmic barrier theorem on that canonical `L²` owner over complete real
  inner-product spaces;
* project `IsSelfConcordantBarrierOnWith`, the canonical barrier owner targeted by the theorem
  below.

Source/core/bridge triage:
* source-facing: the explicit second-order cone barrier formula;
* core/canonical: the second-order cone itself, best owned as `ConvexCone ℝ (E × ℝ)`;
* bridge/view: the membership and evaluation lemmas exposing the textbook formulas directly.

The refinement here is therefore to keep the explicit textbook cone and barrier on raw pairs, use
the canonical `ConvexCone` owner for the cone data, realize its carrier through the chapter
epigraph owner instead of a duplicate set-builder, and state the barrier theorem on the canonical
`L²` product owner `WithLp 2 (E × ℝ)` via the bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook model `ℝⁿ × ℝ`. -/

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
theorem secondOrderCone_smul_mem {τ : ℝ} (hτ : 0 < τ) {p : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) :
    ‖(τ • p).1‖ ≤ (τ • p).2 := by
  calc
    ‖(τ • p).1‖ = τ * ‖p.1‖ := by
      simp [norm_smul, Real.norm_of_nonneg hτ.le]
    _ ≤ τ * p.2 := mul_le_mul_of_nonneg_left hp hτ.le
    _ = (τ • p).2 := by rfl

omit [NormedSpace ℝ E] in
/-- The second-order cone is closed under vector addition. -/
theorem secondOrderCone_add_mem {p q : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) (hq : ‖q.1‖ ≤ q.2) :
    ‖(p + q).1‖ ≤ (p + q).2 := by
  calc
    ‖(p + q).1‖ ≤ ‖p.1‖ + ‖q.1‖ := norm_add_le _ _
    _ ≤ p.2 + q.2 := add_le_add hp hq
    _ = (p + q).2 := rfl

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
def secondOrderCone (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ConvexCone ℝ (E × ℝ) where
  carrier := constrainedEpigraph (Set.univ : Set E) fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)
  smul_mem' := fun {_c} hc {_x} hx ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_smul_mem hc (by simpa [constrainedEpigraph] using hx)
  add_mem' := fun {_x} hx {_y} hy ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_add_mem
        (by simpa [constrainedEpigraph] using hx)
        (by simpa [constrainedEpigraph] using hy)

namespace SecondOrderCone

/- Source-facing notation for the second-order cone owner as a subset of `E × ℝ`. -/
scoped notation "K₂[" E "]" => (secondOrderCone E : Set (E × ℝ))

end SecondOrderCone

open scoped SecondOrderCone

-- Proof sketch: unfold `secondOrderCone`; membership is exactly the displayed norm inequality in
-- the defining set-builder.
/-- Membership in `secondOrderCone` means that the scalar coordinate dominates the Euclidean norm
of the vector coordinate. -/
@[simp]
theorem mem_secondOrderCone_iff (p : E × ℝ) :
    p ∈ K₂[E] ↔ ‖p.1‖ ≤ p.2 := by
  change p ∈ constrainedEpigraph (Set.univ : Set E) (fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)) ↔
      ‖p.1‖ ≤ p.2
  simp [constrainedEpigraph]

-- Proof sketch: `secondOrderCone` is the closed sublevel set of the continuous function
-- `p ↦ ‖p.1‖ - p.2`, so its interior is obtained by replacing the weak inequality by the strict
-- inequality `‖p.1‖ < p.2`.
/-- A point lies in the interior of `secondOrderCone` exactly when its scalar coordinate is
strictly larger than the Euclidean norm of its vector coordinate. -/
theorem mem_interior_secondOrderCone_iff (p : E × ℝ) :
    p ∈ interior K₂[E] ↔ ‖p.1‖ < p.2 := sorry

/-- The logarithmic barrier `(x, t) ↦ -log (t^2 - ‖x‖^2)` on the second-order cone. -/
def secondOrderConeBarrier : E × ℝ → ℝ :=
  fun p ↦ -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ))

-- Proof sketch: unfold `secondOrderConeBarrier`.
omit [NormedSpace ℝ E] in
/-- Evaluating `secondOrderConeBarrier` reproduces the textbook formula
`(x, t) ↦ -log (t^2 - ‖x‖^2)`. -/
@[simp]
theorem secondOrderConeBarrier_apply (p : E × ℝ) :
    secondOrderConeBarrier p =
      -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) := rfl

variable [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: restrict the function to an arbitrary affine line `α ↦ (x + α • h, t + α * τ)`
-- inside `E × ℝ` and compute the derivatives of
-- `-log ((t + α * τ)^2 - ‖x + α • h‖^2)` as in the textbook. The inequality
-- `(t * τ - ⟪x, h⟫)^2 ≥ (t^2 - ‖x‖^2) * (τ^2 - ‖h‖^2)` gives the barrier-parameter bound with
-- `ν = 2`, and the same one-dimensional derivative computation yields the standard
-- self-concordance part on the interior domain `‖x‖ < t`.
/-- Lemma 5.4.3.3: the function `(x, t) ↦ -log (t^2 - ‖x‖^2)` is a `2`-self-concordant barrier
for the second-order cone `K₂ = {(x, t) ∈ E × ℝ | ‖x‖ ≤ t}`, viewed on the canonical `L²`
product owner `WithLp 2 (E × ℝ)` through the canonical raw-pair bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ × ℝ` statement. -/
theorem secondOrderConeBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior K₂[E])
      2
      (secondOrderConeBarrier ∘ ofZ) := sorry

/-! ### Lemma_5_4_3_4 (from Chap05) -/
open Set Topology
open scoped BigOperators
open scoped SecondOrderCone

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

/- Lemma 5.4.3.4 lies in the Chapter 5 second-order-cone / self-concordant-barrier domain.

Sampled owner declarations in this domain:
* `secondOrderCone` and `mem_interior_secondOrderCone_iff` from `Lemma_5_4_3_3`, the chapter owner
  for the second-order cone as a `ConvexCone ℝ (E × ℝ)`;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, the canonical `L²` ambient owner for
  barriers on the second-order cone;
* mathlib `ConvexCone.convex`, which derives convexity from that cone owner instead of storing a
  parallel set-level wrapper;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for self-concordant
  barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical lower-bound owner theorem specialized here.

Source/core/bridge triage:
* source-facing: the lower bound `ν ≥ 2` for barriers on the second-order cone;
* core/canonical: the raw-pair cone owner `secondOrderCone : ConvexCone ℝ (E × ℝ)` together
  with the barrier owner
  `IsSelfConcordantBarrierOnWith ((fun z : Z ↦ z.ofLp) ⁻¹' interior K₂[E]) ν F`;
* bridge/view: the textbook inequalities `‖x‖ ≤ t` and `‖x‖ < t`, already exposed by
  `mem_secondOrderCone_iff` and `mem_interior_secondOrderCone_iff`, together with the source
  notation `K₂[E]` and the ambient bridge `z ↦ z.ofLp`.

Primitive data:
* a nontrivial real Hilbert-space ambient `E`, used only to choose a norm-one vector;
* the self-concordant barrier owner on the pulled-back interior
  `IsSelfConcordantBarrierOnWith ((fun z : Z ↦ z.ofLp) ⁻¹' interior K₂[E]) ν F`.

Derived API:
* the source-facing lower bound `(2 : ℝ) ≤ (ν : ℝ)`.

This file therefore reuses the existing second-order-cone owner from `Lemma_5_4_3_3` instead of
keeping a parallel coordinate model. The source-facing cone notation remains on raw pairs, while
the barrier owner lives on the canonical `L²` product owner and is accessed through `z ↦ z.ofLp`.
The earlier `ℝⁿ` proof ingredient is refined to the intrinsic owner-level fact that a nontrivial
real normed space contains a norm-one vector. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to
-- `secondOrderCone : ConvexCone ℝ (E × ℝ)` with base point `(0, 1)`, recession directions
-- `(h, 1)` and `(-h, 1)` for a unit vector `h : E`, and coefficients
-- `α₁ = α₂ = β₁ = β₂ = 1 / 2`. Transport the cone to the canonical `L²` product owner
-- `Z = WithLp 2 (E × ℝ)` through `z ↦ z.ofLp`; the backward steps land on the boundary, the
-- combined step reaches `(0, 0) ∈ K₂[E]`, and the general lower-bound theorem yields `1 + 1 ≤ ν`.
/-- Lemma 5.4.3.4: every `ν`-self-concordant barrier for the interior of the second-order cone
`K₂ = {(x, t) ∈ E × ℝ | ‖x‖ ≤ t}` in a nontrivial real Hilbert space `E`, viewed on the canonical
`L²` product ambient space through `z ↦ z.ofLp`, has barrier parameter at least `2`. Specializing
to `E = EuclideanSpace ℝ (Fin n)` with `0 < n` recovers the textbook `ℝⁿ` statement. -/
theorem secondOrderCone_barrierParameter_ge_two
    {ν : NNReal} {F : Z → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior K₂[E]) ν F) :
    (2 : ℝ) ≤ (ν : ℝ) := by
  let Q : Set Z := ofZ ⁻¹' K₂[E]
  have hQ_interior :
      interior Q = ofZ ⁻¹' interior K₂[E] := by
    simpa [Q] using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toHomeomorph.preimage_interior K₂[E]).symm
  have hFQ : IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    simpa [hQ_interior] using hF
  obtain ⟨h, hh_norm⟩ : ∃ h : E, ‖h‖ = 1 := by
    simpa using (exists_norm_eq E (show 0 ≤ (1 : ℝ) by positivity))
  let xBar : Z := WithLp.toLp 2 ((0 : E), (1 : ℝ))
  let p : Fin 2 → Z
    | 0 => WithLp.toLp 2 (h, 1)
    | 1 => WithLp.toLp 2 (-h, 1)
  let β : Fin 2 → ℝ := fun _ ↦ 1 / 2
  let α : Fin 2 → ℝ := fun _ ↦ 1 / 2
  have hQ_convex : Convex ℝ Q := by
    simpa [Q] using
      (secondOrderCone E).convex.linear_preimage
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toLinearMap
  have hxBar : xBar ∈ interior Q := by
    rw [hQ_interior]
    change xBar.ofLp ∈ interior K₂[E]
    rw [mem_interior_secondOrderCone_iff]
    simp [xBar]
  have hp :
      ∀ j : Fin 2,
        ∀ ⦃x : Z⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p j ∈ Q := by
    intro j x hx t ht
    have hxK : x.ofLp ∈ K₂[E] := by
      simpa [Q] using hx
    change (x + t • p j).ofLp ∈ K₂[E]
    rw [mem_secondOrderCone_iff] at hxK ⊢
    fin_cases j
    · calc
        ‖(x + t • p 0).ofLp.1‖ = ‖x.ofLp.1 + t • h‖ := by simp [p]
        _ ≤ ‖x.ofLp.1‖ + ‖t • h‖ := norm_add_le _ _
        _ = ‖x.ofLp.1‖ + t := by
          rw [norm_smul, hh_norm, Real.norm_of_nonneg ht, mul_one]
        _ ≤ x.ofLp.2 + t := by linarith [hxK]
        _ = (x + t • p 0).ofLp.2 := by simp [p]
    · calc
        ‖(x + t • p 1).ofLp.1‖ = ‖x.ofLp.1 + t • -h‖ := by simp [p]
        _ ≤ ‖x.ofLp.1‖ + ‖t • -h‖ := norm_add_le _ _
        _ = ‖x.ofLp.1‖ + t := by
          rw [norm_smul, norm_neg, hh_norm, Real.norm_of_nonneg ht, mul_one]
        _ ≤ x.ofLp.2 + t := by linarith [hxK]
        _ = (x + t • p 1).ofLp.2 := by simp [p]
  have hβ_pos : ∀ j : Fin 2, 0 < β j := by
    intro j
    norm_num [β]
  have hβ_exit : ∀ j : Fin 2, xBar - β j • p j ∉ interior Q := by
    intro j
    rw [hQ_interior]
    change (xBar - β j • p j).ofLp ∉ interior K₂[E]
    rw [mem_interior_secondOrderCone_iff]
    fin_cases j <;>
      simp [xBar, β, p, hh_norm, norm_smul, not_lt] <;>
      norm_num
  have hα_nonneg : ∀ j : Fin 2, 0 ≤ α j := by
    intro j
    norm_num [α]
  have hy : xBar - ∑ j, α j • p j ∈ Q := by
    have hyK : (xBar - ∑ j, α j • p j).ofLp ∈ K₂[E] := by
      rw [mem_secondOrderCone_iff]
      simp [xBar, α, p, Fin.sum_univ_two]
      norm_num
    simpa [Q] using hyK
  have hbound :=
    hFQ.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex hxBar p hp β α hβ_pos hβ_exit hα_nonneg hy
  simpa [α, β, Fin.sum_univ_two] using hbound

end

/-! ### Proposition_5_4_3_1 (from Chap05) -/
open Set Topology Filter
open scoped EuclideanOrthant Gradient

noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Proposition 5.4.3.1 lies in the Chapter 5 self-concordant barrier / path-following
specialization domain.

Sampled owner declarations in this domain:
* `linearOptimizationProblemWithNonnegativityConstraints` from `Definition_5_4_3_1`, the chapter
  owner for the linear program with equality constraints and nonnegative-orthant basic set;
* `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet` from
  `Definition_5_4_3_1`, the owner-level strict feasible slice for the same linear program;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the ambient logarithmic-barrier
  bridge on `ℝⁿ`;
* `pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon` from
  `Theorem_5_3_11`, the canonical stopping theorem.

Best owner abstraction:
* source-facing: the Chapter 5 linear-program owner
  `linearOptimizationProblemWithNonnegativityConstraints A b c` together with its strict feasible
  slice `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`;
* core/canonical: the generic stopping theorem for `IsSelfConcordantBarrierOnWith`;
* bridge/view: the ambient logarithmic barrier `standardLogarithmicBarrierAmbient n`.

Primitive data:
* the linear-program owner `linearOptimizationProblemWithNonnegativityConstraints A b c`;
* the strict feasible-set owner
  `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`.

Derived API:
* the path-following complexity statement, which is only a specialization of
  `pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon`.

Source/core/bridge triage:
* source-facing: the strict feasible-set owner
  `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`;
* core/canonical: the stopping theorem from `Theorem_5_3_11`;
* bridge/view: the ambient barrier `standardLogarithmicBarrierAmbient n`.

The previous version specialized the stopping theorem through a raw objective
`x ↦ ⟪c, x⟫` and a raw feasible-set presentation. This refinement reuses the Chapter 5 linear
program owner and its strict feasible-set owner from `Definition_5_4_3_1`, so the proposition is
organized around the LP owner itself rather than around parallel coordinate-level surface data.
-/

section
local notation "F" => standardLogarithmicBarrierAmbient n

/-
Proposition 5.4.3.1 is the direct Chapter 5 LP specialization of the generic stopping theorem,
with LP owner `linearOptimizationProblemWithNonnegativityConstraints A b c`, strict feasible-set
owner `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`, and barrier
`standardLogarithmicBarrierAmbient n`.
-/
theorem
    linearOptimizationProblemWithNonnegativityConstraints_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ)
    [IsSelfConcordantBarrierOnWith
      (linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
      n
      F]
    {β γ ε : ℝ}
    (xCenter : linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
    (hcenter :
      IsMinOn F
        (linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
        (xCenter : Eₙ))
    (hxCenterH : (fderiv ℝ (∇ F) (xCenter : Eₙ)).det ≠ 0)
    (xOpt :
      (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet)
    (hopt :
      ∀ y :
        (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet,
        linearOptimizationProblemWithNonnegativityConstraints A b c (xOpt : Eₙ) ≤
          linearOptimizationProblemWithNonnegativityConstraints A b c (y : Eₙ))
    (t : ℕ → ℝ) (x : ℕ → Eₙ)
    (mem_dom :
      ∀ k : ℕ, x k ∈ linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (hβ_half : β < 1 / 2)
    (hγ : 0 < γ)
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex →
        t k < barrierPathFollowingStoppingThreshold n β ε)
    (hstop : barrierPathFollowingStoppingThreshold n β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xCenter : Eₙ)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xCenter.2)
                  hxCenterH
                  ((InnerProductSpace.toDual ℝ Eₙ) c)) *
            (1 + γ / (β + Real.sqrt (n : ℝ))) ^ (k - 1) ≤
          t k)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_dom stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ Eₙ)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    stopIndex ≤
        ⌈barrierPathFollowingTerminationBound n β γ ε
          (HessianDualLocalNorm.ofDetNeZero F (xCenter : Eₙ)
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xCenter.2) hxCenterH
            ((InnerProductSpace.toDual ℝ Eₙ) c))⌉₊ ∧
      linearOptimizationProblemWithNonnegativityConstraints A b c (x stopIndex) -
          linearOptimizationProblemWithNonnegativityConstraints A b c (xOpt : Eₙ) ≤
        ε := by
  let problem := linearOptimizationProblemWithNonnegativityConstraints A b c
  let strictDom := linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b
  have hxCenter_eq : A.mulVec (xCenter : Eₙ) = b :=
    (mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff A b).1 xCenter.2
      |>.1
  have hxCenter_pos : ∀ i : Fin n, 0 < (xCenter : Eₙ) i := by
    simpa using
      (mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff A b).1
        xCenter.2 |>.2
  have hstrict_subset_eq : strictDom ⊆ problem.equalityFeasibleSet := by
    intro z hz
    rw [mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff] at hz
    rw [mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff]
    refine ⟨?_, hz.1⟩
    intro i
    exact (EuclideanSpace.mem_positiveOrthant_iff.mp hz.2 i).le
  have hclosed_eq : IsClosed problem.equalityFeasibleSet := by
    have hclosed_nonnegativeOrthant : IsClosed (ℝ₊^n : Set Eₙ) := by
      let e : Eₙ ≃ₜ (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      have hnonnegativeOrthant :
          (ℝ₊^n : Set Eₙ) =
            e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) := by
        ext x
        simp [Pi.le_def, e, EuclideanSpace.nonnegativeOrthant]
      rw [hnonnegativeOrthant]
      exact (isClosed_set_pi fun _ _ ↦ isClosed_Ici).preimage e.continuous
    have hclosed_eqConstraint : IsClosed {z : Eₙ | A.toEuclideanLin z = b} := by
      exact
        isClosed_singleton.preimage
          (LinearMap.continuous_of_finiteDimensional A.toEuclideanLin)
    have heq :
        problem.equalityFeasibleSet = (ℝ₊^n : Set Eₙ) ∩ {z : Eₙ | A.toEuclideanLin z = b} := by
      ext z
      rw [PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff]
      simp [problem, linearOptimizationProblemWithNonnegativityConstraints]
    rw [heq]
    exact hclosed_nonnegativeOrthant.inter hclosed_eqConstraint
  have hclosure_subset_eq : closure strictDom ⊆ problem.equalityFeasibleSet :=
    closure_minimal hstrict_subset_eq hclosed_eq
  have heq_subset_closure : problem.equalityFeasibleSet ⊆ closure strictDom := by
    intro z hz
    let path : ℝ → Eₙ := fun s ↦ z + s • ((xCenter : Eₙ) - z)
    have hpath : Filter.Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have hcont : Continuous path := by
        dsimp [path]
        exact continuous_const.add (continuous_id.smul continuous_const)
      have hpath0 : Filter.Tendsto path (𝓝 (0 : ℝ)) (𝓝 (path 0)) := hcont.continuousAt.tendsto
      simpa [path] using
        (hpath0.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))
    have hz_nonneg_eq :
        (∀ i : Fin n, 0 ≤ z i) ∧ A.mulVec z = b := by
      simpa using
        (mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff A b c).1
          hz
    have hpath_mem :
        ∀ᶠ s in 𝓝[>] (0 : ℝ), path s ∈ strictDom := by
      have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
        Ioo_mem_nhdsGT zero_lt_one
      filter_upwards [hIoo] with s hs
      rw [mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff]
      constructor
      · have hs0 : 0 ≤ s := hs.1.le
        have hs1 : s ≤ 1 := hs.2.le
        calc
          A.mulVec (path s)
              = A.mulVec z + s • (A.mulVec ((xCenter : Eₙ) - z)) := by
                  simp [path, Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = b + s • (b - b) := by simp [hz_nonneg_eq.2, hxCenter_eq, Matrix.mulVec_sub]
          _ = b := by simp
      · rw [EuclideanSpace.mem_positiveOrthant_iff]
        intro i
        have hcoord : path s i = (1 - s) * z i + s * (xCenter : Eₙ) i := by
          calc
            path s i = z i + s * ((xCenter : Eₙ) i - z i) := by
              simp [path]
            _ = (1 - s) * z i + s * (xCenter : Eₙ) i := by ring
        rw [hcoord]
        nlinarith [hz_nonneg_eq.1 i, hxCenter_pos i, hs.1, hs.2]
    exact mem_closure_of_tendsto hpath hpath_mem
  let xOptClosure : closure strictDom := ⟨(xOpt : Eₙ), heq_subset_closure xOpt.2⟩
  have hoptClosure :
      ∀ y : closure strictDom, inner ℝ c (xOptClosure : Eₙ) ≤ inner ℝ c (y : Eₙ) := by
    intro y
    exact hopt ⟨y, hclosure_subset_eq y.2⟩
  simpa [linearOptimizationProblemWithNonnegativityConstraints_objective_apply] using
    (pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
      c xCenter hcenter hxCenterH xOptClosure hoptClosure
      t x mem_dom hessian_nondegenerate stopIndex
      hβ_half hγ hcontinue hstop hgrowth happrox_stop)

end

end

/-! ### Proposition_5_4_3_2 (from Chap05) -/
noncomputable section

open QuadraticallyConstrainedQuadraticOptimizationProblem

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.4.3.2 lies in the Chapter 5 QCQP / logarithmic-barrier / short-step
path-following domain.

Sampled owner declarations in this domain:
* `QuadraticallyConstrainedQuadraticOptimizationProblem.strictEpigraphFeasibleSet`,
  `StrictEpigraphFeasiblePoint`, `epigraphLogarithmicBarrier`, and
  `epigraphLogarithmicBarrierAmbient` from `Definition_5_4_3_5`, the QCQP owner API for the
  strict epigraph barrier;
* `BarrierPathFollowingScheme` from `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers on an ambient domain;
* the chapter `RealProdL2` pattern, used in nearby files to keep raw pair owners on the public
  surface while realizing the ambient Euclidean structure through the canonical `WithLp 2`
  `L²` model only internally.

Source/core/bridge triage:
* source-facing: the QCQP strict epigraph feasible region and its logarithmic barrier;
* core/canonical: `BarrierPathFollowingScheme` together with `IsSelfConcordantBarrierOnWith`;
* bridge/view: the local `L²` inner-product structure on the raw pair space `Eₙ × ℝ`,
  implemented through `WithLp.toLp`.

Primitive data:
* the QCQP owner `problem`.

Derived API:
* the strict-to-nonstrict epigraph-feasibility inclusion;
* the closure bridge identifying the closure of the strict QCQP epigraph domain with the
  nonstrict QCQP epigraph feasible set;
* the raw-pair self-concordant-barrier instance needed by `BarrierPathFollowingScheme`, with the
  `WithLp` realization kept internal to this file;
* the common short-step existence package theorem and its source-facing projections.

The refined file therefore removes the redundant public `WithLp`-surface wrappers from
Proposition 5.4.3.2. The QCQP owner barrier remains primary, and the `WithLp` model is used only
internally to equip the raw epigraph pair space with its `L²` ambient structure. -/

section

variable (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)

noncomputable local instance : SeminormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedSpace ℝ (Eₙ × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : InnerProductSpace ℝ (Eₙ × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 Eₙ ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace (Eₙ × ℝ) := inferInstance

local notation "𝒟" =>
  problem.strictEpigraphFeasibleSet
local notation "F" =>
  problem.epigraphLogarithmicBarrierAmbient
local notation "P" =>
  problem.epigraphOptimizationProblem
local notation "ℱ" =>
  problem.epigraphFeasibleSet
local notation "cτ" =>
  ((0 : Eₙ), (1 : ℝ))

-- Proof sketch: a strict inequality implies the corresponding weak inequality, so the strict
-- epigraph domain is contained in the nonstrict epigraph feasible set of the same QCQP.
/-- Every point of the strict QCQP epigraph domain is feasible for the nonstrict epigraph
reformulation of the same QCQP. -/
theorem qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet :
    𝒟 ⊆ problem.epigraphFeasibleSet := sorry

-- Proof sketch: if `(x, τ)` is feasible for the closed QCQP epigraph problem and `(x̄, τ̄)` is a
-- strict feasible point, then every convex combination `(1 - s) • (x, τ) + s • (x̄, τ̄)` with
-- `0 < s < 1` satisfies the strict inequalities because the QCQP objective and constraints are
-- convex. Sending `s → 0⁺` shows that every feasible epigraph point is a limit of strict ones.
/-- If the strict QCQP epigraph domain is nonempty, every feasible epigraph point is a limit of
strictly feasible epigraph points. -/
theorem epigraphFeasibleSet_subset_closure_strictEpigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    ℱ ⊆ closure 𝒟 := sorry

-- Proof sketch: the strict QCQP epigraph domain is contained in the nonstrict feasible set by
-- `qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet`, while the converse closure inclusion is
-- the theorem above.
/-- If the strict QCQP epigraph domain is nonempty, its closure is exactly the nonstrict QCQP
epigraph feasible set. -/
theorem closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    closure 𝒟 = ℱ := sorry

-- Proof sketch: each slack function `τ - q₀(x)` and `βᵢ - qᵢ(x)` is concave on the strict
-- epigraph domain because the corresponding `qᵢ` is convex. The logarithmic barrier of the
-- `m + 1` positive scalar slacks is therefore the standard `(m + 1)`-self-concordant barrier for
-- the QCQP epigraph domain.
/-- The QCQP epigraph logarithmic barrier is an `(m + 1)`-self-concordant barrier on the strict
epigraph domain. The raw pair ambient space `Eₙ × ℝ` carries the canonical `L²` inner-product
structure locally inside this file, so the public theorem surface stays on the QCQP epigraph
owner itself rather than on an exposed `WithLp` transport. -/
theorem qcqpStrictEpigraphLogarithmicBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F := sorry

local instance : IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F :=
  qcqpStrictEpigraphLogarithmicBarrier_isSelfConcordantBarrierOnWith problem

-- Proof sketch: identify `closure 𝒟` with the owner feasible set `ℱ` using
-- `closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet`, then specialize the generic
-- short-step existence and complexity theory for self-concordant barriers to the QCQP epigraph
-- barrier. The resulting common witnesses `β`, `γ`, `C`, `x₀`, and `scheme` simultaneously
-- satisfy the six source-facing clauses of Proposition 5.4.3.2.
/-- Proposition 5.4.3.2: if a convex QCQP in epigraph form has nonempty strict feasible region,
admits an epigraph-optimal feasible point `xOpt`, and `ε > 0`, then there exist common
parameters `β`, `γ`, `C`, a starting point `x₀`, and a short-step path-following scheme for the
QCQP epigraph barrier such that:
`β < 1 / 2`, `γ > 0`, `C > 0`, the stopping iterate is feasible for the epigraph
reformulation, its epigraph objective value is within `ε` of the epigraph-optimal reference
value `P (xOpt : Eₙ × ℝ)`, and its stopping index satisfies the stated logarithmic iteration
bound. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              beta < 1 / 2 ∧
                0 < gamma ∧
                scheme scheme.stopIndex ∈ ℱ ∧
                P (scheme scheme.stopIndex) ≤ P (xOpt : Eₙ × ℝ) + ε ∧
                scheme.stopIndex ≤
                  ⌈((C : NNReal) : ℝ) * Real.sqrt (m + 1 : ℝ) *
                      Real.log ((m + 1 : ℝ) / ε)⌉₊ := sorry

-- Proof sketch: project the `β < 1 / 2` clause from the common witness package theorem above.
/-- Proposition 5.4.3.2 (1): under the hypotheses of Proposition 5.4.3.2, the common short-step
scheme can be chosen with initial centering parameter `β < 1 / 2`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_beta_lt_half
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            beta < 1 / 2 := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, hβ, -, -, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hβ⟩

-- Proof sketch: specialize the general short-step path-following existence theorem for the
-- QCQP epigraph logarithmic barrier and extract the positive stepsize parameter `γ`.
/-- Proposition 5.4.3.2 (2): under the same hypotheses, there exists such a short-step scheme
with a positive update parameter `γ`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_gamma_pos
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            0 < gamma := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, hγ, -, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hγ⟩

-- Proof sketch: the same existence theorem yields a positive absolute constant controlling the
-- complexity bound in the QCQP epigraph setting.
/-- Proposition 5.4.3.2 (3): under the same hypotheses, there exists such a short-step scheme
with a positive iteration-bound constant `C`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_constant_pos
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              0 < ((C : NNReal) : ℝ) := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, -, -⟩
  refine ⟨beta, gamma, C, x0, scheme, ?_⟩
  have hC : (0 : NNReal) < (C : NNReal) := by
    exact pos_iff_ne_zero.mpr (Units.ne_zero C)
  exact_mod_cast hC

-- Proof sketch: the short-step existence theory produces a stopping iterate that remains in the
-- strict barrier domain, hence is feasible for the nonstrict QCQP epigraph problem.
/-- Proposition 5.4.3.2 (4): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping iterate is feasible for the epigraph reformulation. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_feasible
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            scheme scheme.stopIndex ∈ ℱ := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, hfeas, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hfeas⟩

-- Proof sketch: specialize the generic `ε`-accuracy guarantee for short-step path-following on
-- self-concordant barriers to the QCQP epigraph owner `P`, whose objective is the slack
-- coordinate `τ`, and compare the stopping iterate with the epigraph-optimal reference point
-- `xOpt`.
/-- Proposition 5.4.3.2 (5): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping iterate has epigraph-objective value within `ε` of the epigraph-optimal
reference value `P (xOpt : Eₙ × ℝ)`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_tau_le_add_epsilon
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            P (scheme scheme.stopIndex) ≤ P (xOpt : Eₙ × ℝ) + ε := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, hgap, -⟩
  exact ⟨beta, gamma, x0, scheme, hgap⟩

-- Proof sketch: combine the source-facing `xOpt` comparison with the owner-level optimality
-- property of `xOpt` on the feasible set `ℱ` to compare the stopping iterate with any feasible
-- epigraph point.
/-- Companion corollary: under the same hypotheses, the stopping iterate from Proposition
5.4.3.2 also has `τ`-value within `ε` of every feasible epigraph value. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_tau_le_feasible_add_epsilon
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            ∀ y ∈ ℱ, P (scheme scheme.stopIndex) ≤ P y + ε := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, hgap, -⟩
  refine ⟨beta, gamma, x0, scheme, ?_⟩
  intro y hy
  have hopt' : ∀ z ∈ ℱ, P (xOpt : Eₙ × ℝ) ≤ P z :=
    isMinOn_iff.mp hopt
  have hxOpt_le : P (xOpt : Eₙ × ℝ) ≤ P y := by
    exact hopt' y hy
  have hxOpt_le_add : P (xOpt : Eₙ × ℝ) + ε ≤ P y + ε := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hxOpt_le ε
  exact le_trans hgap hxOpt_le_add

-- Proof sketch: apply the standard short-step iteration complexity estimate for
-- `ν = m + 1` self-concordant barriers to the QCQP epigraph barrier.
/-- Proposition 5.4.3.2 (6): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping index satisfies the bound
`O(√(m + 1) log ((m + 1) / ε))` with an explicit constant `C`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_iteration_bound
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              scheme.stopIndex ≤
                ⌈((C : NNReal) : ℝ) * Real.sqrt (m + 1 : ℝ) *
                    Real.log ((m + 1 : ℝ) / ε)⌉₊ := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, -, hbound⟩
  exact ⟨beta, gamma, C, x0, scheme, hbound⟩

end

/-! ### Definition_5_4_4_1 (from Chap05) -/
open Matrix

/- Definition 5.4.4.1 is a recall-only item in the real symmetric-matrix domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical symmetric-matrix submodule.

Primary domain:
- the real vector space `𝕊^n` of symmetric `n × n` matrices.

Sampled owner-style declarations:
- mathlib `selfAdjointMatricesSubmodule`
- mathlib `mem_selfAdjointMatricesSubmodule`
- mathlib `Matrix.IsSymm`
- mathlib `Matrix.IsSymm.eq`

Best owner abstraction:
- source-facing: the vector space `𝕊^n` of real symmetric matrices;
- core/canonical: `selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ)`;
- bridge/view: membership rewritten as `Matrix.IsSymm`, equivalently `Xᵀ = X`.

Primitive data:
- `n : ℕ`

Derived API:
- the canonical symmetric-matrix owner `selfAdjointMatricesSubmodule`
- the source-facing notation `𝕊^n`
- the owner-branded symmetry bridge `RealSymmetricMatrixSpace.mem_iff_isSymm`
- the owner-branded transpose bridge `RealSymmetricMatrixSpace.mem_iff_transpose_eq`

This file therefore removes the duplicate local definition `realSymmetricMatrixSubspace` and
reuses the matrix-specific canonical owner directly. The textbook surface is then recovered by
thin owner-branded companion lemmas on `𝕊^n`, written directly in `Matrix.IsSymm` / `Xᵀ = X`
form. -/

recall selfAdjointMatricesSubmodule
recall mem_selfAdjointMatricesSubmodule

scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg =>
  selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ)
open scoped RealSymmetricMatrixSpace

section

variable (n : ℕ)

/- Definition 5.4.4.1: the vector space `𝕊^n` of real symmetric matrices is the canonical
self-adjoint submodule specialized to real square matrices. -/
#check (𝕊^n : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))

end

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

namespace RealSymmetricMatrixSpace

/-- Membership in `𝕊^n` is exactly symmetry. -/
theorem mem_iff_isSymm
    {X : Mat} :
    X ∈ 𝕊^n ↔ X.IsSymm := by
  rw [mem_selfAdjointMatricesSubmodule]
  simp [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair, Matrix.IsSymm]

/-- Membership in `𝕊^n` is exactly the equation `Xᵀ = X`. -/
theorem mem_iff_transpose_eq
    {X : Mat} :
    X ∈ 𝕊^n ↔ Xᵀ = X := by
  simpa [Matrix.IsSymm] using
    (mem_iff_isSymm :
      X ∈ 𝕊^n ↔ X.IsSymm)

/-- A point of `𝕊^n` is symmetric as an ambient real matrix. -/
theorem isSymm (X : 𝕊^n) :
    ((X : 𝕊^n) : Mat).IsSymm :=
  mem_iff_isSymm.mp X.2

end RealSymmetricMatrixSpace

end

/-- The identity matrix is a canonical element of `𝕊^n`. -/
instance {n : ℕ} : One (𝕊^n) where
  one := ⟨1, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    exact Matrix.isSymm_one⟩

/-- The numeral `1` on `𝕊^n` is the identity matrix. -/
instance {n : ℕ} : OfNat (𝕊^n) 1 where
  ofNat := (1 : 𝕊^n)

noncomputable section

namespace RealSymmetricMatrixSpace

@[simp] theorem coe_one
    {n : ℕ} :
    ((1 : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  rfl

/-- A real symmetric matrix in `𝕊^n` is Hermitian. -/
theorem isHermitian
    {n : ℕ} (X : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    isSymm X

/-- The intrinsic eigenvalue list of a real symmetric matrix in `𝕊^n`. -/
abbrev eigenvalues
    {n : ℕ} (X : 𝕊^n) :
    Fin n → ℝ :=
  (isHermitian X).eigenvalues

/-- The determinant of a real symmetric matrix is the product of its intrinsic eigenvalues. -/
theorem det_eq_prod_eigenvalues
    {n : ℕ} (X : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ)).det =
      ∏ i : Fin n, eigenvalues X i := by
  simpa using (isHermitian X).det_eq_prod_eigenvalues

end RealSymmetricMatrixSpace

end

/-! ### Definition_5_4_4_2 (from Chap05) -/
open Matrix
open scoped RealSymmetricMatrixSpace

/- Definition 5.4.4.2 is a source-facing owner item in the symmetric-matrix Frobenius domain.

Layer targeted by this refinement:
- source-facing: the Frobenius pairing and norm on the chapter owner `𝕊^n`.

Primary domain:
- the Frobenius pairing and Frobenius norm on real square matrices and their restriction to
  `𝕊^n`.

Sampled owner-style declarations:
- mathlib `Matrix.trace`
- mathlib `norm_eq_sqrt_real_inner`
- mathlib `real_inner_self_nonneg`
- mathlib `Matrix.toMatrixInnerProductSpace`
- mathlib `Submodule.innerProductSpace`
- mathlib `Submodule.coe_norm`
- Chapter 5 `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` from Definition 5.4.4.1
- the source-facing notation `𝕊^n`

Best owner abstraction:
- source-facing: the Frobenius inner product and norm on symmetric matrices;
- core/canonical: the inherited real inner-product-space structure on `𝕊^n`;
- bridge/view: the coercion `↥(𝕊^n) → Matrix (Fin n) (Fin n) ℝ` and the trace identity
  `trace (Y Xᵀ) = trace (Xᵀ Y)`.

Primitive data:
- `n : ℕ`
- `X Y : 𝕊^n`

Derived API:
- the restricted pairing owner `RealSymmetricMatrixSpace.frobeniusInner`
- the source-facing notation `⟪X, Y⟫_F`
- the inherited Frobenius inner-product structure on `𝕊^n`
- the bridge theorem `‖X‖ = Real.sqrt ⟪X, X⟫_F`
- the ambient multiplication bridges `RealSymmetricMatrixSpace.sandwich X Y` and
  `RealSymmetricMatrixSpace.cube X` on `𝕊^n`

Source/core/bridge triage:
- source-facing: the Frobenius inner product and norm on `𝕊^n`;
- core/canonical: the inherited real inner product on `𝕊^n`;
- bridge/view: the coercion from `𝕊^n` to matrices.

This file keeps the Chapter 5 owner `⟪·, ·⟫_F` and the inherited Frobenius normed-space
structure on `𝕊^n`, while exposing only the thin ambient-multiplication bridges actually needed by
the downstream Chapter 5 semidefinite files.
-/

noncomputable section

namespace RealSymmetricMatrixSpace

private instance ambientMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
  toMatrixNormedAddCommGroup (1 : Matrix (Fin n) (Fin n) ℝ) PosDef.one

private instance ambientMatrixInnerProductSpace {n : ℕ} :
    InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  toMatrixInnerProductSpace (1 : Matrix (Fin n) (Fin n) ℝ) PosDef.one.posSemidef

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius normed-group structure. -/
noncomputable instance symmetricMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  exact Submodule.normedAddCommGroup (𝕊^n)

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius normed-space structure. -/
noncomputable instance symmetricMatrixNormedSpace {n : ℕ} :
    NormedSpace ℝ (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  exact Submodule.normedSpace (𝕊^n)

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius inner-product structure. -/
noncomputable instance symmetricMatrixInnerProductSpace {n : ℕ} : InnerProductSpace ℝ (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixInnerProductSpace
  exact Submodule.innerProductSpace (𝕊^n)

/-- Definition 5.4.4.2: on `𝕊^n`, the Frobenius inner product is the inherited real inner product,
written on the theorem surface in Frobenius notation. -/
abbrev frobeniusInner {n : ℕ} (X Y : 𝕊^n) : ℝ :=
  inner ℝ X Y

scoped[RealSymmetricMatrixSpace] notation "⟪" X ", " Y "⟫_F" =>
  RealSymmetricMatrixSpace.frobeniusInner X Y

/-- Expanding the Frobenius pairing on `𝕊^n` gives the ambient trace formula. -/
theorem frobeniusInner_def {n : ℕ} (X Y : 𝕊^n) :
    ⟪X, Y⟫_F =
      Matrix.trace
        ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) := by
  change inner ℝ X Y =
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ))
  change Matrix.trace ((Y : Matrix (Fin n) (Fin n) ℝ) * 1 * (X : Matrix (Fin n) (Fin n) ℝ)ᵀ) =
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ))
  simpa using
    (Matrix.trace_mul_comm (Y : Matrix (Fin n) (Fin n) ℝ)
      ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ))

/-- The symmetric-matrix carrier `𝕊^n` inherits the ambient uniform additive-group structure. -/
instance symmetricMatrixIsUniformAddGroup {n : ℕ} : IsUniformAddGroup (𝕊^n) := by
  refine IsUniformAddGroup.mk' ?_ ?_
  · exact
      ((uniformContinuous_subtype_val.comp uniformContinuous_fst).add
        (uniformContinuous_subtype_val.comp uniformContinuous_snd)).subtype_mk
        fun p ↦ (𝕊^n).add_mem p.1.2 p.2.2
  · exact (uniformContinuous_subtype_val.neg).subtype_mk fun X ↦ (𝕊^n).neg_mem X.2

/-- In Frobenius scope, the norm on `𝕊^n` is the ambient matrix Frobenius norm. -/
@[simp] theorem norm_coe {n : ℕ} (X : 𝕊^n) :
    ‖X‖ = ‖(X : Matrix (Fin n) (Fin n) ℝ)‖ := by
  exact Submodule.coe_norm X

/-- The induced inner product on `𝕊^n` is exactly the Chapter 5 Frobenius pairing. -/
@[simp] theorem inner_eq_frobeniusInner {n : ℕ} (X Y : 𝕊^n) :
    inner ℝ X Y = ⟪X, Y⟫_F :=
  rfl

-- Proof sketch: rewrite the inherited norm by the real inner-product-space identity
-- `‖X‖ = Real.sqrt (inner ℝ X X)` and then use `inner_eq_frobeniusInner`.
/-- The Frobenius norm on `𝕊^n` is the square root of the Frobenius self-pairing. -/
theorem norm_eq_sqrt_frobeniusInner {n : ℕ} (X : 𝕊^n) :
    ‖X‖ = Real.sqrt (⟪X, X⟫_F) := by
  change ‖X‖ = Real.sqrt (inner ℝ X X)
  exact norm_eq_sqrt_real_inner X

-- Proof sketch: combine the positivity of `inner ℝ X X` in the inherited inner-product space
-- with `inner_eq_frobeniusInner`.
/-- The Frobenius self-pairing on `𝕊^n` is nonnegative. -/
theorem frobeniusInner_self_nonneg {n : ℕ} (X : 𝕊^n) :
    0 ≤ ⟪X, X⟫_F := by
  change 0 ≤ inner ℝ X X
  exact real_inner_self_nonneg

private theorem sandwich_mem {n : ℕ} (X Y : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
        (X : Matrix (Fin n) (Fin n) ℝ)) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  rw [Matrix.IsSymm]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, (isSymm X).eq, (isSymm Y).eq]

/-- The ambient sandwich product `XYX`, viewed back in the symmetric carrier `𝕊^n`. -/
def sandwich {n : ℕ} (X Y : 𝕊^n) : 𝕊^n :=
  ⟨(X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
      (X : Matrix (Fin n) (Fin n) ℝ), sandwich_mem X Y⟩

@[simp] theorem coe_sandwich {n : ℕ} (X Y : 𝕊^n) :
    ((RealSymmetricMatrixSpace.sandwich X Y : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
        (X : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

private theorem cube_mem {n : ℕ} (X : 𝕊^n) :
    (((X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ)) : Matrix (Fin n) (Fin n) ℝ) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa using (isSymm X).pow (3 : ℕ)

/-- The ambient cube `X^3`, viewed back in the symmetric carrier `𝕊^n`. -/
def cube {n : ℕ} (X : 𝕊^n) : 𝕊^n :=
  ⟨(X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ), cube_mem X⟩

@[simp] theorem coe_cube {n : ℕ} (X : 𝕊^n) :
    ((RealSymmetricMatrixSpace.cube X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ) :=
  rfl

/-- The Frobenius symmetric-matrix carrier `𝕊^n` is complete. -/
noncomputable instance symmetricMatrixCompleteSpace {n : ℕ} : CompleteSpace (𝕊^n) := by
  letI : IsUniformAddGroup (𝕊^n) := symmetricMatrixIsUniformAddGroup
  exact FiniteDimensional.complete ℝ (𝕊^n)

end RealSymmetricMatrixSpace

/-! ### Definition_5_4_4_3 (from Chap05) -/
noncomputable section

open Matrix
open scoped MatrixOrder NNReal RealInnerProductSpace RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

/- Definition 5.4.4.3 lies in the real symmetric-matrix positivity domain.

Layer targeted by this refinement:
- source-facing: the textbook cone notation `𝕊^n₊` inside the symmetric carrier `𝕊^n`;
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`;
- bridge/view: coercion from `𝕊^n` to matrices and quadratic-form characterizations through
  `Matrix.toEuclideanLin`.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` from `Definition_5_4_4_1`, the symmetric-matrix owner;
- mathlib `Matrix.PosSemidef`, the canonical positive-semidefinite matrix predicate;
- mathlib `selfAdjoint.submodule`, the canonical carrier behind `𝕊^n`;
- mathlib `Matrix.isPositive_toEuclideanLin_iff`, the Euclidean-operator positivity bridge;
- mathlib `Matrix.PosDef.of_dotProduct_mulVec_pos` and `Matrix.PosDef.dotProduct_mulVec_pos`,
  the positive-definite owner API.

Primitive data:
- `n : ℕ`

Derived API:
- the source-facing notation `𝕊^n₊ : Set (𝕊^n)`;
- the owner bridge `X ∈ 𝕊^n₊ ↔ (X : Mat).PosSemidef`;
- the intrinsic cone bridge `PositiveSemidefiniteCone.nnrpow X p` for nonnegative powers of PSD
  matrices;
- the quadratic-form and positive-definite companion characterizations.

This file therefore deletes the duplicate local owner `positiveSemidefiniteCone`, keeps the
textbook cone notation on the intrinsic symmetric carrier `𝕊^n`, avoids any public
Euclidean-array realization wrapper, and derives the rest of the API from the canonical
matrix-positivity owners.
-/

recall Matrix.PosSemidef
recall Matrix.isPositive_toEuclideanLin_iff

set_option quotPrecheck false in
scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg "₊" =>
  ({X : 𝕊^n | ((X : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} : Set (𝕊^n))

section

variable (n : ℕ)

/- Definition 5.4.4.3: the cone `𝕊ⁿ₊` of positive semidefinite real symmetric `n × n` matrices
is the canonical subset of the symmetric carrier `𝕊^n` cut out by `Matrix.PosSemidef`. -/
#check (𝕊^n₊ : Set (𝕊^n))

end

/-- Membership in `𝕊ⁿ₊` is exactly the canonical predicate `Matrix.PosSemidef`. -/
@[simp] theorem mem_positiveSemidefiniteCone_iff
    (X : SymmMat) :
    X ∈ 𝕊^n₊ ↔ (X : Mat).PosSemidef :=
  Iff.rfl

namespace PositiveSemidefiniteCone

private theorem nnrpow_posSemidef
    (X : 𝕊^n₊) (p : ℝ≥0) :
    ((((X : SymmMat) : Mat) ^ p) : Mat).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (show 0 ≤ ((((X : SymmMat) : Mat) ^ p) : Mat) by
      exact CFC.nnrpow_nonneg)

private theorem nnrpow_mem_symm
    (X : 𝕊^n₊) (p : ℝ≥0) :
    ((((X : SymmMat) : Mat) ^ p) : Mat) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (nnrpow_posSemidef X p).isHermitian

/-- The ambient nonnegative real power of a positive-semidefinite symmetric matrix, viewed back
in `𝕊^n₊`. -/
def nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) : 𝕊^n₊ :=
  ⟨⟨(((X : SymmMat) : Mat) ^ p), nnrpow_mem_symm X p⟩, nnrpow_posSemidef X p⟩

/-- The textbook nonnegative real power notation on `𝕊^n₊` is induced by `nnrpow`. -/
instance : Pow (𝕊^n₊) ℝ≥0 where
  pow X p := nnrpow X p

@[simp] theorem pow_eq_nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    X ^ p = nnrpow X p :=
  rfl

@[simp] theorem coe_nnrpow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    (((nnrpow X p : SymmMat) : Mat)) = (((X : SymmMat) : Mat) ^ p) :=
  rfl

@[simp] theorem coe_pow
    (X : 𝕊^n₊) (p : ℝ≥0) :
    (((X ^ p : 𝕊^n₊) : SymmMat) : Mat) = (((X : SymmMat) : Mat) ^ p) :=
  rfl

end PositiveSemidefiniteCone

-- Proof sketch: unfold membership in `𝕊^n₊`; then use the real-matrix characterization of
-- `Matrix.PosSemidef` by nonnegativity of the quadratic form `u ↦ ⟪Xu, u⟫`; the symmetry part is
-- already built into the carrier `𝕊^n`.
/-- For a symmetric matrix, membership in the positive-semidefinite cone is equivalent to
nonnegativity of the quadratic form `u ↦ ⟪Xu, u⟫` on `ℝⁿ`. -/
theorem mem_positiveSemidefiniteCone_iff_inner_nonneg
    (X : SymmMat) :
    X ∈ 𝕊^n₊ ↔ ∀ u : E, 0 ≤ ⟪(X : Mat).toEuclideanLin u, u⟫ := by
  rw [mem_positiveSemidefiniteCone_iff, ← Matrix.isPositive_toEuclideanLin_iff,
    LinearMap.isPositive_iff]
  constructor
  · rintro ⟨_, hpos⟩
    exact hpos
  · intro hpos
    refine ⟨?_, hpos⟩
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr <|
      by simpa [Matrix.IsHermitian, Matrix.IsSymm] using
        RealSymmetricMatrixSpace.isHermitian X

-- Proof sketch: apply the standard characterization of `Matrix.PosDef`; under the symmetry
-- built into `𝕊^n`, positivity of the quadratic form on all nonzero vectors is exactly the
-- textbook condition.
/-- A real symmetric matrix is positive definite exactly when its quadratic form is positive on
every nonzero vector. -/
theorem matrix_posDef_iff_forall_inner_pos
    (X : SymmMat) :
    (X : Mat).PosDef ↔ ∀ u : E, u ≠ 0 → 0 < ⟪(X : Mat).toEuclideanLin u, u⟫ := by
  constructor
  · intro hPos u hu
    have hu' : u.ofLp ≠ 0 := by
      simpa using hu
    have hquad := hPos.dotProduct_mulVec_pos hu'
    simpa using hquad
  · intro hquad
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun {u} hu ↦ ?_
    · simpa using RealSymmetricMatrixSpace.isHermitian X
    · let uE : E := (EuclideanSpace.equiv (Fin n) ℝ).symm u
      have huE : uE ≠ 0 := by
        intro huE0
        apply hu
        simpa [uE] using congrArg (EuclideanSpace.equiv (Fin n) ℝ) huE0
      have h := hquad uE huE
      simpa [uE] using h

end
