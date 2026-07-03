import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.LeftRightLim

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_24_8 (from Chap05) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} [Preorder 𝕜]
variable {E : Type u}

namespace Function

/-- Finite-valuedness on a set at the chapter codomain layer. This keeps the source-facing
finiteness data (`x ∈ dom(f)` and `f x ≠ ⊥`) as one reusable owner. -/
abbrev IsFiniteOn (f : E → WithTopBot 𝕜) (C : Set E) : Prop :=
  ∀ x, x ∈ C → x ∈ dom(f) ∧ f x ≠ ⊥

end Function

end

section

open Filter
open scoped Pointwise Rockafellar Topology

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.8 is a continuity theorem for directional derivatives and
  subdifferentials under pointwise convergence of convex functions on a convex set with intrinsic
  relative-openness owner `IsRelativelyOpen 𝕜 C`, where all functions are finite.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.directionalDerivativeAt`, `_root_.subdifferentialAt`,
  `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` / its one-sided uniform consequence
  from Chapter 10, and the support-function containment criterion
  `closure_subset_closure_iff_supportFunction_le` from Chapter 13.
- `bridge/view`: the public theorem keeps Rockafellar's pointwise-convergence hypotheses, but its
  conclusions are written directly in the existing Chapter 23 owners rather than through a local
  duplicate directional-derivative or subgradient package.

Domain-style sampling used here:
- `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` from
  `Items/Chap02/Theorem_10_8`;
- `eventually_le_add_of_limsup_le_of_convexOn_on_closed_bounded` from
  `Items/Chap02/Corollary_10_8_1`;
- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
  `Items/Chap05/Lemma_23_0_1`;
- `closure_subset_closure_iff_supportFunction_le` from
  `Items/Chap03/Corollary_13_1_1`.

Primitive data vs derived API:
- primitive source data: the convex functions `fSeq i` and `f`, the convex region `C` with
  intrinsic relative-openness owner `IsRelativelyOpen 𝕜 C` on which they are finite, encoded
  canonically by `x ∈ dom(f)` / `x ∈ dom(fSeq i)` together with exclusion of the value `⊥`, the
  pointwise convergence on `C`, and convergent sequences `xSeq → x` inside `C` and `ySeq → y`;
- derived API: the upper-semicontinuity inequality for `directionalDerivativeAt`; the companion
  closed-ball containment theorem below is pairing-parametric on a normed dual-side codomain.

Layer target: `source-facing`. The theorem is not collapsed to a pure
`TendstoLocallyUniformlyOn` owner statement, because the source item itself is explicitly about
 directional derivatives and subdifferentials under pointwise convergence.

Ambient-assumption minimization:
- Chapter 23's directional-derivative and dual-subdifferential owners already live on
  `WithTopBot 𝕜` over a scalar-generic normed-space layer, so the theorem surface follows that
  owner level directly;
- no inner-product identification is part of the primary statement layer; the companion
  closed-ball clause below stays at the same scalar layer and is pairing-parametric in a normed
  dual-side codomain `Y`.
-/

namespace Function

variable {C : Set E}
variable (fSeq : ℕ → E → WithTopBot 𝕜) (f : E → WithTopBot 𝕜)

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_theorem5248 : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

-- Proof sketch: restrict the convex functions to the convex region `C` with intrinsic
-- relative-openness owner `IsRelativelyOpen 𝕜 C`, pass to the Chapter 10
-- pointwise-convergence owner on finite scalar-valued convex functions, and then compare the
-- resulting directional-difference quotients along the affine lines
-- `xSeq i + t • ySeq i`.
/-- Theorem 5.24.8, directional-derivative form: if convex extended-real-valued functions
`fSeq i` converge pointwise on a convex set `C` with intrinsic relative-openness owner
`IsRelativelyOpen 𝕜 C` to a limit `f` with `ConvexOn 𝕜 C f`, and all of these functions are
finite on `C`, then
directional derivatives are upper semicontinuous along convergent base-point and direction
sequences inside `C`. -/
theorem limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convexOn : ConvexOn 𝕜 C f) (hfSeq_convexOn : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hf_finite : f.IsFiniteOn C)
    (hfSeq_finite : ∀ i, (fSeq i).IsFiniteOn C)
    (hlimit : ∀ x, x ∈ C → Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x)))
    {x : E} (hx : x ∈ C) {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x))
    {y : E} {ySeq : ℕ → E} (hySeq : Tendsto ySeq atTop (𝓝 y)) :
    limsup (fun i ↦ directionalDerivativeAt (fSeq i) (xSeq i) (ySeq i)) atTop ≤
      directionalDerivativeAt f x y := by
  sorry


variable {C : Set E}
variable (fSeq : ℕ → E → WithTopBot 𝕜) (f : E → WithTopBot 𝕜)
variable {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]

-- Proof sketch: use the directional theorem with a constant direction to obtain eventual support-
-- function domination on the unit closed ball, then rewrite the support term for the ball and
-- invoke the Chapter 13 support-function containment criterion.
/-- Theorem 5.24.8, subdifferential form: under the same hypotheses (with intrinsic
relative-openness owner `IsRelativelyOpen 𝕜 C`), every `ε > 0` eventually forces the
pairing-level subdifferential `∂[Y]fSeq i(xSeq i)` to lie in the
Minkowski sum of `∂[Y]f(x)` with the closed `Y`-ball of radius `ε`. -/
theorem eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convexOn : ConvexOn 𝕜 C f) (hfSeq_convexOn : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hf_finite : f.IsFiniteOn C)
    (hfSeq_finite : ∀ i, (fSeq i).IsFiniteOn C)
    (hlimit : ∀ x, x ∈ C → Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x)))
    {x : E} (hx : x ∈ C) {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      (∂[Y]fSeq i(xSeq i)) ⊆
        (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  sorry

end Function

end

/-! ### Theorem_5_24_9 (from Chap05) -/
noncomputable section

open Filter
open scoped Pointwise Rockafellar Topology

universe u v

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-!
Source/core/bridge triage for clause (1).

- `source-facing`: Theorem 5.24.9 (1) studies one fixed closed proper convex function `f`, a
  sequence `xᵢ → x` approaching `x` with asymptotic direction `y`, and the resulting upper
  semicontinuity of the directional derivatives.
- `core/canonical`: the owner declarations already present upstream are
  `Function.IsClosedProperConvex`, `Function.directionalDerivativeAt`, the Chapter 5 continuity
  owner `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex`, and the
  iterated-direction comparison `Function.iterated_directionalDerivativeAt_le`.
- `bridge/view`: the source notation `f'(x; y; z)` is represented directly by the canonical
  iterated owner `directionalDerivativeAt (directionalDerivativeAt f x) y z`; no second
  directional-derivative wrapper is introduced.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.iterated_directionalDerivativeAt_le` from
  `Chap05.Proposition_5_24_2`;
- `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` from
  `Chap05.Theorem_5_24_8`;
- `Function.IsClosedProperConvex` from the Chapter 23 owner chain reused by these statements.

Primitive data vs derived API:
- primitive source data: the closed proper convex function `f`, the base point `x ∈ dom(f)`, the
  approaching sequence `xSeq`, its normalized displacement limit `y`, the finiteness hypothesis
  `f'(x; y) > -∞`, and the hypothesis that the half-line `x + ℝ≥0 • y` meets `riDom(f)`;
- derived API: the limsup inequality for `directionalDerivativeAt f (xSeq i) z`.

Layer target: `source-facing`. Clause (1) is explicitly about directional continuity along one
approaching sequence, so it stays on the directional-derivative owner rather than on a generic
convergence package.

Ambient-assumption minimization:
- the theorem surface uses only the Chapter 5 directional-derivative owner chain on a
  finite-dimensional real normed space;
- no inner-product identification or Euclidean subdifferential bridge appears in clause (1), so
  those assumptions are deferred to the second section below.
-/

variable {f : E → WithTopBot ℝ} {x y : E} {xSeq : ℕ → E}

-- Proof sketch: apply the Chapter 5 upper-semicontinuity argument to the fixed convex function
-- `f` on a polytope inside `dom(f)` generated by a point in `riDom(f)` on the ray
-- `x + ℝ≥0 • y`. The
-- normalized displacements converge to `y`, so the corresponding difference-quotient comparison
-- yields the limsup bound, and the iterated owner
-- `directionalDerivativeAt (directionalDerivativeAt f x) y z` is exactly Rockafellar's
-- `f'(x; y; z)`.
/-- Theorem 5.24.9 (1): if a closed proper convex function is approached by a sequence
`xSeq i → x` whose normalized displacements converge to `y`, with `f'(x; y) ≠ -∞` and the
half-line `x + ℝ≥0 • y` meeting `riDom(f)`, then for every direction `z` the limsup of
the directional derivatives at `xSeq i` is bounded above by the iterated directional derivative
`directionalDerivativeAt (directionalDerivativeAt f x) y z`, which is the source quantity
`f'(x; y; z)`. -/
theorem limsup_directionalDerivativeAt_le_iterated_directionalDerivativeAt_of_tendsto_normalized_sub
    (hf : IsClosedProperConvex[ℝ] f) (hx : x ∈ dom(f)) (hxSeq_dom : ∀ i, xSeq i ∈ dom(f))
    (hxSeq_ne : ∀ i, xSeq i ≠ x) (hxSeq : Tendsto xSeq atTop (𝓝 x))
    (hy :
      Tendsto (fun i ↦ ‖xSeq i - x‖⁻¹ • (xSeq i - x)) atTop (𝓝 y))
    (hy_bot : directionalDerivativeAt f x y ≠ ⊥)
    (hriDom_ray : ∃ t : ℝ, 0 ≤ t ∧ x + t • y ∈ riDom(f))
    (z : E) :
    limsup (fun i ↦ directionalDerivativeAt f (xSeq i) z) atTop ≤
      directionalDerivativeAt (directionalDerivativeAt f x) y z := sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Function

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-!
Source/core/bridge triage for the intrinsic face owner and clause (2).

- `source-facing`: Theorem 5.24.9 (2) localizes subdifferentials near the source face
  `∂f(x)_y`.
- `core/canonical`: the owner declarations already present upstream are
  `_root_.subdifferentialAt`, the normal-cone owner `N[ℝ](· | ·)`, and the
  Chapter 5 containment owner
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`.
- `bridge/view`: the source face `∂f(x)_y` is owned intrinsically at the pairing layer by
  normal-cone membership over the dual-side codomain `Y`, with `StrongDual ℝ E` as the default
  specialization.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- the normal-cone owner `N[ℝ](· | ·)` from `Chap01.Definition_2_7_10`;
- `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  from `Chap05.Theorem_5_24_8`.

Primitive data vs derived API:
- primitive source data: the same sequence data as in clause (1), with subdifferentials kept on
  the canonical pairing owner `_root_.subdifferentialAt`;
- derived API: the source-face notation layer `∂[Y]f(x; y)` and the eventual containment of
  `_root_.subdifferentialAt f (xSeq i)` in the
  `ε`-neighborhood of that face.

Layer target:
- `bridge/view` for the source-face notation `∂[Y]f(x; y)` and its membership lemma;
- `source-facing` for clause (2), stated directly on the intrinsic source face `∂f(x)_y`.
-/
scoped[Rockafellar] notation "∂[" Y "]" f "(" x "; " y ")" =>
  (setOf (fun xStar : Y ↦ y ∈ N[ℝ](xStar | (∂[Y]f(x)))) : Set Y)

/-- Pairing-level membership characterization of the source-face notation `∂[Y]f(x; y)`. -/
@[simp] theorem mem_subdifferentialFace {f : E → WithTopBot ℝ} {x y : E}
    {Y : Type v} [Sub Y] [HasPairing E Y ℝ] [HasPairing Y E ℝ] {xStar : Y} :
    xStar ∈ (∂[Y]f(x; y)) ↔ y ∈ N[ℝ](xStar | (∂[Y]f(x))) :=
  Iff.rfl

/-- In the canonical continuous-dual model, the source-face owner is exactly the exposed face cut
out by the evaluation functional `xStar ↦ xStar y`. -/
@[simp] theorem mem_subdifferentialFace_iff_mem_toExposed
    {f : E → WithTopBot ℝ} {x y : E} {xStar : StrongDual ℝ E} :
    xStar ∈ (∂[StrongDual ℝ E]f(x; y)) ↔
      xStar ∈ (ContinuousLinearMap.apply ℝ ℝ y).toExposed (∂ f at x) := by
  change y ∈ N[ℝ](xStar | (∂ f at x)) ↔
      xStar ∈ (ContinuousLinearMap.apply ℝ ℝ y).toExposed (∂ f at x)
  rw [mem_normalCone_iff]
  constructor
  · rintro ⟨hxStar, hnormal⟩
    refine ⟨hxStar, ?_⟩
    intro z hz
    have hsub : 0 ≤ (xStar - z) y := hnormal z hz
    rw [ContinuousLinearMap.sub_apply] at hsub
    exact sub_nonneg.mp hsub
  · rintro ⟨hxStar, hface⟩
    refine ⟨hxStar, ?_⟩
    intro z hz
    have hsub : 0 ≤ xStar y - z y := sub_nonneg.mpr (hface z hz)
    change 0 ≤ (xStar - z) y
    rw [ContinuousLinearMap.sub_apply]
    exact hsub

variable {f : E → WithTopBot ℝ} {x y : E} {xSeq : ℕ → E}

-- Proof sketch: repeat the argument of the preceding clause on the support-function side. The
-- source face `∂f(x; y)` is the closed convex set whose support
-- function is the iterated directional derivative at `(x, y)`, so the Chapter 5 subdifferential
-- upper-semicontinuity mechanism yields eventual inclusion of `subdifferentialAt f (xSeq i)` in
-- the Minkowski sum of that face with the dual closed ball of radius `ε`.
/-- Theorem 5.24.9 (2): under the same hypotheses, for every `ε > 0` the intrinsic dual
subdifferentials along the sequence are eventually contained in the `ε`-neighborhood of the
source face `∂[Y]f(x; y)`, i.e. of the source set `∂f(x)_y`, for any dual-side codomain `Y`
equipped with the two pairing orientations needed by `_root_.subdifferentialAt` and
`normalCone`. -/
theorem
    eventually_subdifferentialAt_subset_subdifferentialFace_add_closedBall_of_tendsto_normalized_sub
    {Y : Type v} [NormedAddCommGroup Y] [HasPairing E Y ℝ] [HasPairing Y E ℝ]
    [FiniteDimensional ℝ E]
    (hf : IsClosedProperConvex[ℝ] f) (hx : x ∈ dom(f)) (hxSeq_dom : ∀ i, xSeq i ∈ dom(f))
    (hxSeq_ne : ∀ i, xSeq i ≠ x) (hxSeq : Tendsto xSeq atTop (𝓝 x))
    (hy :
      Tendsto (fun i ↦ ‖xSeq i - x‖⁻¹ • (xSeq i - x)) atTop (𝓝 y))
    (hy_bot : directionalDerivativeAt f x y ≠ ⊥)
    (hriDom_ray : ∃ t : ℝ, 0 ≤ t ∧ x + t • y ∈ riDom(f))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      (∂[Y]f(xSeq i)) ⊆ (∂[Y]f(x; y)) + Metric.closedBall (0 : Y) ε := sorry

end Function

end

/-! ### Theorem_5_24_10 (from Chap05) -/
noncomputable section

open Bornology Function
open scoped Rockafellar SetRel

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.10 studies the set `∂f(S) = ⋃ x ∈ S, ∂f(x)` for a nonempty
  closed bounded set `S`, proves nonemptiness/closedness of this set from `S ⊆ riDom(f)`,
  proves boundedness from `S ⊆ interior (dom(f))`, and then uses the supremum of the dual norms
  of its elements to bound directional derivatives and the oscillation of `f` on `S`.
- `core/canonical`: the owner abstraction is the upstream intrinsic graph/image layer from
  Definition 5.24.3, namely `subdifferentialGraph` and `subdifferentialImage`, surfaced here by
  the notation `∂f(S)`, together with the Chapter 23 directional-derivative owner
  `directionalDerivativeAt` and mathlib's canonical `IsBounded`, `IsClosed`, and
  `LipschitzOnWith`.
- `bridge/view`: on inner-product spaces, `Function.subdifferentialGraph f` is only the
  Fréchet-Riesz specialization of the same owner. It is not the main public surface of this file.

Domain-style sampling used here:
- `subdifferentialImage`, `∂f(S)`, and `mem_subdifferentialImage` from
  `Chap05/Definition_5_24_3`;
- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from `Chap05/Lemma_23_0_1`;
- `Function.subdifferentialAt_nonempty_of_mem_riDom`,
  `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom`, and
  `Function.directionalDerivativeAt_finite_everywhere_of_mem_interior_dom` from
  `Chap05/Theorem_23_4`.

Best owner abstraction first:
- the source set `∂f(S)` is canonically the upstream owner `subdifferentialImage f S`, i.e. the
  relation image of the dual-valued graph owner, not the Euclidean bridge graph;
- this file uses that owner only through the source-facing notation `∂f(S)`, so theorem surfaces
  avoid local alias wrappers and long owner-heavy terms.

Primitive data vs derived API:
- primitive source-facing data: the set `S` and the canonical image owner `∂f(S)`;
- derived API: nonemptiness, closedness, boundedness, the source supremum
  `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}`, the resulting directional-derivative estimate, and the Lipschitz
  bound for `f.realBranch` on `S`.

Layer target:
- `source-facing` theorems stated directly through the `core/canonical` owner
  `∂f(S)`;
- no parallel Euclidean graph wrapper is kept as the main theorem surface.

Ambient-assumption minimization:
- the source's `R^n` is represented by an arbitrary finite-dimensional real normed space;
- the scalar remains `ℝ` here because the reused canonical owners
  `directionalDerivativeAt`, `dom(·)`, `Function.IsConvex`, `Function.IsProper`, and the
  closed-graph clause through `Function.IsClosedProperConvex` are all surfaced on
  `E → WithBotTop ℝ` in the current upstream Chapter 23/24 API;
- the codomain owner for `∂f(S)` is already pairing-parametric upstream in
  `subdifferentialImage`; this theorem specializes to `StrongDual ℝ E` only where the dual norm
  bound `sSup (norm '' ∂f(S))` is the statement's actual content.
-/

-- Proof sketch: choose `x ∈ S`. Since `S ⊆ riDom(f)`, Theorem 23.4 gives a nonempty
-- subdifferential at that point, and any of its elements belongs to the image
-- `∂f(S)`.
/-- The source set `∂f(S)` is
nonempty whenever `S` is nonempty and lies in `riDom(f)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_riDom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ riDom(f)) :
    (∂f(S)).Nonempty := sorry

/-- Intrinsic-domain source-facing form for nonemptiness of `∂f(S)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ riDom(f)) :
    (∂f(S)).Nonempty :=
  subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_riDom
    hf_convex hf_proper hS_nonempty hS_subset

/-- Ambient-interior bridge for nonemptiness of `∂f(S)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ interior (dom(f))) :
    (∂f(S)).Nonempty := by
  exact
    subdifferentialImage_nonempty_of_isConvex_isProper
      hf_convex hf_proper hS_nonempty
      (fun x hx ↦ interior_subset_intrinsicInterior (𝕜 := ℝ) (hS_subset hx))

-- Proof sketch: take a convergent sequence in `∂f(S)`. Pick
-- corresponding base points in `S`; boundedness and closedness of `S` give a convergent
-- subsequence with limit still in `S`, and Theorem 5.24.7 closes the graph of the subdifferential
-- to keep the limit dual subgradient inside the same image set.
/-- For a closed proper convex function, the source set `∂f(S)` is closed when `S` is closed,
bounded, and contained in `riDom(f)`. -/
theorem isClosed_subdifferentialImage_of_isClosedProperConvex
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ riDom(f)) :
    IsClosed (∂f(S)) := sorry

/-- Ambient-interior bridge for closedness of `∂f(S)`. -/
theorem isClosed_subdifferentialImage_of_isClosedProperConvex_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsClosed (∂f(S)) := by
  exact
    isClosed_subdifferentialImage_of_isClosedProperConvex
      hf hS_closed hS_bounded
      (fun x hx ↦ interior_subset_intrinsicInterior (𝕜 := ℝ) (hS_subset hx))

-- Proof sketch: for each `x ∈ S`, Theorem 23.4 gives boundedness of `subdifferentialAt f x`
-- from the interior-domain hypothesis `x ∈ interior (dom(f))`. Corollary 5.24.2 makes the
-- subdifferential map locally upper-semicontinuous on `riDom(f)`; a finite-dimensional
-- compactness argument on the closed bounded set `S` upgrades these local bounds to one global
-- bound on the image.
/-- For a proper convex function, the source set `∂f(S)` is bounded when `S` is closed,
bounded, and contained in `interior (dom(f))`. -/
theorem bounded_subdifferentialImage_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsBounded (∂f(S)) := sorry

/-- Companion interior-domain restatement for boundedness of `∂f(S)`. -/
theorem bounded_subdifferentialImage_of_isConvex_isProper_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsBounded (∂f(S)) := by
  exact
    bounded_subdifferentialImage_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset

-- Proof sketch: the canonical Chapter 23 owner theorem
-- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt` identifies
-- `directionalDerivativeAt f x` with the support function of `subdifferentialAt f x` for each
-- `x ∈ S`. Since `subdifferentialAt f x` contributes to `∂f(S)`,
-- every support value is bounded above by `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)} · ‖z‖` via the dual norm
-- inequality.
/-- The source constant `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}` uniformly bounds the directional derivatives of
`f` at points of `S`. -/
theorem
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) {x : E} (hx : x ∈ S)
    (z : E) :
    directionalDerivativeAt f x z ≤
      ((sSup (norm '' (∂f(S))) * ‖z‖ : ℝ) : WithBotTop ℝ) := sorry

/-- Companion interior-domain restatement of the directional-derivative bound from `∂f(S)`. -/
theorem
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) {x : E} (hx : x ∈ S) (z : E) :
    directionalDerivativeAt f x z ≤
      ((sSup (norm '' (∂f(S))) * ‖z‖ : ℝ) : WithBotTop ℝ) := by
  exact
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset hx z

-- Proof sketch: for `x, y ∈ S`, Theorem 23.1 gives
-- `f(y) - f(x) ≥ directionalDerivativeAt f x (y - x)` and the same inequality with `x` and `y`
-- interchanged. Apply the uniform directional-derivative estimate from the previous theorem to
-- `y - x` and `x - y`, then rewrite the two-sided bound in the canonical form
-- `LipschitzOnWith ⟨sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}, _⟩ f.realBranch S`.
/-- Theorem 5.24.10: if `f` is a proper convex function and `S` is a closed bounded subset
of `interior (dom(f))`, then the source constant `α = sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}` gives a
Lipschitz bound on the real branch of `f` over `S`.
The companion declarations in this file record that `∂f(S)` is nonempty when `S` is, that
`∂f(S)` is closed under `S ⊆ riDom(f)`, that `∂f(S)` is bounded under
`S ⊆ interior (dom(f))`, and that
`directionalDerivativeAt f x z ≤ α ‖z‖` for `x ∈ S`. -/
theorem
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    LipschitzOnWith
      ⟨sSup (norm '' (∂f(S))),
        by
          refine Real.sSup_nonneg ?_
          rintro y ⟨xStar, hxStar, rfl⟩
          exact norm_nonneg xStar⟩
      f.realBranch S := sorry

/-- Companion interior-domain restatement of the Lipschitz estimate from Theorem 5.24.10. -/
theorem
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    LipschitzOnWith
      ⟨sSup (norm '' (∂f(S))),
        by
          refine Real.sSup_nonneg ?_
          rintro y ⟨xStar, _, rfl⟩
          exact norm_nonneg xStar⟩
      f.realBranch S := by
  exact
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset

end

/-! ### Theorem_5_24_11 (from Chap05) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜]
variable [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]
variable [AddRightReflectLE 𝕜] [PosSMulMono 𝕜 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.11 characterizes cyclically monotone multivalued mappings as
  exactly those relations contained in the subdifferential graph of some closed proper convex
  function.
- `core/canonical`: the owner abstractions already present in the project are the relation owner
  `SetRel E Y` for multivalued mappings at the pairing layer,
  `SetRel.CyclicallyMonotone` from Definition 5.24.5,
  `subdifferentialGraph`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the source pointwise clause `ρ(x) ⊆ ∂f(x)` is the relation inclusion
  `ρ ≤ subdifferentialGraph f`.

Domain-style sampling used here:
- `SetRel` from mathlib's relation API, which is the canonical owner layer for multivalued maps;
- `SetRel.CyclicallyMonotone` from
  `Items/Chap05/Definition_5_24_5.lean`,
  the source-facing owner introduced for cyclic monotonicity;
- `subdifferentialGraph` from
  `Items/Chap05/Definition_5_24_3.lean`,
  the canonical graph owner for the dual-valued subdifferential;
- `Function.IsClosedProperConvex` from
  `Items/Chap03/Text_12_3_6.lean`,
  the chapter owner for the admissible convex functions;
- the pairing-parametric codomain layer `Y` with `[HasPairing E Y 𝕜]`, so theorem surfaces stay
  at the intrinsic pairing owner and do not hard-code one concrete dual model.

Primitive data vs derived API:
- primitive owner input: a relation `ρ : SetRel E Y`;
- primitive witness in the existence clause: a function `f : E → WithTopBot 𝕜` with
  `IsClosedProperConvex[𝕜] f`;
- derived bridge API: the source pointwise clause `x⋆ ∈ ∂f(x)` is already read through
  `mem_subdifferentialGraph`.

Layer target: `source-facing`. The theorem keeps Rockafellar's characterization theorem as the
main labeled entry, but it is stated directly with the canonical relation owner and the existing
subdifferential graph owner instead of a parallel multivalued-map wrapper.

Ambient-assumption minimization:
- the source is written on `R^n`; this file keeps only the scalar/order layer used by the reused
  owners and stays codomain-parametric at `HasPairing` level;
- finite-dimensionality and inner-product self-identification are excluded from the theorem
  surface, since only the intrinsic pairing-valued subdifferential owner is used.
-/

namespace SetRel

-- Proof sketch: if `ρ ≤ ∂f`, then every cycle in the graph of `ρ` is also in
-- the graph of `∂f`,
-- and Proposition 5.24.3 gives cyclic monotonicity of `∂f`. Conversely, for a cyclically
-- monotone relation, define Rockafellar's supremum of affine functions using a fixed base graph
-- point when the graph is nonempty, and take any closed proper convex function when `ρ = ∅`; the
-- source proof then shows that the resulting function has `ρ ≤ ∂f`.
/-- The converse existence clause of Theorem 5.24.11: a cyclically monotone relation is contained
in the canonical pairing-valued subdifferential graph of some closed proper convex function. -/
theorem CyclicallyMonotone.exists_isClosedProperConvex_le_subdifferentialGraph
    {ρ : SetRel E Y} (hρ : CMon[𝕜](ρ)) :
    ∃ f : E → WithTopBot 𝕜,
      IsClosedProperConvex[𝕜] f ∧ ρ ≤ gph∂[Y](f) := by
  by_cases hρempty : ρ = ∅
  · refine ⟨(δ[𝕜](· | (Set.univ : Set E))), ?_, ?_⟩
    · simpa using
        (indicatorFunction_isClosedProperConvex_of_nonempty
          (𝕜 := 𝕜) (C := (Set.univ : Set E))
          Set.univ_nonempty isClosed_univ
          (convex_univ : Convex 𝕜 (Set.univ : Set E)))
    · intro p hp
      simp [hρempty] at hp
  · -- Nonempty-graph branch: Rockafellar's cyclic-potential construction.
    sorry

/-- Theorem 5.24.11 (Rockafellar's Theorem 24.8): a multivalued mapping on the intrinsic
topological-module layer is cyclically monotone exactly when it is contained in the subdifferential
graph of some closed proper convex function. The theorem surface uses the intrinsic pairing-valued
owner `subdifferentialGraph`, rather than the inner-product bridge owner.
-/
theorem cyclicallyMonotone_iff_exists_isClosedProperConvex_le_subdifferentialGraph
    (ρ : SetRel E Y) :
    CMon[𝕜](ρ) ↔
      ∃ f : E → WithTopBot 𝕜,
        IsClosedProperConvex[𝕜] f ∧ ρ ≤ gph∂[Y](f) := by
  constructor
  · intro hρ
    exact hρ.exists_isClosedProperConvex_le_subdifferentialGraph
  · rintro ⟨f, hf, hρf⟩
    -- The graph `subdifferentialGraph f` is cyclically monotone by Proposition 5.24.3, and
    -- cyclic monotonicity is inherited by subrelations via `hρf`.
    have hsubgrad :
        CMon[𝕜](gph∂[Y](f)) := by
      simpa using (subdifferentialGraph_cyclicallyMonotone (f := f) hf.proper)
    refine ⟨?_⟩
    intro m x xStar hx
    exact hsubgrad.sum_nonpos m x xStar (fun i ↦ hρf (hx i))

end SetRel

end

/-! ### Theorem_5_24_12 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace SetRel

/-- Theorem 5.24.12 (1): maximal cyclically monotone relations are exactly the relations that are
the full subdifferential graph of a closed proper convex function, stated at the intrinsic
pairing-parametric owner layer. -/
theorem maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
    (ρ : SetRel E Y) :
    MaxCMon[𝕜](ρ) ↔
      ∃ f : E → WithBotTop 𝕜,
        IsClosedProperConvex[𝕜] f ∧ gph∂[Y](f) = ρ := sorry

end SetRel

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [_root_.FiniteDimensional ℝ E]

/-- Finite-dimensional real inner-product spaces are complete, so the intrinsic pairing-valued
subdifferential graph owner is available in this item file. -/
local instance finiteDimensionalCompleteSpace : CompleteSpace E :=
  _root_.FiniteDimensional.complete ℝ E

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "subgradGraph" =>
  (fun f : E → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ E _ _ _ f E (by infer_instance))

namespace SetRel

-- Proof sketch: compare two closed proper convex functions with the same intrinsic
-- pairing-level subdifferential graph. The source argument first shows, via inclusion of pointwise
-- subdifferentials, that their directional derivatives agree on the relative interior of the
-- effective domain, hence the functions differ there by a constant; conjugation then extends the
-- same constant to the whole space.
/-- Theorem 5.24.12 (2): a closed proper convex function on a finite-dimensional real
inner-product space is uniquely determined by its intrinsic pairing-level subdifferential graph up
to an additive real constant. -/
theorem eq_add_const_of_gphSubdiff_eq_of_isClosedProperConvex
    {f g : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hgraph : subgradGraph f = subgradGraph g) :
    ∃ α : ℝ, g = fun x ↦ f x + α := sorry

end SetRel

end
