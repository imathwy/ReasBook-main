import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_1_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.10 says that a polyhedral convex function finite-valued at `x` has a
  nonempty polyhedral subdifferential at `x`, and that its directional-derivative function at `x`
  is proper polyhedral convex and equals the support function of that subdifferential.
- `core/canonical`: the owner predicates already present in the project are
  `Function.HasPolyhedralEpigraph`, `_root_.subdifferentialAt` (surface notation `∂ f at x`),
  `Function.directionalDerivativeAt`, and `Function.IsProper`.
- `bridge/view`: the support-function clause is kept directly on the chapter owner
  `δᵛ(· | ∂ f at x)` rather than through an inner-product bridge owner.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` from `Chap04/Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isClosedProperConvex` from `Chap04/Corollary_19_1_2`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` and the support theorem from
  `Chap05/Theorem_23_2`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithBotTop 𝕜` with polyhedral epigraph, together with
  a base point `x` where `f` is finite, rendered as `x ∈ dom(f)` and `f x ≠ ⊥`;
- derived API: nonemptiness and polyhedrality of `∂ f at x`, polyhedrality
  and properness of `Function.directionalDerivativeAt f x`, and the support-function identity.

Layer target: `core/canonical`, stated on the dual-valued owner surface `∂ f at x`
without introducing an auxiliary Euclidean wrapper.

Owner-surface refinement:
- clause (3) is split into the two owner predicates
  `(directionalDerivativeAt f x).HasPolyhedralEpigraph` and
  `(directionalDerivativeAt f x).IsProper` instead of packaging them into one conjunction-valued
  theorem; this keeps the source semantics while matching the chapter’s owner-first API style.
- clause (4) is stated pointwise in `d` so the theorem surface stays on the direct owner equation
  `directionalDerivativeAt f x d = δᵛ(d | ∂ f at x)` without explicit
  function-level type ascription noise.

Abstraction-boundary audit for this file:
- codomain normalization is already applied here (`f : E → WithBotTop 𝕜` instead of `EReal`);
- the theorem surface is scalar-generic at the current chapter-owner layer:
  `_root_.subdifferentialAt`, `Function.directionalDerivativeAt`, and
  `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` are all stated over `𝕜`;
- the theorem surface stays on the established Chapter 23 order/topology owner layer
  (`[ConditionallyCompleteLinearOrder 𝕜]`, `[IsStrictOrderedRing 𝕜]`, and
  `[OrderTopology 𝕜]` / `[OrderTopology (WithBotTop 𝕜)]`) used by the upstream
  subdifferential-directional-derivative bridges this item relies on;
- the finite-dimensional ambient assumption is imported from the polyhedral bridge currently used to
  get the nonempty/proper closed-convex package from `HasPolyhedralEpigraph`;
- this theorem's mathematical content is not an ambient `closure`/`interior` statement, so there
  is no intrinsic-vs-ambient topology reformulation to canonicalize on the theorem surface itself.
-/

namespace Function.HasPolyhedralEpigraph

open Function

variable {f : E → WithBotTop 𝕜} (hf : f.HasPolyhedralEpigraph) {x : E}
variable (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)

-- Proof sketch: pass from the polyhedral-epigraph hypothesis to the canonical closed proper
-- convex owner, then apply the Chapter 23 subgradient-existence theorem at the finite point `x`.
/-- Theorem 23.10 (1): a polyhedral convex function that is finite-valued at `x` is
subdifferentiable at `x`, i.e. its subdifferential is nonempty. -/
theorem subdifferentialAt_nonempty : (∂ f at x).Nonempty := sorry

-- Proof sketch: identify the directional derivative with the support function of the nonempty
-- subdifferential from clause (1), use polyhedrality of the directional-derivative epigraph, and
-- apply the Chapter 19 support-function/polyhedral-set bridge to recover polyhedrality of
-- `∂ f at x`.
/-- Theorem 23.10 (2): at a finite point of a polyhedral convex function, the intrinsic
subdifferential is a polyhedral convex set. -/
theorem subdifferentialAt_isPolyhedral :
    (∂ f at x).IsPolyhedral 𝕜 := sorry

-- Proof sketch: clause (4) identifies `directionalDerivativeAt f x` with the support function of
-- the polyhedral set `∂ f at x` from clause (2). Chapter 19's support-function
-- polyhedrality theorem then gives the owner predicate
-- `(directionalDerivativeAt f x).HasPolyhedralEpigraph`.
/-- Theorem 23.10 (3a): the directional-derivative function at a finite point of a polyhedral
convex function has polyhedral epigraph. -/
theorem directionalDerivativeAt_hasPolyhedralEpigraph :
    (directionalDerivativeAt f x).HasPolyhedralEpigraph := sorry

-- Proof sketch: clause (1) gives subdifferentiability at `x`, and Theorem 23.3 upgrades
-- nonemptiness of the subdifferential at a finite point to properness of the underlying owner.
-- Applying that theorem to `directionalDerivativeAt f x` yields the owner predicate
-- `(directionalDerivativeAt f x).IsProper`.
/-- Theorem 23.10 (3b): the directional-derivative function at a finite point of a polyhedral
convex function is proper. -/
theorem directionalDerivativeAt_isProper :
    (directionalDerivativeAt f x).IsProper := sorry

-- Proof sketch: clause (1) gives nonemptiness of the intrinsic subdifferential, then the exact
-- owner theorem `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
-- `Lemma_23_0_1` applies directly at the finite point `x`.
/-- Theorem 23.10 (4): the directional derivative at a finite point of a polyhedral convex
function is the support function of the intrinsic subdifferential at that point. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt (d : E) :
    directionalDerivativeAt f x d = δᵛ(d | ∂ f at x) :=
  sorry

end Function.HasPolyhedralEpigraph

end
