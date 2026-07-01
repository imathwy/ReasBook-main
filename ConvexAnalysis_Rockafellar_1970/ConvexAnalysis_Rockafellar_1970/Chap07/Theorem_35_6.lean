import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1

noncomputable section

universe u v

open Function Set

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace V] [AddCommMonoid V] [SMul 𝕜 V]

local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) := WithBotTop.instSMul

variable {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
variable {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 35.6 says that at every interior point of a product domain where
  an extended-valued bifunction is concave in the first variable and convex in the second, the mixed
  directional derivative exists, is finite, is positively homogeneous and concave-convex as a
  function of the direction pair, and splits as the sum of the two partial directional
  derivatives.
- `core/canonical`: the directional-derivative owners are already
  `Function.HasDirectionalDerivativeAt` and `Function.directionalDerivativeAt`.
- `bridge/view`: the theorem is stated directly on `uncurry K`, so no separate
  mixed-direction derivative package is introduced.

Domain-style sampling used here:
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- product-topology interior on `C ×ˢ D` together with the additive/scalar-action layer on `U`, `V`
  needed to form the directional rays `u + t • u'` and `v + t • v'`;
- `Bifunction.isConvex_neg_directionalDerivativeAt_first`;
- `Bifunction.isConvex_directionalDerivativeAt_second`;
- `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point`;
- `Bifunction.IsConcaveConvex`.

Primitive data vs derived API:
- primitive source data: the bifunction `K : U → V → WithTopBot 𝕜`, the domain sets `C`, `D`,
  the slice-wise concavity/convexity hypotheses, and the interior base-point condition
  `(u, v) ∈ interior (C ×ˢ D)`, and the direction pair `(u', v')`;
- primitive owner conclusion: existence of the mixed directional derivative with the additive
  partial-derivative formula;
- derived API: the value-level equality, pointwise finiteness, positive homogeneity, and
  concave-convexity of the direction map.

Layer target: `source-facing`, expressed through the existing Chapter 23 directional-derivative
owners and the Chapter 33 concave-convex owner.

Scalar/codomain boundary:
- this file is surfaced at the same generic codomain/scalar layer already used by the Chapter 23
  directional-derivative owners:
  `K : U → V → WithTopBot 𝕜` with right-ray limits along `𝓝[>] (0 : 𝕜)`;
- no local `ℝ`-specific codomain bridge (`toWithTopBot`) remains on theorem surfaces.

Ambient-owner canonicalization:
- the theorem surface keeps the same product-interior source semantics at the minimal topological
  scalar-action layer (`[TopologicalSpace] [AddCommMonoid] [SMul 𝕜 ·]`) needed for directional-ray
  expressions and product-domain interior;
- the directional-derivative owner itself remains `Function.HasDirectionalDerivativeAt` /
  `Function.directionalDerivativeAt`, so no new mixed-direction owner is introduced;
- no norm, inner product, or finite-dimensional structure appears in the primitive data or the
  derived owner conclusions below, so those stronger assumptions are removed from the public API;
- the source's Euclidean spaces are represented here by arbitrary topological `𝕜`-scalar-action
  spaces rather
  than by a coordinate model.
-/

-- Proof sketch: localize around `(u, v)` using the interior-point hypothesis in `C ×ˢ D`,
-- decompose the mixed difference quotient into the first partial quotient plus the shifted second
-- partial quotient, and compare the second term with the second partial directional derivative via
-- convexity in the second variable. Repeating with upper/lower roles exchanged gives the matching
-- bound, hence existence and the additive formula.
/-- Theorem 35.6: at every interior point `(u, v)` of a product domain on which `K` is
concave in the first variable and convex in the second, the mixed directional derivative of
`uncurry K` exists and is the sum of the two intrinsic slice-directional derivatives
`(K · v)'(u; u')` and `(K u)'(v; v')`, rendered by the chapter owner
`Function.directionalDerivativeAt`. -/
theorem hasDirectionalDerivativeAt_uncurry_eq_add_partial
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (u', v')
      (directionalDerivativeAt (K · v) u u' +
        directionalDerivativeAt (K u) v v') := sorry

-- Proof sketch: evaluate the canonical limit-valued owner `directionalDerivativeAt` at the limit
-- supplied by `hasDirectionalDerivativeAt_uncurry_eq_add_partial`.
/-- The mixed directional derivative at an interior saddle point equals the sum of the two
partial directional derivatives. -/
theorem directionalDerivativeAt_uncurry_eq_add_partial
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (u', v') =
      directionalDerivativeAt (K · v) u u' +
        directionalDerivativeAt (K u) v v' := sorry

-- Proof sketch: combine the additive formula with the one-variable Chapter 23 finiteness results
-- for the concave first-variable slice derivative `directionalDerivativeAt (K · v) u` and convex
-- second-variable slice derivative `directionalDerivativeAt (K u) v`; each partial directional
-- derivative is finite, hence so is their sum.
/-- At an interior saddle point, the mixed directional derivative is finite in every direction. -/
theorem directionalDerivativeAt_uncurry_ne_bot_ne_top
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (u', v') ≠ ⊥ ∧
      directionalDerivativeAt (uncurry K) (u, v) (u', v') ≠ ⊤ := sorry

-- Proof sketch: use the additive formula together with positive homogeneity of the two intrinsic
-- slice directional-derivative maps `directionalDerivativeAt (K · v) u` and
-- `directionalDerivativeAt (K u) v` from the one-variable Chapter 23 theory, then rewrite the
-- common scalar action on `(u', v')` as simultaneous scaling of the two summands.
/-- At an interior saddle point, the mixed directional-derivative map is positively homogeneous in
the direction pair. -/
theorem positivelyHomogeneous_directionalDerivativeAt_uncurry
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    :
    (directionalDerivativeAt (uncurry K) (u, v)).PositivelyHomogeneous 𝕜 := sorry

-- Proof sketch: for fixed `v'`, the additive formula reduces the first-variable slice of the
-- mixed-direction map to the intrinsic first slice derivative
-- `u' ↦ directionalDerivativeAt (K · v) u u'` plus a constant, so it is concave by the
-- one-variable concave analogue of Chapter 23. For fixed `u'`, the second-variable slice
-- similarly reduces to `v' ↦ directionalDerivativeAt (K u) v v'` plus a constant, hence is convex
-- by Theorem 23.1. These two slice statements are exactly the Chapter 33 whole-space
-- concave-convex owner.
/-- At an interior saddle point, the mixed directional-derivative map is concave-convex in the
direction variables. -/
theorem isConcaveConvex_directionalDerivativeAt_uncurry
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    :
    IsConcaveConvex 𝕜
      (fun u' v' ↦ directionalDerivativeAt (uncurry K) (u, v) (u', v')) := sorry

end

end Bifunction
