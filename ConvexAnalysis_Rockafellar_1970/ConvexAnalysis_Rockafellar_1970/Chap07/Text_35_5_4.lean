import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1

noncomputable section

section

open Function

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]

local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) := WithBotTop.instSMul

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.4 is a pure existence statement: some saddle-function on `𝕜 × 𝕜`
  has a finite product point where a nonzero mixed-direction directional derivative fails to
  exist.
- `core/canonical`: the project already owns the relevant notions as
  `Bifunction.IsSaddle 𝕜 K`, the effective-domain owner `dom(uncurry K)` together with
  the finite-value guard `(uncurry K) p ≠ ⊥`, and `Function.HasDirectionalDerivativeAt` for
  existence of a directional derivative.
- `bridge/view`: finiteness and directional differentiability are both surfaced directly on the
  canonical product-space owner `uncurry K`, avoiding a split slice-vs-product statement surface.

Domain-style sampling used here:
- `Bifunction.IsSaddle` from `Chap07.Definition33_0_1`;
- `dom(·)` / `mem_effectiveDomain` from `Chap01.Definition_4_4`;
- `Function.HasDirectionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- the nearby Chapter 35 finite-point theorem surfaces
  `Bifunction.isConvex_directionalDerivativeAt_second` and
  `Bifunction.directionalDerivativeAt_uncurry_second_eq_supportFunction_subdifferential2At`,
  which likewise record finiteness of `K u v` by `v ∈ dom(K u)` together with `K u v ≠ ⊥`.
- Layer target: `source-facing`, stated directly on canonical chapter owners without introducing a
  local counterexample package wrapper.
-/

-- Proof sketch: instantiate Rockafellar's counterexample by choosing a saddle bifunction on
-- `𝕜 × 𝕜` whose one-variable slices have the required saddle shape but whose mixed difference
-- quotient along some nonzero direction has no right limit at a finite product point.
/-- Text 35.5.4: there exists a saddle-function on `𝕜 × 𝕜` with a finite value at some point
where a nonzero mixed-direction directional derivative fails to exist.

Abstraction-layer decision audit for this theorem surface:
- Scalar/codomain layer: `K` is exposed at the chapter codomain owner `WithTopBot 𝕜` (not `EReal`)
  and keeps the chapter directional-derivative owner layer (`Field` + `LinearOrder`) required by
  `Function.HasDirectionalDerivativeAt`.
  The textbook real statement is recovered by specialization `𝕜 := ℝ`.
- Owner surface: finiteness and directional-derivative failure are both phrased on the same
  product-space owner `uncurry K`, using a single base point `p : 𝕜 × 𝕜` rather than separate
  coordinates.
- Topology layer: this item is not an ambient `closure`/`interior` theorem, but the
  nonexistence claim lives on the Chapter 23 filter-limit owner and must avoid vacuous
  non-Hausdorff/degenerate topologies. The theorem therefore keeps the primitive topological
  owners together with order-compatibility at both source and codomain:
  `TopologicalSpace 𝕜` + `OrderTopology 𝕜` and
  `TopologicalSpace (WithTopBot 𝕜)` + `OrderTopology (WithTopBot 𝕜)`.
-/
theorem exists_saddleFunction_finite_point_no_mixedDirectionalDerivative :
    ∃ K : 𝕜 → 𝕜 → WithTopBot 𝕜,
      Bifunction.IsSaddle 𝕜 K ∧
        ∃ p d : 𝕜 × 𝕜,
          p ∈ dom(uncurry K) ∧
            (uncurry K) p ≠ ⊥ ∧
            d ≠ 0 ∧
              ¬ ∃ L, HasDirectionalDerivativeAt (uncurry K) p d L :=
  sorry

end
