import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 33.1.3 studies the second-variable partial Fenchel conjugate of a
  bifunction and the resulting slice reconstruction formula.
- `core/canonical`: the chapter already owns that partial conjugate as `Bifunction.lowerPairing`.
  The graph-polyhedral clauses `(1)` to `(3)` should therefore remain on the same paired-space
  owner `lowerPairing F : U → XStar → WithTopBot 𝕜`, using Chapter 19 only as a thin
  conjugate-polyhedral bridge on ordinary pairings. The reconstruction branch `(4)` already lives
  on that paired layer.
- `bridge/view`: the raw owner remains `lowerPairing F`; source-facing theorem surfaces use the
  Chapter 33 slice-conjugate notation when elaboration is unambiguous, and otherwise use the
  equivalent explicit conjugate form `(F u)⋆ x⋆`.

Domain-style sampling used here:
- `Bifunction.lowerPairing` and `Bifunction.lowerPairing_apply` from `Defn_34_2`;
- `Bifunction.lowerPairing_isConcaveConvex_of_uncurry_isConvex` from `Lemma33_0_22`;
- `Function.HasPolyhedralEpigraph.convexConjugate` from `Theorem_19_2`, now on arbitrary pairing
  spaces;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from `Theorem_12_2`, combined with
  the closed-proper-convex owner from `Text_12_3_6` for slice reconstruction.

Primitive data vs derived API:
- primitive source data: `F : U → X → WithTopBot 𝕜`;
- graph-polyhedral owner abstraction: the lower representative `lowerPairing F`, surfaced here as
  the slice-conjugate maps `x⋆ ↦ ⟪F u, x⋆⟫ᶠ`;
- reconstruction owner abstraction: the same `lowerPairing F`, surfaced pointwise as
  `⟪F u, xStar⟫ᶠ`;
- derived API here: polyhedrality and concavity of the slice pairings, and the paired
  slice-reconstruction formulas.

Layer target: `source-facing`, on the paired Chapter 33 owner `lowerPairing F`.
-/

section SliceConjugatePolyhedral

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar] [HasPairing X XStar 𝕜]
variable {F : U → X → WithTopBot 𝕜}

-- Proof sketch: fix `u`; precompose `Function.uncurry F` with the affine-coordinate inclusion
-- `x ↦ (u, x)` to obtain polyhedrality of the slice `F u`, then apply Theorem 19.2 to that
-- slice.
/-- Corollary33.1.3 (1): if the graph function of `F` has polyhedral epigraph, then for each `u`
the Chapter 33 slice-conjugate map `x⋆ ↦ ⟪F u, x⋆⟫ᶠ` has polyhedral epigraph. -/
theorem sliceConjugate_hasPolyhedralEpigraph_of_graphPolyhedral
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph) (u : U) :
    (fun xStar : XStar ↦ ⟪F u, xStar⟫ᶠ).HasPolyhedralEpigraph := sorry

end SliceConjugatePolyhedral

section SliceConjugateConcavity

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [HasPairing X XStar 𝕜]
variable {F : U → X → WithTopBot 𝕜}

-- Proof sketch: each negated slice is polyhedral, hence convex; concavity of the original slice
-- is exactly convexity of its negation.
/-- Primitive owner form for Corollary 33.1.3 (3): if each negated slice
`u ↦ -⟪F u, x⋆⟫ᶠ` has polyhedral epigraph, then each slice
`u ↦ ⟪F u, x⋆⟫ᶠ` is concave. -/
theorem sliceConjugate_isConcave_of_negSliceConjugatePolyhedral
    (hneg_poly : ∀ xStar : XStar,
      (fun u : U ↦ -⟪F u, xStar⟫ᶠ).HasPolyhedralEpigraph)
    (xStar : XStar) :
    (fun u : U ↦ ⟪F u, xStar⟫ᶠ).IsConcave 𝕜 := sorry

end SliceConjugateConcavity

section NegativeSliceConjugatePolyhedral

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [HasPairing X XStar 𝕜]
variable {F : U → X → WithTopBot 𝕜}

-- Proof sketch: use the polyhedral graph hypothesis on `F` to build the auxiliary polyhedral
-- function appearing in the proof of Theorem 33.1, then apply Corollary 19.3.1 to the linear
-- image that gives `u ↦ -⟪F u, x⋆⟫ᶠ`.
/-- Corollary33.1.3 (2): if the graph function of `F` has polyhedral epigraph, then for each
`x⋆` the negated paired-space slice `u ↦ -⟪F u, x⋆⟫ᶠ` has polyhedral epigraph. -/
theorem neg_sliceConjugate_hasPolyhedralEpigraph_of_graphPolyhedral
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph) (xStar : XStar) :
    (fun u : U ↦ -⟪F u, xStar⟫ᶠ).HasPolyhedralEpigraph := sorry

-- Proof sketch: apply the previous clause to obtain polyhedrality of the negated slice, use that
-- polyhedral functions are convex, and then rewrite convexity of the negation as concavity of the
-- original slice.
/-- Corollary33.1.3 (3): if the graph function of `F` has polyhedral epigraph, then for
each `x⋆` the paired-space slice `u ↦ ⟪F u, x⋆⟫ᶠ` is concave. -/
theorem sliceConjugate_isConcave_of_graphPolyhedral
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph) (xStar : XStar) :
    (fun u : U ↦ ⟪F u, xStar⟫ᶠ).IsConcave 𝕜 :=
  sliceConjugate_isConcave_of_negSliceConjugatePolyhedral
    (fun y ↦ neg_sliceConjugate_hasPolyhedralEpigraph_of_graphPolyhedral hF_poly y) xStar

end NegativeSliceConjugatePolyhedral

section SliceReconstruction

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable {F : U → X → WithTopBot 𝕜}

-- Proof sketch: apply slice-wise biconjugacy to each closed proper convex slice `F u`, then
-- rewrite the slice conjugate as the source-facing slice notation `x⋆ ↦ ⟪F u, x⋆⟫ᶠ`.
/-- Primitive owner form for Corollary 33.1.3 (4): a closed proper convex slice `F u` is
recovered from its slice conjugate by the Fenchel supremum formula. -/
theorem slice_eq_iSup_pairing_sub_sliceConjugate_of_slice_closedProperConvex
    (u : U) (hslice_closedProper : IsClosedProperConvex[𝕜] (F u)) (x : X) :
    F u x = ⨆ xStar : XStar, ⟪x, xStar⟫ₚ - ⟪F u, xStar⟫ᶠ := sorry

end SliceReconstruction

section ReconstructionFromGraphPolyhedral

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable {F : U → X → WithTopBot 𝕜}

-- Proof sketch: for fixed `u ∈ dom F`, the graph polyhedrality hypothesis gives polyhedrality of
-- the slice `F u`, hence closedness and convexity. The graph-proper hypothesis rules out `⊥`
-- on every slice, while `u ∈ dom F` supplies a finite slice point. Thus `F u` is closed proper
-- convex, so the slice-wise reconstruction theorem applies.
/-- Corollary33.1.3 (4): if the graph function of `F` has polyhedral epigraph and is proper, then
every slice with `u ∈ dom F` is recovered from its slice conjugate by the Fenchel supremum
formula. -/
theorem slice_eq_iSup_pairing_sub_sliceConjugate_of_graphPolyhedral_of_proper_of_mem_dom
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph)
    (hF_proper : (Function.uncurry F).IsProper)
    {u : U} (hu : u ∈ dom F) (x : X) :
    F u x = ⨆ xStar : XStar, ⟪x, xStar⟫ₚ - ⟪F u, xStar⟫ᶠ := sorry

end ReconstructionFromGraphPolyhedral

end Bifunction
