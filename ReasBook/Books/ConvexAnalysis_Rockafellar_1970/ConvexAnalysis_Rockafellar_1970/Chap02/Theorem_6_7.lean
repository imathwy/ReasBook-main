import Mathlib.Analysis.Normed.Module.FiniteDimension
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_18

-- Declarations for this item will be appended below by the statement pipeline.

section

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.7 states that inverse images of convex sets under a linear map
  preserve relative interior and intrinsic closure, provided the inverse image of the relative
  interior is nonempty. The ordinary-closure clause is a finite-dimensional bridge corollary.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, `intrinsicInterior 𝕜`,
  `intrinsicClosure 𝕜`, `closure`,
  `Set.preimage`, the affine-section owner theorems on `AffineSubspace`, and the linear-image
  owner theorem `Convex.intrinsicInterior_linear_image`.
- `bridge/view`: Rockafellar's `ri C` is represented by `intrinsicInterior 𝕜 C`, the textbook
  inverse image `A⁻¹ C` is `A ⁻¹' C`, and the graph section is expressed canonically by the graph
  submodule `LinearMap.graph A` viewed as an affine subspace.
- Domain-style sampling used here: `AffineSubspace.intrinsicInterior_inter_eq`,
  `AffineSubspace.intrinsicClosure_inter_eq`, `Convex.intrinsicInterior_linear_image`,
  `AffineEquiv.image_intrinsicClosure`, `ri_prod_eq`, and
  `intrinsicClosure_prod_eq`.
- Primitive data vs derived API: the primitive owner data is only the convexity proof `hC` and the
  linear map `A`; the relative-interior and closure identities for inverse images are derived API
  and belong on the existing `Convex` owner surface rather than in a new graph wrapper.
- Best owner abstraction: the file stays `source-facing` in `namespace Convex`, but the proofs are
  refined to the existing graph/image/intersection owner abstractions instead of any new public
  graph-packaged declaration.
-/

namespace Convex

open Topology
open scoped Rockafellar

section Helpers

variable
    {𝕜 E F : Type*}
    [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {C : Set F}

private theorem intrinsicInterior_univ_eq_univ :
    ri[𝕜]((Set.univ : Set E)) = Set.univ := by
  refine subset_antisymm intrinsicInterior_subset ?_
  simpa using
    (interior_subset_intrinsicInterior :
      interior (Set.univ : Set E) ⊆ ri[𝕜]((Set.univ : Set E)))

private abbrev graphEmbedding (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E × F :=
  LinearMap.id.prod A

private abbrev graphAffineSubspace (A : E →ₗ[𝕜] F) : AffineSubspace 𝕜 (E × F) :=
  (LinearMap.graph A).toAffineSubspace

private abbrev graphStrip (E : Type*) (S : Set F) : Set (E × F) :=
  Set.univ ×ˢ S

private theorem graphEmbedding_injective (A : E →ₗ[𝕜] F) :
    Function.Injective (graphEmbedding A) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

private theorem graphEmbedding_image_preimage (A : E →ₗ[𝕜] F) (S : Set F) :
    graphEmbedding A '' (A ⁻¹' S) =
      ((graphAffineSubspace A : AffineSubspace 𝕜 (E × F)) : Set (E × F)) ∩ graphStrip E S := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [graphEmbedding, graphAffineSubspace, Submodule.mem_toAffineSubspace,
        LinearMap.mem_graph_iff]
    · simpa [graphStrip] using hx
  · rintro ⟨hpM, hpS⟩
    have hpgraph : p.2 = A p.1 := by
      simpa [graphAffineSubspace, Submodule.mem_toAffineSubspace, LinearMap.mem_graph_iff] using hpM
    refine ⟨p.1, ?_, ?_⟩
    · simpa [graphStrip, hpgraph] using hpS.2
    · ext <;> simp [graphEmbedding, hpgraph]

private theorem graphSection_intrinsicInterior_nonempty (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    ((graphAffineSubspace A : Set (E × F)) ∩ ri[𝕜](graphStrip E C)).Nonempty := by
  rcases hri with ⟨x, hx⟩
  refine ⟨graphEmbedding A x, ?_, ?_⟩
  · simp [graphEmbedding, graphAffineSubspace, Submodule.mem_toAffineSubspace,
      LinearMap.mem_graph_iff]
  · simpa
      [graphEmbedding, graphStrip, intrinsicInterior_univ_eq_univ, ri_prod_eq] using
      show (x, A x) ∈ ri[𝕜]((Set.univ : Set E)) ×ˢ ri[𝕜](C) from
        ⟨by simp [intrinsicInterior_univ_eq_univ], hx⟩

private theorem eq_of_graphEmbedding_image_eq (A : E →ₗ[𝕜] F) {s t : Set E}
    (h : graphEmbedding A '' s = graphEmbedding A '' t) :
    s = t := by
  ext x
  constructor
  · intro hx
    have hx' : graphEmbedding A x ∈ graphEmbedding A '' t := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, hyx⟩
    exact graphEmbedding_injective A hyx ▸ hy
  · intro hx
    have hx' : graphEmbedding A x ∈ graphEmbedding A '' s := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, hyx⟩
    exact graphEmbedding_injective A hyx ▸ hy

end Helpers

section Main

section RelativeInteriorPreimage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable {C : Set F}

/-- Theorem 6.7 (1): if `A : E →ₗ[𝕜] F` is linear, `C ⊆ F` is convex, and the preimage of the
relative interior of `C` is nonempty, then the relative interior of `A ⁻¹' C` is exactly the
preimage of `ri[𝕜](C)`. -/
-- Proof sketch: embed `E` into `E × F` by the graph map `x ↦ (x, A x)`, so that the image of
-- `A ⁻¹' C` is the affine section of `Set.univ ×ˢ C` cut out by the graph of `A`. Apply
-- Corollary 6.5.1 to that affine section, use Text 6.18 to simplify the product relative
-- interior, and then pull the resulting equality back along the injective graph embedding.
theorem intrinsicInterior_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    ri[𝕜](A ⁻¹' C) = A ⁻¹' (ri[𝕜](C)) := by
  let b := graphEmbedding A
  let m := graphAffineSubspace A
  let d : Set (E × F) := graphStrip E C
  have himage (S : Set F) : b '' (A ⁻¹' S) = (m : Set (E × F)) ∩ graphStrip E S := by
    simpa [b, m] using graphEmbedding_image_preimage A S
  have hdri : ((m : Set (E × F)) ∩ ri[𝕜](d)).Nonempty := by
    simpa [d] using
      graphSection_intrinsicInterior_nonempty A hri
  have hsection :
      ri[𝕜]((m : Set (E × F)) ∩ d) = (m : Set (E × F)) ∩ ri[𝕜](d) :=
    m.intrinsicInterior_inter_eq ((convex_univ : Convex 𝕜 (Set.univ : Set E)).prod hC) hdri
  have himage_eq :
      b '' (ri[𝕜](A ⁻¹' C)) = b '' (A ⁻¹' (ri[𝕜](C))) := by
    calc
      b '' (ri[𝕜](A ⁻¹' C)) = ri[𝕜](b '' (A ⁻¹' C)) := by
        symm
        simpa using (hC.linear_preimage A).intrinsicInterior_linear_image b
      _ = ri[𝕜]((m : Set (E × F)) ∩ d) := by
        rw [himage C]
      _ = (m : Set (E × F)) ∩ ri[𝕜](d) := hsection
      _ = (m : Set (E × F)) ∩ graphStrip E (ri[𝕜](C)) := by
        simp [d, graphStrip, intrinsicInterior_univ_eq_univ]
      _ = b '' (A ⁻¹' (ri[𝕜](C))) :=
        (himage (ri[𝕜](C))).symm
  exact eq_of_graphEmbedding_image_eq A <| by
    simpa [b] using himage_eq

end RelativeInteriorPreimage

section ClosurePreimage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable {C : Set F}

/-- Theorem 6.7 (2), intrinsic owner form: inverse images of convex sets under a linear map
preserve intrinsic closure when the preimage of the relative interior is nonempty. -/
theorem intrinsicClosure_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    cl[𝕜](A ⁻¹' C) = A ⁻¹' cl[𝕜](C) := by
  let b := graphEmbedding A
  let m := graphAffineSubspace A
  let d : Set (E × F) := graphStrip E C
  have hb_inj : Function.Injective b := by
    simpa [b] using graphEmbedding_injective A
  have hb_closed := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hb_inj)
  have himage (S : Set F) : b '' (A ⁻¹' S) = (m : Set (E × F)) ∩ graphStrip E S := by
    simpa [b, m] using graphEmbedding_image_preimage A S
  have hdri : ((m : Set (E × F)) ∩ ri[𝕜](d)).Nonempty := by
    simpa [d] using
      graphSection_intrinsicInterior_nonempty A hri
  have hsection :
      closure ((m : Set (E × F)) ∩ d) = (m : Set (E × F)) ∩ closure d :=
    m.closure_inter_eq ((convex_univ : Convex 𝕜 (Set.univ : Set E)).prod hC) hdri
  have himage_eq :
      b '' closure (A ⁻¹' C) = b '' (A ⁻¹' closure C) := by
    calc
      b '' closure (A ⁻¹' C) = closure (b '' (A ⁻¹' C)) := by
        symm
        simpa using hb_closed.isClosedMap.closure_image_eq_of_continuous hb_closed.continuous
          (A ⁻¹' C)
      _ = closure ((m : Set (E × F)) ∩ d) := by
        rw [himage C]
      _ = (m : Set (E × F)) ∩ closure d := hsection
      _ = (m : Set (E × F)) ∩ graphStrip E (closure C) := by
        simp [d, graphStrip, closure_prod_eq]
      _ = b '' (A ⁻¹' closure C) := (himage (closure C)).symm
  have hclosure :
      closure (A ⁻¹' C) = A ⁻¹' closure C :=
    eq_of_graphEmbedding_image_eq A <| by
      simpa [b] using himage_eq
  simpa [intrinsicClosure_eq_closure 𝕜] using hclosure

/-- Theorem 6.7 (2), ambient-closure bridge core: in finite-dimensional spaces, inverse images of
convex sets under a linear map preserve ordinary closure. -/
theorem closure_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    closure (A ⁻¹' C) = A ⁻¹' closure C := by
  simpa [intrinsicClosure_eq_closure 𝕜] using
    intrinsicClosure_linear_preimage hC A hri

end ClosurePreimage

end Main

end Convex

end
