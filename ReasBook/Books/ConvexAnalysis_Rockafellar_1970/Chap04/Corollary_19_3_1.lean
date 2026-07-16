import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Proposition_9_0_0_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.3.1 says that a linear image of a polyhedral convex function is
  again polyhedral convex, that the fiberwise infimum defining that image is attained whenever it
  is finite, and that precomposition with a linear map preserves polyhedral convexity.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.HasPolyhedralEpigraph` for function-side polyhedrality and `A ◁ f` for the
  textbook image function.
- `bridge/view`: the proof route passes through epigraph images and preimages together with the
  Chapter 2 bridge `Function.linearImageEpigraph_eq_epi_linearImage`.

Domain-style sampling used here:
- `Function.linearImage`;
- `Function.HasPolyhedralEpigraph`;
- `Set.IsPolyhedral.linear_image`;
- `Set.IsPolyhedral.linear_preimage`;
- `Function.linearImageEpigraph_eq_epi_linearImage`;
- `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom`.

Primitive data vs derived API:
- primitive inputs: a linear map `A` and a function with polyhedral epigraph;
- derived API: polyhedrality of `A ◁ f`, attainment of the finite value `(A ◁ f) y`, and
  polyhedrality of `g ∘ A`.

Ambient refinement:
- the image clauses only use the set-side owners `Set.IsPolyhedral.linear_image` and
  `Set.IsPolyhedral.isClosed` on epigraphs, so their public assumptions reduce to finite-
  dimensional Hausdorff topological modules over an ordered scalar field, not inner-product
  spaces;
- the preimage clause only uses `Set.IsPolyhedral.linear_preimage`, so it lives on ordinary scalar
  modules with no topological or finite-dimensional hypotheses.

Layer target: `source-facing` owner lemmas for `Function.HasPolyhedralEpigraph`,
stated directly in the chapter owners `A ◁ f` and `g ∘ A`.
-/

section LinearImage

namespace Function.HasPolyhedralEpigraph

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]
variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] [T2Space F]

private theorem linearImageEpigraph_isPolyhedral
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (Function.linearImageEpigraph A f).IsPolyhedral 𝕜 := by
  rw [Function.linearImageEpigraph_eq_image_epi]
  simpa using
    Set.IsPolyhedral.linear_image hf (A.prodMap LinearMap.id)

private theorem linearImageEpigraph_isClosed
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    IsClosed (Function.linearImageEpigraph A f) :=
  (linearImageEpigraph_isPolyhedral hf A).isClosed_of_finiteDimensional

/-- Corollary 19.3.1 (1): if `f` has polyhedral epigraph, then its image function `A ◁ f`
under a linear map `A : E → F` again has polyhedral epigraph. The textbook `R^n → R^m`
statement is the finite-dimensional Euclidean specialization of this owner-level theorem. -/
theorem linearImage
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (A ◁ f).HasPolyhedralEpigraph := by
  have hImage : (Function.linearImageEpigraph A f).IsPolyhedral 𝕜 :=
    linearImageEpigraph_isPolyhedral hf A
  have hImage_closed : IsClosed (Function.linearImageEpigraph A f) :=
    linearImageEpigraph_isClosed hf A
  change (epi (A ◁ f)).IsPolyhedral 𝕜
  simpa [Function.linearImageEpigraph_eq_epi_linearImage A f hImage_closed] using hImage

/-- Corollary 19.3.1 (2): whenever the value of `A ◁ f` at `y` is finite, the infimum defining
`(A ◁ f) y` is attained by some `x` with `A x = y`. -/
theorem linearImage_attains_of_ne_bot_of_mem_dom
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) (y : F)
    (hy_dom : y ∈ dom (A ◁ f)) (hy_ne_bot : (A ◁ f) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ f x = (A ◁ f) y := by
  have hImage_closed : IsClosed (Function.linearImageEpigraph A f) :=
    linearImageEpigraph_isClosed hf A
  exact
    Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom
      A f y hImage_closed hy_dom hy_ne_bot

end Function.HasPolyhedralEpigraph

end LinearImage

section LinearPreimage

namespace Function.HasPolyhedralEpigraph

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]

/-- Corollary 19.3.1 (3): if `g` has polyhedral epigraph, then the pullback `g ∘ A` along a
linear map `A : E → F` again has polyhedral epigraph. This preimage clause lives already on
the scalar-module owner layer, with no topological or finite-dimensional hypotheses. -/
theorem comp_linearMap
    {g : F → WithTopBot 𝕜} (hg : g.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (g ∘ A).HasPolyhedralEpigraph := by
  change (epi (g ∘ A)).IsPolyhedral 𝕜
  simpa [epi_univ_eq_setOf_le, Function.comp, LinearMap.prodMap_apply] using
    Set.IsPolyhedral.linear_preimage hg (A.prodMap LinearMap.id)

end Function.HasPolyhedralEpigraph

end LinearPreimage
