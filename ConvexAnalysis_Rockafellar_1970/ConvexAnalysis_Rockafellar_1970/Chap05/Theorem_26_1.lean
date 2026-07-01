import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_26_1

noncomputable section

open scoped Gradient SetRel Rockafellar

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 26.1 states that a closed proper convex function has a single-valued
  subdifferential mapping exactly when it is essentially smooth, and then identifies that mapping
  with the gradient on the intrinsic domain owner `riDom(f)`; the textbook
  `interior (dom(f))` phrasing is kept as a bridge view.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallySmooth`, the intrinsic graph relation `subdifferentialGraph f`, the
  single-valuedness owner `(subdifferentialGraph f).RightUnique`, the
  projection-criterion bridge `SetRel.injOn_fst_iff`, and the pointwise owner
  `subdifferentialAt f x`.
- `bridge/view`: the source phrase “`df` is single-valued” is owned by
  `(subdifferentialGraph f).RightUnique`; the graph condition
  `Set.InjOn Prod.fst (subdifferentialGraph f)` is only
  the coordinate-projection reformulation supplied by `Lemma_26_1`.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `subdifferentialGraph` from `Definition_5_24_3`;
- `SetRel.RightUnique` from `Definition_26_0_1`;
- `SetRel.injOn_fst_iff` from `Lemma_26_1`;
- `Function.subdifferentialWithinAt_eq_singleton_gradient` from `Theorem_25_1`,
  together with `Function.mem_subdifferentialAt_of_tendsto` from `Theorem_5_24_7`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f`;
- primitive owner surface: the subdifferential graph `subdifferentialGraph f`, its
  single-valuedness owner `(subdifferentialGraph f).RightUnique`, and the owner
  class
  `f.IsEssentiallySmooth`;
- derived API: source-facing bridge consequences on `Function.subdifferentialAt f x` inside and
  outside `interior (dom(f))`, derived from the intrinsic pointwise `riDom(f)` owner layer.

Layer target:
- the general forward theorems
  `_root_.rightUnique_subdifferentialGraph_of_isEssentiallySmooth` and
  `_root_.injOn_fst_subdifferentialGraph_of_isEssentiallySmooth`: `bridge/view` consequences
  keeping the genuinely ambient-general direction on the intrinsic canonical owner
  `subdifferentialGraph`;
- `_root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth` and
  `_root_.injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth`: `source-facing`
  finite-dimensional equivalences, matching Rockafellar's `ℝⁿ` theorem and the Chapter 25
  finite-dimensional converse differentiability owner;
- the four `Function` theorems below: `bridge/view` companions unpacking the source sentence back
  to the Fréchet-Riesz graph and then to pointwise vector-valued fibers
  `Function.subdifferentialAt f x`.

Scalar-layer note:
- this file remains at scalar `ℝ` because the source-facing owner
  `Function.IsEssentiallySmooth` is currently defined via the finite real branch `f.realBranch`
  and gradient clauses in `Definition_26_1_1`;
- the intrinsic graph codomain owner remains `StrongDual ℝ E` through `gph∂(f)` because
  `subdifferentialGraph` in `Definition_5_24_3` is canonically dual-valued; vector/primal-codomain
  surfaces below are explicit bridge views.
-/

/-- General forward clause of Theorem 26.1 on the intrinsic owner: essential smoothness forces the
subdifferential graph to be right-unique. -/
theorem rightUnique_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    (gph∂(f)).RightUnique := by
  sorry

/-- General projection-form forward clause of Theorem 26.1 on the intrinsic owner: essential
smoothness forces injectivity of `Prod.fst` on the subdifferential graph. -/
  theorem injOn_fst_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    Set.InjOn Prod.fst (gph∂(f)) := by
  exact (SetRel.rightUnique_iff_injOn_fst (gph∂(f))).1
    (rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Theorem 26.1, canonical intrinsic graph-owner form in the source finite-dimensional ambient:
for a closed proper convex function, the subdifferential mapping is single-valued exactly when the
function is essentially smooth. The source phrase “`df` is single-valued” is expressed through
the canonical owner `(subdifferentialGraph f).RightUnique`. -/
theorem rightUnique_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (gph∂(f)).RightUnique ↔
      f.IsEssentiallySmooth := by
  sorry

/-- Dual-domain codomain bridge of Theorem 26.1 in finite dimension: for a closed proper convex
function on `StrongDual ℝ E`, right-uniqueness of the subdifferential graph with primal codomain
`E` is equivalent to essential smoothness. This is the intrinsic owner form matching the
dual-primal graph inversion surface used in Chapter 26 Legendre duality bridges. -/
theorem rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth
    {f : StrongDual ℝ E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (gph∂[E](f)).RightUnique ↔ f.IsEssentiallySmooth := by
  sorry

/-- Theorem 26.1, finite-dimensional projection-criterion companion: the source single-valuedness
clause is equivalently the injectivity of `Prod.fst` on the intrinsic graph relation
`subdifferentialGraph f`. -/
theorem injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    Set.InjOn Prod.fst (gph∂(f)) ↔
      f.IsEssentiallySmooth := by
  rw [← SetRel.rightUnique_iff_injOn_fst]
  exact rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

end FiniteDimensional

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function

private theorem rightUnique_functionSubdifferentialGraph_iff
    {f : E → WithTopBot ℝ} [CompleteSpace E] :
    (subdifferentialGraph f).RightUnique ↔
      (gph∂(f)).RightUnique := by
  sorry

/-- General Fréchet-Riesz forward clause of Theorem 26.1: in a real inner-product space,
essential smoothness forces right-uniqueness of the vector-valued subdifferential graph. -/
theorem rightUnique_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    (subdifferentialGraph f).RightUnique := by
  intro x xStar1 xStar2 hx1 hx2
  apply (InnerProductSpace.toDualMap ℝ E).injective
  have hx1Dual :
      x ~[gph∂(f)]
        (InnerProductSpace.toDualMap ℝ E xStar1) :=
    _root_.mem_subdifferentialGraph.mpr (Function.mem_subdifferentialGraph.mp hx1)
  have hx2Dual :
      x ~[gph∂(f)]
        (InnerProductSpace.toDualMap ℝ E xStar2) :=
    _root_.mem_subdifferentialGraph.mpr (Function.mem_subdifferentialGraph.mp hx2)
  exact (_root_.rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)
    hx1Dual hx2Dual

/-- General Fréchet-Riesz projection-form forward clause of Theorem 26.1: in a real
inner-product space, essential smoothness forces injectivity of `Prod.fst` on the vector-valued
subdifferential graph. -/
theorem injOn_fst_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    Set.InjOn Prod.fst (subdifferentialGraph f) := by
  exact (SetRel.rightUnique_iff_injOn_fst (subdifferentialGraph f)).1
    (rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Theorem 26.1, Fréchet-Riesz owner bridge form in the source finite-dimensional ambient:
single-valuedness of the vector-valued subdifferential graph is equivalent to essential
smoothness. -/
theorem rightUnique_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (subdifferentialGraph f).RightUnique ↔ f.IsEssentiallySmooth := by
  rw [rightUnique_functionSubdifferentialGraph_iff]
  exact _root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

/-- Theorem 26.1, finite-dimensional Fréchet-Riesz projection companion: the vector-valued
subdifferential graph is single-valued exactly when `Prod.fst` is injective on its graph. -/
theorem injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    Set.InjOn Prod.fst (subdifferentialGraph f) ↔ f.IsEssentiallySmooth := by
  rw [← SetRel.rightUnique_iff_injOn_fst]
  exact rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

end FiniteDimensional

section Pointwise

variable [CompleteSpace E]
variable {f : E → WithTopBot ℝ}

/-- Theorem 26.1, intrinsic pointwise clause: for an essentially smooth lower-semicontinuous
function, the vector-valued subdifferential at a point of `riDom(f)` is the singleton containing
the gradient of the canonical finite real branch `f.realBranch`. The convexity and properness
data are already part of `hess`. -/
theorem subdifferentialAt_eq_singleton_gradient_of_mem_riDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ riDom(f)) :
    subdifferentialAt f x = {∇ f.realBranch x} := by
  sorry

/-- Theorem 26.1, intrinsic complement clause: for an essentially smooth lower-semicontinuous
function, the vector-valued subdifferential is empty at every point outside `riDom(f)`. The
convexity and properness data are already part of `hess`. -/
theorem subdifferentialAt_eq_empty_of_not_mem_riDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∉ riDom(f)) :
    subdifferentialAt f x = ∅ := by
  sorry

/-- Source-facing bridge companion of Theorem 26.1: the intrinsic `riDom(f)` pointwise singleton
formula, restated on `interior (dom(f))` via `hess.riDom_eq_interior_dom`. -/
theorem subdifferentialAt_eq_singleton_gradient_of_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ interior (dom(f))) :
    subdifferentialAt f x = {∇ f.realBranch x} := by
  have hx' : x ∈ riDom(f) := by
    simpa [hess.riDom_eq_interior_dom] using hx
  exact subdifferentialAt_eq_singleton_gradient_of_mem_riDom hclosed hess hx'

/-- Source-facing bridge companion of Theorem 26.1: the intrinsic `riDom(f)` emptiness clause,
restated on the textbook ambient complement `x ∉ interior (dom(f))`. -/
theorem subdifferentialAt_eq_empty_of_not_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∉ interior (dom(f))) :
    subdifferentialAt f x = ∅ := by
  have hx' : x ∉ riDom(f) := by
    simpa [hess.riDom_eq_interior_dom] using hx
  exact subdifferentialAt_eq_empty_of_not_mem_riDom hclosed hess hx'

end Pointwise

end Function

end
