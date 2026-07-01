import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar Topology
open Set
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable (fSeq : ℕ → E → 𝕜) {C : Set E} (hC_open : IsRelativelyOpen 𝕜 C)
  (hf_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.8 starts with a relatively open convex set `C`, a sequence of
  convex functions on `C`, and pointwise convergence on a subset `C' ⊆ C` dense in `C`. It
  concludes existence of a convex pointwise limit on all of `C` together with local uniform
  convergence on `C`.
- `core/canonical`: the owner abstractions are the chapter owner
  `IsRelativelyOpen 𝕜 C`, `ConvexOn`, pointwise
  convergence `Tendsto (fun i ↦ f i x) atTop (𝓝 l)`, relative density written as `C' ⊆ C`
  together with `C ⊆ intrinsicClosure 𝕜 C'`, and mathlib's owner predicate
  `TendstoLocallyUniformlyOn`.
- `bridge/view`: Rockafellar's phrase "the limit exists and is finite" is rendered here by a
  `𝕜`-valued function `f : E → 𝕜` together with pointwise convergence to `f`.

Domain-style sampling used here:
- `IsRelativelyOpen 𝕜 C` (chapter owner surface for relative openness);
- `ConvexOn 𝕜 C`;
- `intrinsicClosure 𝕜` for the relative-density hypothesis `C' ⊆ C` and
  `C ⊆ intrinsicClosure 𝕜 C'`;
- `Tendsto ... atTop (𝓝 ...)` for pointwise convergence;
- `TendstoLocallyUniformlyOn` as the canonical owner for convergence on `C`.
- `NormedAddCommGroup`, `NormedSpace`, and `FiniteDimensional` for the ambient layer where
  Chapter 10's local-uniform convex convergence results are formulated.

Primitive data vs derived API:
- primitive inputs: the relative-openness owner `IsRelativelyOpen 𝕜 C`, the sequence `fSeq`,
  convexity of each `fSeq i`
  on `C`, a dense subset `C' ⊆ C`, and pointwise convergence on `C'`;
- derived API: existence of a `𝕜`-valued convex limit on `C` together with the owner predicate
  `TendstoLocallyUniformlyOn fSeq f atTop C`.

Layer target: `source-facing`, with the dense-subset theorem centered on the canonical locally
uniform owner and the pure pointwise conclusion kept only as a companion view.
-/

include hC_open hf_convex

-- Proof sketch: obtain local uniform Cauchy control from the dense-subset convergence assumptions,
-- hence pointwise Cauchy at every point of `C`. Define the `𝕜`-valued limit function by these
-- pointwise limits; convexity is preserved by
-- passing to the limit in the convexity inequality.
/-- Theorem 10.8 in canonical owner form: if a sequence of convex functions on a relatively open
convex set `C` has pointwise limits on a subset `C' ⊆ C` whose intrinsic closure contains `C`,
then there is a `𝕜`-valued convex function on `C` to which the sequence converges locally
uniformly on `C`. -/
theorem exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise
    {C' : Set E} (hC'_subset : C' ⊆ C) (hC'_dense : C ⊆ intrinsicClosure 𝕜 C')
    (hlimit_dense : ∀ x ∈ C', ∃ l : 𝕜, Tendsto (fun i ↦ fSeq i x) atTop (𝓝 l)) :
    ∃ f : E → 𝕜, ConvexOn 𝕜 C f ∧ TendstoLocallyUniformlyOn fSeq f atTop C := sorry

-- Proof sketch: apply the dense-subset theorem with `C' = C`. Then use uniqueness of limits in the
-- Hausdorff codomain `𝕜` to identify the produced limit with the prescribed pointwise limit `f`.
/-- Companion specialization of Theorem 10.8: if the pointwise limit on `C` is already specified
as a `𝕜`-valued function `f`, then `f` is convex on `C` and the convergence is locally uniform on
`C`. -/
theorem convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit
    {f : E → 𝕜} (hlimit : ∀ x ∈ C, Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x))) :
    ConvexOn 𝕜 C f ∧ TendstoLocallyUniformlyOn fSeq f atTop C := by
  obtain ⟨g, hg_convex, hg_tendsto⟩ :=
    exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise
      fSeq hC_open hf_convex Subset.rfl subset_intrinsicClosure (fun x hx ↦ ⟨f x, hlimit x hx⟩)
  have hgf : C.EqOn g f := fun x hx ↦
    tendsto_nhds_unique (hg_tendsto.tendsto_at hx) (hlimit x hx)
  exact ⟨hg_convex.congr hgf, hg_tendsto.congr_right hgf⟩

omit hC_open hf_convex

end
