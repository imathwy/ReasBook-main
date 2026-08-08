import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {ι : Type v}
variable [AddCommGroup E] [Module ℝ E]

/-
Theorem 3.23 is `source-facing` at the Chapter 3 owner `extendedRealSubdifferential`. Domain sampling for the
weak max-rule API points to the following declarations:

* `is_subgradient_at` in `Definition_3_1` as the primitive predicate.
* `extendedRealSubdifferential` in `Definition_3_2` as the owner set-valued map.
* `convex_subdifferential` in `Definition_3_2` as the owner-level derived convexity needed to pass
  from the active union to its convex hull.
* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` as the matching canonical
  active-index subtype for pointwise suprema.

The primitive data here is only the ambient extendedRealSubdifferential of the supremum; the active-index
collection at `x` is derived data, so the public statement keeps it inline as the subtype
`{i // f i x = iSup fun j ↦ f j x}` instead of introducing a parallel `activeIndices` wrapper. The
theorem stays directly on the owner declaration from `Definition_3_2` rather than depending on the
later strong-dual bridge/view files: the weak inclusion itself is purely algebraic and needs no
topological dual packaging. The textbook properness and convexity hypotheses are ambient for the
convex-calculus context, but this weak inclusion already holds for the owner `extendedRealSubdifferential`
without additional assumptions, so the API stays on that minimal canonical statement.
-/
recall extendedRealSubdifferential
recall convex_subdifferential

-- Proof sketch: if `g ∈ ∂ fᵢ(x)` and `f i x = ⨆ j, f j x`, then for every `y` we have
-- `⨆ j, f j y ≥ f i y ≥ f i x + g (y - x) = (⨆ j, f j x) + g (y - x)`, so
-- `g ∈ ∂ (fun y ↦ ⨆ j, f j y) x`. Hence the union of the active subdifferentials is contained in
-- the ambient extendedRealSubdifferential. Since every extendedRealSubdifferential is convex, the convex hull of that
-- union is contained there as well.
/-- Theorem 3.23: weak maximum rule of extendedRealSubdifferential calculus. For the pointwise supremum of an
arbitrary family of extended-real-valued functions, the convex hull of the active branch
subdifferentials at `x` is contained in the extendedRealSubdifferential of the supremum at `x`. -/
theorem convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup
    (f : ι → E → EReal) (x : E) :
    convexHull ℝ (⋃ i : {i : ι // f i x = ⨆ j : ι, f j x}, extendedRealSubdifferential (f i) x) ⊆
      extendedRealSubdifferential (fun y ↦ ⨆ i : ι, f i y) x := sorry

end
