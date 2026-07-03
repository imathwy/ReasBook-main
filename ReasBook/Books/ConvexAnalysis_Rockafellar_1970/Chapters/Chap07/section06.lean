import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_6_1 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (1): for a convex function with `dom(f) ⊆ riDom[𝕜](f)`, the
relative interior `ri[𝕜]({x | f x ≤ α})` of the closed `α`-sublevel set is exactly the strict
`α`-sublevel set whenever that strict sublevel set is nonempty. -/
theorem intrinsicInterior_closedSublevel_eq_openSublevel (hf : f.IsConvex 𝕜) (α : 𝕜)
    (hdom_subset_riDom : dom(f) ⊆ riDom[𝕜](f))
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    ri[𝕜]({x : E | f x ≤ α}) = {x : E | f x < α} := by
  calc
    ri[𝕜]({x : E | f x ≤ α}) = riDom[𝕜](f) ∩ {x : E | f x < α} :=
      hf.intrinsicInterior_closedSublevel_eq_riDom_inter_openSublevel α hα
    _ = {x : E | f x < α} := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        refine ⟨hdom_subset_riDom ?_, hx⟩
        rw [mem_effectiveDomain]
        exact lt_trans hx (WithTopBot.coe_lt_top α)

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (2), ambient-closure primitive bridge: if a convex function has nonempty
strict `α`-sublevel set and closed `α`-sublevel set, then the closure of the strict `α`-sublevel
set is the closed `α`-sublevel set. -/
theorem closure_openSublevel_eq_closedSublevel_of_isClosed
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (hsublevel_closed : IsClosed {x : E | f x ≤ α})
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    closure {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  calc
    closure {x : E | f x < α} = {x : E | cl(f) x ≤ α} := by
      simpa using hf.closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα
    _ = closure {x : E | f x ≤ α} := by
      simpa using (hf.closure_closedSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα).symm
    _ = {x : E | f x ≤ α} := hsublevel_closed.closure_eq

/-- Corollary 7.6.1 (2), ambient-closure lower-semicontinuous bridge: if a lower semicontinuous
convex function has nonempty strict `α`-sublevel set, then the closure of the strict `α`-sublevel
set is the closed `α`-sublevel set. -/
theorem closure_openSublevel_eq_closedSublevel
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
    (hf_lsc : LowerSemicontinuous f)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    closure {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  calc
    closure {x : E | f x < α} = {x : E | cl(f) x ≤ α} := by
      simpa using hf.closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα
    _ = {x : E | f x ≤ α} := by
      simp [lowerSemicontinuousHull_eq_self hf_lsc]

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [OrderTopology 𝕜]
  [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (2), intrinsic-closure primitive form. -/
theorem intrinsicClosure_openSublevel_eq_closedSublevel_of_isClosed
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    (hsublevel_closed : IsClosed {x : E | f x ≤ α})
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    intrinsicClosure 𝕜 {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  have hclosure :
      closure ({x : E | f x < α} : Set E) = {x : E | f x ≤ α} :=
    hf.closure_openSublevel_eq_closedSublevel_of_isClosed α hsublevel_closed hα
  have hsubset_affineSpan :
      ({x : E | f x ≤ α} : Set E) ⊆ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
    rw [← hclosure]
    refine closure_minimal (subset_affineSpan 𝕜 ({x : E | f x < α} : Set E)) ?_
    exact (affineSpan 𝕜 ({x : E | f x < α} : Set E)).closed_of_finiteDimensional
  calc
    intrinsicClosure 𝕜 ({x : E | f x < α} : Set E) =
        closure ({x : E | f x < α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa using
        (intrinsicClosure_eq_closure_inter_affineSpan (𝕜 := 𝕜)
          ({x : E | f x < α} : Set E))
    _ = ({x : E | f x ≤ α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa [hclosure]
    _ = {x : E | f x ≤ α} :=
      Set.inter_eq_left.2 hsubset_affineSpan

/-- Corollary 7.6.1 (2), intrinsic-closure lower-semicontinuous bridge. -/
theorem intrinsicClosure_openSublevel_eq_closedSublevel
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
    (hf_lsc : LowerSemicontinuous f)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    intrinsicClosure 𝕜 {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  have hclosure :
      closure ({x : E | f x < α} : Set E) = {x : E | f x ≤ α} :=
    hf.closure_openSublevel_eq_closedSublevel α hf_lsc hα
  have hsubset_affineSpan :
      ({x : E | f x ≤ α} : Set E) ⊆ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
    rw [← hclosure]
    refine closure_minimal (subset_affineSpan 𝕜 ({x : E | f x < α} : Set E)) ?_
    exact (affineSpan 𝕜 ({x : E | f x < α} : Set E)).closed_of_finiteDimensional
  calc
    intrinsicClosure 𝕜 ({x : E | f x < α} : Set E) =
        closure ({x : E | f x < α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa using
        (intrinsicClosure_eq_closure_inter_affineSpan (𝕜 := 𝕜)
          ({x : E | f x < α} : Set E))
    _ = ({x : E | f x ≤ α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa [hclosure]
    _ = {x : E | f x ≤ α} :=
      Set.inter_eq_left.2 hsubset_affineSpan

end Function.IsConvex

end

/-! ### Theorem_7_6 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]
variable {α : Type*}
variable [LinearOrder α] [AddCommMonoid α] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.6 compares the open and closed `α`-sublevel sets of a convex
  function when the strict `α`-sublevel is nonempty, identifying their common closure, their
  common relative interior, and their common affine dimension.
- `core/canonical`: the owner abstractions already present in the chapter are `Function.IsConvex`,
  `Function.IsProper`, the effective-domain owners `dom(·)` and `riDom(·)`, the closure owner
  `cl(·)` for the lower-semicontinuous hull, mathlib's ambient closure `closure`, scalar-indexed
  relative interior notation `ri[𝕜](·)`, and set-dimension notation `dim[𝕜](·)`.
- `bridge/view`: the source phrase `α > inf f` is represented on the primitive owner layer by a
  nonempty strict-sublevel set `({x | f x < α} : Set E).Nonempty`, while the textbook set
  `{x ∈ ri (dom f) | f(x) < α}` is written canonically as
  `riDom[𝕜](f) ∩ {x | f x < α}`.

Domain-style sampling used here:
- `Function.IsConvex.mem_ri_epi_iff` from `Lemma_7_3`;
- `Function.IsConvex.eq_bot_of_mem_riDom` from `Theorem_7_2`;
- `Function.IsConvex.cl_eqOn_riDom_of_not_isProper` from `Text_7_0_15`;
- `Convex.closure_intrinsicInterior_eq_closure` from `Theorem_6_3`;
- `Convex.intrinsicInterior_closure_eq_intrinsicInterior` from `Theorem_6_3`;
- the Chapter 7 owners `dom(·)`, `riDom[𝕜](·)`, `cl(·)`, `ri[𝕜](·)`, and `dim[𝕜](·)`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithTopBot α`, convexity, a codomain level `a : α`, and
  the strict-sublevel nonemptiness witness `({x : E | f x < a} : Set E).Nonempty`;
- derived outputs: the common closure formula, the common relative-interior formula, and the two
  affine-dimension identities for the open and closed `a`-sublevel sets.

Layer target: `source-facing`, split into atomic owner-level clauses rather than one conjunction.
The common closure is expressed directly through `cl(f)`, the common relative interior through
`riDom[𝕜](f)`, and the dimension clause through the canonical set-side owner `dim[𝕜](·)`.

Ambient-space refinement: this item is exported on a finite-dimensional ordered topological-field
module layer, avoiding extra normed/completeness structure not used by the theorem surface.
Only the two clauses whose conclusion uses `cl(·)` require the extra conditionally complete
codomain/topology layer from the Chapter 7 closure owner, while the relative-interior and
affine-dimension clauses remain on the weaker linear-order codomain layer.
-/

namespace Function.IsConvex

variable {f : E → WithTopBot α}

section LowerSemicontinuousHull

variable [TopologicalSpace α] [OrderTopology α]
variable [ConditionallyCompleteLinearOrder α]

-- Proof sketch: first show that the horizontal slice of `closure (epi f)` at height `α` is
-- exactly the closed `α`-sublevel set of `cl(f)` by `closure_epi_eq_epi_lowerSemicontinuousHull`.
-- If `f` is improper, Theorem 7.2 and Text 7.0.15 make `f = cl(f) = ⊥` on `riDom[𝕜](f)`, so the
-- strict-sublevel witness already forces the same closed-sublevel closure formula. In the proper
-- case, use the Chapter 7 epigraph relative-interior theorem to ensure the slice meets
-- `ri[𝕜](epi f)`, so the closure of the closed sublevel set is the projection of that closed
-- horizontal slice.
/-- Theorem 7.6 (1): for a convex function and a level `α` with a strict-sublevel witness, the
closure of the closed `α`-sublevel set is the closed `α`-sublevel set of the closure `cl(f)`.
-/
theorem closure_closedSublevel_eq_closedSublevel_lowerSemicontinuousHull
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : closure {x | f x ≤ a} = {x | cl(f) x ≤ a} := sorry

-- Proof sketch: Theorem 7.6 (1) gives the common closure of the closed and open `α`-sublevel
-- sets once Theorem 7.6 (2) places the common relative interior inside the open sublevel set.
-- Corollary 6.3.1 then upgrades the sandwich
-- `ri(closedSublevel) ⊆ openSublevel ⊆ closure(closedSublevel)` to equality of closures.
/-- Theorem 7.6 (3): the open and closed `α`-sublevel sets have the same closure, namely the
closed `α`-sublevel set of `cl(f)`. -/
theorem closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : closure {x | f x < a} = {x | cl(f) x ≤ a} := sorry

end LowerSemicontinuousHull

section LinearOrderSublevels

-- Proof sketch: intersect the epigraph of `f` with the horizontal affine slice at height `α`.
-- In the improper case, Theorem 7.2 and Text 7.0.15 collapse `riDom[𝕜](f)` to the `⊥` locus, so
-- the displayed set identity reduces to the Chapter 6 closure/interior facts for convex domains.
-- Otherwise the same slice-relative-interior argument as in Corollary 7.6.1, now fed by the
-- strict-sublevel witness through Chapter 7's strict-sublevel existence bridge, identifies the
-- relative interior of the closed `α`-sublevel set with the points of `riDom[𝕜](f)` where
-- `f < α`.
/-- Theorem 7.6 (2): under the same hypotheses, the relative interior of the closed `α`-sublevel
set is exactly `ri (dom f) ∩ {x | f(x) < α}`, written here as
`riDom[𝕜](f) ∩ {x | f x < α}`. -/
theorem intrinsicInterior_closedSublevel_eq_riDom_inter_openSublevel
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : ri[𝕜]({x | f x ≤ a}) =
      riDom[𝕜](f) ∩ {x | f x < a} := sorry

-- Proof sketch: Theorem 7.6 (2) gives the relative interior of the closed `α`-sublevel set.
-- Since that set is contained in the open `α`-sublevel set, while the open sublevel is contained
-- in the closed sublevel, Corollary 6.3.1 yields equality of relative interiors for the two level
-- sets.
/-- Theorem 7.6 (4): the open and closed `α`-sublevel sets have the same relative interior, namely
`riDom[𝕜](f) ∩ {x | f x < α}`. -/
theorem intrinsicInterior_openSublevel_eq_riDom_inter_openSublevel
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : ri[𝕜]({x | f x < a}) =
      riDom[𝕜](f) ∩ {x | f x < a} := sorry

-- Proof sketch: by Theorem 7.6 (2), the closed `α`-sublevel set and `dom(f)` have the same
-- relative interior. For convex sets in finite-dimensional spaces, equality of relative interiors
-- forces equality of affine dimensions via the Chapter 6 closure/interior dimension machinery.
/-- Theorem 7.6 (5): the closed `α`-sublevel set has the same affine dimension as the effective
domain `dom(f)`, and hence the same dimension as `f`. -/
theorem dim_closedSublevel_eq_dim_effectiveDomain
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : dim[𝕜]({x | f x ≤ a}) =
      dim[𝕜](dom(f)) := sorry

-- Proof sketch: Theorem 7.6 (4) gives the same relative interior for the open and closed
-- `α`-sublevel sets, so they have the same affine dimension. Combine this with Theorem 7.6 (5) to
-- identify the affine dimension of the open `α`-sublevel set with that of `dom(f)`.
/-- Theorem 7.6 (6): the open `α`-sublevel set also has the same affine dimension as the effective
domain `dom(f)`, and hence as `f`. -/
theorem dim_openSublevel_eq_dim_effectiveDomain
    (hf : f.IsConvex 𝕜) (a : α)
    (ha : ({x : E | f x < a} : Set E).Nonempty)
    : dim[𝕜]({x | f x < a}) =
      dim[𝕜](dom(f)) := sorry

end LinearOrderSublevels

end Function.IsConvex

end
