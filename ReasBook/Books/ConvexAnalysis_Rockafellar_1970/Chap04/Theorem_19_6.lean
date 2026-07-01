import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise Rockafellar

section

variable {ι 𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 19.6 states that the closed convex hull of finitely many polyhedral
  convex subsets of a finite-dimensional topological `𝕜`-module is again polyhedral convex, and
  for nonempty members identifies that closed convex hull with the simplex-weighted
  Minkowski-recession combinations from the source.
- `core/canonical`: the chapter owner abstraction for polyhedral sets is
  `Set.IsFinitelyGeneratedConvex 𝕜`, via Theorem 19.1, together with the ambient owners
  `closedConvexHull 𝕜`, `StdSimplex 𝕜 ι`, the chapter recession-cone owner `0⁺[𝕜]`, and the
  finite pointwise set sum `∑ i, S i`.
- `bridge/view`: the source polyhedral statements should be organized through the Chapter 19
  polyhedral-to-finite-generation owner bridge, not through the Chapter 2 theorem
  `closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination`. That Chapter 2 theorem is
  a neighboring stronger result with an extra zero-sum recession-lineality hypothesis, and that
  hypothesis is not automatic for arbitrary polyhedral families, so it must not be hidden here as
  a specialization route. The indexed-union display remains a thin companion rewrite of the main
  source-facing equality.

Domain-style sampling used here:
- `Set.IsPolyhedral`;
- `Set.IsFinitelyGeneratedConvex`;
- `closedConvexHull 𝕜`;
- `StdSimplex 𝕜 ι`;
- `0⁺[𝕜]`;
- the Chapter 2 neighboring theorem
  `closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination`, checked here only to rule
  it out as the owner bridge because its extra hypothesis is genuinely stronger.

Primitive data vs derived API:
- primitive inputs: the finite family `C : ι → Set E`, together with polyhedrality and, for
  the source union formula, nonemptiness of each `C i`;
- derived outputs: polyhedrality of the closed convex hull of the union and the simplex-recession
  decomposition of that owner object.

Layer target:
- part (1) has a `core/canonical` owner form in `Set.IsFinitelyGeneratedConvex`, plus the
  source-facing polyhedral bridge surface;
- part (2) has the same split: core owner equalities first, then source-facing polyhedral forms;
- the explicit indexed-union display is the companion `bridge/view` reformulation of each
  set-of-membership equality.
- ambient minimization audit: no theorem surface in this item uses Hausdorff separation, so the
  ambient assumptions are kept at `TopologicalSpace` + additive/topological module structure
  without a `T2Space` requirement.
-/

variable {C : ι → Set E}

/-- Theorem 19.6 simplex/recession-combination owner surface:
for a family `C : ι → Set E`, this is the set of simplex-weighted pointwise sums where the
`i`th branch is `0⁺[𝕜] (C i)` when the simplex weight at `i` vanishes, and `w.weights i • C i`
otherwise. -/
scoped[Rockafellar] notation "simpRec[" 𝕜 "](" C ")" =>
  ({x : E |
    ∃ w : StdSimplex 𝕜 ι,
      x ∈ ∑ i,
        (if w.weights i = 0 then 0⁺[𝕜] (C i)
         else w.weights i • C i : Set E)} : Set E)

namespace Set.IsFinitelyGeneratedConvex

/-- Theorem 19.6 (1), core owner form: the closed convex hull of a finite family of finitely
generated convex subsets of the ambient finite-dimensional topological `𝕜`-module is again
finitely generated convex. -/
-- Proof sketch: write each `C i` as a finite mixed hull of points and directions. Homogenize
-- those generators in a one-dimensional extension, form the finitely generated cone, and identify
-- its height-`1` slice with `closedConvexHull 𝕜 (⋃ i, C i)`.
theorem closedConvexHull_iUnion [Finite ι] (hC : ∀ i, (C i).IsFinitelyGeneratedConvex 𝕜) :
    (closedConvexHull 𝕜 (⋃ i, C i)).IsFinitelyGeneratedConvex 𝕜 := by
  sorry

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolyhedral

/-- Theorem 19.6 (1), source-facing bridge form: the closed convex hull of a finite family of
polyhedral convex subsets of the ambient finite-dimensional topological `𝕜`-module is again a
polyhedral convex set. -/
-- Proof sketch: transport the family to the Chapter 19 finite-generation owner layer, apply the
-- corresponding core owner theorem there, and then transport back to the polyhedral surface.
theorem closedConvexHull_iUnion [Finite ι] (hC : ∀ i, (C i).IsPolyhedral 𝕜) :
    (closedConvexHull 𝕜 (⋃ i, C i)).IsPolyhedral 𝕜 := by
  exact
    (Set.IsFinitelyGeneratedConvex.closedConvexHull_iUnion
      (hC := fun i ↦ (hC i).isFinitelyGeneratedConvex)).isPolyhedral

end Set.IsPolyhedral

variable [Fintype ι]

namespace Set.IsFinitelyGeneratedConvex

/-- Theorem 19.6 (2), core owner form: for nonempty finitely generated convex sets, the closed
convex hull of the union is exactly the set of simplex-weighted Minkowski sums in which
`0⁺[𝕜] (C i)` is substituted when the `i`th coefficient is zero. -/
-- Proof sketch: replace each `C i` by a finite point-direction presentation, homogenize in a
-- one-dimensional extension, and read off the height-`1` slice of the generated cone. Zero simplex
-- weights contribute exactly recession-cone branches.
theorem closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC : ∀ i, (C i).IsFinitelyGeneratedConvex 𝕜)
    (hne : ∀ i, (C i).Nonempty) :
    closedConvexHull 𝕜 (⋃ i, C i) =
      simpRec[𝕜](C) := by
  sorry

/-- Intrinsic-topology companion of Theorem 19.6 (2), core owner form: the same simplex/recession
decomposition written with `intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i))` instead of the ambient
`closedConvexHull 𝕜 (⋃ i, C i)`. -/
theorem intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC : ∀ i, (C i).IsFinitelyGeneratedConvex 𝕜)
    (hclosed_aff :
      IsClosed (aff[𝕜] (conv[𝕜] (⋃ i, C i)) : Set E))
    (hne : ∀ i, (C i).Nonempty) :
    intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i)) =
      simpRec[𝕜](C) := by
  have hclosure :
      intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i)) = closure (conv[𝕜] (⋃ i, C i)) :=
    Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan (𝕜 := 𝕜)
      (C := conv[𝕜] (⋃ i, C i)) hclosed_aff
  simpa [closedConvexHull_eq_closure_convexHull,
    hclosure] using
    closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
      (hC := hC) (hne := hne)

/-- Intrinsic-topology companion display of Theorem 19.6 (2), core owner form: the owner
equality from
`intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination` rewritten as an
indexed union over simplex weights. -/
theorem intrinsicClosure_convexHull_iUnion_eq_iUnion_simplex_recession_combination
    (hC : ∀ i, (C i).IsFinitelyGeneratedConvex 𝕜)
    (hclosed_aff :
      IsClosed (aff[𝕜] (conv[𝕜] (⋃ i, C i)) : Set E))
    (hne : ∀ i, (C i).Nonempty) :
    intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i)) =
      ⋃ w : StdSimplex 𝕜 ι,
        ∑ i,
          (if w.weights i = 0 then 0⁺[𝕜] (C i)
           else w.weights i • C i : Set E) := by
  ext x
  rw [intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC := hC) (hclosed_aff := hclosed_aff) (hne := hne)]
  simp

/-- Theorem 19.6 (2), core owner display: the owner equality from
`closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination` rewritten as an indexed union
over simplex weights. -/
theorem closedConvexHull_iUnion_eq_iUnion_simplex_recession_combination
    (hC : ∀ i, (C i).IsFinitelyGeneratedConvex 𝕜)
    (hne : ∀ i, (C i).Nonempty) :
    closedConvexHull 𝕜 (⋃ i, C i) =
      ⋃ w : StdSimplex 𝕜 ι,
        ∑ i,
          (if w.weights i = 0 then 0⁺[𝕜] (C i)
           else w.weights i • C i : Set E) := by
  ext x
  rw [closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination hC hne]
  simp

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolyhedral

/-- Theorem 19.6 (2), source-facing bridge form: for nonempty polyhedral sets, the closed convex
hull of the union is exactly the set of simplex-weighted Minkowski sums in which `0⁺[𝕜] (C i)` is
substituted when the `i`th coefficient is zero. -/
-- Proof sketch: move from polyhedrality to the finite-generation owner layer of Theorem 19.1,
-- apply the corresponding core owner equality there, and transport back to the source-facing
-- polyhedral surface.
theorem closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC : ∀ i, (C i).IsPolyhedral 𝕜)
    (hne : ∀ i, (C i).Nonempty) :
    closedConvexHull 𝕜 (⋃ i, C i) =
      simpRec[𝕜](C) := by
  simpa using
    Set.IsFinitelyGeneratedConvex.closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
      (hC := fun i ↦ (hC i).isFinitelyGeneratedConvex) (hne := hne)

/-- Intrinsic-topology companion of Theorem 19.6 (2), source-facing bridge form: the same
simplex/recession decomposition on the polyhedral surface, phrased via
`intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i))`. -/
theorem intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC : ∀ i, (C i).IsPolyhedral 𝕜)
    (hclosed_aff :
      IsClosed (aff[𝕜] (conv[𝕜] (⋃ i, C i)) : Set E))
    (hne : ∀ i, (C i).Nonempty) :
    intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i)) =
      simpRec[𝕜](C) := by
  simpa using
    Set.IsFinitelyGeneratedConvex
      .intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination
        (hC := fun i ↦ (hC i).isFinitelyGeneratedConvex)
        (hclosed_aff := hclosed_aff) (hne := hne)

/-- Intrinsic-topology companion display of Theorem 19.6 (2), source-facing bridge form: the
owner equality from
`intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination` rewritten as an
indexed union over simplex weights. -/
theorem intrinsicClosure_convexHull_iUnion_eq_iUnion_simplex_recession_combination
    (hC : ∀ i, (C i).IsPolyhedral 𝕜)
    (hclosed_aff :
      IsClosed (aff[𝕜] (conv[𝕜] (⋃ i, C i)) : Set E))
    (hne : ∀ i, (C i).Nonempty) :
    intrinsicClosure 𝕜 (conv[𝕜] (⋃ i, C i)) =
      ⋃ w : StdSimplex 𝕜 ι,
        ∑ i,
          (if w.weights i = 0 then 0⁺[𝕜] (C i)
           else w.weights i • C i : Set E) := by
  ext x
  rw [intrinsicClosure_convexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hC := hC) (hclosed_aff := hclosed_aff) (hne := hne)]
  simp

/-- Theorem 19.6 (2), source display: the owner equality from
`closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination` rewritten as an indexed union
over simplex weights. -/
theorem closedConvexHull_iUnion_eq_iUnion_simplex_recession_combination
    (hC : ∀ i, (C i).IsPolyhedral 𝕜)
    (hne : ∀ i, (C i).Nonempty) :
    closedConvexHull 𝕜 (⋃ i, C i) =
      ⋃ w : StdSimplex 𝕜 ι,
        ∑ i,
          (if w.weights i = 0 then 0⁺[𝕜] (C i)
           else w.weights i • C i : Set E) := by
  ext x
  rw [closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination hC hne]
  simp

end Set.IsPolyhedral

end
