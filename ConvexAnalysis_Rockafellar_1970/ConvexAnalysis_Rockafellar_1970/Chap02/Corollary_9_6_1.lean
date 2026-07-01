import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar


/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.6.1 is expressed at the generated-cone owner level:
  a closed convex set avoiding `0` and with trivial recession cone has closed generated cone.
- `core/canonical`: the generated cone owner is `cone[𝕜] C` (raw owner `PointedCone.hull 𝕜 C`),
  and the primitive closure trigger is the asymptotic-cone subset condition
  `asymptoticCone 𝕜 C ⊆ ({0} : Set E)`.
- `bridge/view`: Theorem 9.6 gives `closure cone = cone ∪ asymptoticCone`, and
  `Convex.recessionCone_eq_asymptoticCone` bridges the source-facing recession hypothesis to that
  canonical owner hypothesis.

Domain-style sampling used here:
- `cone[𝕜]`;
- `PointedCone.closure_cone_eq_union_asymptoticCone`;
- `Convex.recessionCone_eq_asymptoticCone`;
- `PointedCone.coe_closure`.

Primitive data vs derived API:
- primitive owner-level inputs: `IsClosed C`, `Convex 𝕜 C`, `0 ∉ C`, and
  `asymptoticCone 𝕜 C ⊆ ({0} : Set E)`;
- source-facing bridge input: `0⁺[𝕜] C ⊆ ({0} : Set E)`;
- derived owner output: `IsClosed (cone[𝕜] C : Set E)`;
- nonempty is an internal branch condition used only to invoke Theorem 9.6; the empty-set branch
  is discharged directly from the canonical empty owners.

Layer target:
- canonical owner theorem plus a thin source-facing bridge theorem.
-/

namespace PointedCone

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T1Space E]

/-- Corollary 9.6.1 (canonical owner form, primitive subset layer): if a closed convex set avoids
`0` and has asymptotic cone contained in `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_asymptoticCone_subset_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hAsym : asymptoticCone 𝕜 C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  by_cases hC_nonempty : C.Nonempty
  · have hCone_closure : ((cone[𝕜] C).closure : Set E) = (cone[𝕜] C : Set E) := by
      calc
        ((cone[𝕜] C).closure : Set E)
            = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
              simpa using
                (closure_cone_eq_union_asymptoticCone C hC_nonempty hC_closed hC_convex h0C)
        _ = (cone[𝕜] C : Set E) := by
              refine Set.union_eq_left.2 ?_
              exact Set.Subset.trans hAsym
                (Set.singleton_subset_iff.2 (cone[𝕜] C).zero_mem)
    rw [← closure_eq_iff_isClosed, ← PointedCone.coe_closure]
    exact hCone_closure
  · have hC_empty : C = (∅ : Set E) := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    subst hC_empty
    have hcone_empty : (cone[𝕜] (∅ : Set E) : Set E) = ({0} : Set E) := by
      simp
    rw [hcone_empty]
    exact isClosed_singleton

/-- Corollary 9.6.1 (canonical owner form, equality bridge): if a closed convex set avoids `0` and
has asymptotic cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_asymptoticCone_eq_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hAsym : asymptoticCone 𝕜 C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact isClosed_cone_of_asymptoticCone_subset_singleton_zero
    C hC_closed hC_convex h0C hAsym.subset

/-- Corollary 9.6.1 (source-facing recession form, primitive subset layer): if a closed convex set
avoids `0` and has recession cone contained in `{0}`, then its generated cone `cone[𝕜] C` is
closed. -/
theorem isClosed_cone_of_recessionCone_subset_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  have hAsym : asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
    by_cases hC_nonempty : C.Nonempty
    · rw [← hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty]
      exact hRec
    · have hC_empty : C = (∅ : Set E) := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
      subst hC_empty
      simp [asymptoticCone_empty]
  exact isClosed_cone_of_asymptoticCone_subset_singleton_zero
    C hC_closed hC_convex h0C hAsym

/-- Corollary 9.6.1 (source-facing recession form, equality bridge): if a closed convex set avoids
`0` and has recession cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_eq_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact isClosed_cone_of_recessionCone_subset_singleton_zero
    C hC_closed hC_convex h0C hRec.subset

end OrderedField

end PointedCone

namespace Convex

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T1Space E]

/-- Corollary 9.6.1 in object-prefix source-facing form: if a closed convex set avoids `0` and has
recession cone contained in `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_subset_singleton_zero
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact
    PointedCone.isClosed_cone_of_recessionCone_subset_singleton_zero
      C hC_closed hC_convex h0C hRec

/-- Corollary 9.6.1 in object-prefix source-facing equality form: if a closed convex set avoids
`0` and has recession cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_eq_singleton_zero
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact
    PointedCone.isClosed_cone_of_recessionCone_eq_singleton_zero
      C hC_closed hC_convex h0C hRec

end OrderedField

end Convex

end
