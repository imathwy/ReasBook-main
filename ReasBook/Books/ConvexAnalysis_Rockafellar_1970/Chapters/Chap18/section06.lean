import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_6 (from Chap04) -/
section

open Filter Set

section Core

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
variable {C : Set E}

/-!
Source/core/bridge triage:
- `source-facing`: this file now keeps only the fully justified bridge layer for Theorem 18.6:
  given the ambient closure-density owner
  `C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜)`,
  derive relative-closure and sequential forms.
- `core/canonical`: the owner abstractions are `Set.exposedPoints 𝕜 C`, `Set.extremePoints 𝕜 C`,
  and `closure`, with no extra wrapper owner.
- `bridge/view`: the sequential reformulation is supplied by `mem_closure_iff_seq_limit`.

Domain-style sampling used here:
- `Set.exposedPoints`;
- `Set.extremePoints`;
- `mem_extremePoints`;
- `mem_closure_iff_seq_limit`.

Primitive data vs derived API:
- primitive input: the ambient closure-density owner
  `C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜)`;
- derived API: relative-closure and sequential formulations.

Layer target: `bridge/view`, expressed directly through canonical point-set owners and the
relative closure phrased as `C ∩ closure (C.exposedPoints 𝕜)`.
-/

/-- Relative-closure bridge for Theorem 18.6: if extreme points are in the ambient closure of
`C.exposedPoints 𝕜`, then they are in the relative closure
`C ∩ closure (C.exposedPoints 𝕜)`. -/
theorem extremePoints_subset_closure_exposedPoints_relative
    (hC_density : C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜)) :
    C.extremePoints 𝕜 ⊆ C ∩ closure (C.exposedPoints 𝕜) := by
  intro x hx
  refine ⟨(mem_extremePoints.mp hx).1, ?_⟩
  exact hC_density hx

/-- Ambient-closure owner form used by the bridge declarations below. -/
theorem extremePoints_subset_closure_exposedPoints
    (hC_density : C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜)) :
    C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜) := by
  intro x hx
  exact (extremePoints_subset_closure_exposedPoints_relative hC_density hx).2

end Core

section Sequential

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
  [FrechetUrysohnSpace E]
variable {C : Set E}

/-- Sequential bridge form of Theorem 18.6: under the ambient closure-density owner, every extreme
point is the limit of a sequence of exposed points. -/
theorem exists_exposedPoints_seq_tendsto_of_mem_extremePoints
    (hC_density : C.extremePoints 𝕜 ⊆ closure (C.exposedPoints 𝕜))
    {x : E}
    (hx : x ∈ C.extremePoints 𝕜) :
    ∃ u : ℕ → E, (∀ n, u n ∈ C.exposedPoints 𝕜) ∧ Tendsto u atTop (nhds x) := by
  exact (mem_closure_iff_seq_limit.mp <|
    extremePoints_subset_closure_exposedPoints hC_density hx)

end Sequential

end
