import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open Bornology

namespace Convex

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.7 re-uses the Chapter 2 boundedness criterion for nonempty closed
  convex sets.
- `core/canonical`: the primary owner surface is asymptotic-cone triviality
  `asymptoticCone 𝕜 C ⊆ {0}`.
- `bridge/view`: the recession-cone surface `0⁺[𝕜] C ⊆ {0}` is exposed as a bridge corollary.
- Primitive data vs derived API: primitive inputs are exactly `Convex 𝕜 C`, `IsClosed C`, and
  `C.Nonempty`; the equality form `0⁺[𝕜] C = {0}` is derived from nonemptiness of the cone.
- Ambient/scalar layer: this node keeps the scalar/ambient assumptions inherited from the upstream
  bridge `recessionCone_eq_asymptoticCone`; no extra codomain or model-specific owner is added.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
variable {C : Set E}

/-- Canonical owner form used at this node: boundedness is equivalent to trivial asymptotic cone
for closed convex sets. -/
theorem isBounded_iff_asymptoticCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  simpa using
    (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
      hC_closed)

/-- Source-facing bridge form: boundedness is equivalent to `0⁺[𝕜] C ⊆ {0}`. -/
theorem isBounded_iff_recessionCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  simpa using
    (hC_convex.isBounded_iff_recessionCone_subset_singleton_zero hC_closed hC_nonempty)

/-- Canonical/source bridge at the same abstraction layer: under the source hypotheses, asymptotic
and recession cone triviality are equivalent. -/
theorem asymptoticCone_trivial_iff_recessionCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    asymptoticCone 𝕜 C ⊆ ({0} : Set E) ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  exact
    (isBounded_iff_asymptoticCone_trivial_of_closed_convex
      (hC_convex := hC_convex) (hC_closed := hC_closed)).symm.trans
      (isBounded_iff_recessionCone_trivial_of_closed_convex
        (hC_convex := hC_convex) (hC_closed := hC_closed) (hC_nonempty := hC_nonempty))

/-- Textbook-equality corollary: this remains downstream from the subset-owner bridge. -/
theorem isBounded_iff_recessionCone_eq_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C = ({0} : Set E) := by
  have hcone_nonempty : (0⁺[𝕜] C).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  exact
    (isBounded_iff_recessionCone_trivial_of_closed_convex
      (hC_convex := hC_convex) (hC_closed := hC_closed) (hC_nonempty := hC_nonempty)).trans
      hcone_nonempty.subset_singleton_iff

end Convex

end
