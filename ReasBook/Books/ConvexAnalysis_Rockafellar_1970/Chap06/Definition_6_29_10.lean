import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.10 introduces the stronger consistency notions for the
  generalized convex program associated with a bifunction `F`, namely strong consistency and
  strict consistency.
- `core/canonical`: the source-facing domain owner `dom F` from Definition 6.29.8 and the
  intrinsic/ambient topological owners `intrinsicInterior`, `interior`, and `nhds`.
- `bridge/view`: on the complete-lattice codomain layer, `dom F = dom(perturbationFunction F)`, so
  strong consistency is equivalent to `0 ∈ riDom[𝕜](perturbationFunction F)` and strict
  consistency is equivalent to `0 ∈ interior (dom(perturbationFunction F))`.

Project sampling used here:
- `Bifunction.dom` from `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8`;
- `Bifunction.mem_dom_perturbationFunction_iff_mem_dom` and
  `Bifunction.mem_ri_dom_iff_mem_riDom_perturbationFunction` from the same file.

Mathlib sampling used here:
- `intrinsicInterior` from `Mathlib/Analysis/Convex/Intrinsic.lean`;
- `intrinsicInterior_subset` from the same file;
- `interior_subset_intrinsicInterior` from the same file.

- Primitive data vs derived API:
- primitive owner data: the source-facing bifunction domain `dom F`;
- source-facing predicates: `IsStronglyConsistent 𝕜 F` and `IsStrictlyConsistent F`;
- derived API: the bridges to the perturbation-domain formulations, the canonical implication
  `strict ⇒ strong`, the interior/open-set bridge for strict consistency, then the implications to
  ordinary consistency.

Layer target: `source-facing`, built directly on the existing owner `dom F` rather than via the
derived perturbation-function domain.
-/

/-- Definition 6.29.10: a generalized convex program is strongly consistent when the base
perturbation `0` lies in the relative interior of the bifunction domain. -/
def IsStronglyConsistent (F : U → X → β) : Prop :=
  0 ∈ ri[𝕜](dom F)

@[simp] theorem isStronglyConsistent_iff (F : U → X → β) :
    IsStronglyConsistent 𝕜 F ↔ 0 ∈ ri[𝕜](dom F) :=
  Iff.rfl

end

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- Strong consistency implies ordinary consistency. -/
theorem IsStronglyConsistent.isConsistent {F : U → X → β}
    (hF : IsStronglyConsistent 𝕜 F) :
    IsConsistent F := by
  exact (isConsistent_iff_zero_mem_dom F).2
    (intrinsicInterior_subset hF)

end

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [CompleteLattice β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- On the complete-lattice codomain layer, strong consistency is equivalent to membership of
`0` in the relative interior of `dom(perturbationFunction F)`. -/
@[simp] theorem isStronglyConsistent_iff_mem_riDom_perturbationFunction
    (F : U → X → β) :
    IsStronglyConsistent 𝕜 F ↔ 0 ∈ riDom[𝕜](perturbationFunction F) := by
  have hzero :
      (0 : U) ∈ ri[𝕜](dom F) ↔
        0 ∈ riDom[𝕜](perturbationFunction F) :=
    mem_ri_dom_iff_mem_riDom_perturbationFunction
  simpa [isStronglyConsistent_iff] using hzero

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Zero U] [TopologicalSpace U]

/-- Definition 6.29.10: a generalized convex program is strictly consistent when `0` admits an
open neighborhood contained in the bifunction domain, equivalently when `0` lies in the interior
of that domain. The canonical owner is neighborhood-membership of `dom F` at `0`, with interior
membership as a bridge theorem. -/
def IsStrictlyConsistent (F : U → X → β) : Prop :=
  dom F ∈ nhds (0 : U)

/-- Strict consistency is exactly neighborhood-membership of the bifunction domain at `0`. -/
theorem isStrictlyConsistent_iff_mem_nhds (F : U → X → β) :
    IsStrictlyConsistent F ↔ dom F ∈ nhds (0 : U) :=
  Iff.rfl

theorem isStrictlyConsistent_iff_exists_open_zero_subset_dom (F : U → X → β) :
    IsStrictlyConsistent F ↔ ∃ C : Set U, IsOpen C ∧ (0 : U) ∈ C ∧ C ⊆ dom F :=
  by
    constructor
    · intro hnhds
      have hzeroInterior : (0 : U) ∈ interior (dom F) :=
        (mem_interior_iff_mem_nhds).2 hnhds
      exact ⟨interior (dom F), isOpen_interior, hzeroInterior, interior_subset⟩
    · rintro ⟨C, hC_open, hC_zero, hC_sub⟩
      exact Filter.mem_of_superset (IsOpen.mem_nhds hC_open hC_zero) hC_sub

@[simp] theorem isStrictlyConsistent_iff (F : U → X → β) :
    IsStrictlyConsistent F ↔ 0 ∈ interior (dom F) :=
  (mem_interior_iff_mem_nhds : (0 : U) ∈ interior (dom F) ↔ dom F ∈ nhds (0 : U)).symm

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Zero U] [TopologicalSpace U]

/-- Strict consistency implies ordinary consistency. -/
theorem IsStrictlyConsistent.isConsistent {F : U → X → β}
    (hF : IsStrictlyConsistent F) :
    IsConsistent F := by
  have hzero : (0 : U) ∈ interior (dom F) :=
    (isStrictlyConsistent_iff (F := F)).1 hF
  exact (isConsistent_iff_zero_mem_dom F).2
    (interior_subset hzero)

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [CompleteLattice β]
variable [Zero U] [TopologicalSpace U]

/-- On the complete-lattice codomain layer, strict consistency is equivalent to membership of `0`
in the interior of `dom(perturbationFunction F)`. -/
@[simp] theorem isStrictlyConsistent_iff_mem_interior_dom_perturbationFunction
    (F : U → X → β) :
    IsStrictlyConsistent F ↔ 0 ∈ interior (dom(perturbationFunction F)) := by
  simpa [isStrictlyConsistent_iff] using
    (mem_interior_dom_iff_mem_interior_dom_perturbationFunction
      (F := F) (u := (0 : U)))

end

section

variable {𝕜 : Type w} {U : Type u} {V : Type*} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- Strict consistency implies strong consistency. -/
theorem IsStrictlyConsistent.isStronglyConsistent {F : U → X → β}
    (hF : IsStrictlyConsistent F) :
    IsStronglyConsistent 𝕜 F := by
  exact interior_subset_intrinsicInterior ((isStrictlyConsistent_iff (F := F)).1 hF)

end

end Bifunction
