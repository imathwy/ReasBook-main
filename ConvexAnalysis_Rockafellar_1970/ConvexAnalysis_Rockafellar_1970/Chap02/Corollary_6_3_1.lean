import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 6.3.1 gives three equivalent conditions for two sets:
  equality of relative closures, equality of relative interiors, and the sandwich condition
  `ri C1 ⊆ C2 ⊆ cl[𝕜](C1)`.
- `core/canonical`: the owner notions are `intrinsicClosure 𝕜` and `intrinsicInterior 𝕜`.
  The primitive data needed for the equivalence are exactly the two stability bridges
  `ri (cl[𝕜](C)) = ri C` and `cl[𝕜](ri C) = cl[𝕜](C)` for each set.
- `bridge/view`: Rockafellar's `ri` is formalized by mathlib's `intrinsicInterior 𝕜`.
- Domain-style sampling: the relevant canonical/project declarations are
  `intrinsicClosure_mono`, `intrinsicClosure_idem`, `subset_intrinsicClosure`,
  and `intrinsicInterior_subset`.
- Primitive data vs derived API: the set-level stability bridges are primitive for this
  equivalence theorem; convexity and finite-dimensional assumptions are source-facing sufficient
  hypotheses supplied by a bridge theorem from `Theorem_6_3`.
- Layer target: the main theorem is the canonical owner-level equivalence at the primitive bridge
  layer; the convex finite-dimensional statement is a thin downstream wrapper.
-/

namespace Set

section Primitive

variable {𝕜 V P : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace P] [AddTorsor V P]

/-- Corollary 6.3.1 on the primitive set-level bridge layer: if each set is stable under the two
relative closure/interior bridges `ri(cl[𝕜](C)) = ri C` and
`cl[𝕜](ri C) = cl[𝕜](C)`, then equality of relative closures, equality of
relative interiors, and the sandwich condition are equivalent. -/
theorem tfae_intrinsicClosure_eq_ri_eq_sandwich_of_stable
    {C1 C2 : Set P}
    (hC1stable : ri[𝕜](cl[𝕜](C1)) = ri[𝕜](C1) ∧
      cl[𝕜](ri[𝕜](C1)) = cl[𝕜](C1))
    (hC2stable : ri[𝕜](cl[𝕜](C2)) = ri[𝕜](C2) ∧
      cl[𝕜](ri[𝕜](C2)) = cl[𝕜](C2)) :
    List.TFAE
      [cl[𝕜](C1) = cl[𝕜](C2),
        ri[𝕜](C1) = ri[𝕜](C2),
        ri[𝕜](C1) ⊆ C2 ∧ C2 ⊆ cl[𝕜](C1)] := by
  rcases hC1stable with ⟨hC1ri, hC1cl⟩
  rcases hC2stable with ⟨hC2ri, hC2cl⟩
  tfae_have 1 → 2 := by
    intro h
    calc
      ri[𝕜](C1) = ri[𝕜](cl[𝕜](C1)) := by
        simpa using hC1ri.symm
      _ = ri[𝕜](cl[𝕜](C2)) := by simp [h]
      _ = ri[𝕜](C2) := by
        simpa using hC2ri
  tfae_have 2 → 3 := by
    intro h
    have hcl : cl[𝕜](C1) = cl[𝕜](C2) :=
      calc
        cl[𝕜](C1) = cl[𝕜](ri[𝕜](C1)) := hC1cl.symm
        _ = cl[𝕜](ri[𝕜](C2)) := by simp [h]
        _ = cl[𝕜](C2) := hC2cl
    refine ⟨?_, ?_⟩
    · simpa [h] using (intrinsicInterior_subset : ri[𝕜](C2) ⊆ C2)
    · intro x hx
      have hx' : x ∈ cl[𝕜](C2) := subset_intrinsicClosure hx
      simpa [hcl] using hx'
  tfae_have 3 → 1 := by
    rintro ⟨hri, hC2C1⟩
    apply subset_antisymm
    · calc
        cl[𝕜](C1) = cl[𝕜](ri[𝕜](C1)) := hC1cl.symm
        _ ⊆ cl[𝕜](C2) := intrinsicClosure_mono hri
    · calc
        cl[𝕜](C2) ⊆ cl[𝕜](cl[𝕜](C1)) :=
          intrinsicClosure_mono hC2C1
        _ = cl[𝕜](C1) := by simp
  tfae_finish

end Primitive

end Set

namespace Convex

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Corollary 6.3.1 as a source-facing `Convex` owner theorem in finite-dimensional spaces. -/
theorem tfae_intrinsicClosure_eq_ri_eq_sandwich
    {C1 C2 : Set E} (hC1 : Convex 𝕜 C1) (hC2 : Convex 𝕜 C2) :
    List.TFAE
      [cl[𝕜](C1) = cl[𝕜](C2),
        ri[𝕜](C1) = ri[𝕜](C2),
        ri[𝕜](C1) ⊆ C2 ∧ C2 ⊆ cl[𝕜](C1)] := by
  exact Set.tfae_intrinsicClosure_eq_ri_eq_sandwich_of_stable
    ⟨hC1.ri_intrinsicClosure_eq_ri, hC1.intrinsicClosure_ri_eq_intrinsicClosure⟩
    ⟨hC2.ri_intrinsicClosure_eq_ri, hC2.intrinsicClosure_ri_eq_intrinsicClosure⟩

end SourceFacing

end Convex

end
