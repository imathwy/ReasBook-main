import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_32_3_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_32_3_3

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.4 says that for a polyhedral set `C` containing no affine
  lines, any convex function whose value-image on `C` is bounded above attains its supremum at an
  extreme point of `C`.
- `core/canonical`: this file now reuses canonical boundedness owners
  `BddAbove (f '' C)` and `BddAbove (f '' affineHalfLine x r)`, the canonical convex-function
  owner `ConvexOn 𝕜 C f`, and the Chapter 32 attainment owners `IsMaxOn` / `Set.extremePoints`.
- `bridge/view`: this file is the thin source-facing specialization that first uses the Chapter 19
  bridge `Set.IsPolyhedral.isFinitelyGeneratedConvex` to obtain a maximizer from Corollary 32.3.3,
  then invokes Corollary 32.3.1 to move that maximizer to an extreme point.

Domain-style sampling used here:
- `Set.IsPolyhedral.isFinitelyGeneratedConvex` from `Theorem_19_1`;
- `Set.IsFinitelyGeneratedConvex.exists_mem_isMaxOn_of_bddAbove_affineHalfLines` from
  Corollary 32.3.3;
- `exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_not_hasAffineLine` from
  Corollary 32.3.1;
- `Set.IsPolyhedral.convex` and `Set.IsPolyhedral.isClosed`.

Primitive data vs derived API:
- primitive inputs: global convexity `f.IsConvex 𝕜`, local convexity owner `ConvexOn 𝕜 C f`, the
  polyhedral owner `C.IsPolyhedral 𝕜`, explicit nonemptiness of `C`, the source-facing no-line
  hypothesis `¬ Set.HasAffineLine 𝕜 C`, explicit domain inclusion `C ⊆ dom(f)`, and boundedness of
  `f '' C`;
- derived API: existence of a maximizing extreme point in owner form `IsMaxOn`, and the companion
  `sSup` equality at such an extreme point.

Semantic-fidelity note:
- the textbook sentence omits nonemptiness/setup needed for attainment. This is made explicit
  because the conclusion is false for `C = ∅`.

Ambient refinement:
- this file stays on the scalar/pairing-generic finite-dimensional topological module layer used by
  Chapter 32 owner theorems.

Layer target: `bridge/view`, keeping the source-facing polyhedral hypothesis while delegating the
maximizer and extreme-point steps to existing owner theorems.
-/

section IsMaxOnLayer

variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [SMul 𝕜 (WithTopBot α)]

namespace Set.IsPolyhedral

/-- Corollary 32.3.4 owner form: if `C` is polyhedral, contains no affine lines, and `f '' C` is
bounded above, then `f` attains its maximum over `C` at an extreme point of `C`. Nonemptiness of
`C` is stated explicitly because attainment would otherwise be false for `C = ∅`.
-/
theorem exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E} (hC_poly : C.IsPolyhedral 𝕜)
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_nonempty : C.Nonempty)
    (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  have hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r) := by
    intro x r hsubset
    exact hC_bddAbove.mono (by
      intro z hz
      exact ⟨z, hsubset hz, rfl⟩)
  have hC_closed : IsClosed C := (hC_poly.isClosed_hasFiniteFaces).1
  obtain ⟨x, hxC, hxmax⟩ :=
    hC_poly.isFinitelyGeneratedConvex.exists_mem_isMaxOn_of_bddAbove_affineHalfLines
      hf_onC hC_nonempty hhalfLine_bddAbove
  exact exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_not_hasAffineLine
    hf hC_closed hC_poly.convex hC_dom hC_noAffineLine ⟨x, hxC, hxmax⟩

end Set.IsPolyhedral

/-- Corollary 32.3.4: if `C` is polyhedral, contains no affine lines, and `f '' C` is bounded
above, then `f` attains its maximum over `C` at an extreme point of `C`.
-/
theorem exists_mem_extremePoints_isMaxOn_of_polyhedral_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E}
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_poly : C.IsPolyhedral 𝕜)
    (hC_nonempty : C.Nonempty) (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C)
    (hC_dom : C ⊆ dom(f)) (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y :=
  hC_poly.exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
    hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove

end IsMaxOnLayer

section sSupLayer

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [AddCommMonoid α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [SMul 𝕜 (WithTopBot α)]

namespace Set.IsPolyhedral

/-- Corollary 32.3.4 value companion: under the hypotheses of the main corollary, some extreme
point of `C` realizes the supremum value `sSup (f '' C)`.
-/
theorem exists_mem_extremePoints_eq_sSup_image_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E} (hC_poly : C.IsPolyhedral 𝕜)
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_nonempty : C.Nonempty)
    (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  obtain ⟨y, hyext, hymax⟩ :=
    hC_poly.exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
      hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove
  refine ⟨y, hyext, le_antisymm ?_ ?_⟩
  · exact le_sSup <| Set.mem_image_of_mem f (mem_extremePoints.mp hyext).1
  · refine sSup_le ?_
    rintro _ ⟨z, hzC, rfl⟩
    exact hymax hzC

end Set.IsPolyhedral

/-- A source-facing supremum-value companion: under the hypotheses of the main corollary, some
extreme point of `C` realizes the supremum value `sSup (f '' C)`.
-/
theorem exists_mem_extremePoints_eq_sSup_image_of_polyhedral_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E}
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_poly : C.IsPolyhedral 𝕜)
    (hC_nonempty : C.Nonempty) (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C)
    (hC_dom : C ⊆ dom(f)) (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) :=
  hC_poly.exists_mem_extremePoints_eq_sSup_image_of_not_hasAffineLine_of_bddAbove
    hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove

end sSupLayer

end
