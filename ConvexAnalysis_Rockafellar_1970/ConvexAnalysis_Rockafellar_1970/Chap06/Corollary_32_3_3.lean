import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_4

open scoped Rockafellar

section

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.3 concludes that the supremum of a convex function over `C` is
  attained when no half-line contained in `C` carries `f` unbounded above.
- `core/canonical`: the primitive set-side owner for the Chapter 19 finite-extreme bridge is
  `C.IsFinitelyGeneratedConvex R`; the canonical half-line surface is `affineHalfLine x r`; the
  canonical boundedness surface is `BddAbove (f '' s)`; and the canonical attainment owner is
  `IsMaxOn`.
- `bridge/view`: the source phrase “there are no half-lines in `C` on which `f` is unbounded
  above” is expressed directly as `BddAbove (f '' affineHalfLine x r)` on each included half-line.

Domain-style sampling used here:
- `Set.IsFinitelyGeneratedConvex` from `Chap04/Text_19_0_4`;
- `affineHalfLine` from `Chap04/Defn_18_4`;
- `ConvexOn` from the canonical convex-function owner layer;
- `IsMaxOn` as the canonical mathlib owner for attained suprema.

Primitive data vs derived API:
- primitive inputs: the convex function `f`, the feasible set `C`, the primitive finite-generation
  owner `C.IsFinitelyGeneratedConvex R`, convexity of `f` on `C`, explicit nonemptiness of `C`,
  and the source half-line boundedness hypothesis;
- derived API: existence of a maximizer in owner form `∃ x ∈ C, IsMaxOn f C x`, and the
  companion source wording `f x = sSup (f '' C)`.

Semantic-fidelity note:
- the extracted sentence omits the ambient setup needed by its proof. The explicit hypothesis
  `C.Nonempty` is made visible because attainment over `∅` would be false.

Ambient refinement:
- codomain layer: the public codomain surface is `WithTopBot α` rather than a concrete alias;
- scalar layer: the geometric owner is stated on the scalar-generic Chapter 18/19 layer.

Layer target: `core/canonical` for the primitive owner theorem.
-/

namespace Set.IsFinitelyGeneratedConvex

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type*} [AddCommMonoid E] [Module R E]

section IsMaxOnLayer

variable {α : Type*} [PartialOrder α] [AddCommMonoid α]
variable [SMul R α] [SMul R (WithTopBot α)]

/-- Core owner form of Corollary 32.3.3: for a nonempty finitely generated convex set `C`, if
`f` is convex on `C` and every affine half-line contained in `C` has bounded image under `f`,
then the supremum of `f` over `C` is attained. -/
theorem exists_mem_isMaxOn_of_bddAbove_affineHalfLines
    {f : E → WithTopBot α} {C : Set E} (hC_fg : C.IsFinitelyGeneratedConvex R)
    (hf : ConvexOn R C f) (hC_nonempty : C.Nonempty)
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray R E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r)) :
    ∃ x ∈ C, IsMaxOn f C x := by
  sorry

end IsMaxOnLayer

section sSupLayer

variable {α : Type*}
variable [ConditionallyCompleteLinearOrder α] [AddCommMonoid α]
variable [SMul R α] [SMul R (WithTopBot α)]

/-- Core owner companion to Corollary 32.3.3: under the same finitely generated hypotheses, some
point of `C` realizes the supremum value `sSup (f '' C)`. -/
theorem exists_mem_eq_sSup_image_of_bddAbove_affineHalfLines
    {f : E → WithTopBot α} {C : Set E} (hC_fg : C.IsFinitelyGeneratedConvex R)
    (hf : ConvexOn R C f) (hC_nonempty : C.Nonempty)
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray R E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r)) :
    ∃ x ∈ C, f x = sSup (f '' C) := by
  by_cases htop : ∃ x ∈ C, f x = (⊤ : WithTopBot α)
  · rcases htop with ⟨x, hxC, hfx_top⟩
    refine ⟨x, hxC, ?_⟩
    have hsSup_top : sSup (f '' C) = ⊤ := by
      exact top_le_iff.mp <| by
        simpa [hfx_top] using (le_sSup (Set.mem_image_of_mem f hxC))
    rw [hfx_top, hsSup_top]
  obtain ⟨x, hxC, hxmax⟩ :=
    hC_fg.exists_mem_isMaxOn_of_bddAbove_affineHalfLines
      hf hC_nonempty hhalfLine_bddAbove
  have hRange : Set.range (fun y : C ↦ f y) = f '' C := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hyC, rfl⟩
      exact ⟨⟨y, hyC⟩, rfl⟩
  refine ⟨x, hxC, ?_⟩
  calc
    f x = ⨆ y : C, f y := (hxmax.iSup_eq hxC).symm
    _ = sSup (Set.range fun y : C ↦ f y) := by rw [sSup_range]
    _ = sSup (f '' C) := by rw [hRange]

end sSupLayer

end Set.IsFinitelyGeneratedConvex

end
