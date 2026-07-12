import Mathlib.Topology.Maps.Proper.Basic
import StacksProject_2024.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open Set
open Topology

section

variable {X Y : LCCat.{u}}

namespace CategoryTheory.SemiRepresentableFamily.Over.IsQcCoveringOne

/- Domain-style sampling for Lemma 21.31.4:
- primary domain: qc-covering families in `LC` and their interaction with proper maps of
  Hausdorff weakly locally compact spaces;
- sampled owner declarations:
  `SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `SemiRepresentableFamily.Over.IsQcCoveringOne.exists_finite_compact_image_neighborhood`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `quasiProper_closed_iff_isProperMap`,
  `IsProperMap`;
- best owner abstraction: `SemiRepresentableFamily.Over.IsQcCoveringOne` is the source-facing
  owner predicate, so this file should contribute an owner-level closure lemma rather than a
  parallel standalone theorem name;
- primitive vs derived:
  primitive data are the singleton owner family `ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)` and
  the hypotheses `IsProperMap f`, `Function.Surjective f`;
  the qc-covering conclusion is derived API for the owner predicate.

Source/core/bridge triage:
- `source-facing`: the singleton qc covering induced by a proper surjective map in `LC`;
- `core/canonical`: the owner predicate `SemiRepresentableFamily.Over.IsQcCoveringOne` and
  mathlib's proper-map owner `IsProperMap`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows` for the singleton indexed family, with
  no further wrapper layer. -/

-- Proof sketch: for a singleton indexed family, the finite image-union witness in the definition
-- can be merged into one compact subset of the source by taking a finite union; conversely, one
-- compact witness gives the singleton qc-covering datum immediately.
/-- The qc-covering condition for a singleton family is equivalent to requiring that every target
point has a neighborhood contained in the image of one compact subset of the source. -/
theorem singleton_isQcCoveringOne_iff (f : X ⟶ Y) :
    (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).IsQcCoveringOne ↔
      ∀ y : Y.obj, ∃ K : Set X.obj, IsCompact K ∧ f '' K ∈ 𝓝 y := by
  rw [ofArrows_isQcCoveringOne_iff]
  constructor
  · intro h y
    obtain ⟨s, E, hEcompact, hEnhds⟩ := h y
    refine ⟨⋃ i : s, E i, ?_, ?_⟩
    · simpa using isCompact_iUnion fun i : s ↦ hEcompact i
    · have himage :
          f '' (⋃ i : s, E i) = ⋃ i : s, f '' E i := by
            ext z
            constructor
            · rintro ⟨x, hx, rfl⟩
              simp only [Set.mem_iUnion] at hx ⊢
              rcases hx with ⟨i, hxi⟩
              exact ⟨i, ⟨x, hxi, rfl⟩⟩
            · simp only [Set.mem_iUnion]
              rintro ⟨i, x, hx, rfl⟩
              exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
      simpa [himage] using hEnhds
  · intro h y
    obtain ⟨K, hKcompact, hKnhds⟩ := h y
    refine ⟨{PUnit.unit}, fun _ ↦ K, ?_, ?_⟩
    · intro _
      simpa using hKcompact
    · have hsingle :
          (⋃ i : ({PUnit.unit} : Finset PUnit), f '' K) = f '' K := by
            ext z
            constructor
            · intro hz
              simp only [Set.mem_iUnion] at hz
              rcases hz with ⟨i, hz⟩
              exact hz
            · intro hz
              exact Set.mem_iUnion.mpr ⟨⟨PUnit.unit, by simp⟩, hz⟩
      rw [hsingle]
      exact hKnhds

-- Proof sketch: for each `y : Y`, use surjectivity to view the fiber over `y` inside `X`. Properness
-- makes this fiber compact, so finitely many compact neighborhoods upstairs cover it. Since proper
-- maps are closed, the complement of the union of the corresponding source opens has closed image,
-- and its complement is the desired neighborhood of `y` contained in the image of one compact
-- subset of `X`.
/-- Lemma 21.31.4: if `f : X ⟶ Y` in `LC` is proper and surjective, then the singleton family
`{f : X ⟶ Y}` is a qc covering 1. -/
@[stacks 09X5]
theorem singleton_of_proper_surjective (f : X ⟶ Y)
    (hf : IsProperMap f) (hsurj : Function.Surjective f) :
    (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).IsQcCoveringOne := by
  rw [singleton_isQcCoveringOne_iff]
  intro y
  have hfiberCompact : IsCompact (f ⁻¹' ({y} : Set Y.obj)) :=
    hf.isCompact_preimage isCompact_singleton
  obtain ⟨V, hV_open, hfiber_subset, hV_compact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hfiberCompact
  have himageNhds : f '' closure V ∈ 𝓝 y := by
    have himageClosed : IsClosed (f '' Vᶜ) :=
      hf.isClosedMap _ hV_open.isClosed_compl
    have hy_not_mem : y ∉ f '' Vᶜ := by
      rintro ⟨x, hxV, rfl⟩
      exact hxV <| hfiber_subset <| by simp
    refine Filter.mem_of_superset (himageClosed.isOpen_compl.mem_nhds hy_not_mem) ?_
    intro z hz
    rcases hsurj z with ⟨x, rfl⟩
    have hxV : x ∈ V := by
      by_contra hxV
      have hz' : f x ∉ f '' Vᶜ := by
        simpa using hz
      exact hz' ⟨x, by simpa using hxV, rfl⟩
    exact ⟨x, subset_closure hxV, rfl⟩
  exact ⟨closure V, hV_compact, himageNhds⟩

end CategoryTheory.SemiRepresentableFamily.Over.IsQcCoveringOne

end
