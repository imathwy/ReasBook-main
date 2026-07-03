import StacksProject_2024.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open Set
open Topology

section

variable {X Y : LCCat.{u}}

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

-- Proof sketch: for each `y : Y`, use surjectivity to view the fiber over `y` inside `X`. Properness
-- makes this fiber compact, so finitely many compact neighborhoods upstairs cover it. Since proper
-- maps are closed, the complement of the union of the corresponding source opens has closed image,
-- and its complement is the desired neighborhood of `y` contained in the image of one compact
-- subset of `X`.
/-- Lemma 21.31.4: if `f : X ⟶ Y` in `LC` is proper and surjective, then the singleton family
`{f : X ⟶ Y}` is a qc covering 1. -/
theorem IsQcCoveringOne.singleton_of_proper_surjective (f : X ⟶ Y)
    (hf : IsProperMap f) (hsurj : Function.Surjective f) :
    (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).IsQcCoveringOne := by
  letI : T2Space X.obj := X.property.1
  letI : WeaklyLocallyCompactSpace X.obj := X.property.2
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
  have hsingletonUnion :
      (⋃ i : ({PUnit.unit} : Finset PUnit),
          (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).obj i.1 |>.hom '' (fun _ ↦ closure V) i) =
        f '' closure V := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨i, hz⟩
      exact hz
    · intro hz
      simp only [Set.mem_iUnion]
      exact ⟨⟨PUnit.unit, by simp⟩, hz⟩
  refine ⟨({PUnit.unit} : Finset PUnit), fun _ ↦ closure V, ?_⟩
  constructor
  · intro _
    simpa using hV_compact
  · rw [hsingletonUnion]
    exact himageNhds

end
