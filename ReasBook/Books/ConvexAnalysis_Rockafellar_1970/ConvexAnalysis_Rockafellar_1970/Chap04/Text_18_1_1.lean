import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_18_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

section

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]

/-!
Source/core/bridge triage:
- Primary mathematical domain: faces of sets, ordered by inclusion.
- `source-facing`: Text 18.1.1 says that the family of faces of a convex set has arbitrary infima
  and suprema, and in finite-dimensional spaces has no infinite strictly decreasing chains of
  faces.
- `core/canonical`: the owner abstraction is `Set.IsFace`, with face-family owner
  `𝓕[R](C) = Set.IsFace.faces R C`, and the order-theoretic owner API is
  `lowerBounds`, `upperBounds`, `IsGreatest`, and `IsLeast`.
- `bridge/view`: the infimum clause is realized intrinsically as `⋂₀ (insert C S)`, and the
  supremum clause is the intersection of all face
  upper bounds of `S`; only the descending-chain clause uses the chapter's affine-dimension-drop
  theorem for proper faces, so that clause should stay on the same generalized owner layer rather
  than on a local concrete-scalar specialization.

Domain-style sampling used here:
- `Set.IsFace`;
- `Set.IsFace.faces` with notation `𝓕[R](C)`;
- `Set.IsFace.refl`;
- `Set.IsFace.sInter`;
- `lowerBounds`, `upperBounds`, `IsGreatest`, and `IsLeast`;
- the chapter's `Set.IsFace.affineDim_lt_of_ssubset`.

Primitive data vs derived API:
- primitive inputs: the ambient set `C` and a family `S` of its faces;
- derived API: the infimum and supremum statements in the face order, and the absence of infinite
  strictly decreasing chains of faces; for the descending-chain clause the source convexity
  hypothesis is redundant on the owner surface.
- ambient minimization: the lattice clauses already live on the ordered-semiring
  scalar-action layer of
  `Set.IsFace`, while the descending-chain clause should live on the ordered complete
  nontrivially normed field layer already used by
  `Set.IsFace.affineDim_lt_of_ssubset`.

Layer target:
- the lattice clauses are `source-facing` statements on `Set.IsFace`, derived from the owner
  theorems `Set.IsFace.refl` and `Set.IsFace.sInter`;
- the descending-chain clause is `bridge/view`, routed through affine dimension.
-/

namespace Set.IsFace

variable {C : Set E} {S : Set (Set E)}

/-- Owner-level infimum criterion on the face family: every nonempty subfamily of `𝓕[R](C)` has
the greatest lower bound given by its intersection. -/
theorem isGreatest_lowerBounds_sInter
    (hS_nonempty : S.Nonempty) (hS : S ⊆ 𝓕[R](C)) :
    IsGreatest (𝓕[R](C) ∩ lowerBounds S) (⋂₀ S) := by
  have hS_face : ∀ ⦃F : Set E⦄, F ∈ S → F.IsFace R C := by
    intro F hF
    simpa using hS hF
  refine ⟨?_, ?_⟩
  · constructor
    · exact sInter hS_nonempty fun F hF ↦ hS_face hF
    · intro F hF x hx
      exact (mem_sInter.mp hx) F hF
  · intro F hF x hx
    exact mem_sInter.mpr (fun T hT ↦ hF.2 hT hx)

/-- Text 18.1.1 (1): the collection of faces of `C` has arbitrary infima; concretely, for any
family `S ⊆ 𝓕[R](C)`, the set `⋂₀ (insert C S)` is the greatest face contained in every
member of `S`. -/
theorem isGreatest_lowerBounds_inter_sInter
    (hC : Convex R C) (hS : S ⊆ 𝓕[R](C)) :
    IsGreatest (𝓕[R](C) ∩ lowerBounds S) (⋂₀ insert C S) := by
  have hgreat_insert :
      IsGreatest (𝓕[R](C) ∩ lowerBounds (insert C S)) (⋂₀ insert C S) := by
    refine isGreatest_lowerBounds_sInter (C := C) (S := insert C S) ⟨C, by simp⟩ ?_
    intro F hF
    rcases mem_insert_iff.mp hF with rfl | hF
    · exact refl hC
    · exact hS hF
  refine ⟨?_, ?_⟩
  · refine ⟨hgreat_insert.1.1, ?_⟩
    intro F hF x hx
    have hF_insert : F ∈ insert C S := by simp [hF]
    exact hgreat_insert.1.2 hF_insert hx
  · intro F hF
    have hF_insert : F ∈ 𝓕[R](C) ∩ lowerBounds (insert C S) := by
      refine ⟨hF.1, ?_⟩
      intro G hG x hx
      rcases mem_insert_iff.mp hG with rfl | hG
      · exact hF.1.subset hx
      · exact hF.2 hG hx
    exact hgreat_insert.2 hF_insert

/-- Owner-level supremum criterion on the face family: if the set of face upper bounds of `S` is
nonempty, its intersection is their least element. -/
theorem isLeast_upperBounds_sInter_of_nonempty
    (hUB_nonempty : (𝓕[R](C) ∩ upperBounds S).Nonempty) :
    IsLeast (𝓕[R](C) ∩ upperBounds S) (⋂₀ (𝓕[R](C) ∩ upperBounds S)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact sInter hUB_nonempty fun F hF ↦ hF.1
    · intro G hG x hx
      exact mem_sInter.mpr fun F hF ↦ hF.2 hG hx
  · intro F hF
    exact sInter_subset_of_mem hF

/-- Text 18.1.1 (2): the collection of faces of `C` has arbitrary suprema; concretely, for any
family `S ⊆ 𝓕[R](C)`, the intersection of all face upper bounds of `S` is the least face
containing every member of `S`. -/
theorem isLeast_upperBounds_sInter
    (hC : Convex R C) (hS : S ⊆ 𝓕[R](C)) :
    IsLeast (𝓕[R](C) ∩ upperBounds S) (⋂₀ (𝓕[R](C) ∩ upperBounds S)) := by
  have hUB_nonempty : (𝓕[R](C) ∩ upperBounds S).Nonempty := by
    refine ⟨C, refl hC, ?_⟩
    intro F hF
    exact (hS hF).subset
  exact isLeast_upperBounds_sInter_of_nonempty (C := C) (S := S) hUB_nonempty

/-- Primitive owner criterion for Text 18.1.1 (3): if faces of `C` admit a rank map `μ` into a
codomain set `s` that is already well-founded for strict descent, and strict inclusion of faces
strictly decreases `μ`, then strict inclusion is well-founded on `𝓕[R](C)`. -/
theorem wellFoundedOn_ssubset_of_mapsTo
    {C : Set E} {α : Type*} [Preorder α] {μ : Set E → α} {s : Set α}
    (hμ_maps : MapsTo μ (𝓕[R](C)) s) (hμ_wf : s.WellFoundedOn (· > ·))
    (hμ_drop : ∀ {F G : Set E}, F ∈ 𝓕[R](C) → G ∈ 𝓕[R](C) → G ⊂ F → μ G < μ F) :
    (𝓕[R](C)).WellFoundedOn (fun F G ↦ G ⊂ F) := by
  have hμ_wf_on :
      (𝓕[R](C)).WellFoundedOn (Function.onFun (· > ·) μ) := by
    exact Set.WellFoundedOn.mapsTo μ hμ_maps hμ_wf
  exact hμ_wf_on.mono' fun F hF G hG hFG ↦ hμ_drop hF hG hFG

/-- Derived rank criterion on the canonical face-image surface: on a locally finite ordered
codomain, if the rank values `μ '' 𝓕[R](C)` are bounded above and strict face inclusion strictly
decreases `μ`, then strict inclusion is well-founded on `𝓕[R](C)`. -/
theorem wellFoundedOn_ssubset_of_bddAbove_image
    {C : Set E} {α : Type*} [Preorder α] [LocallyFiniteOrder α] {μ : Set E → α}
    (hμ_bdd : BddAbove (μ '' 𝓕[R](C)))
    (hμ_drop : ∀ {F G : Set E}, F ∈ 𝓕[R](C) → G ∈ 𝓕[R](C) → G ⊂ F → μ G < μ F) :
    (𝓕[R](C)).WellFoundedOn (fun F G ↦ G ⊂ F) := by
  refine wellFoundedOn_ssubset_of_mapsTo (C := C) (μ := μ) (s := μ '' 𝓕[R](C)) ?_ ?_ hμ_drop
  · intro F hF
    exact ⟨F, hF, rfl⟩
  · exact BddAbove.wellFoundedOn_gt hμ_bdd

/-- Bridge form of `wellFoundedOn_ssubset_of_bddAbove_image`: if rank values map into a
bounded-above codomain set `s`, then strict inclusion is well-founded on `𝓕[R](C)`. -/
theorem wellFoundedOn_ssubset_of_mapsTo_bddAbove
    {C : Set E} {α : Type*} [Preorder α] [LocallyFiniteOrder α] {μ : Set E → α} {s : Set α}
    (hμ_maps : MapsTo μ (𝓕[R](C)) s) (hs_bdd : BddAbove s)
    (hμ_drop : ∀ {F G : Set E}, F ∈ 𝓕[R](C) → G ∈ 𝓕[R](C) → G ⊂ F → μ G < μ F) :
    (𝓕[R](C)).WellFoundedOn (fun F G ↦ G ⊂ F) := by
  have hμ_bdd : BddAbove (μ '' 𝓕[R](C)) := by
    rcases hs_bdd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro b hb
    rcases hb with ⟨F, hF, rfl⟩
    exact ha (hμ_maps hF)
  exact wellFoundedOn_ssubset_of_bddAbove_image hμ_bdd hμ_drop

end Set.IsFace

end

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [OrderTopology 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

namespace Set.IsFace

/-- Text 18.1.1 (3): every strictly decreasing chain of faces of a set in a finite-dimensional
normed `𝕜`-space has finite length, expressed intrinsically as well-foundedness of strict
inclusion on the set of faces of `C`. The source states this for convex `C`, but that binder
is redundant in the owner API: if `F' ⊊ F` are faces of `C`, then `F'` is a proper face of the
convex set `F`, so Corollary 18.1.3 already forces a strict affine-dimension drop. Specializing
to concrete coordinate models recovers the textbook presentation. -/
-- Proof sketch: measure a face by its affine dimension. Every face has affine dimension at most
-- `Module.finrank 𝕜 E`, so the possible values are bounded above in `ℤ`, hence well-founded for
-- `>`. A strict inclusion `F' ⊂ F` of faces makes `F'` a proper face of the convex face `F`, so
-- Corollary 18.1.3 gives `Set.affineDim 𝕜 F' < Set.affineDim 𝕜 F`.
theorem wellFoundedOn_ssubset {C : Set E} :
    (𝓕[𝕜](C)).WellFoundedOn (fun F G ↦ G ⊂ F) := by
  let μ : Set E → ℤ := fun F ↦ Set.affineDim 𝕜 F
  have hμ_maps :
      MapsTo μ (𝓕[𝕜](C)) (Set.Iic (Module.finrank 𝕜 E : ℤ)) := by
    intro F hF
    have hbound : Set.affineDim 𝕜 F ≤ (Module.finrank 𝕜 E : ℤ) := by
      by_cases hspan : affineSpan 𝕜 F = ⊥
      · have hF_empty : F = ∅ := (affineSpan_eq_bot _).mp hspan
        simp [Set.affineDim, AffineSubspace.affineDim, hF_empty]
      · rw [Set.affineDim, AffineSubspace.affineDim, if_neg hspan]
        exact_mod_cast Submodule.finrank_le (affineSpan 𝕜 F).direction
    simpa [μ, Set.mem_Iic] using hbound
  have hμ_bdd : BddAbove (μ '' 𝓕[𝕜](C)) := by
    refine ⟨(Module.finrank 𝕜 E : ℤ), ?_⟩
    intro n hn
    rcases hn with ⟨F, hF, rfl⟩
    simpa [Set.mem_Iic] using hμ_maps hF
  refine wellFoundedOn_ssubset_of_bddAbove_image (C := C) (μ := μ) hμ_bdd ?_
  intro F G hF hG hFG
  have hG_face_F : G.IsFace 𝕜 F := hG.mono hFG.1 hF.subset
  simpa [μ] using hG_face_F.affineDim_lt_of_ssubset hF.convex hFG

end Set.IsFace

end
