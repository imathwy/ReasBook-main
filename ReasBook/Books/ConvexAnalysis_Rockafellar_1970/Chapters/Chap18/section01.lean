import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_18_1_1 (from Chap04) -/
section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.1.1 says that a face `C'` of a convex set `C`, represented by
  `C'.IsFace 𝕜 C`, is exactly the
  intersection of `C` with the intrinsic closure of `C'`; the ambient `closure` formulation is a
  finite-dimensional bridge corollary, and therefore a face is closed whenever `C` is closed.
- `core/canonical`: the source-facing owner is `Set.IsFace`, together with the upstream owner
  theorem `Set.IsFace.subset_of_nonempty_inter_ri`, plus `intrinsicClosure` and
  `IsClosed`.
- `bridge/view`: the ambient closure identity is a theorem-level bridge obtained from
  `intrinsicClosure_eq_closure`.

Domain-style sampling used here:
- `Set.IsFace.subset_of_nonempty_inter_ri`;
- `Set.IsFace.subset`;
- `Convex 𝕜 C`;
- `intrinsicClosure` and `subset_intrinsicClosure`;
- `intrinsicClosure_eq_closure`;
- `IsClosed.inter` and `isClosed_closure`.

Primitive data vs derived API:
- primitive owner input: the face hypothesis `C'.IsFace 𝕜 C` together with the meet witness
  `(C' ∩ ri[𝕜](C ∩ intrinsicClosure 𝕜 C')).Nonempty`;
  plus convexity of `C` yields the same intrinsic identity directly;
- derived finite-dimensional bridge API: finite-dimensional hypotheses plus an explicit witness
  `C'.Nonempty` produce the owner-level relative-interior witness via
  `Convex.intrinsicInterior_nonempty`.
- ambient closure bridge and closedness are then derived.

Layer target: the intrinsic closure identity is `source-facing`; the ambient closure statement and
closedness theorem are `bridge/view` corollaries.

Ambient refinement: the primitive owner theorem only uses `Theorem_18_1`, hence it stays on the
same scalar-general owner layer as `Set.IsFace.subset_of_nonempty_inter_ri`. Finite-dimensional
normed assumptions are needed only for the bridge from `C'.Nonempty` (via
`Convex.intrinsicInterior_nonempty`, then `Convex.ri_intrinsicClosure_eq_ri`) and for the ambient
closure bridge
`intrinsicClosure_eq_closure`. Specializing `𝕜 = ℝ` recovers the textbook formulation.
-/

namespace Set.IsFace

section PrimitiveOwner

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Primitive owner form behind Corollary 18.1.1: if a face `C'` of `C` meets
`ri[𝕜](C ∩ intrinsicClosure 𝕜 C')`, then `C' = C ∩ intrinsicClosure 𝕜 C'`. -/
theorem eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hmeet : (C' ∩ ri[𝕜](C ∩ intrinsicClosure 𝕜 C')).Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact ⟨hC'.subset hx, subset_intrinsicClosure hx⟩
  · exact hC'.subset_of_nonempty_inter_ri inter_subset_left hmeet

end PrimitiveOwner

section RelativeInteriorBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Owner-level bridge to `eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter`: a
nonempty relative interior witness for `C'` provides the needed meet condition. -/
theorem eq_inter_intrinsicClosure_of_nonempty_ri {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hriC' : (ri[𝕜](C')).Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  let D := C ∩ intrinsicClosure 𝕜 C'
  have hC'D : C' ⊆ D := by
    intro x hx
    exact ⟨hC'.subset hx, subset_intrinsicClosure hx⟩
  have hD_conv : Convex 𝕜 D := hC.inter (Convex.intrinsicClosure (𝕜 := 𝕜) hC'.convex)
  have hclosure : intrinsicClosure 𝕜 D = intrinsicClosure 𝕜 C' := by
    refine Subset.antisymm ?_ (intrinsicClosure_mono (𝕜 := 𝕜) hC'D)
    simpa [D] using
      intrinsicClosure_mono (𝕜 := 𝕜)
        (inter_subset_right : C ∩ intrinsicClosure 𝕜 C' ⊆ intrinsicClosure 𝕜 C')
  have hri : ri[𝕜](C') = ri[𝕜](D) := by
    calc
      ri[𝕜](C') = ri[𝕜](intrinsicClosure 𝕜 C') := by
        simpa using (hC'.convex.ri_intrinsicClosure_eq_ri_of_nonempty hriC').symm
      _ = ri[𝕜](intrinsicClosure 𝕜 D) := by rw [← hclosure]
      _ = ri[𝕜](D) := by
        simpa using hD_conv.ri_intrinsicClosure_eq_ri
  rcases hriC' with ⟨x, hxri⟩
  have hmeet : (C' ∩ ri[𝕜](D)).Nonempty := by
    refine ⟨x, intrinsicInterior_subset hxri, ?_⟩
    rwa [hri] at hxri
  simpa [D] using hC'.eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter hmeet

end RelativeInteriorBridge

section FiniteDimensionalBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Finite-dimensional bridge to `eq_inter_intrinsicClosure_of_nonempty_ri`: an explicit witness
`C'.Nonempty` provides the needed relative-interior witness. -/
theorem eq_inter_intrinsicClosure_of_nonempty {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hC'ne : C'.Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  exact hC'.eq_inter_intrinsicClosure_of_nonempty_ri hC
    (hC'.convex.intrinsicInterior_nonempty hC'ne)

/-- Primitive ambient-closure bridge for Corollary 18.1.1, from
`eq_inter_intrinsicClosure_of_nonempty`. -/
theorem eq_inter_closure_of_nonempty {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C)
    (hC'ne : C'.Nonempty) :
    C' = C ∩ closure C' := by
  simpa [intrinsicClosure_eq_closure 𝕜 C'] using
    hC'.eq_inter_intrinsicClosure_of_nonempty hC hC'ne

end FiniteDimensionalBridge

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Corollary 18.1.1, intrinsic owner form: a face `C'` of a convex set `C`, represented by
`C'.IsFace 𝕜 C`, is exactly `C ∩ intrinsicClosure 𝕜 C'`. -/
theorem eq_inter_intrinsicClosure {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  obtain rfl | hC'ne := Set.eq_empty_or_nonempty C'
  · simp
  exact hC'.eq_inter_intrinsicClosure_of_nonempty hC hC'ne

/-- Corollary 18.1.1, ambient-closure bridge: in the same finite-dimensional setting,
`eq_inter_intrinsicClosure` rewrites to `C' = C ∩ closure C'`. -/
theorem eq_inter_closure {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) :
    C' = C ∩ closure C' := by
  simpa [intrinsicClosure_eq_closure 𝕜 C'] using hC'.eq_inter_intrinsicClosure hC

/-- A face of a closed convex set is closed. -/
-- Proof sketch: rewrite `C'` using `hC'.eq_inter_closure hC`; then `C ∩ closure C'` is
-- closed because it is the intersection of the closed set `C` with the closed set `closure C'`.
theorem isClosed {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hC_closed : IsClosed C) : IsClosed C' := by
  rw [hC'.eq_inter_closure hC]
  exact hC_closed.inter isClosed_closure

end SourceFacing

end Set.IsFace

end

/-! ### Text_18_1_1 (from Chap04) -/
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

/-! ### Theorem_18_1 (from Chap04) -/
section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- Primary mathematical domain: convex faces and relative interior over an ordered normed field.
- `source-facing`: Theorem 18.1 says that if a subset `D ⊆ C` has relative interior meeting a
  face `C'` of `C`, then the whole of `D` lies in that face.
- `core/canonical`: the primitive owner abstraction is the extreme-subset predicate
  `IsExtreme 𝕜 C C'` together with open-segment membership from points of `D`; the
  source-facing theorem is then
  obtained by the chapter relative-interior notation `ri[𝕜](D) = intrinsicInterior 𝕜 D`.
- `bridge/view`: Rockafellar's face language is represented by `C'.IsFace 𝕜 C`, while
  `ri[𝕜](D)` is represented by `intrinsicInterior 𝕜 D`; the segment prolongation bridge is
  supplied by the project owner theorem
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`.
- Domain-style sampling used here:
  `Set.IsFace` from `Defn_18_1`,
  `IsExtreme.left_mem_of_mem_openSegment`,
  `IsExtreme.right_mem_of_mem_openSegment`,
  `ri[𝕜](·)`,
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`,
  and `lineMap_mem_openSegment`.
- Primitive data vs derived API: the primitive owner theorem uses the extreme-subset hypothesis
  `IsExtreme 𝕜 C C'`, containment `D ⊆ C`, and the open-segment witness hypothesis
  `∀ x ∈ D, ∃ y ∈ D, z ∈ openSegment 𝕜 x y`; the relative-interior theorem is a bridge obtained
  from this primitive owner layer by
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`.
- Layer target: primitive owner theorem on `IsExtreme`, then bridge theorems on
  `ri[𝕜](·)` and `Set.IsFace`.
- Redundant-source-assumption check: the textbook states the result for faces of a convex set, but
  the proof only uses the owner face hypothesis `C'.IsFace 𝕜 C`, the containment `D ⊆ C`,
  and the relative-interior neighborhood at a meeting point. No separate ambient convexity binder
  on `C` changes the mathematical content here, so the refined statement omits it.
- Ambient refinement: the statement only uses the owner face and relative-interior APIs together
  with the Chapter 2 prolongation theorem, so the ambient scalar does not need to be fixed to
  `ℝ`. Specializing `𝕜 = ℝ` recovers the textbook presentation.
-/

namespace IsExtreme

/-- Primitive owner form behind Theorem 18.1: if `C'` is an extreme subset of `C`, `D ⊆ C`,
`z ∈ C'`, and each `x ∈ D` can be joined to another `y ∈ D` with `z` on the open segment
`openSegment 𝕜 x y`, then `D ⊆ C'`. -/
theorem subset_of_forall_exists_mem_openSegment
    {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C) {z : E} (hzC' : z ∈ C')
    (hseg : ∀ x ∈ D, ∃ y ∈ D, z ∈ openSegment 𝕜 x y) :
    D ⊆ C' := by
  intro x hxD
  rcases hseg x hxD with ⟨y, hyD, hzSeg⟩
  exact hC'.left_mem_of_mem_openSegment (hDC hxD) (hDC hyD) hzC' hzSeg

section IntrinsicInteriorBridge

open AffineMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Primitive witness form of Theorem 18.1 on the `IsExtreme` owner: if
`z ∈ C' ∩ ri[𝕜](D)`, then `D ⊆ C'`. -/
theorem subset_of_mem_inter_ri
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C) {z : E}
    (hz : z ∈ C' ∩ ri[𝕜](D)) :
    D ⊆ C' := by
  refine hC'.subset_of_forall_exists_mem_openSegment hDC hz.1 ?_
  intro x hxD
  rcases Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hz.2 x hxD with
    ⟨μ, hμ, hyD⟩
  have hμpos : 0 < μ := zero_lt_one.trans hμ
  have hμ0 : μ ≠ 0 := hμpos.ne'
  have hμInv : μ⁻¹ ∈ Set.Ioo (0 : 𝕜) 1 := by
    exact ⟨inv_pos.mpr hμpos, (inv_lt_one₀ hμpos).2 hμ⟩
  have hzSeg : z ∈ openSegment 𝕜 x (lineMap x z μ) := by
    simpa [hμ0] using
      (lineMap_mem_openSegment 𝕜 x (lineMap x z μ) hμInv :
        lineMap x (lineMap x z μ) μ⁻¹ ∈ openSegment 𝕜 x (lineMap x z μ))
  exact ⟨lineMap x z μ, hyD, hzSeg⟩

/-- Primitive owner form of Theorem 18.1: an extreme subset `C'` of `C` contains every subset
`D ⊆ C` whose relative interior meets `C'`. -/
theorem subset_of_nonempty_inter_ri
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  rcases hmeet with ⟨z, hz⟩
  exact hC'.subset_of_mem_inter_ri hDC hz

end IntrinsicInteriorBridge

end IsExtreme

namespace Set.IsFace

section IntrinsicInteriorBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! `source-facing` theorem surface in face-family notation. -/
/-- Theorem 18.1 on the face-family surface: if `C' ∈ 𝓕[𝕜](C)` and a subset `D ⊆ C` has
relative interior meeting `C'`, then `D ⊆ C'`. -/
theorem subset_of_nonempty_inter_ri_of_mem_faces
    {C C' D : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  exact (mem_faces_iff.mp hC').isExtreme.subset_of_nonempty_inter_ri hDC hmeet

-- Proof sketch: pass from face language to its primitive owner payload `hC'.isExtreme`, then
-- apply `IsExtreme.subset_of_nonempty_inter_ri`.
/-- Theorem 18.1: if `C'` is a face of `C`, represented by `C'.IsFace 𝕜 C`, and a subset
`D ⊆ C` has relative interior `ri[𝕜](D)` meeting `C'`, then `D ⊆ C'`. The source
also assumes `C` convex, but that ambient convexity hypothesis is redundant for this owner-level
statement. -/
theorem subset_of_nonempty_inter_ri
    {C C' D : Set E} (hC' : C'.IsFace 𝕜 C) (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  exact subset_of_nonempty_inter_ri_of_mem_faces (C := C) (C' := C') (D := D)
    (mem_faces_iff.mpr hC') hDC hmeet

end IntrinsicInteriorBridge
end Set.IsFace

end

/-! ### Corollary_18_1_2 (from Chap04) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.1.2 says that two faces of `C` are equal whenever their relative
  interiors meet.
- `core/canonical`: the primitive owner is `IsExtreme 𝕜 C ·`, while the source-facing owners are
  chapter face-family membership `C' ∈ 𝓕[𝕜](C)` and `Set.IsFace`; relative interior is written on
  theorem surfaces as `ri[𝕜](·)`.
- `bridge/view`: Rockafellar's face language is represented by `C' ∈ 𝓕[𝕜](C)` and
  `C'' ∈ 𝓕[𝕜](C)`, bridged to the primitive owner through `mem_faces_iff` and
  `hC'.isExtreme`/`hC''.isExtreme`.
- Domain-style sampling used here:
  `IsExtreme.eq_of_nonempty_inter_ri`,
  `IsExtreme.subset_of_nonempty_inter_ri`,
  `IsExtreme.subset`,
  `ri[𝕜](·)`,
  and `intrinsicInterior_subset`.
- Primitive data vs derived API: the primitive inputs are the two extreme-subset hypotheses and
  the source-level nonempty relative-interior intersection
  `(ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty`. Face hypotheses are bridge data that provide the
  corresponding extreme-subset hypotheses.
- Layer target: primitive theorem in `IsExtreme`, then source-facing bridge theorems on
  `𝓕[𝕜](C)` and `Set.IsFace`.

The source assumes `C` is convex, but for this equality statement the proof only uses the two face
hypotheses themselves, so no separate ambient convexity binder is needed.

Ambient refinement: the proof only uses the owner theorem from `Theorem_18_1` and
`intrinsicInterior_subset`, so neither finite-dimensionality, nor the specialization `𝕜 = ℝ`, nor
the concrete model `EuclideanSpace ℝ (Fin n)` is part of the mathematical content.
-/

namespace IsExtreme

variable {C C' C'' : Set E}

/-- Primitive one-sided owner form behind Corollary 18.1.2: if the relative interiors of two
extreme subsets of `C` meet, then the first subset is contained in the second. -/
private theorem subset_of_nonempty_inter_ri_ri_aux
    (hC' : IsExtreme 𝕜 C C') (hC'' : IsExtreme 𝕜 C C'')
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' ⊆ C'' := by
  exact hC''.subset_of_nonempty_inter_ri hC'.subset
    (hri.mono fun x hx ↦ ⟨intrinsicInterior_subset hx.2, hx.1⟩)

/-- Primitive owner form behind Corollary 18.1.2: if the relative interiors of two extreme
subsets meet, then the subsets are equal. -/
theorem eq_of_nonempty_inter_ri
    (hC' : IsExtreme 𝕜 C C') (hC'' : IsExtreme 𝕜 C C'')
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  refine subset_antisymm ?_ ?_
  · exact subset_of_nonempty_inter_ri_ri_aux hC' hC'' hri
  · exact subset_of_nonempty_inter_ri_ri_aux hC'' hC'
      (hri.mono fun x hx ↦ ⟨hx.2, hx.1⟩)

end IsExtreme

namespace Set.IsFace

variable {C C' C'' : Set E}

/-- Corollary 18.1.2 on the chapter face-family surface: if `C'` and `C''` are members of
`𝓕[𝕜](C)` and their relative interiors have a point in common, then `C' = C''`. -/
theorem eq_of_nonempty_inter_ri_of_mem_faces
    (hC' : C' ∈ 𝓕[𝕜](C)) (hC'' : C'' ∈ 𝓕[𝕜](C))
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  exact (mem_faces_iff.mp hC').isExtreme.eq_of_nonempty_inter_ri
    (mem_faces_iff.mp hC'').isExtreme hri

/-- Corollary 18.1.2: if `C'` and `C''` are faces of `C`, represented by `C'.IsFace 𝕜 C` and
`C''.IsFace 𝕜 C`, and their relative interiors have a point in common, then `C' = C''`. -/
-- Proof sketch: route through the chapter face-family notation theorem
-- `eq_of_nonempty_inter_ri_of_mem_faces`.
theorem eq_of_nonempty_inter_ri
    (hC' : C'.IsFace 𝕜 C) (hC'' : C''.IsFace 𝕜 C)
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  exact eq_of_nonempty_inter_ri_of_mem_faces (mem_faces_iff.mpr hC') (mem_faces_iff.mpr hC'') hri

end Set.IsFace

end

/-! ### Corollary_18_1_3 (from Chap04) -/
section

open scoped Rockafellar

namespace IsExtreme

section AmbientNonempty

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]

/-- Owner-level properness consequence: if `C'` is a proper extreme subset of `C`, then `C` is
nonempty. -/
theorem ambient_nonempty_of_ne
    {C C' : Set E} (hC' : IsExtreme R C C') (hne : C' ≠ C) :
    C.Nonempty := by
  by_contra hCne
  have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
  apply hne
  rw [hCempty]
  exact Set.Subset.antisymm (by
    intro x hx
    simpa [hCempty] using hC'.subset hx) (Set.empty_subset _)

/-- Strict-inclusion surface of `ambient_nonempty_of_ne` on the primitive owner. -/
theorem ambient_nonempty_of_ssubset
    {C C' : Set E} (hC' : IsExtreme R C C') (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact hC'.ambient_nonempty_of_ne hssub.ne

end AmbientNonempty

end IsExtreme

namespace Set.IsFace

section AmbientNonempty

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]

/-- Face-family notation surface of properness: if `C' ∈ 𝓕[R](C)` and `C' ≠ C`, then `C` is
nonempty. -/
theorem ambient_nonempty_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[R](C)) (hne : C' ≠ C) :
    C.Nonempty := by
  exact (mem_faces_iff.mp hC').isExtreme.ambient_nonempty_of_ne hne

/-- Owner-level properness consequence: if `C'` is a proper face of `C`, then `C` is nonempty. -/
theorem ambient_nonempty_of_ne
    {C C' : Set E} (hC' : C'.IsFace R C) (hne : C' ≠ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ne_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hne

/-- Face-family notation strict-inclusion surface of `ambient_nonempty_of_ne_of_mem_faces`. -/
theorem ambient_nonempty_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[R](C)) (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ne_of_mem_faces hC' hssub.ne

/-- Strict-inclusion surface of `ambient_nonempty_of_ne` on `Set.IsFace`. -/
theorem ambient_nonempty_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace R C) (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hssub

end AmbientNonempty

end Set.IsFace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage:

- Primary mathematical domain: faces, relative boundary, and affine dimension in
  finite-dimensional normed spaces over an ordered complete nontrivially normed field.
- `source-facing`: Corollary 18.1.3 says that a proper face of a convex set lies in the relative
  boundary of the ambient set, and therefore has strictly smaller affine dimension.
- `core/canonical`: the primitive owner abstraction is `IsExtreme 𝕜 C C'`, while the
  source-facing bridge owner is `Set.IsFace`; the codomain-side owners are `rb[𝕜](·)` and the
  chapter owner theorem `Convex.affineDim_lt_of_subset_rb`.
- `bridge/view`: first prove the proper-extreme-subset to relative-boundary inclusion on
  `IsExtreme`, then route the affine-dimension clause through the canonical face owner
  `Set.IsFace`.

Domain-style sampling used here:
- `IsExtreme.subset_of_nonempty_inter_ri`;
- `IsExtreme.subset`;
- `rb[𝕜](·)`;
- `intrinsicClosure_diff_intrinsicInterior`;
- `Convex.affineDim_lt_of_subset_rb`.
- Primitive data vs derived API: the primitive owner input is `IsExtreme 𝕜 C C'` for the
  relative-boundary inclusion. The affine-dimension drop is source-facing on `Set.IsFace`, where
  face convexity is carried by the owner itself.
- Layer target: primitive owner theorem on `IsExtreme` for boundary inclusion, then source-facing
  bridge theorems on `Set.IsFace` (including the affine-dimension drop).
- Ambient refinement: the face-to-boundary step already lives on the ordered nontrivially normed
  field layer used by `Theorem_18_1`, and the affine-dimension drop then follows on the stronger
  finite-dimensional ordered-complete layer required by
  `Convex.affineDim_lt_of_subset_rb`.
-/

namespace IsExtreme

section RelativeBoundary

variable [IsStrictOrderedRing 𝕜]

/-- Primitive owner form of Corollary 18.1.3: a proper extreme subset `C'` of `C` lies in the
relative boundary `rb[𝕜](C)` of `C`. -/
-- Proof sketch: if some point of `C'` lay in `ri[𝕜](C)`, then Theorem 18.1 applied to `D = C`
-- would give `C ⊆ C'`. Together with `hC'.subset`, that would force `C' = C`, contradicting
-- properness. Since `C' ⊆ C ⊆ intrinsicClosure 𝕜 C`, disjointness from the relative interior
-- rewrites through `intrinsicClosure_diff_intrinsicInterior`.
theorem subset_rb_of_ne
    {C C' : Set E} (hC' : IsExtreme 𝕜 C C') (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  intro x hxC'
  have hxC : x ∈ C := hC'.subset hxC'
  have hx_not_ri : x ∉ ri[𝕜](C) := by
    intro hxri
    have hC_subset : C ⊆ C' :=
      hC'.subset_of_nonempty_inter_ri subset_rfl ⟨x, hxC', hxri⟩
    exact hne <| Set.Subset.antisymm hC'.subset hC_subset
  rw [← intrinsicClosure_diff_intrinsicInterior]
  exact ⟨subset_intrinsicClosure hxC, hx_not_ri⟩

/-- Properness-on-`⊂` surface for Corollary 18.1.3 on the primitive owner: a strict extreme
subset of `C` lies in `rb[𝕜](C)`. -/
theorem subset_rb_of_ssubset
    {C C' : Set E} (hC' : IsExtreme 𝕜 C C') (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact hC'.subset_rb_of_ne hssub.ne

end RelativeBoundary

end IsExtreme

namespace Set.IsFace

section RelativeBoundary

variable [IsStrictOrderedRing 𝕜]

/-- Face-family notation form of Corollary 18.1.3: if `C' ∈ 𝓕[𝕜](C)` and `C' ≠ C`, then
`C' ⊆ rb[𝕜](C)`. -/
theorem subset_rb_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  exact (mem_faces_iff.mp hC').isExtreme.subset_rb_of_ne hne

/-- Corollary 18.1.3: a face `C'` of a convex set `C` that is not equal to `C` is contained in the
relative boundary `rb[𝕜](C)` of `C`. -/
theorem subset_rb_of_ne
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ne_of_mem_faces (C := C) (C' := C') (mem_faces_iff.mpr hC') hne

/-- Corollary 18.1.3 on strict inclusion, face-family notation surface. -/
theorem subset_rb_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ne_of_mem_faces hC' hssub.ne

/-- Corollary 18.1.3 on strict inclusion: a strict face of `C` lies in `rb[𝕜](C)`. -/
theorem subset_rb_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hssub

section

variable [OrderTopology 𝕜] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Face-family notation owner surface: if `C' ∈ 𝓕[𝕜](C)` is proper and `C` is convex, then
`dim[𝕜](C') < dim[𝕜](C)`. -/
theorem affineDim_lt_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hC : Convex 𝕜 C) (hne : C' ≠ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  have hFace : C'.IsFace 𝕜 C := mem_faces_iff.mp hC'
  have hCne : C.Nonempty := ambient_nonempty_of_ne_of_mem_faces hC' hne
  exact Convex.affineDim_lt_of_subset_rb hC hCne hFace.convex
    (subset_rb_of_ne_of_mem_faces hC' hne)

/-- A proper face of a convex set in a finite-dimensional normed `𝕜`-space has strictly smaller
affine dimension than the ambient convex set. -/
theorem affineDim_lt_of_ne
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) (hne : C' ≠ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ne_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hC hne

/-- Face-family notation strict-inclusion surface of `affineDim_lt_of_ne_of_mem_faces`. -/
theorem affineDim_lt_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hC : Convex 𝕜 C) (hssub : C' ⊂ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ne_of_mem_faces hC' hC hssub.ne

/-- A strict face of a convex set in a finite-dimensional normed `𝕜`-space has strictly smaller
affine dimension than the ambient convex set. -/
theorem affineDim_lt_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) (hssub : C' ⊂ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hC hssub

end

end RelativeBoundary

end Set.IsFace

end
