import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_18_1_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace Set.IsFace

section RiNonemptyFaceFamily

open scoped Rockafellar

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable (𝕜)

/-- Rockafellar's Chapter 18 family `𝒰`: relative interiors of the nonempty faces of `C`. -/
def riNonemptyFaces (C : Set E) : Set (Set E) :=
  (fun F : Set E ↦ ri[𝕜](F)) '' {F : Set E | F.IsFace 𝕜 C ∧ F.Nonempty}

@[simp] theorem mem_riNonemptyFaces_iff {C U : Set E} :
    U ∈ riNonemptyFaces 𝕜 C ↔
      ∃ F : Set E, F.IsFace 𝕜 C ∧ F.Nonempty ∧ U = ri[𝕜](F) := by
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF.1, hF.2, rfl⟩
  · rintro ⟨F, hF_face, hF_nonempty, rfl⟩
    exact ⟨F, ⟨hF_face, hF_nonempty⟩, rfl⟩

@[simp] theorem mem_riNonemptyFaces_iff_exists_mem_faces {C U : Set E} :
    U ∈ riNonemptyFaces 𝕜 C ↔
      ∃ F : Set E, F ∈ 𝓕[𝕜](C) ∧ F.Nonempty ∧ U = ri[𝕜](F) := by
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, Set.IsFace.mem_faces_iff.mpr hF.1, hF.2, rfl⟩
  · rintro ⟨F, hF_faces, hF_nonempty, rfl⟩
    exact ⟨F, ⟨Set.IsFace.mem_faces_iff.mp hF_faces, hF_nonempty⟩, rfl⟩

end RiNonemptyFaceFamily

end Set.IsFace

/-- Rockafellar's Chapter 18 notation for the family of relative interiors of nonempty faces. -/
scoped[Rockafellar] notation "𝒰[" 𝕜 "](" C ")" =>
  Set.IsFace.riNonemptyFaces 𝕜 C

namespace Set

section RelativelyOpenConvexFamily

open scoped Rockafellar

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable (𝕜)

/-- Family of relatively open convex subsets of `C`. -/
def relOpenConvexSubsets (C : Set E) : Set (Set E) :=
  {V : Set E | V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V}

@[simp] theorem mem_relOpenConvexSubsets_iff {C V : Set E} :
    V ∈ relOpenConvexSubsets 𝕜 C ↔
      V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V :=
  Iff.rfl

end RelativelyOpenConvexFamily

end Set

/-- Family notation for relatively open convex subsets of `C`. -/
scoped[Rockafellar] notation "𝒪[" 𝕜 "](" C ")" =>
  Set.relOpenConvexSubsets 𝕜 C

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Set.IsFace

/-- Distinct faces of `C` have disjoint relative interiors. This is the owner-level core behind
Theorem 18.2 (1); the source-facing nonempty-face family is then obtained by restricting this
canonical face-family theorem. -/
theorem pairwiseDisjoint_riFaces {C : Set E} :
    (𝓕[𝕜](C)).PairwiseDisjoint (fun F ↦ ri[𝕜](F)) := by
  rw [Set.pairwiseDisjoint_iff]
  intro F hF G hG hri
  simpa using (show F.IsFace 𝕜 C from hF).eq_of_nonempty_inter_ri (show G.IsFace 𝕜 C from hG) hri

/-- Owner-level bridge behind Theorem 18.2 (1): relative interiors indexed by
`𝒰[𝕜](C)` are pairwise disjoint. -/
theorem pairwiseDisjoint_riNonemptyFaces {C : Set E} :
    (𝒰[𝕜](C)).PairwiseDisjoint id := by
  rw [Set.pairwiseDisjoint_iff]
  intro U hU V hV hUV
  rcases (mem_riNonemptyFaces_iff (𝕜 := 𝕜) (C := C) (U := U)).1 hU with
    ⟨F, hF_face, -, rfl⟩
  rcases (mem_riNonemptyFaces_iff (𝕜 := 𝕜) (C := C) (U := V)).1 hV with
    ⟨G, hG_face, -, rfl⟩
  have hFG : F = G := hF_face.eq_of_nonempty_inter_ri hG_face hUV
  simp [hFG]

end Set.IsFace

open Set.IsFace

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 18.2 studies Rockafellar's family `𝒰` of relative interiors of the
  nonempty faces of a convex set `C`, asserting that these pieces partition `C`, absorb every
  relatively open convex subset of `C`, and are exactly the maximal relatively open convex subsets
  of `C`.
- `core/canonical`: the source-facing owner notions are `Set.IsFace.faces` (surface notation
  `𝓕[𝕜](C)`), `Set.IsFace.riNonemptyFaces` (surface notation `𝒰[𝕜](C)`),
  `Set.relOpenConvexSubsets` (surface notation `𝒪[𝕜](C)`),
  `ri[𝕜](·) = intrinsicInterior 𝕜`,
  `IsRelativelyOpen 𝕜`, `Set.PairwiseDisjoint`, `⋃₀`, and `Maximal` on `Set E`.
- `bridge/view`: the family `𝒰[𝕜](C)` packages the source set-builder
  `{ri[𝕜](F) | F ∈ 𝓕[𝕜](C), F.Nonempty}` directly at the owner level, while `𝒪[𝕜](C)` packages
  the recurring predicate `V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V`.

Domain-style sampling used here:
- `Set.IsFace.sInter`;
- `Set.IsFace.eq_of_nonempty_inter_ri`;
- `IsExtreme.subset`;
- `IsRelativelyOpen 𝕜 U`.

Primitive data vs derived API:
- primitive source-facing content: a nonempty face `F` of `C` and its relative interior
  `ri[𝕜](F)`;
- derived API: pairwise disjointness of the family `𝒰[𝕜](C)`, covering `C`, the absorption
  theorem for members of `𝒪[𝕜](C)`, and the maximality
  characterization in that same primitive owner language.

Layer target: `source-facing`, stated directly in the owner face and relative-interior API.

Ambient refinement: part (1) only uses the chapter face API and `ri[𝕜](·)`, so it lives on the
same scalar-generic ordered nontrivially normed field layer as
`Set.IsFace.eq_of_nonempty_inter_ri`. Part (2) uses the chapter's finite-dimensional
minimal-face and affine-dimension owner machinery, so its statement is kept on the same
scalar-generic finite-dimensional ordered nontrivially normed field layer rather than being
specialized to `ℝ`. Parts (3) and (4) are also source-facing finite-dimensional face statements:
their public content only involves faces, convexity, inclusion, relative interior, relative
openness, and maximality. The older real specialization came only from one Chapter 11 proof route
through supporting hyperplanes, so it is removed from the statement surface rather than preserved
as ambient API debt.
-/

/-- Theorem 18.2 (1): the members of `𝒰[𝕜](C)` are pairwise disjoint. -/
-- Proof sketch: if `U, V ∈ 𝒰[𝕜](C)`, write `U = ri[𝕜](F₁)` and `V = ri[𝕜](F₂)` with nonempty
-- faces `F₁`, `F₂` of `C`. If `U ∩ V` is nonempty, Corollary 18.1.2 gives `F₁ = F₂`, hence
-- `U = V`. This is exactly `Set.PairwiseDisjoint` for the family `𝒰[𝕜](C)`.
theorem pairwiseDisjoint_ri_nonempty_faces
    {C : Set E} :
    (𝒰[𝕜](C)).PairwiseDisjoint id := by
  simpa using (Set.IsFace.pairwiseDisjoint_riNonemptyFaces (𝕜 := 𝕜) (C := C))

end

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section FiniteDimensionalFaces

variable [FiniteDimensional 𝕜 E]

namespace Set.IsFace

/-- Owner-level form behind Theorem 18.2 (2): the family `𝒰[𝕜](C)` covers `C`. -/
theorem sUnion_riNonemptyFaces_eq
    {C : Set E} (hC : Convex 𝕜 C) :
    ⋃₀ 𝒰[𝕜](C) = C := sorry

end Set.IsFace

/-- Theorem 18.2 (2): for a convex set `C`, the union of the family `𝒰[𝕜](C)` is exactly `C`.
The source adds `C ≠ ∅`, but that binder is redundant for this owner-level covering statement;
the finite-dimensional ordered normed-field layer is not redundant here because the minimal-face
proof route uses the chapter affine-dimension machinery. -/
-- Proof sketch: every member of `𝒰[𝕜](C)` has the form `ri[𝕜](F)` for a nonempty face `F` of
-- `C`, hence is contained in `C`. Conversely, if `x ∈ C`, let `F` be the intersection of all
-- faces of `C` containing `x`. This is a nonempty face by `Set.IsFace.sInter`, and in
-- finite-dimensional spaces Rockafellar's minimal-face argument shows `x ∈ ri[𝕜](F)`. Hence
-- every point of `C` lies in `⋃₀ 𝒰[𝕜](C)`.
theorem sUnion_ri_nonempty_faces_eq
    {C : Set E} (hC : Convex 𝕜 C) :
    ⋃₀ 𝒰[𝕜](C) = C := by
  simpa using (Set.IsFace.sUnion_riNonemptyFaces_eq (𝕜 := 𝕜) (C := C) hC)

end FiniteDimensionalFaces

section FiniteDimensionalRelativelyOpenFaces

variable [FiniteDimensional 𝕜 E]

namespace Set.IsFace

/-- Owner-level form behind Theorem 18.2 (3): a relatively open convex subset of a nonempty convex
set is contained in some member of `𝒰[𝕜](C)`. -/
theorem exists_riNonemptyFaces_superset_of_relativelyOpenConvex
    {C D : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty)
    (hD : D ∈ 𝒪[𝕜](C)) :
    ∃ U : Set E, U ∈ 𝒰[𝕜](C) ∧ D ⊆ U := sorry

/-- Owner-level form behind Theorem 18.2 (4): `U` belongs to `𝒰[𝕜](C)` iff it is
maximal among relatively open convex subsets of `C`. -/
theorem mem_riNonemptyFaces_iff_maximal_relativelyOpenConvex
    {C U : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (U ∈ 𝒰[𝕜](C)) ↔
      Maximal (· ∈ 𝒪[𝕜](C)) U := sorry

end Set.IsFace

/-- Theorem 18.2 (3): every relatively open convex subset `D` of a nonempty convex set `C` is
contained in some member of `𝒰[𝕜](C)`. The public surface uses the canonical family owner
`𝒪[𝕜](C)` for relatively open convex subsets of `C`. -/
-- Proof sketch: if `D = ∅`, choose any point of the nonempty convex set `C` and use part (2) to
-- place that point in some member of `𝒰[𝕜](C)`, which then trivially contains `D`. Otherwise let
-- `F` be the intersection of all faces of `C` containing `D`. If `D` were contained in the
-- relative boundary of `F`, a finite-dimensional supporting-functional boundary-cut argument would
-- produce a proper face of `F`, hence a smaller face of `C` still containing `D`, contradicting
-- minimality. Therefore `D` meets `ri[𝕜](F)`, and Corollary 6.5.2 upgrades that meeting point to
-- inclusion in that member of `𝒰[𝕜](C)`.
theorem exists_mem_ri_nonempty_faces_superset_of_relativelyOpenConvex
    {C D : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty)
    (hD : D ∈ 𝒪[𝕜](C)) :
    ∃ U : Set E, U ∈ 𝒰[𝕜](C) ∧ D ⊆ U := by
  simpa using
    (Set.IsFace.exists_riNonemptyFaces_superset_of_relativelyOpenConvex
      (𝕜 := 𝕜) (C := C) (D := D) hC hC_nonempty hD)

/-- Theorem 18.2 (4): for a nonempty convex set `C`, a subset `U` is in `𝒰[𝕜](C)` exactly when
`U` is a maximal relatively open convex subset of `C`.
Maximality is taken with respect to inclusion inside the canonical family owner `𝒪[𝕜](C)`. -/
-- Proof sketch: if `U ∈ 𝒰[𝕜](C)`, write `U = ri[𝕜](F)` for a nonempty face `F` of `C`; then `U`
-- is relatively open and convex, and part (3) shows maximality. Conversely, if `U` is maximal
-- among relatively open convex subsets of `C`, part (3) puts `U` inside some member of
-- `𝒰[𝕜](C)`; maximality forces equality, so `U ∈ 𝒰[𝕜](C)`.
theorem mem_ri_nonempty_faces_iff_maximal_relativelyOpenConvex
    {C U : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (U ∈ 𝒰[𝕜](C)) ↔
      Maximal (· ∈ 𝒪[𝕜](C)) U := by
  simpa using
    (Set.IsFace.mem_riNonemptyFaces_iff_maximal_relativelyOpenConvex
      (𝕜 := 𝕜) (C := C) (U := U) hC hC_nonempty)

end FiniteDimensionalRelativelyOpenFaces

end
