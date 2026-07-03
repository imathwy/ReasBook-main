import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_3_1 (from Chap02) -/
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

/-! ### Corollary_6_3_2 (from Chap02) -/
section

open scoped Rockafellar
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 6.3.2 says that for a convex set `C` in a finite-dimensional ordered
  normed-field ambient space, every ambient open set meeting `intrinsicClosure 𝕜 C` also meets
  the relative interior of `C`; the ambient-`closure` phrasing is a bridge corollary. Specializing
  to `𝕜 = ℝ` recovers the textbook statement.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`, `IsOpen`, and
  `intrinsicInterior 𝕜`; both primitive and source-facing surfaces are intrinsic-first, with
  ambient-`closure` phrasing retained as a bridge theorem.
- `bridge/view`: the primitive intrinsic theorem below is the owner-level core; the
  ambient-`closure` and convex finite-dimensional statements are thin wrappers from `Theorem_6_3`.
- Domain-style sampling: the relevant canonical declarations in this domain are
  `intrinsicInterior`, `Convex.intrinsicClosure_ri_eq_intrinsicClosure` and
  `Convex.closure_intrinsicInterior_eq_closure` from `Theorem_6_3`,
  `closure_inter_open_nonempty_iff`, and mathlib's `intrinsicInterior_nonempty`.
- Primitive data vs derived API: no new data is introduced here; the nonemptiness conclusion is a
  derived topological consequence of the owner closure theorem.
- Layer target: this item is a `bridge/view` consequence. The primitive bridge surface belongs to
  `Set`, while the finite-dimensional convex corollary stays on the `Convex` owner namespace.
-/

namespace Set

section Primitive

variable {𝕜 V P : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace P] [AddTorsor V P]

/-- Primitive ambient-closure bridge: if `closure (ri[𝕜](C)) = closure C` and an ambient open set
`U` meets `closure C`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    {C U : Set P} (hri : closure (ri[𝕜](C)) = closure C) (hU : IsOpen U)
    (hCU : (closure C ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact (closure_inter_open_nonempty_iff hU).1 <| by
    simpa [hri] using hCU

/-- Primitive intrinsic-closure owner bridge: if `cl[𝕜](ri[𝕜](C)) = cl[𝕜](C)` and an ambient open
set `U` meets `cl[𝕜](C)`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    {C U : Set P} (hri : cl[𝕜](ri[𝕜](C)) = cl[𝕜](C)) (hU : IsOpen U)
    (hCU : (cl[𝕜](C) ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact (closure_inter_open_nonempty_iff hU).1 <| by
    rcases hCU with ⟨x, hxC, hxU⟩
    have hxri : x ∈ cl[𝕜](ri[𝕜](C)) := by
      simpa [hri] using hxC
    exact ⟨x, intrinsicClosure_subset_closure hxri, hxU⟩

end Primitive

end Set

namespace Convex

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Corollary 6.3.2, intrinsic-closure owner form in finite-dimensional spaces: if `C` is convex
and an ambient open set `U` meets `cl[𝕜](C)`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    {C U : Set E} (hC : Convex 𝕜 C) (hU : IsOpen U)
    (hCU : (cl[𝕜](C) ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact Set.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    hC.intrinsicClosure_ri_eq_intrinsicClosure hU hCU

/-- Corollary 6.3.2, ambient-closure bridge in finite-dimensional spaces: if `C` is convex and an
ambient open set `U` meets `closure C`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    {C U : Set E} (hC : Convex 𝕜 C) (hU : IsOpen U) (hCU : (closure C ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact Set.inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    hC.closure_intrinsicInterior_eq_closure hU hCU

end SourceFacing

end Convex

end

/-! ### Corollary_6_3_3 (from Chap02) -/
noncomputable section

open AffineSubspace
open scoped Rockafellar

section

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.3.3 says that a convex subset of the relative boundary of a
  nonempty convex set has strictly smaller affine dimension than the ambient set.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicFrontier 𝕜`,
  `ri[𝕜](C)`, and the chapter owner `Set.affineDim`.
- `bridge/view`: Rockafellar's relative boundary and relative interior are represented by
  `rb[𝕜](C)` and `ri[𝕜](C)`.
- Domain-style sampling used here: `Convex.intrinsicInterior_nonempty`,
  `Convex.ri_intrinsicClosure_eq_ri`,
  `mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset`,
  `Set.exists_simplex_points_subset_affineDim_eq`, and
  `Affine.Simplex.affineDim_le_of_points_subset`.
- Primitive data vs derived API: the core bridge theorem isolates the primitive closure/interior
  inclusion `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, nonemptiness of `ri[𝕜](C')`, and
  `C' ⊆ rb[𝕜](C)`; convexity/nonemptiness assumptions are deferred to a thin source-facing
  wrapper.
- Layer target: this item has a primitive bridge theorem at a weaker affine-torsor metric layer,
  with a source-facing convex finite-dimensional wrapper on the chapter's ordered-complete
  nontrivially normed field layer.
-/

namespace Convex

section Primitive

variable {𝕜 V P : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [PseudoMetricSpace P] [AddTorsor V P] [FiniteDimensional 𝕜 V]

/-- If `ri[𝕜](C')` is nonempty, `C' ⊆ intrinsicClosure 𝕜 C`, and `C'` has the same affine
dimension as `C`, then `C'` meets `ri[𝕜](intrinsicClosure 𝕜 C)`. -/
private theorem inter_intrinsicInterior_nonempty_of_subset_intrinsicClosure_of_affineDim_eq
    {C C' : Set P} (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ intrinsicClosure 𝕜 C) (hdim : dim[𝕜](C') = dim[𝕜](C)) :
    (C' ∩ ri[𝕜](intrinsicClosure 𝕜 C)).Nonempty := by
  obtain ⟨x, hxri⟩ := hC'ri
  have hxC' : x ∈ C' := intrinsicInterior_subset hxri
  have hspan : affineSpan 𝕜 C' = affineSpan 𝕜 C := by
    have hle : affineSpan 𝕜 C' ≤ affineSpan 𝕜 C := by
      have hle' : affineSpan 𝕜 C' ≤ affineSpan 𝕜 (intrinsicClosure 𝕜 C) :=
        affineSpan_mono 𝕜 hsubset
      exact hle'.trans_eq (affineSpan_intrinsicClosure (𝕜 := 𝕜) C)
    have hspan_nonempty : (affineSpan 𝕜 C' : Set P).Nonempty := by
      exact ⟨x, subset_affineSpan 𝕜 C' hxC'⟩
    have hC'bot : affineSpan 𝕜 C' ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot (affineSpan 𝕜 C')).1 hspan_nonempty
    have hCbot : affineSpan 𝕜 C ≠ ⊥ := by
      intro hCbot
      exact hC'bot <| eq_bot_iff.mpr <| hCbot ▸ hle
    change
      AffineSubspace.affineDim (affineSpan 𝕜 C') =
        AffineSubspace.affineDim (affineSpan 𝕜 C) at hdim
    rw [AffineSubspace.affineDim, AffineSubspace.affineDim, if_neg hC'bot, if_neg hCbot] at hdim
    have hdir_eq : (affineSpan 𝕜 C').direction = (affineSpan 𝕜 C).direction := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact AffineSubspace.direction_le hle
      · exact_mod_cast hdim
    exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq hspan_nonempty hle
  obtain ⟨_, ε, hε, hxball⟩ :=
    (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hxri
  have hxri_closure : x ∈ ri[𝕜](intrinsicClosure 𝕜 C) := by
    refine
      (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).2
        ⟨subset_affineSpan 𝕜 (intrinsicClosure 𝕜 C) (hsubset (intrinsicInterior_subset hxri)),
          ε, hε, ?_⟩
    intro y hy
    exact hsubset <| hxball <| by
      have hySpan : y ∈ affineSpan 𝕜 C := by
        exact (affineSpan_intrinsicClosure (𝕜 := 𝕜) C) ▸ hy.2
      refine ⟨hy.1, ?_⟩
      simpa [hspan] using hySpan
  exact ⟨x, hxC', hxri_closure⟩

/-- Primitive bridge form of Corollary 6.3.3: if `ri[𝕜](C')` is nonempty,
`C' ⊆ rb[𝕜](C)`, and `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, then
`C'` has strictly smaller affine dimension than `C`. -/
-- Proof sketch: first note that `C' ⊆ intrinsicClosure 𝕜 C`, so every simplex contained in `C'`
-- is also contained in `intrinsicClosure 𝕜 C`; Theorem 2.4 therefore gives
-- `C'.affineDim ≤ C.affineDim`. If equality
-- held, then `C'` and `C` would have the same affine span. A relative-interior point of `C'`
-- would then satisfy the closed-ball criterion in the common affine span and hence lie in
-- `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, contradicting `C' ⊆ rb[𝕜](C)`.
theorem affineDim_lt_of_subset_rb_of_ri_intrinsicClosure_subset_ri
    {C C' : Set P} (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ rb[𝕜](C))
    (hri : ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  have hC'ne : C'.Nonempty := hC'ri.mono intrinsicInterior_subset
  have hsubset_iclosure : C' ⊆ intrinsicClosure 𝕜 C := by
    exact hsubset.trans <| by
      exact (intrinsicFrontier_subset_intrinsicClosure :
        rb[𝕜](C) ⊆ intrinsicClosure 𝕜 C)
  have hle : dim[𝕜](C') ≤ dim[𝕜](C) := by
    rcases C'.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hC'ne with
      ⟨n, hC'dim, s, hs⟩
    calc
      dim[𝕜](C') = n := hC'dim
      _ ≤ dim[𝕜](intrinsicClosure 𝕜 C) := by
        exact s.affineDim_le_of_points_subset (hs.trans hsubset_iclosure)
      _ = dim[𝕜](C) := by
        change AffineSubspace.affineDim (affineSpan 𝕜 (intrinsicClosure 𝕜 C)) =
          AffineSubspace.affineDim (affineSpan 𝕜 C)
        exact congrArg (fun A : AffineSubspace 𝕜 P => AffineSubspace.affineDim A)
          (affineSpan_intrinsicClosure (𝕜 := 𝕜) C)
  by_contra hlt
  have hdim : dim[𝕜](C') = dim[𝕜](C) := le_antisymm hle (not_lt.mp hlt)
  rcases inter_intrinsicInterior_nonempty_of_subset_intrinsicClosure_of_affineDim_eq
      hC'ri hsubset_iclosure hdim with ⟨x, hxC', hxri_closure⟩
  have hxri : x ∈ ri[𝕜](C) := by
    exact hri hxri_closure
  have hxnot : x ∉ rb[𝕜](C) := by
    have hxpair : x ∈ intrinsicClosure 𝕜 C \ rb[𝕜](C) := by
      simpa [intrinsicClosure_diff_intrinsicFrontier] using hxri
    exact hxpair.2
  exact hxnot (hsubset hxC')

end Primitive

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Source-facing owner form of Corollary 6.3.3 at the canonical intrinsic-owner layer:
if `C` is convex with nonempty `ri[𝕜](C)`, and `ri[𝕜](C')` is nonempty with
`C' ⊆ rb[𝕜](C)`, then `C'` has strictly smaller affine dimension than `C`. -/
theorem affineDim_lt_of_subset_rb_of_ri_nonempty
    {C C' : Set E} (hC : Convex 𝕜 C) (hCri : (ri[𝕜](C)).Nonempty)
    (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ rb[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_subset_rb_of_ri_intrinsicClosure_subset_ri hC'ri hsubset (by
    intro x hx
    exact hC.ri_intrinsicClosure_eq_ri_of_nonempty hCri ▸ hx)

variable [OrderTopology 𝕜] [CompleteSpace 𝕜]

/-- Corollary 6.3.3: if `C'` is a convex subset of the relative boundary
`rb[𝕜](C)` of a nonempty convex set `C` in a finite-dimensional normed space over an ordered
complete nontrivially normed field `𝕜`, then `C'` has strictly smaller affine dimension than `C`. -/
theorem affineDim_lt_of_subset_rb
    {C C' : Set E} (hC : Convex 𝕜 C) (hCne : C.Nonempty) (hC' : Convex 𝕜 C')
    (hsubset : C' ⊆ rb[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  obtain rfl | hC'ne := Set.eq_empty_or_nonempty C'
  · rcases C.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hCne with
      ⟨n, hCdim, s, hs⟩
    have hEmpty : dim[𝕜]((∅ : Set E)) = -1 := by
      simp [Set.affineDim, AffineSubspace.affineDim]
    rw [hEmpty, hCdim]
    have hn : (0 : ℤ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    linarith
  exact affineDim_lt_of_subset_rb_of_ri_nonempty hC
    (hC.intrinsicInterior_nonempty hCne)
    (hC'.intrinsicInterior_nonempty hC'ne) hsubset

end SourceFacing

end Convex

end

/-! ### Text_6_3 (from Chap02) -/
scoped[Rockafellar] notation "B" => Metric.closedBall (0 : _) (1 : ℝ)

section

variable {E : Type*} [PseudoMetricSpace E] [Zero E]

open scoped Rockafellar

/-- Text 6.3 owner bridge: the chapter notation `B` is the canonical unit closed ball. -/
@[simp] theorem B_eq_closedBall : (B : Set E) = Metric.closedBall (0 : E) (1 : ℝ) := rfl

/-
Source/core/bridge triage:
- `source-facing`: Text 6.3 fixes the textbook unit ball and gives it the reusable chapter
  notation `B`, with membership surface `x ∈ B`.
- `core/canonical`: mathlib's owner object is the closed ball `closedBall (0 : E) 1`.
- `bridge/view`: the notation `B` is a thin source-facing surface for the canonical owner
  `closedBall (0 : E) 1`; metric and norm membership are bridge views.
- Primitive data vs derived API: no wrapper data is introduced; the source's membership
  descriptions stay derived API over the closed-ball owner.
- Domain-style sampling: `closedBall`, `mem_closedBall`, `mem_closedBall_zero_iff`,
  and the project bridge `closedBall_eq_add_smul_unitClosedBall` that uses this fixed unit ball
  downstream.
- Layer target: `source-facing` notation over the canonical closed-ball owner.
- Ambient-space refinement: the canonical owner and the metric membership view
  `mem_closedBall` live at the pseudometric + zero layer, so this file keeps those as the
  owner assumptions and isolates the norm-language view in a separate seminormed section.
-/

/-
Text 6.3 fixes the textbook unit ball as the notation `B`, i.e. the canonical closed ball
`closedBall (0 : E) 1`.
-/
theorem mem_B_iff_dist_zero_le_one {x : E} :
    x ∈ B ↔ dist x (0 : E) ≤ 1 := by
  exact (Metric.mem_closedBall : x ∈ (B : Set E) ↔ dist x (0 : E) ≤ 1)

end

section

variable {E : Type*} [SeminormedAddGroup E]

open scoped Rockafellar

/- Text 6.3's norm-language unit-ball membership surface is the canonical theorem
`mem_closedBall_zero_iff`, specialized to the chapter notation `B`. -/
theorem mem_B_iff_norm_le_one {x : E} :
    x ∈ B ↔ ‖x‖ ≤ 1 := by
  exact (mem_closedBall_zero_iff (a := x) (r := (1 : ℝ)))

end

/-! ### Theorem_6_3 (from Chap02) -/
section

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.3 states two closure/relative-interior identities for a convex set
  in `ℝ^n`.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`, and
  `intrinsicInterior 𝕜`.
- `bridge/view`: Rockafellar's `ri C` is represented canonically by `intrinsicInterior ℝ C`.
- Domain-style sampling used here: the chapter owner notation `ri[𝕜](C)` from `Text_6_8`,
  `intrinsicInterior`, `intrinsicClosure`, `intrinsicClosure_eq_closure`,
  `Set.Nonempty.intrinsicInterior`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`,
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem`,
  and the intrinsic affine-hull owner theorem `affineSpan_intrinsicClosure`.
- Primitive data vs derived API: the primitive owner data is just `hC : Convex 𝕜 C`; both
  closure/relative-interior identities are derived API, so they belong on the `Convex`
  owner abstraction rather than as parallel global wrappers.
- Layer target: the intrinsic closure/interior identities are the primary public owner theorems;
  the ambient `closure` statements are finite-dimensional bridge corollaries.
-/

namespace Convex

open AffineMap

variable {𝕜 E : Type*} {C : Set E}

section Primitive

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem right_mem_intrinsicClosure_openSegment (x y : E) :
    y ∈ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  refine ⟨segment_subset_closure_openSegment (right_mem_segment 𝕜 x y), ?_⟩
  let u : E := lineMap x y ((1 : 𝕜) / 2)
  let v : E := lineMap u y ((1 : 𝕜) / 2)
  have hu : u ∈ openSegment 𝕜 x y := by
    dsimp [u]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hv : v ∈ openSegment 𝕜 x y := by
    dsimp [v, u]
    rw [lineMap_lineMap_left]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hy_line : y ∈ line[𝕜, u, v] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(2 : 𝕜), ?_⟩
    dsimp [v]
    rw [lineMap_lineMap_right]
    norm_num
  exact
    (affineSpan_pair_le_of_mem_of_mem
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hu)
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hv)) hy_line

/-- Primitive intrinsic owner form behind Theorem 6.3 (1): if `ri[𝕜](C)` is nonempty, then taking
intrinsic closure after relative interior leaves intrinsic closure unchanged. -/
theorem intrinsicClosure_ri_eq_intrinsicClosure_of_nonempty (hC : Convex 𝕜 C)
    (hri : (ri[𝕜](C)).Nonempty) :
    intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C := by
  refine subset_antisymm (intrinsicClosure_mono intrinsicInterior_subset) ?_
  rcases hri with ⟨x, hx⟩
  intro y hy
  have hseg : openSegment 𝕜 x y ⊆ ri[𝕜](C) :=
    hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hx hy
  exact intrinsicClosure_mono hseg <| right_mem_intrinsicClosure_openSegment (𝕜 := 𝕜) x y

omit [OrderTopology 𝕜] in
/-- Theorem 6.3 (2), intrinsic owner form with explicit nonemptiness of `ri[𝕜](C)`. -/
theorem ri_intrinsicClosure_eq_ri_of_nonempty (hC : Convex 𝕜 C) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜](intrinsicClosure 𝕜 C) = ri[𝕜](C) := by
  refine subset_antisymm ?_ ?_
  · rcases hri with ⟨x, hx⟩
    intro z hz
    have hxcl : x ∈ intrinsicClosure 𝕜 C := subset_intrinsicClosure (intrinsicInterior_subset hx)
    rcases
        Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior
          (C := intrinsicClosure 𝕜 C) hz x hxcl with
      ⟨μ, hμ, hy⟩
    have hμ_inv : 0 < μ⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hμ)
    have hμ_inv_lt_one : μ⁻¹ < 1 := by
      rw [inv_lt_one₀]
      · linarith
      · linarith
    have hz_seg : z ∈ openSegment 𝕜 x (lineMap x z μ) := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨μ⁻¹, ⟨hμ_inv, hμ_inv_lt_one⟩, ?_⟩
      have hμ0 : μ ≠ 0 := (lt_trans zero_lt_one hμ).ne'
      calc
        lineMap x (lineMap x z μ) μ⁻¹ = lineMap x z (μ⁻¹ * μ) := by simp
        _ = lineMap x z (1 : 𝕜) := by rw [inv_mul_cancel₀ hμ0]
        _ = z := lineMap_apply_one x z
    exact Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hC hx hy
      hz_seg
  · intro z hz
    rw [intrinsicInterior] at hz ⊢
    rw [affineSpan_intrinsicClosure (𝕜 := 𝕜) C]
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, interior_mono (Set.preimage_mono subset_intrinsicClosure) hy, rfl⟩

end Primitive

section FiniteDimensionalBridge

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Theorem 6.3 (1), intrinsic owner form: for a convex set `C`, taking intrinsic closure after
relative interior leaves the intrinsic closure unchanged. -/
theorem intrinsicClosure_ri_eq_intrinsicClosure (hC : Convex 𝕜 C) :
    intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C := by
  obtain rfl | hCne := Set.eq_empty_or_nonempty C
  · simp
  exact hC.intrinsicClosure_ri_eq_intrinsicClosure_of_nonempty (hC.intrinsicInterior_nonempty hCne)

/-- Theorem 6.3 (1), ambient-closure bridge: in finite-dimensional spaces,
`closure (ri[𝕜](C)) = closure C`. -/
theorem closure_intrinsicInterior_eq_closure (hC : Convex 𝕜 C) :
    closure (ri[𝕜](C)) = closure C := by
  simpa [intrinsicClosure_eq_closure 𝕜 (ri[𝕜](C)),
    intrinsicClosure_eq_closure 𝕜 C] using
    intrinsicClosure_ri_eq_intrinsicClosure hC

/-- Theorem 6.3 (2), intrinsic owner form: for a convex set `C`, taking relative interior after
intrinsic closure leaves the relative interior unchanged. -/
theorem ri_intrinsicClosure_eq_ri (hC : Convex 𝕜 C) :
    ri[𝕜](intrinsicClosure 𝕜 C) = ri[𝕜](C) := by
  obtain rfl | hCne := Set.eq_empty_or_nonempty C
  · simp
  exact hC.ri_intrinsicClosure_eq_ri_of_nonempty (hC.intrinsicInterior_nonempty hCne)

/-- Theorem 6.3 (2), ambient-closure bridge: in finite-dimensional spaces,
`ri[𝕜](closure C) = ri[𝕜](C)`. -/
theorem intrinsicInterior_closure_eq_intrinsicInterior (hC : Convex 𝕜 C) :
    ri[𝕜](closure C) = ri[𝕜](C) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    ri_intrinsicClosure_eq_ri hC

end FiniteDimensionalBridge

end Convex

end
