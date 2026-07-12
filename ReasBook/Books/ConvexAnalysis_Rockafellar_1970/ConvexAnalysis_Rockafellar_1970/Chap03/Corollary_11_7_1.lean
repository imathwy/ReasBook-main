import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_5_16
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- If a nonempty cone `K` is contained in a closed half-space `s` that excludes `x`, then `K`
is already contained in a homogeneous closed half-space that still excludes `x`. -/
theorem exists_homogeneous_closedHalfSpace_containing_excluding
    {K s : Set X} (hK_nonempty : K.Nonempty) (hK_cone : Set.IsCone 𝕜 K)
    (hs : IsClosedHalfSpace Y 𝕜 s)
    (hKs : K ⊆ s) {x : X} (hx : x ∉ s) :
    ∃ t : Set X, (homClosedHalfSpace[Y,𝕜] t) ∧ K ⊆ t ∧ x ∉ t := by
  rcases hs with ⟨b, β, hb, rfl | rfl⟩
  · have hβ : ∀ z ∈ K, ⟪z, b⟫ₚ ≤ β := fun z hz ↦
      mem_closedHalfSpaceLE_iff.mp (show z ∈ closedHalfSpaceLE b β from hKs hz)
    have hβ_nonneg : 0 ≤ β :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty hK_cone hK_nonempty hβ
    have hβ_bdd : BddAbove ((fun z : X ↦ (⟪z, b⟫ₚ : 𝕜)) '' K) := by
      refine ⟨β, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact hβ z hz
    have hK_nonpos : ∀ z ∈ K, ⟪z, b⟫ₚ ≤ (0 : 𝕜) := fun z hz ↦
      Set.IsCone.pairing_nonpos_of_bddAbove hK_cone hβ_bdd z hz
    have hx_gt : β < ⟪x, b⟫ₚ := by
      exact lt_of_not_ge <| by simpa [mem_closedHalfSpaceLE_iff] using hx
    refine ⟨closedHalfSpaceLE b (0 : 𝕜), ?_, ?_, ?_⟩
    · exact Set.IsHomogeneousClosedHalfSpace.closedHalfSpaceLE_zero b hb
    · intro z hz
      exact mem_closedHalfSpaceLE_iff.mpr <| hK_nonpos z hz
    · rw [mem_closedHalfSpaceLE_iff]
      exact not_le.mpr <| lt_of_le_of_lt hβ_nonneg hx_gt
  · have hβ : ∀ z ∈ K, ⟪z, -b⟫ₚ ≤ -β := by
      intro z hz
      have hzβ : β ≤ ⟪z, b⟫ₚ :=
        mem_closedHalfSpaceGE_iff.mp (show z ∈ closedHalfSpaceGE b β from hKs hz)
      simpa using (neg_le_neg hzβ)
    have hβ_nonneg : 0 ≤ -β :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty hK_cone hK_nonempty hβ
    have hβ_bdd : BddAbove ((fun z : X ↦ (⟪z, -b⟫ₚ : 𝕜)) '' K) := by
      refine ⟨-β, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact hβ z hz
    have hK_nonneg : ∀ z ∈ K, (0 : 𝕜) ≤ ⟪z, b⟫ₚ := by
      intro z hz
      have hz_nonpos : ⟪z, -b⟫ₚ ≤ (0 : 𝕜) :=
        Set.IsCone.pairing_nonpos_of_bddAbove hK_cone hβ_bdd z hz
      have hz_nonpos' : -⟪z, b⟫ₚ ≤ (0 : 𝕜) := by simpa using hz_nonpos
      exact neg_nonpos.mp hz_nonpos'
    have hβ_nonpos : β ≤ (0 : 𝕜) := by
      linarith
    have hx_lt : ⟪x, b⟫ₚ < β := by
      exact lt_of_not_ge <| by simpa [mem_closedHalfSpaceGE_iff] using hx
    have hx_lt_zero : ⟪x, b⟫ₚ < (0 : 𝕜) := lt_of_lt_of_le hx_lt hβ_nonpos
    refine ⟨closedHalfSpaceGE b (0 : 𝕜), ?_, ?_, ?_⟩
    · exact Set.IsHomogeneousClosedHalfSpace.closedHalfSpaceGE_zero b hb
    · intro z hz
      exact mem_closedHalfSpaceGE_iff.mpr <| hK_nonneg z hz
    · rw [mem_closedHalfSpaceGE_iff]
      exact not_le.mpr hx_lt_zero

end

section

open Set
open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [Nontrivial (StrongDual ℝ E)]
local notation "E⋆" => StrongDual ℝ E

local instance instHasLinearPairingStrongDualTopologicalCor1171 :
    HasLinearPairing E E⋆ ℝ where
  pairingLinear :=
    { toFun := fun x =>
        { toFun := fun l => l x
          map_add' := by
            intro l₁ l₂
            simp
          map_smul' := by
            intro a l
            simp }
      map_add' := by
        intro x z
        ext l
        simp
      map_smul' := by
        intro a x
        ext l
        simp }

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 11.7.1 says that a nonempty closed convex cone in a real
  locally convex topological vector space is the
  intersection of all homogeneous closed half-spaces containing it.
- `core/canonical`: the owner abstractions are the dual-owner closed-half-space predicate
  `closedHalfSpace[E⋆,ℝ]`, the homogeneous owner `homClosedHalfSpace[E⋆,ℝ]`, the cone predicate
  `Set.IsCone ℝ`, and
  the set-theoretic intersection `⋂₀`.
- `bridge/view`: the local homogenization theorem
  `exists_homogeneous_closedHalfSpace_containing_excluding` turns an arbitrary containing
  dual-owner closed half-space into one of the canonical homogeneous owner surfaces.
- Primitive data vs derived API: the primitive input is the set `K`; nonemptiness, closedness,
  convexity, and conic closure are hypotheses, while the intersection formula is theorem-level
  content.
- Domain-style sampling used here: the chapter owner declarations
  `Set.IsClosedHalfSpace`, `homClosedHalfSpace[_,_]`, the cone predicate `Set.IsCone ℝ`,
  the upstream cone/pairing owner theorems
  `Set.IsCone.pairing_upperBound_nonneg_of_nonempty` and
  `Set.IsCone.pairing_nonpos_of_bddAbove`, and the earlier half-space/intersection owner theorem
  `closed_convex_eq_sInter_closedHalfSpacesContaining`.
- Layer target: `source-facing`, stated directly as a set equality rather than by packaging the
  family of containing homogeneous half-spaces into a new wrapper object.
- Ambient refinement: as in `Theorem_11_5`, the proof only uses dual half-space owners and the
  canonical closed-convex intersection theorem, so it belongs to real locally convex topological
  vector spaces with nontrivial continuous dual, not to an inner-product model.
- Scalar-layer justification: this statement remains over `ℝ` because its upstream owner theorem
  `closed_convex_eq_sInter_closedHalfSpacesContaining` is currently proved at the real continuous-
  dual layer, and the conic homogenization step simultaneously needs ordered-scalar cone
  inequalities (`pairing_upperBound_nonneg_of_nonempty` and `pairing_nonpos_of_bddAbove`). In the
  present project API these two ingredients meet canonically at `ℝ`; this is an owner-level
  dependency, not a proof-script convenience.
-/

/-- Corollary 11.7.1 at the canonical dual-owner layer: a nonempty closed convex cone is the
intersection of homogeneous dual-owner closed half-spaces containing it. -/
theorem closed_convex_cone_eq_sInter_homogeneousClosedHalfSpacesContaining {K : Set E}
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : Set.IsCone ℝ K) :
    K = ⋂₀ {s : Set E | (homClosedHalfSpace[E⋆,ℝ] s) ∧ K ⊆ s} := by
  classical
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_sInter.mpr fun s hs ↦ hs.2 hx
  · intro x hxH
    by_contra hxK
    have hx_not_mem : x ∉ ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ K ⊆ s} := by
      rwa [closed_convex_eq_sInter_closedHalfSpacesContaining K hK_closed hK_convex] at hxK
    simp only [Set.mem_sInter] at hx_not_mem
    push Not at hx_not_mem
    rcases hx_not_mem with ⟨s, hs, hx_not_s⟩
    rcases
        (exists_homogeneous_closedHalfSpace_containing_excluding
          hK_nonempty hK_cone hs.1 hs.2 hx_not_s)
      with
      ⟨t, ht_homogeneous, hKt, hx_not_t⟩
    exact hx_not_t <| (Set.mem_sInter.mp hxH) t ⟨ht_homogeneous, hKt⟩

end
