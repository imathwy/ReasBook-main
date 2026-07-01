import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Set
open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [Nontrivial (StrongDual ℝ E)]
local notation "E⋆" => StrongDual ℝ E

local instance instHasLinearPairingStrongDualTopological :
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

/-- Theorem 11.5 at the continuous-dual bridge layer: a closed convex subset of a real locally
convex topological vector space with nontrivial continuous dual is the intersection of all
continuous-dual closed half-spaces that contain it. -/
theorem closed_convex_eq_sInter_closedHalfSpacesContaining (C : Set E)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    C = ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ C ⊆ s} := by
  let H : Set (Set E) := {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ C ⊆ s}
  refine Subset.antisymm ?_ ?_
  · change C ⊆ ⋂₀ H
    exact subset_sInter fun s hs ↦ hs.2
  · intro x hx
    have hxH : x ∈ ⋂₀ H := by
      simpa [H] using hx
    by_cases hC_empty : C = ∅
    · exfalso
      obtain ⟨l, hl⟩ : ∃ l : StrongDual ℝ E, l ≠ 0 := exists_ne (0 : StrongDual ℝ E)
      let c : ℝ := l x - 1
      have hl_nontrivial : HasLinearPairing.pairingLinear.flip l ≠ (0 : E →ₗ[ℝ] ℝ) := by
        intro hzero
        apply hl
        ext z
        exact DFunLike.congr_fun hzero z
      have hs :
          (closedHalfSpace[E⋆,ℝ] (closedHalfSpaceLE l c : Set E)) :=
        Set.closedHalfSpaceLE_isClosedHalfSpace hl_nontrivial
      have hxmem : x ∈ closedHalfSpaceLE l c :=
        (sInter_subset_of_mem
          (by simp [H, hs, hC_empty] : (closedHalfSpaceLE l c : Set E) ∈ H)) hxH
      have hxle : l x ≤ c := mem_closedHalfSpaceLE_iff.mp hxmem
      have hxle' : l x ≤ l x - 1 := by
        simpa [c] using hxle
      linarith
    · obtain ⟨y, hyC⟩ : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      have hx' :
          x ∈ ⋂ (l : StrongDual ℝ E) (c : ℝ) (_ : ∀ z ∈ C, l z ≤ c), {z : E | l z ≤ c} := by
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        intro l c hc
        by_cases hl : l = 0
        · simpa [hl] using hc y hyC
        · have hl_nontrivial : HasLinearPairing.pairingLinear.flip l ≠ (0 : E →ₗ[ℝ] ℝ) := by
            intro hzero
            apply hl
            ext z
            exact DFunLike.congr_fun hzero z
          have hsubset : C ⊆ (closedHalfSpaceLE l c : Set E) := by
            intro z hz
            exact mem_closedHalfSpaceLE_iff.mpr (hc z hz)
          have hxmem : x ∈ closedHalfSpaceLE l c :=
            (sInter_subset_of_mem
              (by
                simp [H, Set.closedHalfSpaceLE_isClosedHalfSpace hl_nontrivial, hsubset]
                  : (closedHalfSpaceLE l c : Set E) ∈ H)) hxH
          exact mem_closedHalfSpaceLE_iff.mp hxmem
      have hhalfspaces :
          ⋂ (l : StrongDual ℝ E) (c : ℝ) (_ : ∀ z ∈ C, l z ≤ c), {z : E | l z ≤ c} = C :=
        RCLike.iInter_halfSpaces_eq' hC_convex hC_closed
      simpa [hhalfspaces] using hx'

/-- Theorem 11.5 at the intrinsic linear-functional owner layer: a closed convex subset of a real
locally convex topological vector space with nontrivial continuous dual is the intersection of all
closed linear half-spaces that contain it. -/
theorem closed_convex_eq_sInter_closedLinearHalfSpacesContaining (C : Set E)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    C = ⋂₀ {s : Set E | (closedLinearHalfSpace[ℝ] s) ∧ C ⊆ s} := by
  let Hstrong : Set (Set E) := {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ C ⊆ s}
  let Hlinear : Set (Set E) := {s : Set E | (closedLinearHalfSpace[ℝ] s) ∧ C ⊆ s}
  have hstrong_sub_linear : Hstrong ⊆ Hlinear := by
    intro s hs
    exact ⟨hs.1.toClosedLinearHalfSpace, hs.2⟩
  have hdual : C = ⋂₀ Hstrong := by
    simpa [Hstrong] using
      (closed_convex_eq_sInter_closedHalfSpacesContaining (E := E) C hC_closed hC_convex)
  refine Subset.antisymm ?_ ?_
  · change C ⊆ ⋂₀ Hlinear
    exact subset_sInter fun s hs ↦ hs.2
  · intro x hx
    have hxdual : x ∈ ⋂₀ Hstrong := by
      refine mem_sInter.mpr ?_
      intro s hs
      exact (mem_sInter.mp hx) s (hstrong_sub_linear hs)
    simpa [hdual] using hxdual

end

section

open Set
open scoped RealInnerProductSpace Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Source/core/bridge triage:
- `source-facing`: this bridge recovers the textbook coordinate normal-vector phrasing in which
  closed half-spaces are cut out by normals `b : E`.
- `core/canonical`: Theorem 11.5 is the intrinsic closed-linear-half-space statement
  `closed_convex_eq_sInter_closedLinearHalfSpacesContaining`, proved above at
  `Set.IsClosedLinearHalfSpace ℝ`.
- `bridge/upstream`: the continuous-dual theorem
  `closed_convex_eq_sInter_closedHalfSpacesContaining` provides the separation-theoretic input.
- `bridge/view`: the family `{s : Set E | IsClosedHalfSpace E ℝ s ∧ C ⊆ s}` is obtained from the
  continuous-dual family via Riesz representation `InnerProductSpace.toDual`.
- Primitive data vs derived API: the primitive owner inputs are the intrinsic closed-linear
  half-space theorem data; the inner-product normal-vector phrasing is bridge-level API.
- Domain-style sampling used here: `RCLike.iInter_halfSpaces_eq'`,
  `InnerProductSpace.toDual`, `IsClosedHalfSpace`, and `closedHalfSpaceLE`.
- Layer target: this theorem is `bridge/view`; the canonical owner theorem is the intrinsic
  declaration above.
- Ambient refinement: this bridge needs surjectivity of `InnerProductSpace.toDual`, so it lives on
  nontrivial complete real inner-product spaces rather than coordinate models.
-/

private theorem pairing_apply_toDual_symm (l : StrongDual ℝ E) (x : E) :
    (HasLinearPairing.pairingLinear x) ((InnerProductSpace.toDual ℝ E).symm l) = l x := by
  let b : E := (InnerProductSpace.toDual ℝ E).symm l
  have hb : l x = inner ℝ b x := by
    simp [b, InnerProductSpace.toDual_symm_apply]
  calc
    (HasLinearPairing.pairingLinear x) b = inner ℝ x b := by rfl
    _ = inner ℝ b x := by simp [real_inner_comm]
    _ = l x := hb.symm

private theorem pairing_apply_toDual (b x : E) :
    (HasLinearPairing.pairingLinear x) b = (InnerProductSpace.toDual ℝ E b) x := by
  simpa using pairing_apply_toDual_symm (E := E) (l := InnerProductSpace.toDual ℝ E b) (x := x)

private theorem dual_closedHalfSpaceLE_eq_inner (l : StrongDual ℝ E) (c : ℝ) :
    (closedHalfSpaceLE l c : Set E) = closedHalfSpaceLE ((InnerProductSpace.toDual ℝ E).symm l) c :=
by
  ext x
  constructor
  · intro hx
    refine mem_closedHalfSpaceLE_iff.mpr ?_
    change l x ≤ c at hx
    change (HasLinearPairing.pairingLinear x) ((InnerProductSpace.toDual ℝ E).symm l) ≤ c
    rw [pairing_apply_toDual_symm (E := E) (l := l) (x := x)]
    exact hx
  · intro hx
    refine mem_closedHalfSpaceLE_iff.mpr ?_
    change (HasLinearPairing.pairingLinear x) ((InnerProductSpace.toDual ℝ E).symm l) ≤ c at hx
    rw [pairing_apply_toDual_symm (E := E) (l := l) (x := x)] at hx
    change l x ≤ c
    exact hx

private theorem dual_closedHalfSpaceGE_eq_inner (l : StrongDual ℝ E) (c : ℝ) :
    (closedHalfSpaceGE l c : Set E) = closedHalfSpaceGE ((InnerProductSpace.toDual ℝ E).symm l) c :=
by
  ext x
  constructor
  · intro hx
    refine mem_closedHalfSpaceGE_iff.mpr ?_
    change c ≤ l x at hx
    change c ≤ (HasLinearPairing.pairingLinear x) ((InnerProductSpace.toDual ℝ E).symm l)
    rw [pairing_apply_toDual_symm (E := E) (l := l) (x := x)]
    exact hx
  · intro hx
    refine mem_closedHalfSpaceGE_iff.mpr ?_
    change c ≤ (HasLinearPairing.pairingLinear x) ((InnerProductSpace.toDual ℝ E).symm l) at hx
    rw [pairing_apply_toDual_symm (E := E) (l := l) (x := x)] at hx
    change c ≤ l x
    exact hx

private theorem inner_closedHalfSpaceLE_eq_dual (b : E) (c : ℝ) :
    (closedHalfSpaceLE b c : Set E) = closedHalfSpaceLE (InnerProductSpace.toDual ℝ E b) c := by
  ext x
  constructor
  · intro hx
    refine mem_closedHalfSpaceLE_iff.mpr ?_
    change (HasLinearPairing.pairingLinear x) b ≤ c at hx
    change (InnerProductSpace.toDual ℝ E b) x ≤ c
    rw [← pairing_apply_toDual (E := E) (b := b) (x := x)]
    exact hx
  · intro hx
    refine mem_closedHalfSpaceLE_iff.mpr ?_
    change (InnerProductSpace.toDual ℝ E b) x ≤ c at hx
    change (HasLinearPairing.pairingLinear x) b ≤ c
    rw [pairing_apply_toDual (E := E) (b := b) (x := x)]
    exact hx

private theorem inner_closedHalfSpaceGE_eq_dual (b : E) (c : ℝ) :
    (closedHalfSpaceGE b c : Set E) = closedHalfSpaceGE (InnerProductSpace.toDual ℝ E b) c := by
  ext x
  constructor
  · intro hx
    refine mem_closedHalfSpaceGE_iff.mpr ?_
    change c ≤ (HasLinearPairing.pairingLinear x) b at hx
    change c ≤ (InnerProductSpace.toDual ℝ E b) x
    rw [← pairing_apply_toDual (E := E) (b := b) (x := x)]
    exact hx
  · intro hx
    refine mem_closedHalfSpaceGE_iff.mpr ?_
    change c ≤ (InnerProductSpace.toDual ℝ E b) x at hx
    change c ≤ (HasLinearPairing.pairingLinear x) b
    rw [pairing_apply_toDual (E := E) (b := b) (x := x)]
    exact hx

private theorem isClosedHalfSpace_dual_iff_inner {s : Set E} :
    IsClosedHalfSpace (StrongDual ℝ E) ℝ s ↔ IsClosedHalfSpace E ℝ s := by
  constructor
  · intro hs
    rcases hs with ⟨l, c, hl, hs⟩
    rcases hs with rfl | rfl
    · let b : E := (InnerProductSpace.toDual ℝ E).symm l
      have hl0 : l ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero hl
      have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : E →ₗ[ℝ] ℝ) := by
        intro hzero
        apply hl0
        ext z
        have hz0 : ((HasLinearPairing.pairingLinear.flip b : E →ₗ[ℝ] ℝ) z) = 0 := by
          simpa using DFunLike.congr_fun hzero z
        simpa [pairing_apply_toDual_symm (E := E) (l := l) (x := z), b] using hz0
      simpa [dual_closedHalfSpaceLE_eq_inner (E := E), b] using
        (Set.closedHalfSpaceLE_isClosedHalfSpace hbflip :
          IsClosedHalfSpace E ℝ (closedHalfSpaceLE b c))
    · let b : E := (InnerProductSpace.toDual ℝ E).symm l
      have hl0 : l ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero hl
      have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : E →ₗ[ℝ] ℝ) := by
        intro hzero
        apply hl0
        ext z
        have hz0 : ((HasLinearPairing.pairingLinear.flip b : E →ₗ[ℝ] ℝ) z) = 0 := by
          simpa using DFunLike.congr_fun hzero z
        simpa [pairing_apply_toDual_symm (E := E) (l := l) (x := z), b] using hz0
      simpa [dual_closedHalfSpaceGE_eq_inner (E := E), b] using
        (Set.closedHalfSpaceGE_isClosedHalfSpace hbflip :
          IsClosedHalfSpace E ℝ (closedHalfSpaceGE b c))
  · intro hs
    rcases hs with ⟨b, c, hb, hs⟩
    rcases hs with rfl | rfl
    · let l : StrongDual ℝ E := InnerProductSpace.toDual ℝ E b
      have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero hb
      have hl0 : l ≠ 0 := by
        intro hl0
        apply hb0
        exact (InnerProductSpace.toDual ℝ E).injective (by simpa [l] using hl0)
      have hl : HasLinearPairing.pairingLinear.flip l ≠ (0 : E →ₗ[ℝ] ℝ) := by
        intro hzero
        apply hl0
        ext z
        exact DFunLike.congr_fun hzero z
      rw [inner_closedHalfSpaceLE_eq_dual (E := E) b c]
      exact
        (Set.closedHalfSpaceLE_isClosedHalfSpace hl :
          IsClosedHalfSpace (StrongDual ℝ E) ℝ (closedHalfSpaceLE l c))
    · let l : StrongDual ℝ E := InnerProductSpace.toDual ℝ E b
      have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero hb
      have hl0 : l ≠ 0 := by
        intro hl0
        apply hb0
        exact (InnerProductSpace.toDual ℝ E).injective (by simpa [l] using hl0)
      have hl : HasLinearPairing.pairingLinear.flip l ≠ (0 : E →ₗ[ℝ] ℝ) := by
        intro hzero
        apply hl0
        ext z
        exact DFunLike.congr_fun hzero z
      rw [inner_closedHalfSpaceGE_eq_dual (E := E) b c]
      exact
        (Set.closedHalfSpaceGE_isClosedHalfSpace hl :
          IsClosedHalfSpace (StrongDual ℝ E) ℝ (closedHalfSpaceGE l c))

private theorem containing_halfSpace_family_dual_eq_inner (C : Set E) :
    {s : Set E | IsClosedHalfSpace (StrongDual ℝ E) ℝ s ∧ C ⊆ s} =
      {s : Set E | IsClosedHalfSpace E ℝ s ∧ C ⊆ s} := by
  ext s
  constructor <;> rintro ⟨hs, hsubset⟩
  · exact ⟨(isClosedHalfSpace_dual_iff_inner (E := E)).1 hs, hsubset⟩
  · exact ⟨(isClosedHalfSpace_dual_iff_inner (E := E)).2 hs, hsubset⟩

/-- Theorem 11.5, inner-product bridge specialization of the continuous-dual statement:
a closed convex set in a nontrivial complete real
inner product space is the intersection of all closed half-spaces that contain it. -/
-- Proof sketch: rewrite the inner-product half-space family as the continuous-dual half-space
-- family via `InnerProductSpace.toDual`; then apply the continuous-dual theorem
-- `closed_convex_eq_sInter_closedHalfSpacesContaining`.
theorem closed_convex_eq_sInter_closedHalfSpacesContaining_inner (C : Set E)
    [Nontrivial E]
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    C = ⋂₀ {s : Set E | (closedHalfSpace[E,ℝ] s) ∧ C ⊆ s} := by
  simpa [containing_halfSpace_family_dual_eq_inner (E := E) C] using
    (closed_convex_eq_sInter_closedHalfSpacesContaining (E := E) C hC_closed hC_convex)

end
