import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_11_5_1 (from Chap03) -/
section

open Set
open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Nontrivial (StrongDual ℝ E)]
local notation "E⋆" => StrongDual ℝ E

local instance instHasLinearPairingStrongDualTopologicalCor1151 :
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

- `source-facing`: Corollary 11.5.1 states that for any subset `S ⊆ R^n`, the closure of its
  convex hull is, in positive dimension, the intersection of all closed half-spaces containing
  `S`.
- `core/canonical`: the owner abstractions are `closedConvexHull ℝ`, the chapter predicate
  `closedHalfSpace[_,_]`, and the set-theoretic intersection operator `⋂₀`.
- `bridge/view`: the textbook phrase “the closed half-spaces containing `S`” is rendered as the
  family `{s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s}`.
- Primitive data vs derived API: the primitive input is the subset `S`, while the canonical owner
  object `closedConvexHull ℝ S` is generated data. The half-space containment equivalence and the
  displayed intersection formula are theorem-level bridge API.
- Domain-style sampling used here: `closedConvexHull ℝ`,
  `closedConvexHull_eq_closure_convexHull`, the owner methods
  `Set.IsClosedHalfSpace.convex`, the orientation closedness bridges
  `closedHalfSpaceLE_closed_of_continuous`/`closedHalfSpaceGE_closed_of_continuous`, and the
  preceding chapter theorem
  `closed_convex_eq_sInter_closedHalfSpacesContaining`.
- Layer target: `bridge/view`; this is the specialization of Theorem 11.5 to the canonical owner
  `closedConvexHull ℝ S`, together with the observation that a closed half-space contains that
  owner object exactly when it contains `S`.
- Ambient refinement: the source `R^n` statement in positive dimension is a Euclidean
  specialization of the canonical real locally convex topological vector-space statement with
  nontrivial continuous dual, phrased with dual-owner closed half-spaces.
-/

theorem closedConvexHull_eq_sInter_closedHalfSpacesContaining {S : Set E} :
    closedConvexHull ℝ S = ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
  have hfamily :
      {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ closedConvexHull ℝ S ⊆ s} =
        {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
    ext s
    constructor
    · rintro ⟨hs, hsubset⟩
      exact ⟨hs, subset_trans subset_closedConvexHull hsubset⟩
    · rintro ⟨hs, hsubset⟩
      have hs_closed : IsClosed s := by
        rcases hs with ⟨l, β, -, rfl | rfl⟩
        · exact closedHalfSpaceLE_closed_of_continuous l β l.continuous
        · exact closedHalfSpaceGE_closed_of_continuous l β l.continuous
      exact ⟨hs, closedConvexHull_min hsubset hs.convex hs_closed⟩
  simpa [hfamily] using
    closed_convex_eq_sInter_closedHalfSpacesContaining (closedConvexHull ℝ S)
      isClosed_closedConvexHull convex_closedConvexHull

theorem closure_convexHull_eq_sInter_closedHalfSpacesContaining {S : Set E} :
    closure (convexHull ℝ S) =
      ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
  simpa [closedConvexHull_eq_closure_convexHull] using
    (closedConvexHull_eq_sInter_closedHalfSpacesContaining (S := S))

end

/-! ### Corollary_11_5_2 (from Chap03) -/
section

open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Nontrivial (StrongDual ℝ E)]

local instance instHasLinearPairingStrongDualTopologicalCor11_5_2 :
    HasLinearPairing E (StrongDual ℝ E) ℝ where
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

/-
Source/core/bridge triage:
- `source-facing`: Corollary 11.5.2 asserts that every proper convex subset of `R^n` is contained
  in some closed half-space.
- `core/canonical`: the owner abstractions are `Convex ℝ` on subsets of `E`, the intrinsic
  chapter predicate `closedLinearHalfSpace[ℝ]`, and the earlier project owner
  `barr[ℝ](C)` for “functionals bounded above on `C`”, with theorem surfaces using
  intrinsic linear-functional owners.
- `bridge/view`: the textbook reformulation “there exists `b` such that `⟪·, b⟫` is bounded above
  on `C`” is the membership condition `b ∈ barr[ℝ](C)`, equivalently
  `BddAbove ((fun x ↦ ⟪x, b⟫) '' C)`.
- Primitive data vs derived API: the primitive input is the convex set `C` together with the
  closure-level properness condition `closure C ≠ Set.univ`; the source-facing properness
  `C ≠ Set.univ` is a stronger specialization used later in finite-dimensional ambient spaces.
  The continuous-dual owner `StrongDual ℝ E` is kept as a bridge/view layer only.
- Domain-style sampling used here: the project declarations `IsClosedHalfSpace`,
  `closedHalfSpaceLE`, `closed_convex_eq_sInter_closedHalfSpacesContaining`, and `barrier`
  identify the chapter/project owner abstractions in this domain;
  `mem_barrier_iff_exists_bound` supplies the canonical bridge to the textbook bounded-above
  quantifier form.
- Layer target: the primitive declarations are closure-level intrinsic linear-functional-owner
  statements, with continuous-dual and finite-dimensional forms as bridge/source-facing
  corollaries; the raw bounded-above linear-functional phrasing is recovered directly from
  `barrierCone` membership rather than kept as a parallel public theorem.
-/

/-- Continuous-dual bridge form: if a convex set has proper closure, then it is contained in a
continuous-dual closed half-space. -/
theorem exists_closedHalfSpace_containing_strongDual_of_convex_closure_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hclosure_ne_univ : closure C ≠ Set.univ) :
    ∃ s : Set E, (closedHalfSpace[StrongDual ℝ E,ℝ] s) ∧ C ⊆ s := by
  classical
  let H : Set (Set E) := {s : Set E | (closedHalfSpace[StrongDual ℝ E,ℝ] s) ∧ closure C ⊆ s}
  have hclosure_eq : closure C = ⋂₀ H := by
    simpa [H] using
      closed_convex_eq_sInter_closedHalfSpacesContaining (closure C) isClosed_closure
        hC_conv.closure
  have hfamily_nonempty : H.Nonempty := by
    by_contra hfamily_empty
    exact hclosure_ne_univ <| hclosure_eq.trans <| by
      simp [H, Set.not_nonempty_iff_eq_empty.mp hfamily_empty]
  rcases hfamily_nonempty with ⟨s, hs⟩
  exact ⟨s, hs.1, subset_closure.trans hs.2⟩

/-- Primitive canonical intrinsic-owner form: if a convex set has proper closure, then it is
contained in a closed linear half-space. -/
theorem exists_closedHalfSpace_containing_of_convex_closure_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hclosure_ne_univ : closure C ≠ Set.univ) :
    ∃ s : Set E, (closedLinearHalfSpace[ℝ] s) ∧ C ⊆ s := by
  rcases exists_closedHalfSpace_containing_strongDual_of_convex_closure_ne_univ hC_conv
      hclosure_ne_univ with ⟨s, hs, hCs⟩
  exact ⟨s, hs.toClosedLinearHalfSpace, hCs⟩

/-- Continuous-dual bridge consequence: a convex set with proper closure has a nonzero element in
its continuous-dual barrier set. -/
-- Proof sketch: choose a closed half-space `s` containing `C` from
-- `exists_closedHalfSpace_containing_strongDual_of_convex_closure_ne_univ`. The canonical predicate
-- `IsClosedHalfSpace Y 𝕜 s` presents `s` directly as `closedHalfSpaceLE l β` for some nontrivial
-- continuous linear functional `l`, and the containment `C ⊆ s` exactly says that `l` lies in
-- `barr[ℝ](C)`.
theorem exists_nonzero_mem_barrier_strongDual_of_convex_closure_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hclosure_ne_univ : closure C ≠ Set.univ) :
    ∃ l : StrongDual ℝ E, l ≠ 0 ∧
      l ∈ barr[ℝ](C) := by
  rcases exists_closedHalfSpace_containing_strongDual_of_convex_closure_ne_univ
      hC_conv hclosure_ne_univ with
    ⟨_, hs, hC_halfSpace⟩
  rcases hs with ⟨l, β, hl, rfl | rfl⟩
  · have hl' : l ≠ 0 := by
      intro hl0
      apply hl
      ext x
      simp [hl0]
    refine ⟨l, hl', mem_barrier_iff_exists_bound.2 ?_⟩
    refine ⟨β, fun x hx ↦ ?_⟩
    exact mem_closedHalfSpaceLE_iff.mp (hC_halfSpace hx)
  · have hl' : l ≠ 0 := by
      intro hl0
      apply hl
      ext x
      simp [hl0]
    refine
      ⟨-l, neg_ne_zero.mpr hl', mem_barrier_iff_exists_bound.2 ?_⟩
    refine ⟨-β, fun x hx ↦ ?_⟩
    have hxβ : β ≤ (⟪x, l⟫ₚ : ℝ) := mem_closedHalfSpaceGE_iff.mp (hC_halfSpace hx)
    change (⟪x, -l⟫ₚ : ℝ) ≤ -β
    rw [HasPairingNegRight.pairing_neg_right (x := x) (y := l)]
    exact neg_le_neg hxβ

/-- Primitive canonical barrier consequence: a convex set with proper closure has a nonzero
element in its pairing-level barrier set on `E →ₗ[ℝ] ℝ`. -/
theorem exists_nonzero_mem_barrier_of_convex_closure_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hclosure_ne_univ : closure C ≠ Set.univ) :
    ∃ l : E →ₗ[ℝ] ℝ, l ≠ 0 ∧ l ∈ barr[ℝ](C) := by
  rcases exists_nonzero_mem_barrier_strongDual_of_convex_closure_ne_univ hC_conv
      hclosure_ne_univ with ⟨l, hl, hlC⟩
  refine ⟨l.toLinearMap, ?_, ?_⟩
  · intro hzero
    apply hl
    ext x
    exact DFunLike.congr_fun hzero x
  · rcases mem_barrier_iff_exists_bound.mp hlC with ⟨β, hβ⟩
    refine mem_barrier_iff_exists_bound.mpr ⟨β, ?_⟩
    intro x hx
    exact hβ x hx

end

section

open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
private theorem closure_ne_univ_of_convex_ne_univ {C : Set E} (hC_conv : Convex ℝ C)
    (hC_ne_univ : C ≠ Set.univ) :
    closure C ≠ Set.univ := by
  intro hclosure_univ
  have hspan : affineSpan ℝ C = ⊤ := by
    calc
      affineSpan ℝ C = affineSpan ℝ (closure C) := Set.affineSpan_closure.symm
      _ = ⊤ := by simp [hclosure_univ]
  rcases (hC_conv.interior_nonempty_iff_affineSpan_eq_top).2 hspan with ⟨x, hx⟩
  have hinterior_eq_univ : interior C = Set.univ := by
    rw [← hC_conv.interior_closure_eq_interior_of_nonempty_interior ⟨x, hx⟩]
    simp [hclosure_univ]
  exact hC_ne_univ <|
    Set.eq_univ_iff_forall.mpr fun y ↦ interior_subset (by simp [hinterior_eq_univ])

/-- Corollary 11.5.2, in canonical intrinsic-owner form: every proper convex subset of a
nontrivial finite-dimensional real normed space is contained in some closed linear half-space. -/
theorem exists_closedHalfSpace_containing_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ s : Set E, (closedLinearHalfSpace[ℝ] s) ∧ C ⊆ s := by
  exact exists_closedHalfSpace_containing_of_convex_closure_ne_univ hC_conv
    (closure_ne_univ_of_convex_ne_univ hC_conv hC_ne_univ)

/-- A proper convex subset of a nontrivial finite-dimensional real normed space has a nonzero
element in its pairing-level barrier set on `E →ₗ[ℝ] ℝ`. -/
theorem exists_nonzero_mem_barrier_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ l : E →ₗ[ℝ] ℝ, l ≠ 0 ∧ l ∈ barr[ℝ](C) := by
  exact exists_nonzero_mem_barrier_of_convex_closure_ne_univ hC_conv
    (closure_ne_univ_of_convex_ne_univ hC_conv hC_ne_univ)

/-- Continuous-dual bridge specialization of Corollary 11.5.2 at closure-level properness. -/
theorem exists_closedHalfSpace_containing_strongDual_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ s : Set E, (closedHalfSpace[StrongDual ℝ E,ℝ] s) ∧ C ⊆ s := by
  exact exists_closedHalfSpace_containing_strongDual_of_convex_closure_ne_univ hC_conv
    (closure_ne_univ_of_convex_ne_univ hC_conv hC_ne_univ)

/-- Continuous-dual bridge specialization of the barrier conclusion at `C ≠ Set.univ`. -/
theorem exists_nonzero_mem_barrier_strongDual_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ l : StrongDual ℝ E, l ≠ 0 ∧ l ∈ barr[ℝ](C) := by
  exact exists_nonzero_mem_barrier_strongDual_of_convex_closure_ne_univ hC_conv
    (closure_ne_univ_of_convex_ne_univ hC_conv hC_ne_univ)

section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Inner-product bridge: a proper convex subset of a nontrivial finite-dimensional real
inner-product space has a nonzero element in the textbook self-dual barrier set. -/
theorem exists_nonzero_mem_barrier_inner_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ b : E, b ≠ 0 ∧ b ∈ barr[ℝ](C) := by
  rcases exists_nonzero_mem_barrier_strongDual_of_convex_ne_univ hC_conv hC_ne_univ with
    ⟨l, hl, hlC⟩
  let b : E := (InnerProductSpace.toDual ℝ E).symm l
  have hb : b ≠ 0 := by
      intro hb0
      apply hl
      calc
        l = (InnerProductSpace.toDual ℝ E) b := by
          simp [b]
        _ = 0 := by simp [hb0]
  have hbC : b ∈ barr[ℝ](C) := by
    rcases mem_barrier_iff_exists_bound.mp hlC with ⟨β, hβ⟩
    refine mem_barrier_iff_exists_bound.mpr ⟨β, ?_⟩
    intro x hx
    have hxle : (⟪x, l⟫ₚ : ℝ) ≤ β := hβ x hx
    have hxle' : ⟪b, x⟫ ≤ β := by
      change inner ℝ b x ≤ β
      have hxle' : l x ≤ β := by
        change l x ≤ β at hxle
        exact hxle
      calc
        inner ℝ b x = l x := by
          simp [b, InnerProductSpace.toDual_symm_apply]
        _ ≤ β := hxle'
    simpa [real_inner_comm] using hxle'
  exact ⟨b, hb, hbC⟩

/-- Inner-product bridge: every proper convex subset of a nontrivial finite-dimensional real
inner-product space is contained in a closed half-space cut out by a nonzero normal vector. -/
theorem exists_closedHalfSpace_containing_inner_of_convex_ne_univ {C : Set E}
    (hC_conv : Convex ℝ C) (hC_ne_univ : C ≠ Set.univ) :
    ∃ s : Set E, (closedHalfSpace[E,ℝ] s) ∧ C ⊆ s := by
  rcases exists_nonzero_mem_barrier_inner_of_convex_ne_univ hC_conv hC_ne_univ with
    ⟨b, hb, hbC⟩
  rcases mem_barrier_iff_exists_bound.mp hbC with ⟨β, hβ⟩
  have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : E →ₗ[ℝ] ℝ) := by
    intro hzero
    apply hb
    have hbb : HasLinearPairing.pairingLinear b b = (0 : ℝ) := by
      simpa using DFunLike.congr_fun hzero b
    have hbb_pos : (0 : ℝ) < HasLinearPairing.pairingLinear b b := by
      change (0 : ℝ) < inner ℝ b b
      simpa using (real_inner_self_pos (x := b)).2 hb
    linarith
  refine ⟨closedHalfSpaceLE b β, Set.closedHalfSpaceLE_isClosedHalfSpace hbflip, ?_⟩
  intro x hx
  exact mem_closedHalfSpaceLE_iff.mpr (hβ x hx)

end

end

/-! ### Theorem_11_5 (from Chap03) -/
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
