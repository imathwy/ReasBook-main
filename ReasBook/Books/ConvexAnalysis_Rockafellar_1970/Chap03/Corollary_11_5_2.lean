import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_11
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_5

-- Declarations for this item will be appended below by the statement pipeline.

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
