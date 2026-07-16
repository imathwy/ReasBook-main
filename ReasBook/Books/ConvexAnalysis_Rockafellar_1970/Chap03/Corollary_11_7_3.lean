import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_0_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_5_16
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_11_5_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_11_7_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Nontrivial (StrongDual ℝ E)]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 11.7.3 says that a proper convex cone in `R^n` is contained in a
  homogeneous closed half-space.
- `core/canonical`: the owner abstractions are the set-level predicates `Convex ℝ` and
  `Set.IsCone ℝ` on subsets of `E`, together with pairing-level owners on `E →ₗ[ℝ] ℝ`
  (`homClosedHalfSpace[E →ₗ[ℝ] ℝ,ℝ]` and linear-functional inequalities).
- `bridge/view`: the continuous-dual and inner-product formulations are bridge layers; the
  inner-product specialization reads as a nonzero normal vector `b` with `⟪x, b⟫ ≤ 0`.
- Primitive data vs derived API: the primitive input is the subset `K`; convexity, conic closure,
  and closure-level properness `closure K ≠ Set.univ` are hypotheses, while the existence of a
  proper containing homogeneous half-space is theorem-level content.
- Domain-style sampling used here: the chapter predicate `Set.IsCone ℝ`, the owner-side
  `Set.IsClosedHalfSpace (E →ₗ[ℝ] ℝ) ℝ`, the half-space constructor `closedHalfSpaceLE`, the
  homogeneous owner predicate `homClosedHalfSpace[E →ₗ[ℝ] ℝ,ℝ]`, the chapter homogenization
  theorem `exists_homogeneous_closedHalfSpace_containing_excluding`, and the earlier barrier-cone
  and containing-half-space consequences from Corollary 11.5.2.
- Codomain/ambient check: the proof uses barrier and closed-half-space owners from Corollary 11.5.2
  (`exists_nonzero_mem_barrier_of_convex_closure_ne_univ`,
  `exists_closedHalfSpace_containing_of_convex_closure_ne_univ`) and the homogenization bridge
  from Corollary 11.7.1. The continuous-dual bridge layer `StrongDual ℝ E` is now confined to the
  downstream inner-product transport step.
- Layer target: primitive theorem at closure-level properness; source-facing `K ≠ Set.univ`
  theorem obtained as the finite-dimensional specialization.
-/

/-- Pairing-level primitive bridge: a convex cone with proper closure admits a nonzero linear
functional whose values are nonpositive on the cone. -/
-- Proof sketch: Corollary 11.5.2 gives a nonzero `l ∈ barr[ℝ](K)`, so `⟪x, l⟫ₚ` is bounded
-- above by some `β` on `K`. The cone lemma
-- `Set.IsCone.pairing_nonpos_of_bddAbove` then sharpens this to `⟪x, l⟫ₚ ≤ 0`.
theorem exists_nonzero_pairing_nonpos_of_convex_cone_closure_ne_univ {K : Set E}
    (hK_convex : Convex ℝ K) (hK_cone : Set.IsCone ℝ K)
    (hK_closure_ne_univ : closure K ≠ Set.univ) :
    ∃ l : E →ₗ[ℝ] ℝ, l ≠ 0 ∧ ∀ x ∈ K, l x ≤ 0 := by
  rcases exists_nonzero_mem_barrier_of_convex_closure_ne_univ
      hK_convex hK_closure_ne_univ with
    ⟨l, hl, hlK⟩
  rcases mem_barrier_iff_exists_bound.mp hlK with ⟨β, hβ⟩
  have hβ_bdd : BddAbove ((fun x : E ↦ (⟪x, l⟫ₚ : ℝ)) '' K) := by
    refine ⟨β, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hβ x hx
  refine ⟨l, hl, ?_⟩
  intro x hx
  change (⟪x, l⟫ₚ : ℝ) ≤ 0
  exact Set.IsCone.pairing_nonpos_of_bddAbove hK_cone hβ_bdd x hx

omit [Nontrivial (StrongDual ℝ E)] in
private theorem Set.IsClosedHalfSpace.compl_nonempty {Y : Type*}
    [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
    {s : Set E} (hs : Set.IsClosedHalfSpace Y ℝ s) :
    sᶜ.Nonempty := by
  rcases hs with ⟨b, β, hb, rfl | rfl⟩
  · rcases Set.IsOpenHalfSpace.nonempty
      (Set.openHalfSpaceGT_isOpenHalfSpace hb :
        Set.IsOpenHalfSpace Y ℝ (openHalfSpaceGT b β))
      with ⟨x, hx⟩
    exact ⟨x, by
      change x ∉ closedHalfSpaceLE b β
      intro hxle
      exact (not_lt_of_ge (mem_closedHalfSpaceLE_iff.mp hxle))
        (mem_openHalfSpaceGT_iff.mp hx)⟩
  · rcases Set.IsOpenHalfSpace.nonempty
      (Set.openHalfSpaceLT_isOpenHalfSpace hb :
        Set.IsOpenHalfSpace Y ℝ (openHalfSpaceLT b β))
      with ⟨x, hx⟩
    exact ⟨x, by
      change x ∉ closedHalfSpaceGE b β
      intro hxge
      exact (not_lt_of_ge (mem_closedHalfSpaceGE_iff.mp hxge))
        (mem_openHalfSpaceLT_iff.mp hx)⟩

/-- Primitive owner form: a convex cone with proper closure is contained in a proper homogeneous
pairing-owner closed half-space. -/
-- Proof sketch: if `K = ∅`, take any nonzero linear functional `l` from Corollary 11.5.2 and use
-- `closedHalfSpaceLE l 0`. Otherwise Corollary 11.5.2 gives a pairing-owner closed half-space `s`
-- containing `K`; the local complement lemma provides `x ∉ s`, and the chapter homogenization
-- theorem turns `s` into a containing homogeneous half-space.
theorem exists_homogeneous_closedHalfSpace_containing_of_convex_cone_closure_ne_univ {K : Set E}
    (hK_convex : Convex ℝ K) (hK_cone : Set.IsCone ℝ K)
    (hK_closure_ne_univ : closure K ≠ Set.univ) :
    ∃ s : Set E, (homClosedHalfSpace[E →ₗ[ℝ] ℝ,ℝ] s) ∧ K ⊆ s ∧ s ≠ Set.univ := by
  by_cases hK_empty : K = ∅
  · -- In the empty-cone branch we only need a nonzero dual functional witness.
    -- Corollary 11.5.2 now exposes this through pairing-level `barr[ℝ](K)` membership.
    rcases exists_nonzero_mem_barrier_of_convex_closure_ne_univ
        hK_convex hK_closure_ne_univ with
      ⟨l, hl, -⟩
    have hl' : HasLinearPairing.pairingLinear.flip l ≠ (0 : E →ₗ[ℝ] ℝ) := by
      simpa using hl
    have hs_closed :
        Set.IsClosedHalfSpace (E →ₗ[ℝ] ℝ) ℝ (closedHalfSpaceLE l (0 : ℝ) : Set E) :=
      Set.closedHalfSpaceLE_isClosedHalfSpace hl'
    have hs_not_univ : (closedHalfSpaceLE l (0 : ℝ) : Set E) ≠ Set.univ := by
      intro hs_univ
      rcases hs_closed.compl_nonempty with ⟨x, hx⟩
      exact hx <| by simp [hs_univ]
    refine ⟨closedHalfSpaceLE l 0, ?_, ?_, hs_not_univ⟩
    · exact Set.IsHomogeneousClosedHalfSpace.closedHalfSpaceLE_zero l hl'
    · simp [hK_empty]
  · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    have hflip_surj :
        Function.Surjective
          (HasLinearPairing.pairingLinear.flip : (E →ₗ[ℝ] ℝ) → E →ₗ[ℝ] ℝ) := by
      intro f
      refine ⟨f, ?_⟩
      ext x
      rfl
    rcases exists_closedHalfSpace_containing_of_convex_closure_ne_univ
        hK_convex hK_closure_ne_univ
      with
      ⟨s, hsLinear, hKs⟩
    have hs : Set.IsClosedHalfSpace (E →ₗ[ℝ] ℝ) ℝ s :=
      hsLinear.toClosedHalfSpace_of_surjective_pairingLinear_flip
        (Y := E →ₗ[ℝ] ℝ) hflip_surj
    rcases hs.compl_nonempty with ⟨x, hx⟩
    rcases exists_homogeneous_closedHalfSpace_containing_excluding
        hK_nonempty hK_cone hs hKs hx with
      ⟨t, ht_homogeneous, hKt, hx_not_t⟩
    refine ⟨t, ht_homogeneous, hKt, ?_⟩
    intro ht_univ
    exact hx_not_t <| by simp [ht_univ]

end

section SourceSpecialization

open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
private theorem closure_ne_univ_of_convex_ne_univ {K : Set E} (hK_convex : Convex ℝ K)
    (hK_ne_univ : K ≠ Set.univ) :
    closure K ≠ Set.univ := by
  intro hclosure_univ
  have hspan : affineSpan ℝ K = ⊤ := by
    calc
      affineSpan ℝ K = affineSpan ℝ (closure K) := Set.affineSpan_closure.symm
      _ = ⊤ := by simp [hclosure_univ]
  rcases (hK_convex.interior_nonempty_iff_affineSpan_eq_top).2 hspan with ⟨x, hx⟩
  have hinterior_eq_univ : interior K = Set.univ := by
    rw [← hK_convex.interior_closure_eq_interior_of_nonempty_interior ⟨x, hx⟩]
    simp [hclosure_univ]
  exact hK_ne_univ <|
    Set.eq_univ_iff_forall.mpr fun y ↦ interior_subset (by simp [hinterior_eq_univ])

/-- Source-facing bridge specialization: in finite-dimensional real spaces, a proper convex cone
admits a nonzero linear functional whose values are nonpositive on the cone. -/
theorem exists_nonzero_pairing_nonpos_of_convex_cone_ne_univ {K : Set E}
    (hK_convex : Convex ℝ K) (hK_cone : Set.IsCone ℝ K) (hK_ne_univ : K ≠ Set.univ) :
    ∃ l : E →ₗ[ℝ] ℝ, l ≠ 0 ∧ ∀ x ∈ K, l x ≤ 0 := by
  exact exists_nonzero_pairing_nonpos_of_convex_cone_closure_ne_univ hK_convex hK_cone
    (closure_ne_univ_of_convex_ne_univ hK_convex hK_ne_univ)

/-- Corollary 11.7.3, source-facing specialization: every proper convex cone in a nontrivial
finite-dimensional real normed space is contained in a proper homogeneous pairing-owner closed
half-space. Specializing to `EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement for
`0 < n`. -/
theorem exists_homogeneous_closedHalfSpace_containing_of_convex_cone_ne_univ {K : Set E}
    (hK_convex : Convex ℝ K) (hK_cone : Set.IsCone ℝ K) (hK_ne_univ : K ≠ Set.univ) :
    ∃ s : Set E, (homClosedHalfSpace[E →ₗ[ℝ] ℝ,ℝ] s) ∧ K ⊆ s ∧ s ≠ Set.univ := by
  exact exists_homogeneous_closedHalfSpace_containing_of_convex_cone_closure_ne_univ hK_convex
    hK_cone (closure_ne_univ_of_convex_ne_univ hK_convex hK_ne_univ)

end SourceSpecialization

section InnerProductBridge

open scoped Rockafellar
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Corollary 11.7.3, inner-product form: a proper convex cone admits a nonzero normal vector
whose values are nonpositive on the cone. -/
-- Proof sketch: first apply the pairing-level theorem
-- `exists_nonzero_pairing_nonpos_of_convex_cone_ne_univ`, then transport the nonzero functional
-- through the Riesz isomorphism `InnerProductSpace.toDual` and rewrite pairings as inner
-- products.
theorem exists_nonzero_inner_nonpos_of_convex_cone_ne_univ {K : Set E}
    (hK_convex : Convex ℝ K) (hK_cone : Set.IsCone ℝ K) (hK_ne_univ : K ≠ Set.univ) :
    ∃ b : E, b ≠ 0 ∧ ∀ x ∈ K, ⟪x, b⟫ ≤ 0 := by
  rcases exists_nonzero_pairing_nonpos_of_convex_cone_ne_univ hK_convex hK_cone hK_ne_univ with
    ⟨l, hl, hl_nonpos⟩
  let lStrong : StrongDual ℝ E :=
    { toLinearMap := l
      cont := LinearMap.continuous_of_finiteDimensional l }
  have hlStrong : lStrong ≠ 0 := by
    intro hlStrong0
    apply hl
    ext x
    have hx0 : lStrong x = 0 := congrArg (fun f : StrongDual ℝ E => f x) hlStrong0
    simpa [lStrong] using hx0
  let b : E := (InnerProductSpace.toDual ℝ E).symm lStrong
  have hb : b ≠ 0 := by
    intro hb0
    apply hlStrong
    calc
      lStrong = (InnerProductSpace.toDual ℝ E) b := by simp [b]
      _ = 0 := by simp [hb0]
  refine ⟨b, hb, ?_⟩
  intro x hx
  have hxle : l x ≤ 0 := hl_nonpos x hx
  have hxle' : ⟪b, x⟫ ≤ 0 := by
    change inner ℝ b x ≤ 0
    calc
      inner ℝ b x = lStrong x := by
        simp [b, InnerProductSpace.toDual_symm_apply]
      _ = l x := rfl
      _ ≤ 0 := hxle
  simpa [real_inner_comm] using hxle'

end InnerProductBridge
