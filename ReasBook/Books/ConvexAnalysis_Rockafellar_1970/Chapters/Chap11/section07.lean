import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_11_7_1 (from Chap03) -/
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

/-! ### Corollary_11_7_2 (from Chap03) -/
section

open Set
open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
local notation "E⋆" => StrongDual ℝ E

local instance instHasLinearPairingStrongDualTopologicalCor1172 :
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

local instance instHasContinuousPairingStrongDualTopologicalCor1172 :
    HasContinuousPairing E E⋆ ℝ where
  continuous_pairing_left l := l.continuous

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 11.7.2 states that for any subset `S`, the closure of the convex
  cone generated by `S` is the intersection of all homogeneous closed half-spaces containing `S`.
- `core/canonical`: the generated-cone owner is `cone[ℝ] S`, and the containing family is indexed
  by the canonical homogeneous half-space owner
  `homClosedHalfSpace[E⋆,ℝ]`.
- `bridge/view`: this item is the direct specialization of Corollary 11.7.1 to
  `K = ((cone[ℝ] S).closure : Set E)` together with the closure-containment equivalence
  `((cone[ℝ] S).closure : Set E) ⊆ s ↔ S ⊆ s` for homogeneous containing half-spaces.
- Primitive data vs derived API: the primitive input is the subset `S`; generated-cone closure and
  the homogeneous-half-space intersection formula are theorem-level API.
- Layer target: `source-facing` on the canonical pairing-based owner layer (dual-owner
  homogeneous closed half-spaces), avoiding inner-product-only owners.
- Scalar-layer justification: this declaration remains over `ℝ` because it is a direct
  specialization of `closed_convex_cone_eq_sInter_homogeneousClosedHalfSpacesContaining`, whose
  current canonical owner layer is the real continuous-dual setting from Corollary 11.7.1.
-/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
private theorem homogeneousClosedHalfSpace_isClosed {s : Set E}
    (hs : homClosedHalfSpace[E⋆,ℝ] s) :
    IsClosed s := by
  exact hs.isClosedHalfSpace.isClosed

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
private theorem zero_mem_of_homogeneousClosedHalfSpace {s : Set E}
    (hs : homClosedHalfSpace[E⋆,ℝ] s) :
    (0 : E) ∈ s := by
  rcases hs with ⟨l, _, rfl | rfl⟩
  · have hpair0 : (HasPairing.pairing (0 : E) l : ℝ) = 0 := by
      change (HasLinearPairing.pairingLinear (0 : E)) l = 0
      simp [LinearMap.map_zero]
    exact mem_closedHalfSpaceLE_iff.mpr hpair0.le
  · have hpair0 : (HasPairing.pairing (0 : E) l : ℝ) = 0 := by
      change (HasLinearPairing.pairingLinear (0 : E)) l = 0
      simp [LinearMap.map_zero]
    exact mem_closedHalfSpaceGE_iff.mpr hpair0.ge

omit [LocallyConvexSpace ℝ E] in
private theorem closure_cone_subset_iff_subset {S s : Set E}
    (hs_homogeneous : homClosedHalfSpace[E⋆,ℝ] s) :
    ((cone[ℝ] S).closure : Set E) ⊆ s ↔ S ⊆ s := by
  constructor
  · intro h x hx
    exact h <| by
      simpa using
        ((PointedCone.mem_closure).2 (subset_closure (PointedCone.subset_hull hx)))
  · intro hS
    have hs_cone : Set.IsCone ℝ s := hs_homogeneous.isCone
    have hs_convex : Convex ℝ s := hs_homogeneous.isConvexCone.convex
    have h0 : (0 : E) ∈ s := zero_mem_of_homogeneousClosedHalfSpace hs_homogeneous
    let C : ConvexCone ℝ E := {
      carrier := s
      smul_mem' := fun {_} ha {_} hx ↦ hs_cone.smul_mem ha hx
      add_mem' := fun {_} hx {_} hy ↦ hs_cone.add_mem hs_convex hx hy
    }
    let P : PointedCone ℝ E := C.toPointedCone h0
    have hHull : (cone[ℝ] S) ≤ P := by
      exact Submodule.span_le.mpr <| by
        intro x hx
        simpa [P, C] using hS hx
    have hHull' : (cone[ℝ] S : Set E) ⊆ s := by
      intro x hx
      simpa [P, C] using hHull hx
    exact closure_minimal hHull' (homogeneousClosedHalfSpace_isClosed hs_homogeneous)

variable [Nontrivial (StrongDual ℝ E)]

/-- Corollary 11.7.2, in canonical dual-owner form: for any subset `S` of a real locally convex
topological vector space,
the closure of the convex cone generated by `S` is the intersection of all homogeneous
closed dual-owner half-spaces containing `S`. Specializing to `EuclideanSpace ℝ (Fin n)` recovers
the textbook `R^n` statement. -/
-- Proof sketch: apply Corollary 11.7.1 to `K = ((cone[ℝ] S).closure : Set E)`.
-- Then identify containing homogeneous half-spaces by
-- `((cone[ℝ] S).closure : Set E) ⊆ s ↔ S ⊆ s`.
theorem closure_convexConeGenerated_eq_sInter_homogeneousClosedHalfSpacesContaining {S : Set E} :
    ((cone[ℝ] S).closure : Set E) =
      ⋂₀ {s : Set E | (homClosedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
  let K : Set E := ((cone[ℝ] S).closure : Set E)
  have hfamily :
      {s : Set E | (homClosedHalfSpace[E⋆,ℝ] s) ∧ K ⊆ s} =
        {s : Set E | (homClosedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
    ext s
    constructor
    · rintro ⟨hs_homogeneous, hsubset⟩
      exact ⟨hs_homogeneous, (closure_cone_subset_iff_subset hs_homogeneous).1 hsubset⟩
    · rintro ⟨hs_homogeneous, hsubset⟩
      exact ⟨hs_homogeneous, (closure_cone_subset_iff_subset hs_homogeneous).2 hsubset⟩
  have hnonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ ((cone[ℝ] S).closure : Set E)
    exact (cone[ℝ] S).closure.zero_mem
  have hclosed : IsClosed K := by
    simp [K, PointedCone.coe_closure]
  have hconvex : Convex ℝ K := by
    simpa [K] using (cone[ℝ] S).closure.convex
  have hcone : Set.IsCone ℝ K := by
    simpa [K] using (((cone[ℝ] S).closure : ConvexCone ℝ E).isCone)
  have hK :
      K = ⋂₀ {s : Set E | (homClosedHalfSpace[E⋆,ℝ] s) ∧ K ⊆ s} :=
    closed_convex_cone_eq_sInter_homogeneousClosedHalfSpacesContaining
      hnonempty hclosed hconvex hcone
  rw [hfamily] at hK
  simpa [K] using hK

end

/-! ### Corollary_11_7_3 (from Chap03) -/
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

/-! ### Theorem_11_7 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.7 says that when two nonempty subsets admit a proper separating
  hyperplane and at least one of them is a cone, one can choose such a hyperplane to pass through
  the origin.
- `core/canonical`: the owner abstractions are the chapter predicate `Set.IsCone 𝕜` on subsets
  and the affine-subspace separation predicate `AffineSubspace.SeparatesProperly`.
- `bridge/view`: the textbook phrase "passes through the origin" is represented by the canonical
  owner-membership statement `0 ∈ H`.
- Domain-style sampling used here: the project declaration `Set.IsCone 𝕜` from Definition 2.5.9,
  its owner lemma `Set.IsCone.smul_mem`, `AffineSubspace.SeparatesProperly` and its symmetry
  theorem from Text 11.0.2, and mathlib's `AffineSubspace` owner API.
- Primitive data vs derived API: the primitive inputs are the two sets, their nonemptiness, the
  existence of a proper separator, and a one-sided cone hypothesis on one chosen set.
- Layer target: `source-facing`, stated directly in terms of the canonical affine-subspace owner
  instead of repackaging the hyperplane data.
- Ambient refinement: the public statement uses only the existing cone predicate, the proper-
  separation owner relation, and origin membership in the separator. The one-sided core is
  therefore canonically stated on arbitrary pairing spaces over ordered fields. The symmetric
  theorem below is then stated at the same ordered-field layer via
  `AffineSubspace.SeparatesProperly.symm`.
-/
/-- The one-sided core of Theorem 11.7: when the second set is a cone, a proper separating
hyperplane may be chosen through the origin. The full symmetric theorem below is derived from this
core case using `AffineSubspace.SeparatesProperly.symm`. -/
theorem exists_separatesProperly_through_origin_of_isCone_right
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty)
    (hC2_cone : Set.IsCone 𝕜 C2)
    (hsep : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2)) :
    ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2) ∧ 0 ∈ H := by
  rcases hsep with ⟨H, hH⟩
  rcases hH.separates with ⟨b, β, hb, rfl, hC1_le, hC2_ge⟩
  have hC2_upper : ∀ x ∈ C2, (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) ≤ -β := by
    intro x hx
    have hx_ge : β ≤ (⟪x, b⟫ₚ : 𝕜) := mem_closedHalfSpaceGE_iff.mp (hC2_ge hx)
    have hneg : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) = -⟪x, b⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    rw [hneg]
    linarith
  have hC2_bdd : BddAbove ((fun x : E ↦ (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜)) '' C2) := by
    refine ⟨-β, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hC2_upper x hx
  have hβ_nonpos : β ≤ 0 := by
    have hnegβ_nonneg : 0 ≤ -β :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty hC2_cone hC2_nonempty hC2_upper
    linarith
  have hC1_le_zero : C1 ⊆ closedHalfSpaceLE b (0 : 𝕜) := by
    intro x hx
    rw [mem_closedHalfSpaceLE_iff]
    exact le_trans (mem_closedHalfSpaceLE_iff.mp (hC1_le hx)) hβ_nonpos
  have hC2_ge_zero : C2 ⊆ closedHalfSpaceGE b (0 : 𝕜) := by
    intro x hx
    rw [mem_closedHalfSpaceGE_iff]
    have hx_nonpos : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) ≤ 0 :=
      Set.IsCone.pairing_nonpos_of_bddAbove hC2_cone hC2_bdd x hx
    have hneg : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) = -⟪x, b⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    rw [hneg] at hx_nonpos
    linarith
  refine ⟨affineHyperplane b (0 : 𝕜), ?_, ?_⟩
  · refine ⟨⟨b, 0, hb, rfl, hC1_le_zero, hC2_ge_zero⟩, ?_⟩
    intro hboth
    rcases hC1_nonempty with ⟨x1, hx1⟩
    have hβ_nonneg : 0 ≤ β := by
      have hx1H : x1 ∈ (affineHyperplane b (0 : 𝕜) : AffineSubspace 𝕜 E) := hboth.1 hx1
      have hx1_eq : (⟪x1, b⟫ₚ : 𝕜) = 0 := by
        simpa [mem_affineHyperplane_iff] using hx1H
      have hx1_le : (⟪x1, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hC1_le hx1)
      linarith
    have hβ_zero : β = 0 := by linarith
    have h_aff : (affineHyperplane b (0 : 𝕜) : AffineSubspace 𝕜 E) = affineHyperplane b β := by
      simp [hβ_zero]
    exact hH.not_both_subset <| by simpa [h_aff] using hboth
  · simp

end

section

open scoped Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]

/-- Theorem 11.7, stated in the canonical ambient form: if nonempty sets `C1` and `C2` admit a
proper separating hyperplane and at least one of them is a cone, then they admit a proper
separating hyperplane which passes through the origin. -/
-- Proof sketch: by symmetry, reduce to the case that `C2` is a cone. If
-- `affineHyperplane b β` separates `C1` and `C2` properly, conic closure of `C2` forces
-- `C2 ⊆ closedHalfSpaceGE b 0` and hence `β ≤ 0`; therefore `C1 ⊆ closedHalfSpaceLE b 0`. The
-- homogeneous hyperplane `affineHyperplane b 0` still separates the two sets. If both sets lay in
-- that new hyperplane, nonemptiness of `C1` would force `β ≥ 0`, hence `β = 0`, contradicting
-- properness of the original separator.
theorem exists_separatesProperly_through_origin_of_one_isCone
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty)
    (hcone : Set.IsCone 𝕜 C1 ∨ Set.IsCone 𝕜 C2)
    (hsep : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2)) :
    ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2) ∧ 0 ∈ H := by
  rcases hcone with hC1_cone | hC2_cone
  · have hsep' : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C2 and C1) := by
      rcases hsep with ⟨H, hH⟩
      exact ⟨H, hH.symm⟩
    rcases
        exists_separatesProperly_through_origin_of_isCone_right
          hC2_nonempty hC1_nonempty hC1_cone hsep'
      with
      ⟨H, hH, h0H⟩
    exact ⟨H, hH.symm, h0H⟩
  · exact
      exists_separatesProperly_through_origin_of_isCone_right
        hC1_nonempty hC2_nonempty hC2_cone hsep

end
