import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap03.Corollary_3_24
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Proposition_3_27
import BauschkeLean.Chap03.Proposition_3_30
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap15.Corollary_15_35
import BauschkeLean.Chap25.Corollary_25_36
import BauschkeLean.Chap25.Proposition_25_31

open EuclideanGeometry
open scoped ContinuousLinearMap InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction SetValuedOperator

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable (C D : ClosedSubmodule ℝ 𝓗)

local notation "P_C" => C.starProjection
local notation "P_D" => D.starProjection
local notation "P_CD" => P_C + P_D

-- Domain sampling:
-- * `source-facing`: Proposition 25.37 is the Anderson--Duffin projector identity on
--   `ClosedSubmodule`.
-- * `core/canonical`: the owner surfaces are `ClosedSubmodule.starProjection`,
--   `Function.toSetValuedOperator`, set-valued inverse `A⁻¹`, and Moore-Penrose notation
--   `T⁺[hT_closed]`.
-- * `bridge/view`: the local notation `P_C`, `P_D` restores the textbook projector surface over
--   that canonical owner, and Corollary 25.38 specializes the result to finite-dimensional
--   submodules.

/-- Helper for Proposition 25.37: the set-valued projector onto a closed submodule is the
singleton-valued operator induced by `starProjection`. -/
lemma setValuedProjector_closedSubmodule_eq_starProjection
    (V : ClosedSubmodule ℝ 𝓗) :
    P[((V : Submodule ℝ 𝓗) : Set 𝓗)] = V.starProjection.toSetValuedOperator := by
  ext x u
  let hV_cheb : IsChebyshev (((V : Submodule ℝ 𝓗) : Set 𝓗)) :=
    isChebyshev_of_nonempty_isClosed_convex ⟨0, by simp⟩ V.isClosed V.convex
  have hstar_best :
      IsBestApproximation x (((V : Submodule ℝ 𝓗) : Set 𝓗)) (V.starProjection x) := by
    constructor
    · exact (V : Submodule ℝ 𝓗).starProjection_apply_mem x
    · simpa [Metric.infDist_eq_iInf, dist_eq_norm] using
        ((V : Submodule ℝ 𝓗).starProjection_minimal x)
  have hproj_eq : P[(((V : Submodule ℝ 𝓗) : Set 𝓗)), hV_cheb] x = V.starProjection x := by
    symm
    exact eq_projectionPoint_of_isBestApproximation
      (((V : Submodule ℝ 𝓗) : Set 𝓗)) hV_cheb hstar_best
  constructor
  · intro hu
    have hu_proj : u = P[(((V : Submodule ℝ 𝓗) : Set 𝓗)), hV_cheb] x :=
      eq_projectionPoint_of_isBestApproximation
        (((V : Submodule ℝ 𝓗) : Set 𝓗)) hV_cheb hu
    rw [hproj_eq] at hu_proj
    simpa [Function.toSetValuedOperator_apply] using hu_proj
  · intro hu
    have hu_eq : u = V.starProjection x := by
      simpa [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] using hu
    rw [hu_eq]
    exact hstar_best

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 25.37: on a closed submodule, the normal cone is its orthogonal
complement. -/
lemma normalConeClosedSubmodule_eq_orthogonal_of_mem
    (V : ClosedSubmodule ℝ 𝓗) {x : 𝓗} (hx : x ∈ (V : Set 𝓗)) :
    N[((V : Submodule ℝ 𝓗) : Set 𝓗)] x = ((Vᗮ : ClosedSubmodule ℝ 𝓗) : Set 𝓗) := by
  let A : AffineSubspace ℝ 𝓗 := (V : Submodule ℝ 𝓗).toAffineSubspace
  have hAset : (((V : Submodule ℝ 𝓗) : Set 𝓗)) = (A : Set 𝓗) := by
    -- The affine subspace attached to a submodule has the same carrier.
    ext y
    simp [A, Submodule.mem_toAffineSubspace]
  rw [hAset]
  have hxA : x ∈ (A : Set 𝓗) := by
    simpa [A, Submodule.mem_toAffineSubspace] using hx
  -- On the submodule, Example 6.43 identifies the normal cone with the orthogonal complement.
  simpa [A, Submodule.toAffineSubspace_direction] using
    normalCone_affineSubspace_eq_direction_orthogonal_of_mem A hxA

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 25.37: off a closed submodule, the normal cone is empty. -/
lemma normalConeClosedSubmodule_eq_empty_of_not_mem
    (V : ClosedSubmodule ℝ 𝓗) {x : 𝓗} (hx : x ∉ (V : Set 𝓗)) :
    N[((V : Submodule ℝ 𝓗) : Set 𝓗)] x = ∅ := by
  let A : AffineSubspace ℝ 𝓗 := (V : Submodule ℝ 𝓗).toAffineSubspace
  have hAset : (((V : Submodule ℝ 𝓗) : Set 𝓗)) = (A : Set 𝓗) := by
    ext y
    simp [A, Submodule.mem_toAffineSubspace]
  rw [hAset]
  have hxA : x ∉ (A : Set 𝓗) := by
    simpa [A, Submodule.mem_toAffineSubspace] using hx
  -- Away from the submodule, Example 6.43 gives the empty normal cone.
  simpa using normalCone_affineSubspace_eq_empty_of_not_mem A hxA

/-- Helper for Proposition 25.37: if `C + D` is closed, then the sum of the orthogonal
complements agrees with `(C ⊓ D)ᗮ` on the underlying set surface. -/
lemma orthogonalSup_eq_infOrthogonal_of_isClosed_sup
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗))) :
    ((((((Cᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) ⊔
        ((Dᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗)) : Submodule ℝ 𝓗) : Set 𝓗)) =
      ((((C ⊓ D)ᗮ : ClosedSubmodule ℝ 𝓗) : Set 𝓗)) := by
  have horth_closed :
      IsClosed ((((((Cᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) ⊔
          ((Dᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗)) : Submodule ℝ 𝓗) : Set 𝓗)) := by
    -- Corollary 15.35 transports the closedness of `C + D` to the orthogonal sum.
    simpa using
      (isClosed_sup_iff_isClosed_orthogonal_sup_orthogonal
        (C : Submodule ℝ 𝓗) (D : Submodule ℝ 𝓗) C.isClosed D.isClosed).1 hCD_closed
  calc
    ((((((Cᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) ⊔
        ((Dᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗)) : Submodule ℝ 𝓗) : Set 𝓗)) =
        ((((Cᗮ : ClosedSubmodule ℝ 𝓗) ⊔ Dᗮ : ClosedSubmodule ℝ 𝓗) : Set 𝓗)) := by
          -- On a closed sum, the `ClosedSubmodule.sup` closure collapses back to the raw sum.
          rw [ClosedSubmodule.coe_sup]
          exact horth_closed.closure_eq.symm
    _ = ((((C ⊓ D)ᗮ : ClosedSubmodule ℝ 𝓗) : Set 𝓗)) := by
          -- The closed-submodule orthogonal formula is exactly the desired identification.
          simpa using
            congrArg (fun K : ClosedSubmodule ℝ 𝓗 ↦ (K : Set 𝓗))
              (ClosedSubmodule.sup_orthogonal C D)

/-- Helper for Proposition 25.37: under `IsClosed (C + D)`, the normal cones satisfy
`N[C] + N[D] = N[C ∩ D]`. -/
lemma normalConeAdd_eq_normalConeInf_of_isClosed_sup
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗))) :
    N[((C : Submodule ℝ 𝓗) : Set 𝓗)] + N[((D : Submodule ℝ 𝓗) : Set 𝓗)] =
      N[(((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)] := by
  classical
  ext x u
  change u ∈ (N[((C : Submodule ℝ 𝓗) : Set 𝓗)] x + N[((D : Submodule ℝ 𝓗) : Set 𝓗)] x) ↔
    u ∈ N[(((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)] x
  by_cases hxC : x ∈ (C : Set 𝓗) <;> by_cases hxD : x ∈ (D : Set 𝓗)
  · have hxCD : x ∈ ((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Set 𝓗) := ⟨hxC, hxD⟩
    rw [normalConeClosedSubmodule_eq_orthogonal_of_mem (V := C) hxC,
      normalConeClosedSubmodule_eq_orthogonal_of_mem (V := D) hxD,
      normalConeClosedSubmodule_eq_orthogonal_of_mem (V := C ⊓ D) hxCD]
    constructor
    · intro hu
      rcases Set.mem_add.mp hu with ⟨uC, huC, uD, huD, rfl⟩
      have huSup :
          uC + uD ∈ ((((((Cᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) ⊔
              ((Dᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗)) : Submodule ℝ 𝓗) : Set 𝓗)) := by
        exact Submodule.mem_sup.mpr ⟨uC, huC, uD, huD, rfl⟩
      rw [orthogonalSup_eq_infOrthogonal_of_isClosed_sup
        (C := C) (D := D) hCD_closed] at huSup
      exact huSup
    · intro hu
      have huSup :
          u ∈ ((((((Cᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) ⊔
              ((Dᗮ : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗)) : Submodule ℝ 𝓗) : Set 𝓗)) := by
        rw [orthogonalSup_eq_infOrthogonal_of_isClosed_sup
          (C := C) (D := D) hCD_closed]
        exact hu
      rcases Submodule.mem_sup.mp huSup with ⟨uC, huC, uD, huD, rfl⟩
      exact Set.mem_add.mpr ⟨uC, huC, uD, huD, rfl⟩
  · have hxCD : x ∉ ((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Set 𝓗) := by
      intro hx
      exact hxD hx.2
    -- If `x ∉ D`, both sides are empty because `N[D] x = ∅`.
    rw [normalConeClosedSubmodule_eq_orthogonal_of_mem (V := C) hxC,
      normalConeClosedSubmodule_eq_empty_of_not_mem (V := D) hxD,
      normalConeClosedSubmodule_eq_empty_of_not_mem (V := C ⊓ D) hxCD]
    simp
  · have hxCD : x ∉ ((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Set 𝓗) := by
      intro hx
      exact hxC hx.1
    -- If `x ∉ C`, both sides are empty because `N[C] x = ∅`.
    rw [normalConeClosedSubmodule_eq_empty_of_not_mem (V := C) hxC,
      normalConeClosedSubmodule_eq_orthogonal_of_mem (V := D) hxD,
      normalConeClosedSubmodule_eq_empty_of_not_mem (V := C ⊓ D) hxCD]
    simp
  · have hxCD : x ∉ ((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Set 𝓗) := by
      intro hx
      exact hxC hx.1
    -- Off both subspaces, every normal cone involved is empty.
    rw [normalConeClosedSubmodule_eq_empty_of_not_mem (V := C) hxC,
      normalConeClosedSubmodule_eq_empty_of_not_mem (V := D) hxD,
      normalConeClosedSubmodule_eq_empty_of_not_mem (V := C ⊓ D) hxCD]
    simp

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 25.37: addition of singleton-valued operators induced by linear maps
is the singleton-valued operator of the sum map. -/
lemma add_toSetValuedOperator_eq_toSetValuedOperator_add
    (A B : 𝓗 →L[ℝ] 𝓗) :
    A.toSetValuedOperator + B.toSetValuedOperator = (A + B).toSetValuedOperator := by
  ext x u
  constructor
  · intro hu
    rcases Set.mem_add.mp hu with ⟨a, ha, b, hb, rfl⟩
    have ha_eq : a = A x := by
      simpa [Function.toSetValuedOperator_apply] using ha
    have hb_eq : b = B x := by
      simpa [Function.toSetValuedOperator_apply] using hb
    subst a b
    simp [Function.toSetValuedOperator_apply, ContinuousLinearMap.add_apply]
  · intro hu
    have hu_eq : u = (A + B) x := by
      simpa [Function.toSetValuedOperator_apply] using hu
    refine Set.mem_add.mpr ⟨A x, ?_, B x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · simp [Function.toSetValuedOperator_apply]
    · simpa [ContinuousLinearMap.add_apply] using hu_eq.symm

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 25.37: the right-hand doubling in the parallel-sum formula can be
moved to the left linear factor by rescaling the inverse witness. -/
lemma comp_inverse_comp_rightDouble_eq_leftDouble
    (A B C : 𝓗 →L[ℝ] 𝓗) :
    (((A.toSetValuedOperator.comp (B.toSetValuedOperator)⁻¹).comp C.toSetValuedOperator).comp
        (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator)) =
      ((((2 : ℝ) • A).toSetValuedOperator.comp (B.toSetValuedOperator)⁻¹).comp
        C.toSetValuedOperator) := by
  ext x u
  constructor
  · intro hu
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨y, hy, hu⟩
    have hy_eq : y = (2 : ℝ) • x := by
      simpa [Function.toSetValuedOperator_apply] using hy
    subst y
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨v, hv, hu⟩
    have hv_eq : v = C ((2 : ℝ) • x) := by
      simpa [Function.toSetValuedOperator_apply] using hv
    subst v
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨z, hz, huA⟩
    have hz_eq : B z = C ((2 : ℝ) • x) := by
      rw [SetValuedOperator.mem_inverse_iff] at hz
      simpa [Function.toSetValuedOperator_apply, eq_comm] using hz
    have huA_eq : u = A z := by
      simpa [Function.toSetValuedOperator_apply] using huA
    rw [SetValuedOperator.mem_comp]
    refine ⟨C x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_comp]
      refine ⟨(1 / 2 : ℝ) • z, ?_, ?_⟩
      · rw [SetValuedOperator.mem_inverse_iff]
        have hz_half : B ((1 / 2 : ℝ) • z) = C x := by
          calc
            B ((1 / 2 : ℝ) • z) = (1 / 2 : ℝ) • B z := by simp
            _ = (1 / 2 : ℝ) • C ((2 : ℝ) • x) := by rw [hz_eq]
            _ = C x := by simp
        simpa [Function.toSetValuedOperator_apply, eq_comm] using hz_half
      · have hu_half : u = ((2 : ℝ) • A) ((1 / 2 : ℝ) • z) := by
          calc
            u = A z := huA_eq
            _ = ((2 : ℝ) • A) ((1 / 2 : ℝ) • z) := by simp
        simpa [Function.toSetValuedOperator_apply] using hu_half
  · intro hu
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨v, hv, hu⟩
    have hv_eq : v = C x := by
      simpa [Function.toSetValuedOperator_apply] using hv
    subst v
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨z, hz, huA⟩
    have hz_eq : B z = C x := by
      rw [SetValuedOperator.mem_inverse_iff] at hz
      simpa [Function.toSetValuedOperator_apply, eq_comm] using hz
    have huA_eq : u = ((2 : ℝ) • A) z := by
      simpa [Function.toSetValuedOperator_apply] using huA
    rw [SetValuedOperator.mem_comp]
    refine ⟨(2 : ℝ) • x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_comp]
      refine ⟨C ((2 : ℝ) • x), ?_, ?_⟩
      · simp [Function.toSetValuedOperator_apply]
      · rw [SetValuedOperator.mem_comp]
        refine ⟨(2 : ℝ) • z, ?_, ?_⟩
        · rw [SetValuedOperator.mem_inverse_iff]
          have hz_double : B ((2 : ℝ) • z) = C ((2 : ℝ) • x) := by
            calc
              B ((2 : ℝ) • z) = (2 : ℝ) • B z := by simp
              _ = (2 : ℝ) • C x := by rw [hz_eq]
              _ = C ((2 : ℝ) • x) := by simp
          simpa [Function.toSetValuedOperator_apply, eq_comm] using hz_double
        · have hu_double : u = A ((2 : ℝ) • z) := by
            calc
              u = ((2 : ℝ) • A) z := huA_eq
              _ = A ((2 : ℝ) • z) := by simp
          simpa [Function.toSetValuedOperator_apply] using hu_double

/-- Helper for Proposition 25.37: if `C` and `D` are closed linear subspaces and `C + D` is
closed, then
the orthogonal projection onto `C ∩ D`, viewed as a singleton-valued operator, is
`2 P_C (P_C + P_D)⁻¹ P_D`. -/
theorem inf_starProjection_toSetValuedOperator_eq_double_comp_inverse_comp
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗))) :
    (C ⊓ D).starProjection.toSetValuedOperator =
      (((2 : ℝ) • P_C).toSetValuedOperator.comp ((P_CD).toSetValuedOperator)⁻¹).comp
        (P_D).toSetValuedOperator := by
  have hCD_nonempty :
      ((((C : Submodule ℝ 𝓗) : Set 𝓗) ∩ ((D : Submodule ℝ 𝓗) : Set 𝓗))).Nonempty := by
    -- The intersection of two subspaces contains `0`.
    refine ⟨0, ?_⟩
    simp
  have hnormal :
      N[((C : Submodule ℝ 𝓗) : Set 𝓗)] + N[((D : Submodule ℝ 𝓗) : Set 𝓗)] =
        N[(((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)] :=
    normalConeAdd_eq_normalConeInf_of_isClosed_sup (C := C) (D := D) hCD_closed
  have hproj_inter :
      P[(((C : Submodule ℝ 𝓗) : Set 𝓗) ∩ ((D : Submodule ℝ 𝓗) : Set 𝓗))] =
        (P[((C : Submodule ℝ 𝓗) : Set 𝓗)] □ P[((D : Submodule ℝ 𝓗) : Set 𝓗)]).comp
          (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator) :=
    setValuedProjector_inter_eq_parallelSum_comp_double_of_normalCone_add_eq
      hCD_nonempty C.isClosed D.isClosed C.convex D.convex hnormal
  have hCproj :
      P[((C : Submodule ℝ 𝓗) : Set 𝓗)] = (C.starProjection : 𝓗 → 𝓗).toSetValuedOperator :=
    setValuedProjector_closedSubmodule_eq_starProjection (V := C)
  have hDproj :
      P[((D : Submodule ℝ 𝓗) : Set 𝓗)] = (D.starProjection : 𝓗 → 𝓗).toSetValuedOperator :=
    setValuedProjector_closedSubmodule_eq_starProjection (V := D)
  have hInfproj :
      P[(((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)] =
        (C ⊓ D).starProjection.toSetValuedOperator :=
    setValuedProjector_closedSubmodule_eq_starProjection (V := C ⊓ D)
  have hsingle : ((C.starProjection : 𝓗 → 𝓗).toSetValuedOperator).IsAtMostSingleValued := by
    -- Every singleton-valued operator is automatically at most single-valued.
    intro x
    rw [Function.toSetValuedOperator_apply]
    exact Set.subsingleton_singleton
  -- Route correction: the proof now isolates the normal-cone identity first, then rewrites
  -- Corollary 25.36 through the singleton-valued projector and linear-operator bridges.
  calc
    (C ⊓ D).starProjection.toSetValuedOperator =
        P[(((C ⊓ D : ClosedSubmodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)] := by
          exact hInfproj.symm
    _ =
        (P[((C : Submodule ℝ 𝓗) : Set 𝓗)] □ P[((D : Submodule ℝ 𝓗) : Set 𝓗)]).comp
          (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator) := by
            simpa [Set.inter_eq_left] using hproj_inter
    _ =
        (((P_C).toSetValuedOperator.comp
            (((P_C).toSetValuedOperator + (P_D).toSetValuedOperator)⁻¹)).comp
              (P_D).toSetValuedOperator).comp
            (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator) := by
              rw [hCproj, hDproj]
              exact congrArg
                (fun T : SetValuedOperator 𝓗 𝓗 ↦
                  T.comp (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator))
                (SetValuedOperator.parallelSum_eq_comp_inverse_add_comp_of_isAtMostSingleValued
                  (A := (C.starProjection : 𝓗 → 𝓗).toSetValuedOperator) (B := D.starProjection)
                  hsingle)
    _ =
        (((P_C).toSetValuedOperator.comp
            ((P_CD).toSetValuedOperator)⁻¹).comp
              (P_D).toSetValuedOperator).comp
            (((2 : ℝ) • (id : 𝓗 → 𝓗)).toSetValuedOperator) := by
              rw [add_toSetValuedOperator_eq_toSetValuedOperator_add]
    _ =
        ((((2 : ℝ) • P_C).toSetValuedOperator.comp
            ((P_CD).toSetValuedOperator)⁻¹).comp
              (P_D).toSetValuedOperator) := by
                simpa using
                  comp_inverse_comp_rightDouble_eq_leftDouble
                    (A := P_C) (B := P_C + P_D) (C := P_D)

/-- Helper for Proposition 25.37: once part (1) is available, every vector of `D` belongs to
`range (P_C + P_D)`. -/
lemma mem_range_starProjectionAddStarProjection_of_mem_right
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)))
    {y : 𝓗} (hy : y ∈ D) :
    y ∈ ((P_CD).range : Set 𝓗) := by
  have hsingleton :
      (C ⊓ D).starProjection y ∈ (C ⊓ D).starProjection.toSetValuedOperator y := by
    -- The left-hand side of part (1) is singleton-valued, so its value belongs to its own fiber.
    simp [Function.toSetValuedOperator_apply]
  rw [inf_starProjection_toSetValuedOperator_eq_double_comp_inverse_comp
    (C := C) (D := D) hCD_closed] at hsingleton
  -- Unfold the composed singleton-valued operator to expose the inverse-fiber witness.
  rw [SetValuedOperator.mem_comp] at hsingleton
  rcases hsingleton with ⟨v, hv, hw⟩
  have hv_eq : v = P_D y := by
    simpa using hv
  subst v
  rw [(D : Submodule ℝ 𝓗).starProjection_eq_self_iff.mpr hy] at hw
  rw [SetValuedOperator.mem_comp] at hw
  rcases hw with ⟨z, hz, _⟩
  rw [SetValuedOperator.mem_inverse_iff] at hz
  exact ⟨z, by simpa [eq_comm] using hz⟩

/-- Helper for Proposition 25.37: once part (1) is available, every vector of `C` belongs to
`range (P_C + P_D)`. -/
lemma mem_range_starProjectionAddStarProjection_of_mem_left
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)))
    {y : 𝓗} (hy : y ∈ C) :
    y ∈ ((P_CD).range : Set 𝓗) := by
  have hsingleton :
      (C ⊓ D).starProjection y ∈ (C ⊓ D).starProjection.toSetValuedOperator y := by
    -- The swapped copy of part (1) supplies the inverse-fiber witness for vectors in `C`.
    simp [Function.toSetValuedOperator_apply]
  have hDC_closed :
      IsClosed ((((D : Submodule ℝ 𝓗) ⊔ (C : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)) := by
    simpa [sup_comm] using hCD_closed
  have hswap :
      (C ⊓ D).starProjection.toSetValuedOperator =
        (((2 : ℝ) • D.starProjection).toSetValuedOperator.comp
            ((D.starProjection + C.starProjection).toSetValuedOperator)⁻¹).comp
          C.starProjection.toSetValuedOperator := by
    simpa [inf_comm, add_comm] using
      (inf_starProjection_toSetValuedOperator_eq_double_comp_inverse_comp
        (C := D) (D := C) hDC_closed)
  rw [hswap] at hsingleton
  rw [SetValuedOperator.mem_comp] at hsingleton
  rcases hsingleton with ⟨v, hv, hw⟩
  have hv_eq : v = P_C y := by
    simpa using hv
  subst v
  rw [(C : Submodule ℝ 𝓗).starProjection_eq_self_iff.mpr hy] at hw
  rw [SetValuedOperator.mem_comp] at hw
  rcases hw with ⟨z, hz, _⟩
  rw [SetValuedOperator.mem_inverse_iff] at hz
  exact ⟨z, by simpa [ContinuousLinearMap.add_apply, add_comm, eq_comm] using hz⟩

/-- Helper for Proposition 25.37: under `IsClosed (C + D)`, the range of `P_C + P_D` is exactly
the subspace sum `C ⊔ D`. -/
lemma starProjectionAddStarProjection_range_eq_sup_of_isClosed_sup
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗))) :
    ((P_CD).range : Set 𝓗) =
      ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    -- Every value of `P_C + P_D` is visibly a sum of one vector in `C` and one vector in `D`.
    exact Submodule.mem_sup.mpr ⟨
      P_C x,
      (C : Submodule ℝ 𝓗).starProjection_apply_mem x,
      P_D x,
      (D : Submodule ℝ 𝓗).starProjection_apply_mem x,
      by simp⟩
  · intro hy
    -- Part (1), used for `C` and for `D`, shows both summands already lie in the range.
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, v, hv, rfl⟩
    rcases mem_range_starProjectionAddStarProjection_of_mem_left
        (C := C) (D := D) hCD_closed hu with ⟨x, hx⟩
    rcases mem_range_starProjectionAddStarProjection_of_mem_right
        (C := C) (D := D) hCD_closed hv with ⟨w, hw⟩
    have hx' : P_CD x = u := hx
    have hw' : P_CD w = v := hw
    have hsum : P_CD x + P_CD w = u + v := congrArg₂ (· + ·) hx' hw'
    refine ⟨x + w, ?_⟩
    calc
      P_CD (x + w) = P_C x + P_C w + (P_D x + P_D w) := by
        simp [ContinuousLinearMap.add_apply, add_left_comm, add_comm]
      _ = u + v := by
        simpa [ContinuousLinearMap.add_apply, add_assoc, add_left_comm, add_comm] using hsum

/-- Bridge for Proposition 25.37: if `C + D` is closed, then the range of `P_C + P_D` is closed.
-/
theorem isClosed_range_starProjection_add_starProjection_of_isClosed_sup
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗))) :
    IsClosed (((P_CD).range : Set 𝓗)) := by
  -- The stronger range description reduces the closed-range claim to the hypothesis on `C + D`.
  rw [starProjectionAddStarProjection_range_eq_sup_of_isClosed_sup
    (C := C) (D := D) hCD_closed]
  exact hCD_closed

/-- Proposition 25.37 (2): if `C` and `D` are closed linear subspaces, `C + D` is closed, and
`ran (P_C + P_D)` is closed, then `P_(C ∩ D) = 2 P_C (P_C + P_D)† P_D`. -/
theorem inf_starProjection_eq_double_comp_moorePenroseInverseOperator_comp_of_isClosed_sup
    (hCD_closed :
      IsClosed ((((C : Submodule ℝ 𝓗) ⊔ (D : Submodule ℝ 𝓗) : Submodule ℝ 𝓗) : Set 𝓗)))
    (hP_closed : IsClosed (((P_CD).range : Set 𝓗)) :=
      isClosed_range_starProjection_add_starProjection_of_isClosed_sup C D hCD_closed) :
    (C ⊓ D).starProjection =
      (2 : ℝ) •
        ((P_C).comp (((P_CD)⁺[hP_closed]).comp P_D)) := by
  ext x
  let u := (P_CD)⁺[hP_closed] (P_D x)
  have hPdx_range : P_D x ∈ ((P_CD).range : Set 𝓗) := by
    -- The range description from the bridge theorem
    -- puts every value of `P_D` in `range (P_C + P_D)`.
    rw [starProjectionAddStarProjection_range_eq_sup_of_isClosed_sup
      (C := C) (D := D) hCD_closed]
    exact Submodule.mem_sup.mpr ⟨
      0,
      by simp,
      P_D x,
      (D : Submodule ℝ 𝓗).starProjection_apply_mem x,
      by simp⟩
  have hu_eq : P_CD u = P_D x := by
    -- On points already in the range, the Moore-Penrose inverse lands in a genuine inverse fiber.
    simpa [u, closedRangeProjection_eq_self_of_mem_range P_CD hP_closed hPdx_range] using
      apply_moorePenroseInverse_eq_rangeProjection P_CD hP_closed (P_D x)
  have hsingleton :
      (2 : ℝ) • P_C u ∈ (C ⊓ D).starProjection.toSetValuedOperator x := by
    -- Feed the Moore-Penrose preimage into part (1) as the inverse-fiber witness.
    rw [inf_starProjection_toSetValuedOperator_eq_double_comp_inverse_comp
      (C := C) (D := D) hCD_closed]
    rw [SetValuedOperator.mem_comp]
    refine ⟨P_D x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_comp]
      refine ⟨u, ?_, ?_⟩
      · simpa [SetValuedOperator.mem_inverse_iff, Function.toSetValuedOperator_apply, eq_comm]
          using hu_eq
      · simp [Function.toSetValuedOperator_apply]
  -- The left-hand side is singleton-valued, so membership identifies the pointwise value.
  simpa [Function.toSetValuedOperator_apply, u, eq_comm] using hsingleton

end
