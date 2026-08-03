import Mathlib
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Definition_3_49
import BauschkeLean.Chap03.Proposition_3_39
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap03.Theorem_3_34
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap17.Proposition_17_17
import BauschkeLean.Chap17.Theorem_17_18
import BauschkeLean.Chap18.Proposition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section PointwiseSupremum

variable {H : Type u} {ι : Type v} [Nonempty ι]

-- Proof sketch: choose any index from `ι`; its value is one of the terms in the `iSup`, and each
-- family value lies strictly above `⊥` because the codomain is `Set.Ioi (⊥ : EReal)`.
/-- The pointwise supremum of a nonempty family of `]-∞,+∞]`-valued functions is still strictly
above `-∞`. -/
private theorem bot_lt_iSup_family_apply
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    (⊥ : EReal) < ⨆ i, (f i x : EReal) := by
  let ⟨i₀⟩ := ‹Nonempty ι›
  -- Any family value is one term of the supremum, so its strict lower bound by `⊥` propagates.
  exact lt_of_lt_of_le (f i₀ x).2 (le_iSup (fun i ↦ (f i x : EReal)) i₀)

/-- The pointwise supremum of a nonempty family of `]-∞,+∞]`-valued functions. -/
def pointwiseSup (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) : Set.Ioi (⊥ : EReal) :=
  ⟨⨆ i, (f i x : EReal), bot_lt_iSup_family_apply f x⟩

-- Proof sketch: unfold `pointwiseSup`; the subtype coercion forgets only the proof that the
-- supremum stays in `]-∞,+∞]`.
/-- Coercing `pointwiseSup f` to `EReal` recovers the defining indexed supremum. -/
@[simp] theorem pointwiseSup_apply
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    (pointwiseSup f x : EReal) = ⨆ i, (f i x : EReal) :=
  rfl

/-- Helper for Theorem 18 5: each family value is bounded above by the pointwise supremum. -/
private theorem family_apply_le_pointwiseSup
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) (i : ι) :
    (f i x : EReal) ≤ (pointwiseSup f x : EReal) := by
  -- Rewrite the supremum owner and use the canonical `le_iSup` bound.
  simpa [pointwiseSup_apply] using le_iSup (fun j ↦ (f j x : EReal)) i

/-- The active indices at `x` are those where the family value reaches the pointwise supremum. -/
def activeIndices (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) : Set ι :=
  {i | (f i x : EReal) = (pointwiseSup f x : EReal)}

-- Proof sketch: unfold `activeIndices`.
/-- An index is active exactly when its value at `x` equals the pointwise supremum. -/
@[simp] theorem mem_activeIndices_iff
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) (i : ι) :
    i ∈ activeIndices f x ↔ (f i x : EReal) = (pointwiseSup f x : EReal) :=
  Iff.rfl

end PointwiseSupremum

section PointwiseSupremumSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type v} [Finite ι] [Nonempty ι]

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the support function is the supremum over the subtype indexing the
underlying set. -/
private theorem supportFunction_eq_iSup_subtype
    (C : Set H) :
    σ[C] = fun u : H ↦ ⨆ x : C, ((⟪(x : H), u⟫_ℝ : ℝ) : EReal) := by
  -- Replace the image over `C` by the range of the same functional on the subtype.
  funext u
  rw [supportFunction_eq_sSup_image]
  have himage :
      (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' C =
        Set.range (fun x : C ↦ ((⟪(x : H), u⟫_ℝ : ℝ) : EReal)) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [himage, sSup_range]

-- Route correction: `Theorem_17_18` already imports Chapter 7's `σ[C]` notation from
-- `Definition_7_8`, so importing `Proposition_7_11` here reintroduces the same notation owner and
-- breaks elaboration. Rebuild only the small support-halfspace API needed for Theorem 18 5.

/-- Helper for Theorem 18 5: the support halfspace of `C` in direction `u` is cut out by the
support-function bound `⟪x, u⟫ ≤ σ[C] u`. -/
private def supportFunctionHalfspace (C : Set H) (u : H) : Set H :=
  {x : H | (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u}

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: membership in the support halfspace is exactly the defining support
inequality. -/
private theorem mem_supportFunctionHalfspace_iff (C : Set H) (u x : H) :
    x ∈ supportFunctionHalfspace C u ↔ (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
  -- Unfold the local support-halfspace owner.
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the support function coincides with Chapter 3's `innerSupremumOn`.
-/
private theorem supportFunction_eq_innerSupremumOn (C : Set H) (u : H) :
    σ[C] u = innerSupremumOn C u := by
  -- After importing `Definition_7_8`, the notation `σ[C]` is already `innerSupremumOn C`.
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: every point of `C` lies in each support halfspace of `C`. -/
private theorem supportFunctionHalfspace_contains_set (C : Set H) (u : H) :
    C ⊆ supportFunctionHalfspace C u := by
  intro x hx
  -- Each image value lies below the supremum defining the support function.
  rw [mem_supportFunctionHalfspace_iff, supportFunction_eq_sSup_image]
  exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: nonempty sets have support values strictly above `⊥`. -/
private theorem supportFunction_ne_bot_of_nonempty {C : Set H} (hC_nonempty : C.Nonempty) (u : H) :
    σ[C] u ≠ ⊥ := by
  rcases hC_nonempty with ⟨x, hx⟩
  intro hσ_bot
  have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
    -- One realized value gives a lower bound on the support supremum.
    rw [supportFunction_eq_sSup_image]
    exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
  exact not_le_of_gt (EReal.bot_lt_coe _) (hσ_bot ▸ hx_le)

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: for finite support value, the support halfspace is the usual real
closed halfspace. -/
private theorem supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top {C : Set H}
    (hC_nonempty : C.Nonempty) {u : H} (hσ_top : σ[C] u ≠ ⊤) :
    supportFunctionHalfspace C u = {x : H | ⟪x, u⟫_ℝ ≤ (σ[C] u).toReal} := by
  have hσ_bot : σ[C] u ≠ ⊥ := supportFunction_ne_bot_of_nonempty hC_nonempty u
  ext x
  constructor
  · intro hx
    -- Replace the finite `EReal` threshold by its real representative.
    rw [mem_supportFunctionHalfspace_iff] at hx
    have hx' : (⟪x, u⟫_ℝ : EReal) ≤ ((σ[C] u).toReal : EReal) := by
      simpa [EReal.coe_toReal hσ_top hσ_bot] using hx
    exact_mod_cast hx'
  · intro hx
    -- Cast the real inequality back to the original `EReal` support threshold.
    have hx' : (⟪x, u⟫_ℝ : EReal) ≤ ((σ[C] u).toReal : EReal) := by
      exact_mod_cast hx
    rw [mem_supportFunctionHalfspace_iff]
    simpa [EReal.coe_toReal hσ_top hσ_bot] using hx'

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: support halfspaces of a nonempty set are closed. -/
private theorem supportFunctionHalfspace_isClosed_of_nonempty {C : Set H}
    (hC_nonempty : C.Nonempty) (u : H) :
    IsClosed (supportFunctionHalfspace C u) := by
  by_cases hσ_top : σ[C] u = ⊤
  · -- If the support value is `⊤`, the defining inequality is automatic.
    have hset : supportFunctionHalfspace C u = Set.univ := by
      ext x
      simp [supportFunctionHalfspace, hσ_top]
    rw [hset]
    exact isClosed_univ
  · -- Otherwise rewrite to a standard closed real halfspace.
    rw [supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top hC_nonempty hσ_top]
    have hcont : Continuous (fun x : H ↦ ⟪x, u⟫_ℝ) := continuous_id.inner continuous_const
    simpa using isClosed_le hcont continuous_const

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: support halfspaces of a nonempty set are convex. -/
private theorem supportFunctionHalfspace_isConvex_of_nonempty {C : Set H}
    (hC_nonempty : C.Nonempty) (u : H) :
    Convex ℝ (supportFunctionHalfspace C u) := by
  by_cases hσ_top : σ[C] u = ⊤
  · -- If the support value is `⊤`, the support halfspace is all of `H`.
    have hset : supportFunctionHalfspace C u = Set.univ := by
      ext x
      simp [supportFunctionHalfspace, hσ_top]
    rw [hset]
    exact convex_univ
  · -- Otherwise rewrite to the standard convex halfspace of a linear functional.
    rw [supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top hC_nonempty hσ_top]
    have hlinear : IsLinearMap ℝ (fun x : H ↦ ⟪x, u⟫_ℝ) := by
      refine ⟨?_, ?_⟩
      · intro x y
        rw [inner_add_left]
      · intro a x
        simpa using inner_smul_real_left x u a
    simpa using convex_halfSpace_le hlinear (σ[C] u).toReal

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the support function is monotone under set inclusion. -/
private theorem supportFunction_mono {C D : Set H} (hCD : C ⊆ D) (u : H) :
    σ[C] u ≤ σ[D] u := by
  -- Every value attained on `C` also appears in the image over `D`.
  rw [supportFunction_eq_sSup_image, supportFunction_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (isLUB_sSup _).1 ⟨x, hCD hx, rfl⟩

/-- Helper for Theorem 18 5: the projection variational inequality bounds support values on a
closed convex set by the projection value. -/
private theorem projectionPoint_support_upper_bound {S : Set H}
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x y : H} (hy : y ∈ S) :
    ⟪y, x - projectionPoint S
      (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x⟫_ℝ ≤
      ⟪projectionPoint S
          (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x,
        x - projectionPoint S
          (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x⟫_ℝ := by
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)
  have hprojection :
      p x ∈ S ∧ ∀ z ∈ S, ⟪z - p x, x - p x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hS_nonempty hS_closed hS_convex).mp rfl
  have hy_nonpos : ⟪y - p x, x - p x⟫_ℝ ≤ 0 := hprojection.2 y hy
  have hrewrite :
      ⟪y - p x, x - p x⟫_ℝ = ⟪y, x - p x⟫_ℝ - ⟪p x, x - p x⟫_ℝ := by
    rw [inner_sub_left]
  rw [hrewrite] at hy_nonpos
  linarith

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: a pointwise upper bound on `⟪y, u⟫` bounds the support value over the
whole set. -/
private theorem innerSupremumOn_le_of_forall_inner_le {S : Set H} {u : H} {a : ℝ}
    (hbound : ∀ y ∈ S, ⟪y, u⟫_ℝ ≤ a) :
    innerSupremumOn S u ≤ (a : EReal) := by
  -- Rewrite the support value as a supremum and show that `a` is an upper bound.
  rw [innerSupremumOn_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact show ((⟪y, u⟫_ℝ : EReal) ≤ (a : EReal)) by exact_mod_cast hbound y hy

/-- Helper for Theorem 18 5: a point outside a closed convex set differs from its projection. -/
private theorem projectionPoint_residual_ne_zero {S : Set H}
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x : H} (hx : x ∉ S) :
    x - projectionPoint S
      (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x ≠ 0 := by
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)
  intro hu_zero
  have hp_mem : p x ∈ S := by
    exact projectionPoint_mem S
      (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  have hx_eq : x = p x := sub_eq_zero.mp hu_zero
  exact hx (hx_eq.symm ▸ hp_mem)

/-- Helper for Theorem 18 5: the projection residual creates a strict inner-product gap from the
projection point to the original point. -/
private theorem projectionPoint_support_strict_gap {S : Set H}
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x : H} (hx : x ∉ S) :
    let p :=
      projectionPoint S
        (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)
    ⟪p x, x - p x⟫_ℝ < ⟪x, x - p x⟫_ℝ := by
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)
  have hu_ne : x - p x ≠ 0 :=
    projectionPoint_residual_ne_zero hS_nonempty hS_closed hS_convex hx
  have hnorm_sq_pos : 0 < ‖x - p x‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu_ne) 2
  have hlt :
      ⟪p x, x - p x⟫_ℝ < ⟪p x, x - p x⟫_ℝ + ‖x - p x‖ ^ 2 := by
    linarith
  calc
    ⟪p x, x - p x⟫_ℝ < ⟪p x, x - p x⟫_ℝ + ‖x - p x‖ ^ 2 := hlt
    _ = ⟪x, x - p x⟫_ℝ := by
      calc
        ⟪p x, x - p x⟫_ℝ + ‖x - p x‖ ^ 2
            = ⟪p x, x - p x⟫_ℝ + ⟪x - p x, x - p x⟫_ℝ := by
                rw [real_inner_self_eq_norm_sq]
        _ = ⟪p x + (x - p x), x - p x⟫_ℝ := by
              rw [inner_add_left]
        _ = ⟪x, x - p x⟫_ℝ := by
              congr 1
              abel_nf

/-- Helper for Theorem 18 5: a point outside a nonempty closed convex set admits a separating
direction whose support value is strictly smaller than its inner product at that point. -/
private theorem exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
    {S : Set H} (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x : H} (hx : x ∉ S) :
    ∃ u : H, u ≠ 0 ∧ innerSupremumOn S u < (⟪x, u⟫_ℝ : EReal) := by
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  let u := x - p
  have hu_ne : u ≠ 0 := by
    simpa [u, p] using projectionPoint_residual_ne_zero hS_nonempty hS_closed hS_convex hx
  refine ⟨u, hu_ne, ?_⟩
  have hsup_le : innerSupremumOn S u ≤ (⟪p, u⟫_ℝ : EReal) := by
    -- The projection inequality bounds every support value by the projection value.
    refine innerSupremumOn_le_of_forall_inner_le (S := S) fun y hy ↦ ?_
    simpa [u, p] using projectionPoint_support_upper_bound hS_nonempty hS_closed hS_convex hy
  have hgap : ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ := by
    -- The residual contributes the positive term `‖x - p‖²`.
    simpa [u, p] using projectionPoint_support_strict_gap hS_nonempty hS_closed hS_convex hx
  exact lt_of_le_of_lt hsup_le (by exact_mod_cast hgap)

/-- Helper for Theorem 18 5: the closed convex hull is the intersection of the support halfspaces
cut out by the support function. -/
private theorem closure_convexHull_eq_iInter_supportFunctionHalfspace (C : Set H) :
    closure (convexHull ℝ C) = ⋂ u : H, supportFunctionHalfspace C u := by
  by_cases hC_empty : C = ∅
  · -- In the empty case, the support value is `⊥`, so every support halfspace is empty.
    subst hC_empty
    ext x
    simp [supportFunctionHalfspace, supportFunction_eq_sSup_image]
  · let S : Set H := closedConvexHull ℝ C
    have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    have hS_nonempty : S.Nonempty := hC_nonempty.mono (by
      intro x hx
      exact subset_closedConvexHull hx)
    have hS_closed : IsClosed S := by
      -- `closedConvexHull` is closed by construction.
      simpa [S] using isClosed_closedConvexHull (𝕜 := ℝ) (s := C)
    have hS_convex : Convex ℝ S := by
      -- `closedConvexHull` is convex by construction.
      simpa [S] using convex_closedConvexHull (𝕜 := ℝ) (s := C)
    rw [← closedConvexHull_eq_closure_convexHull]
    apply Set.Subset.antisymm
    · intro x hxS
      rw [Set.mem_iInter]
      intro u
      -- Minimality of the closed convex hull yields the easy inclusion into each support halfspace.
      have hSu : S ⊆ supportFunctionHalfspace C u := by
        refine closedConvexHull_min ?_ ?_ ?_
        · exact supportFunctionHalfspace_contains_set C u
        · exact supportFunctionHalfspace_isConvex_of_nonempty hC_nonempty u
        · exact supportFunctionHalfspace_isClosed_of_nonempty hC_nonempty u
      exact hSu hxS
    · intro x hxInter
      by_contra hxS
      -- Strong separation of `x` from the closed convex hull gives a violating direction.
      rcases exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
          (S := S) hS_nonempty hS_closed hS_convex hxS with ⟨u, _, hsep⟩
      have hx_half : x ∈ supportFunctionHalfspace C u := Set.mem_iInter.mp hxInter u
      have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
        exact (mem_supportFunctionHalfspace_iff C u x).mp hx_half
      have hmono : σ[C] u ≤ σ[S] u := by
        refine supportFunction_mono ?_ u
        intro y hy
        exact subset_closedConvexHull hy
      have hsep' : σ[S] u < (⟪x, u⟫_ℝ : EReal) := by
        -- Translate the Chapter 3 separation inequality to the local support notation.
        rw [supportFunction_eq_innerSupremumOn]
        exact hsep
      exact (not_lt_of_ge (le_trans hx_le hmono)) hsep'

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 5: the active set is nonempty because a finite nonempty family attains
its pointwise supremum. -/
private theorem activeIndices_nonempty
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    (activeIndices f x).Nonempty := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- A finite nonempty family attains its supremum at some index.
  obtain ⟨i, hi⟩ : ∃ i, (f i x : EReal) = ⨆ j, (f j x : EReal) :=
    exists_eq_ciSup_of_finite
  refine ⟨i, ?_⟩
  -- Rewrite the attained supremum in the source-facing active-index form.
  simpa [activeIndices, pointwiseSup_apply] using hi

omit [InnerProductSpace ℝ H] [CompleteSpace H] [Finite ι] in
/-- Helper for Theorem 18 5: an inactive summand stays strictly below a fixed active summand on a
small ball around the base point. -/
private theorem inactive_lt_active_nearby
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x : H}
    (hxcont : ∀ i, x ∈ cont (f i))
    {i i₀ : ι} (hi : i ∉ activeIndices f x) (hi₀ : i₀ ∈ activeIndices f x) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.ball x ρ, (f i z : EReal) < (f i₀ z : EReal) := by
  rcases (mem_cont_iff (f i) x).1 (hxcont i) with ⟨ρi, hρi, hballi, hconti⟩
  rcases (mem_cont_iff (f i₀) x).1 (hxcont i₀) with ⟨ρ₀, hρ₀, hball₀, hcont₀⟩
  have hxi : x ∈ effectiveDomain (f i) := mem_effectiveDomain_of_mem_cont (hxcont i)
  have hxi₀ : x ∈ effectiveDomain (f i₀) := mem_effectiveDomain_of_mem_cont (hxcont i₀)
  have hleSup : (f i x : EReal) ≤ (pointwiseSup f x : EReal) := by
    exact family_apply_le_pointwiseSup f x i
  have hneSup : (f i x : EReal) ≠ (pointwiseSup f x : EReal) := by
    simpa [activeIndices] using hi
  have hltSup : (f i x : EReal) < (pointwiseSup f x : EReal) :=
    lt_of_le_of_ne hleSup hneSup
  have hi₀_eq : (f i₀ x : EReal) = (pointwiseSup f x : EReal) := by
    simpa [activeIndices] using hi₀
  have hlt : (f i x : EReal) < (f i₀ x : EReal) := by
    simpa [hi₀_eq] using hltSup
  have hfi_top : (f i x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxi)
  have hfi₀_top : (f i₀ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxi₀)
  have hfi_bot : (f i x : EReal) ≠ ⊥ := by
    exact ne_of_gt (f i x).2
  have hfi₀_bot : (f i₀ x : EReal) ≠ ⊥ := by
    exact ne_of_gt (f i₀ x).2
  have hltReal : (f i x : EReal).toReal < (f i₀ x : EReal).toReal := by
    have hltCoe :
        (((f i x : EReal).toReal : ℝ) : EReal) <
          (((f i₀ x : EReal).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hfi_top hfi_bot, EReal.coe_toReal hfi₀_top hfi₀_bot] using hlt
    exact EReal.coe_lt_coe_iff.mp hltCoe
  let g : H → ℝ := fun z ↦ (f i₀ z : EReal).toReal - (f i z : EReal).toReal
  have hgcont : ContinuousAt g x := by
    exact hcont₀.sub hconti
  rw [Metric.continuousAt_iff] at hgcont
  have hgx_pos : 0 < g x := by
    dsimp [g]
    linarith
  obtain ⟨ρ, hρ, hρprop⟩ := hgcont (g x) hgx_pos
  let ρ' : ℝ := min ρ (min ρi ρ₀)
  have hρ' : 0 < ρ' := by
    dsimp [ρ']
    exact lt_min hρ (lt_min hρi hρ₀)
  refine ⟨ρ', hρ', ?_⟩
  intro z hz
  have hzdist : dist z x < ρ' := by
    simpa [Metric.mem_ball] using hz
  have hzρ : dist z x < ρ := lt_of_lt_of_le hzdist (min_le_left _ _)
  have hzρi : dist z x < ρi := by
    exact lt_of_lt_of_le hzdist ((min_le_right ρ (min ρi ρ₀)).trans (min_le_left _ _))
  have hzρ₀ : dist z x < ρ₀ := by
    exact lt_of_lt_of_le hzdist ((min_le_right ρ (min ρi ρ₀)).trans (min_le_right _ _))
  have hzi : z ∈ effectiveDomain (f i) := by
    exact hballi (by simpa [Metric.mem_ball] using hzρi)
  have hzi₀ : z ∈ effectiveDomain (f i₀) := by
    exact hball₀ (by simpa [Metric.mem_ball] using hzρ₀)
  have hdist0 : dist (g z) (g x) < g x := hρprop hzρ
  have hdist : |g z - g x| < g x := by
    simpa [Real.dist_eq] using hdist0
  have hgpos : 0 < g z := by
    rcases abs_lt.mp hdist with ⟨hleft, _⟩
    dsimp [g] at hleft ⊢
    linarith
  have hltReal_z : (f i z : EReal).toReal < (f i₀ z : EReal).toReal := by
    dsimp [g] at hgpos
    linarith
  have hfiz_top : (f i z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzi)
  have hfi₀z_top : (f i₀ z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzi₀)
  have hfiz_bot : (f i z : EReal) ≠ ⊥ := by
    exact ne_of_gt (f i z).2
  have hfi₀z_bot : (f i₀ z : EReal) ≠ ⊥ := by
    exact ne_of_gt (f i₀ z).2
  have hltCoe_z :
      (((f i z : EReal).toReal : ℝ) : EReal) <
        (((f i₀ z : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hltReal_z
  simpa [EReal.coe_toReal hfiz_top hfiz_bot, EReal.coe_toReal hfi₀z_top hfi₀z_bot] using hltCoe_z

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 5: one active summand strictly dominates every inactive summand on a
small ball around the base point. -/
private theorem exists_active_index_dominating_inactive_nearby
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x : H}
    (hxcont : ∀ i, x ∈ cont (f i)) :
    ∃ i₀ : ι, i₀ ∈ activeIndices f x ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ z ∈ Metric.ball x ρ, ∀ i, i ∉ activeIndices f x →
          (f i z : EReal) < (f i₀ z : EReal) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rcases activeIndices_nonempty f x with ⟨i₀, hi₀⟩
  let radius : ι → ℝ := fun i ↦
    if hi : (f i x : EReal) = (pointwiseSup f x : EReal) then
      1
    else
      Classical.choose (inactive_lt_active_nearby (f := f) (x := x) hxcont hi hi₀)
  let ρ : ℝ := (Finset.univ.inf' Finset.univ_nonempty radius)
  have hradius_pos : ∀ i, 0 < radius i := by
    intro i
    by_cases hiEq : (f i x : EReal) = (pointwiseSup f x : EReal)
    · have hiEq' : (f i x : EReal) = ⨆ j, (f j x : EReal) := by
        simpa [pointwiseSup_apply] using hiEq
      simp [radius, hiEq']
    · have hiEq' : (f i x : EReal) ≠ ⨆ j, (f j x : EReal) := by
        simpa [pointwiseSup_apply] using hiEq
      simpa [radius, hiEq'] using
        (Classical.choose_spec
          (inactive_lt_active_nearby (f := f) (x := x) hxcont hiEq hi₀)).1
  have hρ : 0 < ρ := by
    have : (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty radius := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hradius_pos i
    simpa [ρ] using this
  refine ⟨i₀, hi₀, ρ, hρ, ?_⟩
  intro z hz i hi
  have hρle : ρ ≤ radius i := by
    dsimp [ρ]
    exact Finset.inf'_le (s := Finset.univ) (f := radius) (Finset.mem_univ i)
  have hzRadius : z ∈ Metric.ball x (radius i) := by
    rw [Metric.mem_ball] at hz ⊢
    exact lt_of_lt_of_le hz hρle
  by_cases hiEq : (f i x : EReal) = (pointwiseSup f x : EReal)
  · exact False.elim (hi (by simpa [activeIndices] using hiEq))
  · have hiEq' : (f i x : EReal) ≠ ⨆ j, (f j x : EReal) := by
      simpa [pointwiseSup_apply] using hiEq
    exact (Classical.choose_spec
      (inactive_lt_active_nearby (f := f) (x := x) hxcont hiEq hi₀)).2 z <|
        by simpa [radius, hiEq'] using hzRadius

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 5: near the base point, the pointwise supremum is already the supremum
over the active summands at `x`. -/
private theorem pointwiseSup_eq_iSup_active_nearby
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x : H}
    (hxcont : ∀ i, x ∈ cont (f i)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.ball x ρ,
        (pointwiseSup f z : EReal) = ⨆ i : activeIndices f x, (f i.1 z : EReal) := by
  rcases exists_active_index_dominating_inactive_nearby (f := f) (x := x) hxcont with
    ⟨i₀, hi₀, ρ, hρ, hdom⟩
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  apply le_antisymm
  · -- Every inactive summand is dominated by the chosen active one, while active summands remain.
    refine iSup_le fun i ↦ ?_
    by_cases hi : i ∈ activeIndices f x
    · exact le_iSup (fun j : activeIndices f x ↦ (f j.1 z : EReal)) ⟨i, hi⟩
    · exact (hdom z hz i hi).le.trans <|
        le_iSup (fun j : activeIndices f x ↦ (f j.1 z : EReal)) ⟨i₀, hi₀⟩
  · -- The active-family supremum is a subfamily of the full supremum.
    refine iSup_le fun i ↦ ?_
    exact le_iSup (fun j ↦ (f j z : EReal)) i.1

omit [Finite ι] [CompleteSpace H] in
/-- Helper for Theorem 18 5: the support function of the active-index union is the pointwise
supremum of the active support functions. -/
private theorem supportFunction_activeSubdifferentials_eq_iSup
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x y : H) :
    σ[⋃ i ∈ activeIndices f x, (∂ f i) x] y =
      ⨆ i : activeIndices f x, σ[(∂ f i.1) x] y := by
  -- Rewrite the support function on the union through a subtype-indexed supremum.
  rw [supportFunction_eq_iSup_subtype]
  apply le_antisymm
  · -- Any point in the active union comes from one active index and one subgradient in that fiber.
    refine iSup_le fun u ↦ ?_
    rcases Set.mem_iUnion.mp u.2 with ⟨i, hu⟩
    rcases Set.mem_iUnion.mp hu with ⟨hi, hu⟩
    refine le_iSup_of_le ⟨i, hi⟩ ?_
    rw [supportFunction_eq_iSup_subtype]
    exact le_iSup_of_le ⟨(u : H), hu⟩ le_rfl
  · -- Each active-fiber support term is already a term of the support function on the union.
    refine iSup_le fun i ↦ ?_
    rw [supportFunction_eq_iSup_subtype]
    refine iSup_le fun u ↦ ?_
    have huUnion : (u : H) ∈ ⋃ j ∈ activeIndices f x, (∂ f j) x := by
      exact Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2 ⟨i.2, u.2⟩⟩
    exact le_iSup_of_le ⟨(u : H), huUnion⟩ le_rfl

/-- Helper for Theorem 18 5: the convex hull of the active subdifferential union is already
closed, so its closed convex hull agrees with its convex hull. -/
private theorem closedConvexHull_activeSubdifferentials_eq_convexHull
    (f : ι → H → Set.Ioi (⊥ : EReal)) (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)))
    {x : H} (hxcont : ∀ i, x ∈ cont (f i)) :
    closedConvexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x) =
      convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x) := by
  let C : activeIndices f x → Set H := fun i ↦ (∂ f i.1) x
  have hcompactWeak :
      IsCompact ((toWeakSpace ℝ H) '' convexHull ℝ (⋃ i : activeIndices f x, C i)) := by
    -- Each active subdifferential fiber is weakly compact at the common continuity point `x`.
    have hweak : ∀ i : activeIndices f x, IsCompact ((toWeakSpace ℝ H) '' C i) := by
      intro i
      exact
        (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
          (f i.1) (hconv i.1) (ContinuousAtOnEffectiveDomain.of_mem_cont (hxcont i.1))).2
    have hconvC : ∀ i : activeIndices f x, Convex ℝ (C i) := by
      intro i
      exact convex_subdifferential (f i.1) x
    simpa [C] using weaklyCompact_convexHull_iUnion_fin C hconvC hweak
  have hclosedHull :
      IsClosed (convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x)) := by
    have hconvHull :
        Convex ℝ (convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x)) :=
      convex_convexHull _ _
    refine (isClosed_iff_weak_image_isClosed_of_convex hconvHull).2 ?_
    simpa [C] using hcompactWeak.isClosed
  -- Once the convex hull is closed, the closed convex hull is just its closure.
  rw [closedConvexHull_eq_closure_convexHull]
  exact hclosedHull.closure_eq

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Finite ι] in
/-- Helper for Theorem 18 5: an effective-domain point of the pointwise supremum is an
effective-domain point of every summand. -/
private theorem mem_effectiveDomain_of_mem_effectiveDomain_pointwiseSup
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x : H}
    (hx : x ∈ effectiveDomain (pointwiseSup f)) (i : ι) :
    x ∈ effectiveDomain (f i) := by
  -- Each summand lies below the supremum, so finiteness of the supremum forces finiteness below.
  rw [mem_effectiveDomain_iff] at hx ⊢
  exact lt_of_le_of_lt (family_apply_le_pointwiseSup f x i) (by simpa using hx)

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the finite pointwise supremum of convex functions is convex on its
effective domain whenever the family has a common continuity point. -/
private theorem convexOn_pointwiseSup_effectiveDomain
    (f : ι → H → Set.Ioi (⊥ : EReal))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i))) {x : H}
    (hxcont : ∀ i, x ∈ cont (f i)) :
    ConvexOn (pointwiseSup f) (effectiveDomain (pointwiseSup f)) := by
  -- Route correction: the old helper statement omitted a common finite point, but the effective
  -- domain of a finite pointwise supremum can be empty. The theorem hypotheses provide `x`.
  have hxSup : x ∈ effectiveDomain (pointwiseSup f) := by
    rcases activeIndices_nonempty f x with ⟨i, hi⟩
    have hxi : x ∈ effectiveDomain (f i) := mem_effectiveDomain_of_mem_cont (hxcont i)
    have hfi_lt : (f i x : EReal) < ⊤ := mem_effectiveDomain_iff.mp hxi
    have hi_eq : (f i x : EReal) = (pointwiseSup f x : EReal) := by
      simpa [activeIndices] using hi
    simpa [mem_effectiveDomain_iff, hi_eq] using hfi_lt
  refine ⟨⟨x, hxSup⟩, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  have hpointwise :
      (⨆ i, (f i (α • x + (1 - α) • y) : EReal)) ≤
        ⨆ i, (α : EReal) * (f i x : EReal) + (1 - α : EReal) * (f i y : EReal) := by
    refine iSup_le fun i ↦ ?_
    have hxi : x ∈ effectiveDomain (f i) :=
      mem_effectiveDomain_of_mem_effectiveDomain_pointwiseSup (f := f) hx i
    have hyi : y ∈ effectiveDomain (f i) :=
      mem_effectiveDomain_of_mem_effectiveDomain_pointwiseSup (f := f) hy i
    exact ((hconv i).2.2 hxi hyi hα0 hα1).trans <|
      le_iSup (fun j ↦ (α : EReal) * (f j x : EReal) + (1 - α : EReal) * (f j y : EReal)) i
  have hone_sub : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  -- Reassemble the familywise Jensen bounds by the weighted-supremum estimate.
  calc
    (pointwiseSup f (α • x + (1 - α) • y) : EReal)
        = ⨆ i, (f i (α • x + (1 - α) • y) : EReal) := by
          rw [pointwiseSup_apply]
    _ ≤ ⨆ i, (α : EReal) * (f i x : EReal) + (1 - α : EReal) * (f i y : EReal) := hpointwise
    _ ≤ (α : EReal) * (pointwiseSup f x : EReal) +
          (1 - α : EReal) * (pointwiseSup f y : EReal) := by
          simpa [pointwiseSup_apply] using
            weighted_iSup_le_weighted_iSup (u := fun i ↦ (f i x : EReal))
              (v := fun i ↦ (f i y : EReal)) hα0.le hone_sub

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 5: the finite active maximum model near `x` gives a source continuity
point for the pointwise supremum. -/
private theorem mem_cont_pointwiseSup_of_mem_cont
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x : H}
    (hxcont : ∀ i, x ∈ cont (f i)) :
    x ∈ cont (pointwiseSup f) := by
  classical
  let _ : Fintype (activeIndices f x) := Fintype.ofFinite (activeIndices f x)
  rcases activeIndices_nonempty f x with ⟨i₀, hi₀⟩
  let i₀' : activeIndices f x := ⟨i₀, hi₀⟩
  let _ : Nonempty (activeIndices f x) := ⟨i₀'⟩
  rcases pointwiseSup_eq_iSup_active_nearby (f := f) (x := x) hxcont with
    ⟨ρsup, hρsup, hsup⟩
  let activeRadius : activeIndices f x → ℝ := fun i ↦
    Classical.choose ((mem_cont_iff (f i.1) x).1 (hxcont i.1))
  let ρ : ℝ := min ρsup (Finset.univ.inf' Finset.univ_nonempty activeRadius)
  have hρ : 0 < ρ := by
    refine lt_min hρsup ?_
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact (Classical.choose_spec ((mem_cont_iff (f i.1) x).1 (hxcont i.1))).1
  have hballSup : Metric.ball x ρ ⊆ effectiveDomain (pointwiseSup f) := by
    intro z hz
    have hzsup : z ∈ Metric.ball x ρsup := by
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hzEq := hsup z hzsup
    obtain ⟨j, hj⟩ :
        ∃ j : activeIndices f x, (f j.1 z : EReal) = ⨆ i : activeIndices f x, (f i.1 z : EReal) :=
      exists_eq_ciSup_of_finite
    have hρle : ρ ≤ activeRadius j := by
      exact le_trans (min_le_right _ _) (Finset.inf'_le (s := Finset.univ) (f := activeRadius)
        (Finset.mem_univ j))
    have hzj : z ∈ effectiveDomain (f j.1) := by
      have hjball :
          Metric.ball x (activeRadius j) ⊆ effectiveDomain (f j.1) :=
        (Classical.choose_spec ((mem_cont_iff (f j.1) x).1 (hxcont j.1))).2.1
      apply hjball
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz hρle
    -- The local active-family supremum is attained by a finite active branch, so it stays finite.
    rw [mem_effectiveDomain_iff]
    calc
      (pointwiseSup f z : EReal) = ⨆ i : activeIndices f x, (f i.1 z : EReal) := hzEq
      _ = (f j.1 z : EReal) := hj.symm
      _ < ⊤ := mem_effectiveDomain_iff.mp hzj
  have hactive_cont :
      ∀ i : activeIndices f x, ContinuousAt (fun z ↦ (f i.1 z : EReal)) x := by
    intro i
    rcases (mem_cont_iff (f i.1) x).1 (hxcont i.1) with ⟨ρi, hρi, hballi, hconti⟩
    let G : H → EReal := fun z ↦ (((f i.1 z : EReal).toReal : ℝ) : EReal)
    have hGcont : ContinuousAt G x := by
      -- Compose the source continuity of the real representative with the coercion `ℝ → EReal`.
      simpa [G] using (continuous_coe_real_ereal.continuousAt.comp hconti)
    have hEq : G =ᶠ[nhds x] fun z ↦ (f i.1 z : EReal) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
      refine ⟨Metric.ball x ρi, Metric.ball_mem_nhds x hρi, ?_⟩
      intro z hz
      have hzdom : z ∈ effectiveDomain (f i.1) := hballi hz
      have hztop : (f i.1 z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzdom)
      have hzbot : (f i.1 z : EReal) ≠ ⊥ := by
        exact ne_of_gt (f i.1 z).2
      simpa [G] using (EReal.coe_toReal hztop hzbot)
    -- Eventual equality on the local effective-domain ball upgrades the real continuity witness.
    exact hGcont.congr hEq
  have hactiveSup_cont :
      ContinuousAt
        (fun z ↦ Finset.univ.sup (fun i : activeIndices f x ↦ (f i.1 z : EReal))) x := by
    -- The active family is finite, so its pointwise supremum is a finite supremum of continuous
    -- `EReal`-valued branches.
    exact ContinuousAt.finset_sup_apply (s := Finset.univ)
      (f := fun i : activeIndices f x ↦ fun z : H ↦ (f i.1 z : EReal))
      (x := x) fun i _ ↦ hactive_cont i
  have hEqSup :
      (fun z ↦ Finset.univ.sup (fun i : activeIndices f x ↦ (f i.1 z : EReal))) =ᶠ[nhds x]
        fun z ↦ (pointwiseSup f z : EReal) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, ?_⟩
    intro z hz
    have hzsup : z ∈ Metric.ball x ρsup := by
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_left _ _)
    calc
      Finset.univ.sup (fun i : activeIndices f x ↦ (f i.1 z : EReal))
          = ⨆ i : activeIndices f x, (f i.1 z : EReal) := Finset.sup_univ_eq_iSup _
      _ = (pointwiseSup f z : EReal) := (hsup z hzsup).symm
  have hpointwiseSup_cont : ContinuousAt (fun z ↦ (pointwiseSup f z : EReal)) x :=
    hactiveSup_cont.congr hEqSup
  have hxSup : x ∈ effectiveDomain (pointwiseSup f) := hballSup (Metric.mem_ball_self hρ)
  have hpointwiseSup_toReal_cont :
      ContinuousAt (fun z ↦ (pointwiseSup f z : EReal).toReal) x := by
    have hxSup_top : (pointwiseSup f x : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxSup)
    have hxSup_bot : (pointwiseSup f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (pointwiseSup f x).2
    -- Once the `EReal` maximum is continuous and finite at `x`, `toReal` is continuous there.
    exact (EReal.tendsto_toReal hxSup_top hxSup_bot).comp hpointwiseSup_cont
  exact ⟨ρ, hρ, hballSup, hpointwiseSup_toReal_cont⟩

/-- Helper for Theorem 18 5: subtracting a finite real shift and dividing by a positive real
scalar commutes with indexed suprema in `EReal`. -/
private theorem ereal_iSup_sub_right_div_of_pos
    {κ : Sort*} (r α : ℝ) (hα : 0 < α) (φ : κ → EReal) :
    (((⨆ i, φ i) - ((r : ℝ) : EReal)) / α) =
      ⨆ i, ((φ i - ((r : ℝ) : EReal)) / α) := by
  let αinv : Set.Ioi (0 : ℝ) := ⟨α⁻¹, inv_pos.mpr hα⟩
  -- Rewrite the common subtraction as a real shift before commuting the positive scalar through
  -- the indexed supremum.
  calc
    (((⨆ i, φ i) - ((r : ℝ) : EReal)) / α)
        = (((⨆ i, φ i) + ((-r : ℝ) : EReal)) * ((α⁻¹ : ℝ) : EReal)) := by
            rw [sub_eq_add_neg, ← EReal.coe_neg, div_eq_mul_inv, ← EReal.coe_inv α]
    _ = (((αinv : ℝ) : EReal)) * (((⨆ i, φ i)) + ((-r : ℝ) : EReal)) := by
          simp [αinv, mul_comm]
    _ = (((αinv : ℝ) : EReal)) * (⨆ i, φ i + ((-r : ℝ) : EReal)) := by
          rw [ereal_iSup_add_of_real_shift (-r) φ]
    _ = ⨆ i, (((αinv : ℝ) : EReal) * (φ i + ((-r : ℝ) : EReal))) := by
          exact ereal_mul_iSup_of_pos αinv (fun i : κ ↦ φ i + ((-r : ℝ) : EReal))
    _ = ⨆ i, ((φ i - ((r : ℝ) : EReal)) / α) := by
          refine iSup_congr fun i ↦ ?_
          rw [sub_eq_add_neg, ← EReal.coe_neg, div_eq_mul_inv, ← EReal.coe_inv α]
          simp [αinv, mul_comm]

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: once the nearby active-family model is fixed, the pointwise-supremum
difference quotient equals the active supremum of the branchwise difference quotients. -/
private theorem pointwiseSup_directionalDifferenceQuotient_eq_iSup_active_of_pos
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hxcont : ∀ i, x ∈ cont (f i)) {ρ α : ℝ} (_hρ : 0 < ρ) (hα : 0 < α)
    (hsup :
      ∀ z ∈ Metric.ball x ρ,
        (pointwiseSup f z : EReal) = ⨆ i : activeIndices f x, (f i.1 z : EReal))
    (hαball : x + α • y ∈ Metric.ball x ρ) :
    (((pointwiseSup f (x + α • y) : EReal) - (pointwiseSup f x : EReal)) / α) =
      ⨆ i : activeIndices f x,
        (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) := by
  rcases activeIndices_nonempty f x with ⟨i₀, hi₀⟩
  have hxi₀ : x ∈ effectiveDomain (f i₀) := mem_effectiveDomain_of_mem_cont (hxcont i₀)
  have hsup_top : (pointwiseSup f x : EReal) ≠ ⊤ := by
    have hfi_top : (f i₀ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxi₀)
    have hi₀_eq : (f i₀ x : EReal) = (pointwiseSup f x : EReal) := by
      simpa [activeIndices] using hi₀
    exact hi₀_eq ▸ hfi_top
  have hsup_bot : (pointwiseSup f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (pointwiseSup f x).2
  let r : ℝ := (pointwiseSup f x : EReal).toReal
  have hr : (((r : ℝ) : EReal)) = (pointwiseSup f x : EReal) := by
    simpa using (EReal.coe_toReal hsup_top hsup_bot)
  -- Rewrite the nearby supremum by the stabilized active family, then normalize the common finite
  -- base value so the `EReal` arithmetic lemma applies.
  calc
    (((pointwiseSup f (x + α • y) : EReal) - (pointwiseSup f x : EReal)) / α)
        = (((⨆ i : activeIndices f x, (f i.1 (x + α • y) : EReal)) -
            (((r : ℝ) : EReal))) / α) := by
              rw [hsup _ hαball, ← hr]
    _ = ⨆ i : activeIndices f x,
          (((f i.1 (x + α • y) : EReal) -
            (((r : ℝ) : EReal))) / α) := by
          exact ereal_iSup_sub_right_div_of_pos r α hα
            (fun i : activeIndices f x ↦ (f i.1 (x + α • y) : EReal))
    _ = ⨆ i : activeIndices f x,
          (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) := by
          refine iSup_congr fun i ↦ ?_
          have hri : (((r : ℝ) : EReal)) = (f i.1 x : EReal) := by
            rw [hr]
            exact i.2.symm
          rw [hri]

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the fixed active-family quotient identity holds eventually along the
positive ray at `0`. -/
private theorem pointwiseSup_directionalDifferenceQuotient_eq_iSup_active_eventually
    (f : ι → H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hxcont : ∀ i, x ∈ cont (f i)) :
    ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((pointwiseSup f (x + α • y) : EReal) - (pointwiseSup f x : EReal)) / α) =
        ⨆ i : activeIndices f x,
          (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) := by
  rcases pointwiseSup_eq_iSup_active_nearby (f := f) (x := x) hxcont with
    ⟨ρ, hρ, hsup⟩
  have hline_cont : Continuous fun α : ℝ ↦ x + α • y := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hline0 : Filter.Tendsto (fun α : ℝ ↦ x + α • y) (nhds (0 : ℝ)) (nhds x) := by
    -- The positive-ray reparameterization is continuous at the base point.
    simpa using (hline_cont.continuousAt : ContinuousAt (fun α : ℝ ↦ x + α • y) 0).tendsto
  have hball_event :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • y ∈ Metric.ball x ρ := by
    have hline :
        Filter.Tendsto (fun α : ℝ ↦ x + α • y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds hline0
    -- Eventually the ray stays inside the stabilization ball where the active-family model holds.
    exact hline.eventually (Metric.ball_mem_nhds x hρ)
  -- Intersect eventual ball-membership with positivity of `α`, then apply the fixed-`α` rewrite.
  filter_upwards [hball_event, self_mem_nhdsWithin] with α hαball hα
  exact pointwiseSup_directionalDifferenceQuotient_eq_iSup_active_of_pos
    (f := f) (x := x) (y := y) hxcont hρ hα hsup hαball

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: the stabilized active-family model yields the directional derivative
of the pointwise supremum as the active supremum of the branch directional derivatives. -/
private theorem hasDirectionalDerivativeAt_pointwiseSup_iSup_active
    (f : ι → H → Set.Ioi (⊥ : EReal))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)))
    {x : H} (hxcont : ∀ i, x ∈ cont (f i)) (y : H) :
    HasDirectionalDerivativeAt (pointwiseSup f) x y
      (⨆ i : activeIndices f x, directionalDerivative (f i.1) x y) := by
  classical
  let _ : Fintype (activeIndices f x) := Fintype.ofFinite (activeIndices f x)
  have hxdomSup : x ∈ effectiveDomain (pointwiseSup f) := by
    exact mem_effectiveDomain_of_mem_cont (mem_cont_pointwiseSup_of_mem_cont (f := f) hxcont)
  refine ⟨hxdomSup, ?_⟩
  have hactive :
      Filter.Tendsto
        (fun α : ℝ ↦
          Finset.univ.sup fun i : activeIndices f x ↦
            (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Finset.univ.sup fun i : activeIndices f x ↦ directionalDerivative (f i.1) x y)) := by
    -- Pass to the finite active family and combine the branchwise directional-derivative limits.
    exact Filter.Tendsto.finset_sup_nhds_apply (s := Finset.univ) fun i _ ↦
      (hasDirectionalDerivativeAt_directionalDerivative
        (f := f i.1) (hconv i.1) (mem_effectiveDomain_of_mem_cont (hxcont i.1)) y).2
  have hEq :
      Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun α : ℝ ↦
          (((pointwiseSup f (x + α • y) : EReal) - (pointwiseSup f x : EReal)) / α))
        fun α : ℝ ↦
          Finset.univ.sup fun i : activeIndices f x ↦
            (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) := by
    filter_upwards
      [pointwiseSup_directionalDifferenceQuotient_eq_iSup_active_eventually
        (f := f) (x := x) (y := y) hxcont] with α hα
    -- Rewrite the stabilized active `iSup` as the finite supremum over `Finset.univ`.
    calc
      (((pointwiseSup f (x + α • y) : EReal) - (pointwiseSup f x : EReal)) / α)
          = ⨆ i : activeIndices f x,
              (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) := hα
      _ = Finset.univ.sup fun i : activeIndices f x ↦
            (((f i.1 (x + α • y) : EReal) - (f i.1 x : EReal)) / α) :=
          (Finset.sup_univ_eq_iSup _).symm
  -- Transfer the finite-sup limit back to the original pointwise-supremum quotient.
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa [Finset.sup_univ_eq_iSup] using hactive

omit [CompleteSpace H] in
/-- Helper for Theorem 18 5: at a continuity point, a convex summand's directional derivative is
the support function of its subdifferential. -/
private theorem directionalDerivative_eq_supportFunction_subdifferential_at_cont
    [CompleteSpace H]
    (g : H → Set.Ioi (⊥ : EReal))
    (hgconv : ConvexOn g (effectiveDomain g))
    {x : H} (hxcont : x ∈ cont g) :
    directionalDerivative g x = σ[(∂ g) x] := by
  funext y
  exact congrFun
    (
      directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
        (f := g) hgconv (ContinuousAtOnEffectiveDomain.of_mem_cont hxcont)
    )
    y

/-- Helper for Theorem 18 5: the directional derivative of the pointwise supremum is the support
function of the union of the active subdifferentials. -/
private theorem directionalDerivative_pointwiseSup_eq_supportFunction_activeSubdifferentials
    (f : ι → H → Set.Ioi (⊥ : EReal))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)))
    {x : H} (hxcont : ∀ i, x ∈ cont (f i)) :
    directionalDerivative (pointwiseSup f) x =
      σ[⋃ i ∈ activeIndices f x, (∂ f i) x] := by
  have hconvSup : ConvexOn (pointwiseSup f) (effectiveDomain (pointwiseSup f)) :=
    convexOn_pointwiseSup_effectiveDomain f hconv hxcont
  -- Specialize the active-family derivative formula to each direction and rewrite each branch by
  -- Theorem 17.18 before collapsing the active `iSup` back to a single support function.
  funext y
  calc
    directionalDerivative (pointwiseSup f) x y
        = ⨆ i : activeIndices f x, directionalDerivative (f i.1) x y := by
            exact directionalDerivative_eq_of_hasDirectionalDerivativeAt
              (f := pointwiseSup f) hconvSup
              (hasDirectionalDerivativeAt_pointwiseSup_iSup_active
                (f := f) hconv hxcont y)
    _ = ⨆ i : activeIndices f x, σ[(∂ f i.1) x] y := by
          refine iSup_congr fun i ↦ ?_
          have hσi :=
            directionalDerivative_eq_supportFunction_subdifferential_at_cont
              (g := f i.1) (hgconv := hconv i.1) (hxcont := hxcont i.1)
          exact congrFun hσi y
    _ = σ[⋃ i ∈ activeIndices f x, (∂ f i) x] y := by
          symm
          exact supportFunction_activeSubdifferentials_eq_iSup f x y

/-- Helper for Theorem 18 5: a support-function description of the directional derivative should
identify the subdifferential with the closed convex hull of the support set. -/
private theorem subdifferential_eq_closedConvexHull_of_local_supportFunction
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x)
    (C : Set H)
    (hσ : directionalDerivative f x = σ[C]) :
    (∂ f) x = closedConvexHull ℝ C := by
  have hσsub :
      directionalDerivative f x = σ[(∂ f) x] :=
    directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
      f hconv hxcont
  have hσsets : σ[(∂ f) x] = σ[C] := by
    calc
      σ[(∂ f) x] = directionalDerivative f x := by simpa using hσsub.symm
      _ = σ[C] := hσ
  have hsub_iInter :
      (∂ f) x = ⋂ y : H, supportFunctionHalfspace ((∂ f) x) y := by
    calc
      (∂ f) x = closure (convexHull ℝ ((∂ f) x)) := by
        rw [(convex_subdifferential f x).convexHull_eq, isClosed_subdifferential f x |>.closure_eq]
      _ = ⋂ y : H, supportFunctionHalfspace ((∂ f) x) y :=
        closure_convexHull_eq_iInter_supportFunctionHalfspace ((∂ f) x)
  have hC_iInter :
      closedConvexHull ℝ C = ⋂ y : H, supportFunctionHalfspace C y := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact closure_convexHull_eq_iInter_supportFunctionHalfspace C
  -- Both sets are the same intersection once the support functions agree pointwise.
  ext u
  constructor
  · intro hu
    rw [hC_iInter]
    refine Set.mem_iInter.mpr ?_
    intro y
    have hu_half : u ∈ ⋂ z : H, supportFunctionHalfspace ((∂ f) x) z := by
      exact hsub_iInter ▸ hu
    have huy : u ∈ supportFunctionHalfspace ((∂ f) x) y :=
      Set.mem_iInter.mp hu_half y
    have huy' : (⟪u, y⟫_ℝ : EReal) ≤ σ[C] y := by
      have hσy : σ[(∂ f) x] y = σ[C] y := congrFun hσsets y
      exact hσy ▸ (mem_supportFunctionHalfspace_iff ((∂ f) x) y u).mp huy
    exact (mem_supportFunctionHalfspace_iff C y u).mpr huy'
  · intro hu
    rw [hsub_iInter]
    refine Set.mem_iInter.mpr ?_
    intro y
    have hu_half : u ∈ ⋂ z : H, supportFunctionHalfspace C z := by
      exact hC_iInter ▸ hu
    have huy : u ∈ supportFunctionHalfspace C y := Set.mem_iInter.mp hu_half y
    have huy' : (⟪u, y⟫_ℝ : EReal) ≤ σ[(∂ f) x] y := by
      have hσy : σ[(∂ f) x] y = σ[C] y := congrFun hσsets y
      exact hσy.symm ▸ (mem_supportFunctionHalfspace_iff C y u).mp huy
    exact (mem_supportFunctionHalfspace_iff ((∂ f) x) y u).mpr huy'

-- Proof sketch: the pointwise supremum of finitely many convex functions is again convex, and at
-- a common point of the source continuity sets `cont (f i)` the directional derivative of the
-- supremum is the pointwise supremum of the directional derivatives of the active functions. Apply
-- Theorem 17.18 to the maximum and to each active summand, then identify support functions under
-- finite convex hull and weak compactness.
/-- Theorem 18 5: for a nonempty finite family of convex `]-∞,+∞]`-valued functions, the
subdifferential of the pointwise supremum at a common source continuity point is the convex hull
of the union of the subdifferentials of the active functions at that point. -/
theorem subdifferential_pointwiseSup_eq_convexHull_activeSubdifferentials
    (f : ι → H → Set.Ioi (⊥ : EReal))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)))
    {x : H} (hxcont : ∀ i, x ∈ cont (f i)) :
    (∂ pointwiseSup f) x =
      convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x) := by
  have hconvSup : ConvexOn (pointwiseSup f) (effectiveDomain (pointwiseSup f)) :=
    convexOn_pointwiseSup_effectiveDomain f hconv hxcont
  have hxcontSup : x ∈ cont (pointwiseSup f) :=
    mem_cont_pointwiseSup_of_mem_cont f hxcont
  have hxcontSup' : ContinuousAtOnEffectiveDomain (pointwiseSup f) x :=
    ContinuousAtOnEffectiveDomain.of_mem_cont hxcontSup
  have hxdomSup : x ∈ effectiveDomain (pointwiseSup f) := hxcontSup'.mem_effectiveDomain
  let C : Set H := ⋃ i ∈ activeIndices f x, (∂ f i) x
  have hσ :
      directionalDerivative (pointwiseSup f) x =
        σ[C] := by
    simpa [C] using
      (directionalDerivative_pointwiseSup_eq_supportFunction_activeSubdifferentials
        (f := f) hconv hxcont)
  have hclosed :
      (∂ pointwiseSup f) x = closedConvexHull ℝ C :=
    subdifferential_eq_closedConvexHull_of_local_supportFunction
      (f := pointwiseSup f) hconvSup hxcontSup' C hσ
  -- The support-function characterization gives the closed convex hull, and the weak compactness
  -- helper removes the closure on the active union.
  calc
    (∂ pointwiseSup f) x = closedConvexHull ℝ C := hclosed
    _ = convexHull ℝ C := by
          dsimp [C]
          exact closedConvexHull_activeSubdifferentials_eq_convexHull f hconv hxcont
    _ = convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x) := by
          rfl

end PointwiseSupremumSubdifferential

end

end ERealFunction
