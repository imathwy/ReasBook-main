import Mathlib
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap17.Proposition_17_25
import BauschkeLean.Chap20.Corollary_20_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

-- Domain-style sampling:
-- - `source-facing`: `Φ[C]` is the Chapter 17 active farthest-point operator.
-- - `core/canonical`: maximality is the owner `Maximal IsMonotone A`, and singleton-valued
--   maximality is handled by
--   `Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous`.
-- - `bridge/view`: Proposition 17.25 already packages the Chebyshev-center geometry through the
--   argmin owner `Argmin (chebyshevCenterObjective C hC_nonempty).asEReal` and the canonical
--   criterion `mem_argmin_chebyshevCenterObjective_iff_mem_closedConvexHull_activeSet`.

/-- Proposition 21.5 (2): if `C` is a nonempty compact subset of `H` and its farthest-point
operator `Φ[C]` is at most single-valued, then `C` is a singleton. -/
theorem exists_eq_singleton_of_chebyshevCenterActiveSet_isAtMostSingleValued
    (C : Set H) (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hsingle : (Φ[C]).IsAtMostSingleValued) :
    ∃ w : H, C = ({w} : Set H) := by
  rcases existsUnique_mem_argmin_chebyshevCenterObjective
      hC_nonempty hCcompact.isBounded with ⟨r, hr_argmin, _⟩
  have hr_hull :
      r ∈ closedConvexHull ℝ (Φ[C] r) :=
    (mem_argmin_chebyshevCenterObjective_iff_mem_closedConvexHull_activeSet
      hC_nonempty hCcompact r).1 hr_argmin
  have hr_dom : r ∈ (Φ[C]).dom := by
    rw [dom_chebyshevCenterActiveSet_eq_univ hC_nonempty hCcompact]
    simp
  rcases (mem_dom_iff (Φ[C]) r).1 hr_dom with ⟨w, hwΦ⟩
  have hΦ_singleton : Φ[C] r = ({w} : Set H) :=
    Set.Subsingleton.eq_singleton_of_mem (hsingle r) hwΦ
  have hr_eq_w : r = w := by
    have hr_mem : r ∈ ({w} : Set H) := by
      simpa [hΦ_singleton, closedConvexHull_eq_closure_convexHull] using hr_hull
    simpa using hr_mem
  have hrΦ : r ∈ Φ[C] r := by
    simpa [hr_eq_w] using hwΦ
  rcases (show r ∈ C ∧ IsMaxOn (fun y ↦ (((‖r - y‖ ^ (2 : ℕ) : ℝ) : EReal))) C r by
      simpa [chebyshevCenterActiveSet] using hrΦ) with ⟨hrC, hrMax⟩
  refine ⟨r, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr hrC)⟩
  intro y hy
  have hyE :
      (((‖r - y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤ (((‖r - r‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    (isMaxOn_iff.mp hrMax) y hy
  have hySq_le : ‖r - y‖ ^ (2 : ℕ) ≤ 0 := by
    have hySq_le' : ‖r - y‖ ^ (2 : ℕ) ≤ ‖r - r‖ ^ (2 : ℕ) := by
      exact_mod_cast hyE
    simpa using hySq_le'
  have hySq : ‖r - y‖ ^ (2 : ℕ) = 0 :=
    le_antisymm hySq_le (sq_nonneg ‖r - y‖)
  have hry : r = y :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hySq))
  exact Set.mem_singleton_iff.mpr hry.symm

/-- Proposition 21.5 (1): if `C` is a nonempty compact subset of `H` and its farthest-point
operator `Φ[C]` is at most single-valued, then `-Φ[C]` is maximally monotone. -/
theorem neg_chebyshevCenterActiveSet_isMaximallyMonotone_of_isAtMostSingleValued
    (C : Set H) (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hsingle : (Φ[C]).IsAtMostSingleValued) :
    Maximal IsMonotone (-Φ[C]) := by
  rcases exists_eq_singleton_of_chebyshevCenterActiveSet_isAtMostSingleValued
      C hC_nonempty hCcompact hsingle with ⟨w, hC_eq⟩
  have hneg :
      -Φ[C] = (fun _ : H ↦ -w).toSetValuedOperator := by
    ext x u
    constructor
    · intro hu
      have hu' : -u ∈ Φ[C] x := by
        simpa using hu
      have huC : -u ∈ C := by
        exact (show -u ∈ C ∧
            IsMaxOn (fun y ↦ (((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal))) C (-u) by
          simpa [chebyshevCenterActiveSet] using hu').1
      have huw : -u = w := by
        simpa [hC_eq] using huC
      have hu_eq : u = -w := by
        simpa using congrArg Neg.neg huw
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
      exact hu_eq
    · intro hu
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
      subst u
      have hmax :
          IsMaxOn (fun y ↦ (((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal))) ({w} : Set H) w := by
        rw [isMaxOn_iff]
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        simp
      have hw : w ∈ C ∧ IsMaxOn (fun y ↦ (((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal))) C w := by
        refine ⟨?_, ?_⟩
        · simp [hC_eq]
        · simpa [hC_eq] using hmax
      have hw' : w ∈ Φ[C] x := by
        simpa [chebyshevCenterActiveSet] using hw
      simpa using hw'
  have hmono : (fun _ : H ↦ -w).toSetValuedOperator.IsMonotone := by
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    simp
  simpa [hneg] using
    Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
      (fun _ ↦ -w) hmono continuous_const

end SetValuedOperator
