import BauschkeLean.Chap04.Theorem_4_27
import BauschkeLean.Chap30.Theorem_30_8

open Filter
open scoped Topology

universe u v

noncomputable section

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

-- Source/core/bridge triage:
-- `source-facing`: Corollary 30.10 is the firmly nonexpansive specialization of Theorem 30.8.
-- `core/canonical`: the operator hypothesis is the Chapter 4 owner
-- `FirmlyNonexpansiveOn (Set.univ : Set H)`.
-- `bridge/view`: the corollary uses firm nonexpansiveness to supply both firm
-- quasinonexpansiveness and Browder demiclosedness for the residual map.

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The source inequality for firm nonexpansiveness implies firm quasinonexpansiveness. -/
theorem firmlyQuasinonexpansive_of_firmlyNonexpansive {T : H → H}
    (hT : FirmlyNonexpansiveOn (Set.univ : Set H) T) :
    FirmlyQuasinonexpansive T := by
  rw [firmlyNonexpansiveOn_iff] at hT
  rw [firmlyQuasinonexpansive_iff]
  intro x y hy
  have hxy :
      ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    simpa using hT x (by simp) y (by simp)
  simpa [hy, norm_sub_rev] using hxy

/-- A firmly nonexpansive self-map has a demiclosed residual map at `0` on `Set.univ`. -/
theorem demiclosedAt_zero_residualMapOnUniv_of_firmlyNonexpansive {T : H → H}
    (hT : FirmlyNonexpansiveOn (Set.univ : Set H) T) :
    DemiclosedAt (Set.univ : Set H) (residualMapOnUniv T) 0 := by
  rw [firmlyNonexpansiveOn_iff] at hT
  have hLipAmbient : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hxy :
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      simpa using hT x (by simp) y (by simp)
    have hsq : ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(x - T x) - (y - T y)‖]
    simpa [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  have hLip : LipschitzWith 1 (fun x : {x : H // x ∈ (Set.univ : Set H)} ↦ T x.1) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq] using hLipAmbient.dist_le_mul (x : H) (y : H)
  simpa [residualMapOnUniv] using
    (demiclosed_residual_of_nonexpansive hLip) 0

/-- Corollary 30.10: if a finite family of firmly nonexpansive self-maps has a nonempty common
fixed-point set `commonFixedPointSet T` and the control map visits every index in each block of
length `m`, then the
Haugazeau iteration `xₙ₊₁ = Q(x₀, xₙ, T_{control n}(xₙ))` converges strongly to the metric
projection of `x₀` onto the common fixed-point set. -/
theorem haugazeau_iteration_tendsto_projection_iInter_fixedPoints_of_firmlyNonexpansive
    (T : I → H → H)
    (hT : ∀ i, FirmlyNonexpansiveOn (Set.univ : Set H) (T i))
    (hC_nonempty : (commonFixedPointSet T).Nonempty)
    {m : ℕ} (control : ℕ → I)
    (hcontrol : VisitsEveryIndexInEachBlock control m)
    (x0 : H) :
    Tendsto (haugazeauIteration T control x0) atTop
      (𝓝 (P[commonFixedPointSet T,
        iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive T
          (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i)) hC_nonempty] x0)) :=
    haugazeau_iteration_tendsto_projection_iInter_fixedPoints T
      (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
      (fun i ↦ demiclosedAt_zero_residualMapOnUniv_of_firmlyNonexpansive (hT i))
      hC_nonempty control hcontrol x0

end
