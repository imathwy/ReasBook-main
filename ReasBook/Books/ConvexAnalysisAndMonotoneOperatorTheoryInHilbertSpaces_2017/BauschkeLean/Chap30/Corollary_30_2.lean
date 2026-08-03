import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap04.Definition_4_1
import BauschkeLean.Chap04.Proposition_4_6
import BauschkeLean.Chap04.Proposition_4_47
import BauschkeLean.Chap30.Theorem_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H} {I : Type v} [Fintype I]
variable {T : I → H → H} {ω : I → ℝ} {x x0 : H} {lam : ℕ → ℝ}

private theorem halpernParams_mem_Icc (hlam_mem : ∀ n, lam n ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ n, lam n ∈ Set.Icc (0 : ℝ) 1 :=
  fun n ↦ ⟨(hlam_mem n).1.le, (hlam_mem n).2.le⟩

private theorem weights_mem_Ioc_of_pos_sum_one (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1 := by
  intro i
  refine ⟨hω_pos i, ?_⟩
  have hi_le_sum : ω i ≤ ∑ j, ω j := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ (hω_pos j).le)
        (by simp : i ∈ (Finset.univ : Finset I)))
  rw [hω_sum] at hi_le_sum
  simpa using hi_le_sum

omit [CompleteSpace H] [Fintype I] in
private theorem iInter_fixedPointSetOn_isClosed (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D) :
    IsClosed (⋂ i, fixedPointSetOn D (T i)) := by
  refine isClosed_iInter fun i ↦ ?_
  exact
    (isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      (hT_nonexp i).quasinonexpansiveOn hD_closed hD_convex).1

omit [CompleteSpace H] [Fintype I] in
private theorem iInter_fixedPointSetOn_convex (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D) :
    Convex ℝ (⋂ i, fixedPointSetOn D (T i)) := by
  refine convex_iInter fun i ↦ ?_
  exact
    (isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      (hT_nonexp i).quasinonexpansiveOn hD_closed hD_convex).2

omit [Fintype I] in
private theorem iInter_fixedPointSetOn_isChebyshev (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D)
    (hFix_nonempty : (⋂ i, fixedPointSetOn D (T i)).Nonempty) :
    IsChebyshev (⋂ i, fixedPointSetOn D (T i)) :=
  isChebyshev_of_nonempty_isClosed_convex hFix_nonempty
    (iInter_fixedPointSetOn_isClosed hD_closed hD_convex hT_nonexp)
    (iInter_fixedPointSetOn_convex hD_closed hD_convex hT_nonexp)

variable (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D)
variable (hFix_nonempty : (⋂ i, fixedPointSetOn D (T i)).Nonempty)
variable (hT_maps : ∀ i, Set.MapsTo (T i) D D)
variable (hω_pos : ∀ i, 0 < ω i) (hω_sum : ∑ i, ω i = 1)

local notation "FixFamily" => ⋂ i, fixedPointSetOn D (T i)
local notation "Avg" => fun y : H ↦ ∑ i, ω i • T i y
local notation "hFix_cheb" =>
  iInter_fixedPointSetOn_isChebyshev hD_closed hD_convex hT_nonexp hFix_nonempty

/- Source/core/bridge triage:
- `source-facing`: Corollary 30.2 is the Halpern convergence statement to the common fixed-point
  set `⋂ i, fixedPointSetOn D (T i)` of a finite weighted family.
- `core/canonical`: the averaging owner is `weightedOperatorAverage`, the iteration owner is
  `halpernIteration`, and the fixed-point owner is `fixedPointSetOn`; the theorem surface uses the
  ambient pointwise form `fun y ↦ ∑ i, ω i • T i y` of that weighted-average owner.
- `bridge/view`: the subtype fixed-point identification
  `fixedPointsWithin_weightedAverage_eq_iInter` and the codomain restriction of the weighted
  average to `D` are proof-only bridges from the ambient statement to the chapter-level fixed-point
  theorem.
-/

/-- Helper for Corollary 30.2: a finite family of positive weights summing to `1`
has a nonempty index type. -/
private theorem nonempty_of_weights_sum_one (hω_sum : ∑ i, ω i = 1) :
    Nonempty I := by
  classical
  by_contra hI
  letI : IsEmpty I := not_nonempty_iff.mp hI
  simp at hω_sum

omit [CompleteSpace H] in
/-- Helper for Corollary 30.2: the weighted average of the family `T i` maps `D` into `D`. -/
private theorem weightedAverage_mapsTo (hD_convex : Convex ℝ D)
    (hT_maps : ∀ i, Set.MapsTo (T i) D D) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    Set.MapsTo Avg D D := by
  intro y hy
  let yD : D := ⟨y, hy⟩
  have hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1 :=
    weights_mem_Ioc_of_pos_sum_one hω_pos hω_sum
  -- View the ambient weighted average through the canonical subtype operator.
  simpa [weightedOperatorAverage_apply] using
    Convex.weightedOperatorAverage_mem hD_convex ω (fun i ↦ fun z : D ↦ T i z)
      (fun i z ↦ hT_maps i z.2) hω_mem hω_sum yD

omit [CompleteSpace H] in
/-- Helper for Corollary 30.2: the weighted average of nonexpansive maps is nonexpansive on `D`.
-/
private theorem weightedAverage_lipschitzOnWith
    (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    LipschitzOnWith 1 Avg D := by
  -- Control the weighted average by the triangle inequality and the pointwise nonexpansive bounds.
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  calc
    dist (Avg y) (Avg z) = ‖(∑ i, ω i • T i y) - ∑ i, ω i • T i z‖ := by
      simp [dist_eq_norm]
    _ = ‖∑ i, ω i • (T i y - T i z)‖ := by
      simp [smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖ω i • (T i y - T i z)‖ := norm_sum_le _ _
    _ = ∑ i, ω i * ‖T i y - T i z‖ := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hω_pos i).le]
    _ ≤ ∑ i, ω i * dist y z := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hTi : ‖T i y - T i z‖ ≤ dist y z := by
        simpa [dist_eq_norm] using (hT_nonexp i).dist_le_mul y hy z hz
      exact mul_le_mul_of_nonneg_left hTi (hω_pos i).le
    _ = (∑ i, ω i) * dist y z := by
      rw [Finset.sum_mul]
    _ = 1 * dist y z := by
      simp [hω_sum]

omit [CompleteSpace H] in
/-- Helper for Corollary 30.2: the weighted-average fixed points in `D` are exactly the common
fixed points of the family. -/
private theorem fixedPointSetOn_weightedAverage_eq_iInter
    (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D)
    (hFix_nonempty : (⋂ i, fixedPointSetOn D (T i)).Nonempty) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    fixedPointSetOn D Avg = FixFamily := by
  classical
  letI : Nonempty I := nonempty_of_weights_sum_one hω_sum
  let Tr : I → D → H := fun i z ↦ T i z
  have hTr_quasi : ∀ i, IsQuasinonexpansiveOn (Tr i) := by
    intro i
    simpa [Tr] using (hT_nonexp i).quasinonexpansiveOn
  have hFixWithin_nonempty : (⋂ i, fixedPointsWithin (Tr i)).Nonempty := by
    rcases hFix_nonempty with ⟨z, hz⟩
    let i0 : I := Classical.choice inferInstance
    have hzD : z ∈ D := (mem_fixedPointSetOn_iff.mp ((Set.mem_iInter.mp hz) i0)).1
    refine ⟨⟨z, hzD⟩, ?_⟩
    -- Convert the ambient common fixed point into the subtype fixed-point family.
    rw [Set.mem_iInter]
    intro i
    rw [mem_fixedPointsWithin_iff]
    exact (mem_fixedPointSetOn_iff.mp ((Set.mem_iInter.mp hz) i)).2
  have hFixWithin_eq :
      fixedPointsWithin (fun z : D ↦ ∑ i, ω i • Tr i z) = ⋂ i, fixedPointsWithin (Tr i) :=
    fixedPointsWithin_weightedAverage_eq_iInter ω Tr hTr_quasi hFixWithin_nonempty hω_pos hω_sum
  ext z
  constructor
  · intro hz
    rcases mem_fixedPointSetOn_iff.mp hz with ⟨hzD, hzfix⟩
    have hzWithin : (⟨z, hzD⟩ : D) ∈ fixedPointsWithin (fun y : D ↦ ∑ i, ω i • Tr i y) := by
      rw [mem_fixedPointsWithin_iff]
      simpa [Tr] using hzfix
    have hzCommon : (⟨z, hzD⟩ : D) ∈ ⋂ i, fixedPointsWithin (Tr i) := by
      rw [← hFixWithin_eq]
      exact hzWithin
    rw [Set.mem_iInter]
    intro i
    have hzi : (⟨z, hzD⟩ : D) ∈ fixedPointsWithin (Tr i) := (Set.mem_iInter.mp hzCommon) i
    rw [mem_fixedPointsWithin_iff] at hzi
    have hzfixed_i : T i z = z := by
      simpa [Tr] using hzi
    exact mem_fixedPointSetOn_iff.mpr ⟨hzD, hzfixed_i⟩
  · intro hz
    let i0 : I := Classical.choice inferInstance
    have hzD : z ∈ D := (mem_fixedPointSetOn_iff.mp ((Set.mem_iInter.mp hz) i0)).1
    have hzCommon : (⟨z, hzD⟩ : D) ∈ ⋂ i, fixedPointsWithin (Tr i) := by
      rw [Set.mem_iInter]
      intro i
      rw [mem_fixedPointsWithin_iff]
      exact (mem_fixedPointSetOn_iff.mp ((Set.mem_iInter.mp hz) i)).2
    have hzWithin : (⟨z, hzD⟩ : D) ∈ fixedPointsWithin (fun y : D ↦ ∑ i, ω i • Tr i y) := by
      rw [hFixWithin_eq]
      exact hzCommon
    rw [mem_fixedPointSetOn_iff]
    refine ⟨hzD, ?_⟩
    rw [mem_fixedPointsWithin_iff] at hzWithin
    simpa [Tr] using hzWithin

omit [CompleteSpace H] in
/-- Helper for Corollary 30.2: the metric projection onto the weighted-average fixed-point set
coincides with the metric projection onto the common fixed-point set. -/
private theorem projection_weightedAverage_eq_projection_iInter
    (hFixCheb : IsChebyshev FixFamily) (hT_nonexp : ∀ i, LipschitzOnWith 1 (T i) D)
    (hFix_nonempty : (⋂ i, fixedPointSetOn D (T i)).Nonempty) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1)
    (hAvg_cheb : IsChebyshev (fixedPointSetOn D Avg)) :
    P[fixedPointSetOn D Avg, hAvg_cheb] x = P[FixFamily, hFixCheb] x := by
  -- Identify both projection targets through the fixed-point-set equality.
  apply eq_projectionPoint_of_isBestApproximation FixFamily hFixCheb
  simpa [fixedPointSetOn_weightedAverage_eq_iInter hT_nonexp hFix_nonempty hω_pos hω_sum] using
    projectionPoint_isBestApproximation (fixedPointSetOn D Avg) hAvg_cheb x

/-- Corollary 30.2: if `D` is a closed convex subset of a complete real Hilbert space, `T i` is a
finite family of nonexpansive self-maps of `D` with nonempty common fixed-point set in `D`, `ω`
is a family of positive weights summing to `1`, and `lam n ∈ ]0,1[` tends to `0` with divergent
partial sums and summable successive differences, then the Halpern iteration generated by the
weighted average `∑ i, ω i • T i` converges strongly to the metric projection of `x` onto the
common fixed-point set `⋂ i, fixedPointSetOn D (T i)`. -/
theorem halpern_iteration_tendsto_projection_iInter_fixedPointSetOn
    (hT_maps : ∀ i, Set.MapsTo (T i) D D)
    (hω_pos : ∀ i, 0 < ω i) (hω_sum : ∑ i, ω i = 1)
    (hx : x ∈ D) (hx0 : x0 ∈ D)
    (hlam_mem : ∀ n, lam n ∈ Set.Ioo (0 : ℝ) 1)
    (hlam_tendsto_zero : Tendsto lam atTop (𝓝 (0 : ℝ)))
    (hlam_sum_diverges : Tendsto (fun N ↦ (Finset.range N).sum (fun n ↦ lam n)) atTop atTop)
    (hlam_successive_diff_summable : Summable (fun n ↦ |lam (n + 1) - lam n|)) :
    Tendsto
      (halpernIteration Avg lam x x0)
      atTop
      (𝓝 (P[FixFamily, hFix_cheb] x)) := by
  have hAvg_maps : Set.MapsTo Avg D D :=
    weightedAverage_mapsTo hD_convex hT_maps hω_pos hω_sum
  have hAvg_nonexp : LipschitzOnWith 1 Avg D :=
    weightedAverage_lipschitzOnWith hT_nonexp hω_pos hω_sum
  have hAvg_fix_nonempty : (fixedPointSetOn D Avg).Nonempty := by
    rw [fixedPointSetOn_weightedAverage_eq_iInter hT_nonexp hFix_nonempty hω_pos hω_sum]
    exact hFix_nonempty
  have hAvg_closed_convex :
      IsClosed (fixedPointSetOn D Avg) ∧ Convex ℝ (fixedPointSetOn D Avg) :=
    isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      hAvg_nonexp.quasinonexpansiveOn hD_closed hD_convex
  have hAvg_cheb : IsChebyshev (fixedPointSetOn D Avg) :=
    isChebyshev_of_nonempty_isClosed_convex
      hAvg_fix_nonempty hAvg_closed_convex.1 hAvg_closed_convex.2
  have hProjection :
      P[fixedPointSetOn D Avg, hAvg_cheb] x = P[FixFamily, hFix_cheb] x :=
    projection_weightedAverage_eq_projection_iInter hFix_cheb hT_nonexp hFix_nonempty
      hω_pos hω_sum hAvg_cheb
  -- Apply Theorem 30.1 to the averaged operator and transport the projection target at the end.
  simpa [hProjection] using
    (halpern_iteration_tendsto_projection_fixedPointSetOn
      (hD_closed := hD_closed) (hD_convex := hD_convex)
      (hT_nonexp := hAvg_nonexp) (hFix_nonempty := hAvg_fix_nonempty)
      (D := D) (T := Avg) (x := x) (x0 := x0) (lam := lam)
      hx hAvg_maps hx0 hlam_mem hlam_tendsto_zero hlam_sum_diverges
      hlam_successive_diff_summable)

end
