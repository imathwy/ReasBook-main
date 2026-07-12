import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».BoundaryGeometry
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».RectangleIntegrals
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackages
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackageBridges

open MeasureTheory
open scoped BigOperators

universe u

namespace ConnectedSetApproximationSupport

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every axis-parallel complex rectangle
is measurable. -/
theorem measurableSet_rectangle (z w : ℂ) :
    MeasurableSet (Complex.Rectangle z w) := by
  -- A rectangle is compact as a product of two closed intervals, hence measurable.
  have hCompact : IsCompact (Complex.Rectangle z w) := by
    simpa [Complex.Rectangle] using
      (isCompact_uIcc.reProdIm
        (isCompact_uIcc : IsCompact (Set.uIcc z.im w.im)))
  exact hCompact.measurableSet

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: continuity on an ambient set makes a
rectangle-contained restriction integrable on that rectangle. -/
theorem ContinuousOn.integrableOn_rectangle
    {C : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f C) {z w : ℂ}
    (hRectC : Complex.Rectangle z w ⊆ C) :
    IntegrableOn f (Complex.Rectangle z w) := by
  -- Restrict continuity to the compact rectangle and invoke compact integrability.
  exact
    (hf.mono hRectC).integrableOn_compact
      (by
        simpa [Complex.Rectangle] using
          (isCompact_uIcc.reProdIm
            (isCompact_uIcc : IsCompact (Set.uIcc z.im w.im))))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the finite union attached to one
rectangle stage stays inside `interior K` as soon as each rectangle does. -/
theorem rectangleStageUnion_subset_interior
    {K : Set ℂ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∀ n, (⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)) ⊆ interior K := by
  intro n ζ hζ
  rcases Set.mem_iUnion.mp hζ with ⟨s, hs⟩
  exact hRectSubset n s hs

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: finite unions of stage rectangles are
measurable because each rectangle is measurable. -/
theorem rectangleStageUnion_measurable
    {N : ℕ → ℕ} (z w : ∀ n, Fin (N n) → ℂ) :
    ∀ n, MeasurableSet (⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)) := by
  intro n
  -- The stage index type is finite, so the union is a measurable finite union of rectangles.
  exact MeasurableSet.iUnion fun s ↦ measurableSet_rectangle (z n s) (w n s)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a rectangle stage already lies in the
ambient domain `C` once it lies in `interior K` and `K ⊆ C`. -/
theorem rectangleStageSubset_domain_of_subset
    {C K : Set ℂ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ} (hKC : K ⊆ C)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C := by
  intro n s
  -- Push the rectangle containment through `interior K ⊆ K ⊆ C`.
  exact Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: continuity on an ambient domain
containing compact `K` makes the restriction integrable on `interior K`. -/
theorem ContinuousOn.integrableOn_interior_of_compact
    {C K : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f C) (hK_compact : IsCompact K)
    (hKC : K ⊆ C) :
    IntegrableOn f (interior K) := by
  -- First integrate on the compact set `K`, then restrict to the smaller interior.
  exact (hf.mono hKC).integrableOn_compact hK_compact |>.mono_set interior_subset

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the centered closed rectangle with
half-side `r / 4` lies in the ambient ball of radius `r`, and the smaller ball of radius `r / 8`
already lies in that rectangle. -/
theorem centeredRectangle_ball_bridge
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    let zL := Complex.mk (z.re - r / 4) (z.im - r / 4)
    let zU := Complex.mk (z.re + r / 4) (z.im + r / 4)
    z ∈ Complex.Rectangle zL zU ∧
      Complex.Rectangle zL zU ⊆ Metric.ball z r ∧
      Metric.ball z (r / 8) ⊆ Complex.Rectangle zL zU := by
  dsimp
  have hreord : z.re - r / 4 ≤ z.re + r / 4 := by linarith
  have himord : z.im - r / 4 ≤ z.im + r / 4 := by linarith
  constructor
  · -- The center point sits strictly inside the symmetric rectangle by construction.
    change z.re ∈ Set.uIcc (z.re - r / 4) (z.re + r / 4) ∧
      z.im ∈ Set.uIcc (z.im - r / 4) (z.im + r / 4)
    constructor
    · have hzre : z.re ∈ Set.Icc (z.re - r / 4) (z.re + r / 4) := by
        constructor <;> linarith
      simpa [Set.uIcc_of_le hreord] using hzre
    · have hzim : z.im ∈ Set.Icc (z.im - r / 4) (z.im + r / 4) := by
        constructor <;> linarith
      simpa [Set.uIcc_of_le himord] using hzim
  constructor
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm]
    have hw' :
        w.re ∈ Set.uIcc (z.re - r / 4) (z.re + r / 4) ∧
          w.im ∈ Set.uIcc (z.im - r / 4) (z.im + r / 4) := by
      simpa [Complex.Rectangle, Complex.mem_reProdIm] using hw
    have hrew :
        z.re - r / 4 ≤ w.re ∧ w.re ≤ z.re + r / 4 := by
      have hwre : w.re ∈ Set.Icc (z.re - r / 4) (z.re + r / 4) := by
        simpa [Set.uIcc_of_le hreord] using hw'.1
      exact hwre
    have himw :
        z.im - r / 4 ≤ w.im ∧ w.im ≤ z.im + r / 4 := by
      have hwim : w.im ∈ Set.Icc (z.im - r / 4) (z.im + r / 4) := by
        simpa [Set.uIcc_of_le himord] using hw'.2
      exact hwim
    have hsubre : (w - z).re = w.re - z.re := by simp
    have hsubim : (w - z).im = w.im - z.im := by simp
    have hre_abs : |(w - z).re| ≤ r / 4 := by
      apply abs_le.mpr
      constructor <;> linarith [hrew.1, hrew.2, hsubre]
    have him_abs : |(w - z).im| ≤ r / 4 := by
      apply abs_le.mpr
      constructor <;> linarith [himw.1, himw.2, hsubim]
    calc
      ‖w - z‖ ≤ |(w - z).re| + |(w - z).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ r / 4 + r / 4 := add_le_add hre_abs him_abs
      _ < r := by linarith
  · intro w hw
    have hnorm : ‖w - z‖ < r / 8 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hsubre : (w - z).re = w.re - z.re := by simp
    have hsubim : (w - z).im = w.im - z.im := by simp
    have hre_abs : |(w - z).re| < r / 4 := by
      calc
        |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ < r / 8 := hnorm
        _ < r / 4 := by linarith
    have him_abs : |(w - z).im| < r / 4 := by
      calc
        |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ < r / 8 := hnorm
        _ < r / 4 := by linarith
    have hre :
        z.re - r / 4 ≤ w.re ∧ w.re ≤ z.re + r / 4 := by
      rcases abs_lt.mp hre_abs with ⟨hre_lo, hre_hi⟩
      constructor <;> linarith [hre_lo, hre_hi, hsubre]
    have him :
        z.im - r / 4 ≤ w.im ∧ w.im ≤ z.im + r / 4 := by
      rcases abs_lt.mp him_abs with ⟨him_lo, him_hi⟩
      constructor <;> linarith [him_lo, him_hi, hsubim]
    change w.re ∈ Set.uIcc (z.re - r / 4) (z.re + r / 4) ∧
      w.im ∈ Set.uIcc (z.im - r / 4) (z.im + r / 4)
    constructor
    · have hwre : w.re ∈ Set.Icc (z.re - r / 4) (z.re + r / 4) := hre
      simpa [Set.uIcc_of_le hreord] using hwre
    · have hwim : w.im ∈ Set.Icc (z.im - r / 4) (z.im + r / 4) := him
      simpa [Set.uIcc_of_le himord] using hwim

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every open subset of `ℂ` admits a
countable pairwise disjoint family of centered closed rectangles that covers it almost everywhere.
-/
theorem IsOpen.exists_countable_centeredRectangle_covering_ae
    {U : Set ℂ} (hU : IsOpen U) :
    ∃ t : Set (ℂ × ℝ),
      t.Countable ∧
      (∀ p ∈ t,
        0 < p.2 ∧
          let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
          let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
          Complex.Rectangle zL zU ⊆ U) ∧
      t.PairwiseDisjoint (fun p =>
        let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
        let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
        Complex.Rectangle zL zU) ∧
      volume
        (U \ ⋃ p ∈ t,
          let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
          let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
          Complex.Rectangle zL zU) = 0 := by
  classical
  let B : ℂ × ℝ → Set ℂ := fun p =>
    let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
    let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
    Complex.Rectangle zL zU
  let t : Set (ℂ × ℝ) := {p | p.1 ∈ U ∧ 0 < p.2 ∧ B p ⊆ U}
  obtain ⟨u, hu_subset, hu_count, hu_disj, hu_cov⟩ :=
    Vitali.exists_disjoint_covering_ae'
      (μ := volume) (s := U) (t := t) (C := (576 : NNReal))
      (r := Prod.snd) (c := Prod.fst) (B := B)
      (hB := by
        intro p hp
        have hr : 0 < p.2 := hp.2.1
        -- The centered rectangle of scale `p.2` lies inside the Euclidean ball of radius `p.2`.
        exact
          (centeredRectangle_ball_bridge p.1 hr).2.1.trans Metric.ball_subset_closedBall)
      (μB := by
        intro p hp
        have hr : 0 < p.2 := hp.2.1
        have hsmall :
            Metric.ball p.1 (p.2 / 8) ⊆ B p := by
          -- The same bridge provides a definite inner ball, so the Vitali size comparison is
          -- reduced to the closed-ball volume formula on `ℂ`.
          intro z hz
          exact (centeredRectangle_ball_bridge p.1 hr).2.2 hz
        calc
          volume (Metric.closedBall p.1 (3 * p.2))
              ≤ (576 : ENNReal) * volume (Metric.ball p.1 (p.2 / 8)) := by
            rw [Complex.volume_closedBall, Complex.volume_ball]
            have hmain : ((3 : ℝ) * p.2) ^ 2 ≤ 576 * (p.2 / 8) ^ 2 := by
              nlinarith
            have hLeft :
                ENNReal.ofReal (3 * p.2) ^ 2 = ENNReal.ofReal ((3 * p.2) ^ 2) := by
              have hMul :
                  ENNReal.ofReal ((3 * p.2) * (3 * p.2)) =
                    ENNReal.ofReal (3 * p.2) * ENNReal.ofReal (3 * p.2) :=
                ENNReal.ofReal_mul (show 0 ≤ 3 * p.2 by positivity)
              simpa [pow_two] using hMul.symm
            have hRight :
                (576 : ENNReal) * (ENNReal.ofReal (p.2 / 8) ^ 2) =
                  ENNReal.ofReal (576 * (p.2 / 8) ^ 2) := by
              have hSquare :
                  ENNReal.ofReal (p.2 / 8) ^ 2 = ENNReal.ofReal ((p.2 / 8) ^ 2) := by
                have hMul :
                    ENNReal.ofReal ((p.2 / 8) * (p.2 / 8)) =
                      ENNReal.ofReal (p.2 / 8) * ENNReal.ofReal (p.2 / 8) :=
                  ENNReal.ofReal_mul (show 0 ≤ p.2 / 8 by positivity)
                simpa [pow_two] using hMul.symm
              rw [hSquare]
              have hMul :
                  ENNReal.ofReal (576 * ((p.2 / 8) ^ 2)) =
                    ENNReal.ofReal (576 : ℝ) * ENNReal.ofReal ((p.2 / 8) ^ 2) :=
                ENNReal.ofReal_mul (show 0 ≤ (576 : ℝ) by positivity)
              simpa using hMul.symm
            calc
              ENNReal.ofReal (3 * p.2) ^ 2 * NNReal.pi =
                  ENNReal.ofReal ((3 * p.2) ^ 2) * NNReal.pi := by rw [hLeft]
              _ ≤ ENNReal.ofReal (576 * (p.2 / 8) ^ 2) * NNReal.pi := by
                exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hmain) _
              _ = ((576 : ENNReal) * (ENNReal.ofReal (p.2 / 8) ^ 2)) * NNReal.pi := by
                rw [hRight]
              _ = (576 : ENNReal) * (ENNReal.ofReal (p.2 / 8) ^ 2 * NNReal.pi) := by
                rw [mul_assoc]
          _ ≤ (576 : ENNReal) * volume (B p) := by
            exact mul_le_mul_left' (measure_mono hsmall) (576 : ENNReal))
      (ht := by
        intro p hp
        have hr : 0 < p.2 := hp.2.1
        have hcenter : p.1 ∈ interior (B p) := by
          refine mem_interior_iff_mem_nhds.mpr ?_
          refine Filter.mem_of_superset ?_ ((centeredRectangle_ball_bridge p.1 hr).2.2)
          exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
        exact ⟨p.1, hcenter⟩)
      (h't := by
        intro p hp
        -- Centered rectangles are compact products of closed intervals.
        have hCompact : IsCompact (B p) := by
          dsimp [B]
          simpa [Complex.Rectangle] using
            ((isCompact_uIcc : IsCompact (Set.uIcc (p.1.re - p.2 / 4) (p.1.re + p.2 / 4))).reProdIm
              (isCompact_uIcc : IsCompact (Set.uIcc (p.1.im - p.2 / 4) (p.1.im + p.2 / 4))))
        exact hCompact.isClosed)
      (hf := by
        intro z hz
        obtain ⟨δ, hδ_pos, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
        -- Every sufficiently small scale `ε` centered at `z` gives a rectangle still contained
        -- in `U`, so the centered rectangles form a fine Vitali family on `U`.
        apply Filter.Eventually.frequently
        filter_upwards [Ioc_mem_nhdsGT hδ_pos] with ε hε
        refine ⟨(z, ε), ?_, rfl, rfl⟩
        refine ⟨hz, hε.1, ?_⟩
        intro w hw
        have hsub :
            B (z, ε) ⊆ Metric.ball z ε := (centeredRectangle_ball_bridge z hε.1).2.1
        exact hδU (Set.mem_of_subset_of_mem (Metric.ball_subset_ball hε.2) (hsub hw)))
  refine ⟨u, hu_count, ?_, hu_disj, ?_⟩
  · intro p hp
    exact (hu_subset hp).2
  · simpa [B] using hu_cov

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every compact subset of an open set
in `ℂ` is covered by finitely many ordered closed rectangles that already lie inside the open
ambient set. -/
theorem IsCompact.exists_finiteOrderedRectangleCoverWithin
    {S U : Set ℂ} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ t : Finset S,
      ∃ ρ : S → ℝ,
        (∀ x ∈ t, 0 < ρ x) ∧
        (∀ x ∈ t,
          let zL := Complex.mk (x.1.re - ρ x / 4) (x.1.im - ρ x / 4)
          let zU := Complex.mk (x.1.re + ρ x / 4) (x.1.im + ρ x / 4)
          (zL.re < zU.re ∧ zL.im < zU.im) ∧
            Complex.Rectangle zL zU ⊆ U) ∧
        S ⊆ ⋃ x ∈ t,
          let zL := Complex.mk (x.1.re - ρ x / 4) (x.1.im - ρ x / 4)
          let zU := Complex.mk (x.1.re + ρ x / 4) (x.1.im + ρ x / 4)
          Complex.Rectangle zL zU := by
  classical
  let ρ : S → ℝ := fun x ↦ Classical.choose (Metric.mem_nhds_iff.mp (hU.mem_nhds (hSU x.2)))
  have hρ_pos : ∀ x : S, 0 < ρ x := by
    intro x
    exact (Classical.choose_spec (Metric.mem_nhds_iff.mp (hU.mem_nhds (hSU x.2)))).1
  have hρ_sub : ∀ x : S, Metric.ball x.1 (ρ x) ⊆ U := by
    intro x
    exact (Classical.choose_spec (Metric.mem_nhds_iff.mp (hU.mem_nhds (hSU x.2)))).2
  have hcover :
      S ⊆ ⋃ x : S, Metric.ball x.1 (ρ x / 8) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (by have := hρ_pos ⟨x, hx⟩; linarith)
  obtain ⟨t, htcover⟩ :=
    hS.elim_finite_subcover (fun x : S ↦ Metric.ball x.1 (ρ x / 8))
      (fun x ↦ Metric.isOpen_ball) hcover
  refine ⟨t, ρ, fun x hx ↦ hρ_pos x, ?_, ?_⟩
  · intro x hx
    -- Each chosen rectangle is symmetric around `x` with strictly ordered corners, and the
    -- ball-to-rectangle bridge keeps it inside the ambient open set `U`.
    refine ⟨by constructor <;> linarith [hρ_pos x], ?_⟩
    exact (centeredRectangle_ball_bridge x.1 (hρ_pos x)).2.1.trans (hρ_sub x)
  · intro x hx
    rcases Set.mem_iUnion₂.mp (htcover hx) with ⟨y, hyt, hyball⟩
    -- Once `x` lands in one of the selected small balls, the local bridge inserts it into the
    -- associated rectangle.
    exact Set.mem_iUnion₂.mpr ⟨y, hyt, (centeredRectangle_ball_bridge y.1 (hρ_pos y)).2.2 hyball⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the countable pairwise-disjoint
centered-rectangle cover of `interior K` can be truncated to finite stages whose omitted volume
tends to zero. -/
theorem IsCompact.exists_finiteCenteredRectangleStageSets_covering_interior
    {K : Set ℂ} (hK_compact : IsCompact K) :
    ∃ T : ℕ → Set (ℂ × ℝ),
      (∀ n, (T n).Finite) ∧
      (∀ n, T n ⊆ T (n + 1)) ∧
      (∀ n p, p ∈ T n →
        0 < p.2 ∧
          let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
          let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
          Complex.Rectangle zL zU ⊆ interior K) ∧
      (∀ n,
        (T n).PairwiseDisjoint (fun p =>
          let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
          let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
          Complex.Rectangle zL zU)) ∧
      Filter.Tendsto
        (fun n ↦
          volume
            (interior K \ ⋃ p ∈ T n,
              let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
              let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
              Complex.Rectangle zL zU))
        Filter.atTop
        (nhds 0) := by
  let B : ℂ × ℝ → Set ℂ := fun p =>
    let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
    let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
    Complex.Rectangle zL zU
  obtain ⟨t, ht_count, ht_rect, ht_disj, ht_null⟩ :=
    IsOpen.exists_countable_centeredRectangle_covering_ae (U := interior K) isOpen_interior
  let T : t.FiniteExhaustion := ht_count.finiteExhaustion
  let R : ℕ → Set ℂ := fun n ↦ interior K \ ⋃ p ∈ T n, B p
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    -- The exhaustion stages are finite by construction.
    exact T.finite n
  · intro n
    -- The finite exhaustion is monotone in `n`.
    exact T.subset_succ n
  · intro n p hp
    -- Each stage rectangle inherits its positive radius and containment in `interior K` from the
    -- original countable cover.
    have hpt : p ∈ t := by
      rw [← T.iUnion_eq]
      exact Set.mem_iUnion.mpr ⟨n, hp⟩
    exact ht_rect p hpt
  · intro n p hp q hq hpq
    -- Pairwise disjointness is stable when restricting the countable family to one finite stage.
    have hpt : p ∈ t := by
      rw [← T.iUnion_eq]
      exact Set.mem_iUnion.mpr ⟨n, hp⟩
    have hqt : q ∈ t := by
      rw [← T.iUnion_eq]
      exact Set.mem_iUnion.mpr ⟨n, hq⟩
    exact ht_disj hpt hqt hpq
  · have hR_meas : ∀ n, NullMeasurableSet (R n) volume := by
      intro n
      -- Each omitted region is measurable because it is the difference between `interior K` and
      -- a finite union of measurable rectangles.
      apply MeasurableSet.nullMeasurableSet
      apply isOpen_interior.measurableSet.diff
      exact MeasurableSet.biUnion (T.finite n).to_countable fun p hp ↦ measurableSet_rectangle _ _
    have hR_anti : Antitone R := by
      intro n m hnm z hz
      refine ⟨hz.1, ?_⟩
      intro hzStage
      apply hz.2
      rcases Set.mem_iUnion₂.mp hzStage with ⟨p, hp, hzp⟩
      exact Set.mem_iUnion₂.mpr ⟨p, T.mono hnm hp, hzp⟩
    have hR_inter :
        (⋂ n, R n) = interior K \ ⋃ p ∈ t, B p := by
      ext z
      constructor
      · intro hz
        have hzAll : ∀ n, z ∈ R n := Set.mem_iInter.mp hz
        refine ⟨(hzAll 0).1, ?_⟩
        intro hzUnion
        rcases Set.mem_iUnion₂.mp hzUnion with ⟨p, hp, hzp⟩
        have hpStage : p ∈ ⋃ n, T n := by
          simpa [T.iUnion_eq] using hp
        rcases Set.mem_iUnion.mp hpStage with ⟨n, hpn⟩
        exact (hzAll n).2 (Set.mem_iUnion₂.mpr ⟨p, hpn, hzp⟩)
      · rintro ⟨hzK, hzUnion⟩
        refine Set.mem_iInter.mpr ?_
        intro n
        refine ⟨hzK, ?_⟩
        intro hzStage
        apply hzUnion
        rcases Set.mem_iUnion₂.mp hzStage with ⟨p, hp, hzp⟩
        have hpt : p ∈ t := by
          rw [← T.iUnion_eq]
          exact Set.mem_iUnion.mpr ⟨n, hp⟩
        exact Set.mem_iUnion₂.mpr ⟨p, hpt, hzp⟩
    have hR_finite : volume (R 0) ≠ ⊤ := by
      -- Every omitted region is contained in the compact set `K`, so its volume is finite.
      refine (lt_of_le_of_lt ?_ (IsCompact.measure_lt_top (μ := volume) hK_compact)).ne
      apply measure_mono
      intro z hz
      exact interior_subset hz.1
    have hR_tendsto :
        Filter.Tendsto (fun n ↦ volume (R n)) Filter.atTop (nhds (volume (⋂ n, R n))) :=
      MeasureTheory.tendsto_measure_iInter_atTop
        (μ := volume) hR_meas hR_anti ⟨0, hR_finite⟩
    have hZero : volume (⋂ n, R n) = 0 := by
      simpa [hR_inter, B] using ht_null
    -- The residual intersection is exactly the null omitted set supplied by the countable cover.
    simpa [R, hZero] using hR_tendsto

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: one finite centered-rectangle stage can
be reindexed by `Fin N` while preserving ordered corners, rectangle containment, disjointness, and
the union of the stage. -/
theorem finiteCenteredRectangleStage_reindex
    {K : Set ℂ} {T : Set (ℂ × ℝ)}
    (hTfin : T.Finite)
    (hTrect :
      ∀ p ∈ T,
        0 < p.2 ∧
          let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
          let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
          Complex.Rectangle zL zU ⊆ interior K)
    (hTdisj :
      T.PairwiseDisjoint (fun p =>
        let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
        let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
        Complex.Rectangle zL zU)) :
    ∃ N : ℕ,
      ∃ z w : Fin N → ℂ,
        (∀ s, (z s).re < (w s).re ∧ (z s).im < (w s).im) ∧
        (∀ s, Complex.Rectangle (z s) (w s) ⊆ interior K) ∧
        (Set.Pairwise (↑(Finset.univ : Finset (Fin N))) fun i j ↦
          Disjoint (Complex.Rectangle (z i) (w i)) (Complex.Rectangle (z j) (w j))) ∧
        (⋃ s : Fin N, Complex.Rectangle (z s) (w s)) =
          ⋃ p ∈ T,
            let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
            let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
            Complex.Rectangle zL zU := by
  classical
  letI : Fintype T := hTfin.fintype
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let z : Fin (Fintype.card T) → ℂ := fun s =>
    let p : T := e.symm s
    Complex.mk (p.1.1.re - p.1.2 / 4) (p.1.1.im - p.1.2 / 4)
  let w : Fin (Fintype.card T) → ℂ := fun s =>
    let p : T := e.symm s
    Complex.mk (p.1.1.re + p.1.2 / 4) (p.1.1.im + p.1.2 / 4)
  refine ⟨Fintype.card T, z, w, ?_, ?_, ?_, ?_⟩
  · intro s
    -- Positive radius makes the chosen lower-left and upper-right corners strictly ordered.
    have hs : (e.symm s).1 ∈ T := (e.symm s).2
    have hpos := (hTrect (e.symm s).1 hs).1
    dsimp [z, w]
    constructor <;> linarith
  · intro s
    -- The reindexed rectangle is exactly the original stage rectangle attached to `e.symm s`.
    have hs : (e.symm s).1 ∈ T := (e.symm s).2
    dsimp [z, w]
    exact (hTrect (e.symm s).1 hs).2
  · intro i hi j hj hij
    -- Disjointness transfers across the finite equivalence between `Fin N` and the finite stage.
    have hneq : (e.symm i).1 ≠ (e.symm j).1 := by
      intro hEq
      have hSubtype : e.symm i = e.symm j := Subtype.ext hEq
      exact hij (by simpa using congrArg e hSubtype)
    have hiT : (e.symm i).1 ∈ T := (e.symm i).2
    have hjT : (e.symm j).1 ∈ T := (e.symm j).2
    simpa [z, w] using hTdisj hiT hjT hneq
  · ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨s, hs⟩
      refine Set.mem_iUnion₂.mpr ⟨(e.symm s).1, (e.symm s).2, ?_⟩
      simpa [z, w] using hs
    · intro hx
      rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxRect⟩
      refine Set.mem_iUnion.mpr ⟨e ⟨p, hp⟩, ?_⟩
      simpa [z, w]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the finite truncations of the
countable disjoint centered-rectangle cover of `interior K` can be repackaged as ordered
`Fin`-indexed rectangle stages whose omitted volume tends to zero. -/
theorem IsCompact.exists_finiteOrderedRectangleExhaustionOnInterior
    {K : Set ℂ} (hK_compact : IsCompact K) :
    ∃ N : ℕ → ℕ,
      ∃ z w : ∀ n, Fin (N n) → ℂ,
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  obtain ⟨T, hTfin, _hTmono, hTrect, hTdisj, hTvol⟩ :=
    IsCompact.exists_finiteCenteredRectangleStageSets_covering_interior hK_compact
  let stage :
      ∀ n,
        ∃ N : ℕ,
          ∃ z w : Fin N → ℂ,
            (∀ s, (z s).re < (w s).re ∧ (z s).im < (w s).im) ∧
            (∀ s, Complex.Rectangle (z s) (w s) ⊆ interior K) ∧
            (Set.Pairwise (↑(Finset.univ : Finset (Fin N))) fun i j ↦
              Disjoint (Complex.Rectangle (z i) (w i))
                (Complex.Rectangle (z j) (w j))) ∧
            (⋃ s : Fin N, Complex.Rectangle (z s) (w s)) =
              ⋃ p ∈ T n,
                let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
                let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
                Complex.Rectangle zL zU := fun n ↦
      finiteCenteredRectangleStage_reindex (K := K) (hTfin n) (hTrect n) (hTdisj n)
  let N : ℕ → ℕ := fun n ↦ Classical.choose (stage n)
  let z : ∀ n, Fin (N n) → ℂ := fun n ↦
    Classical.choose (Classical.choose_spec (stage n))
  let w : ∀ n, Fin (N n) → ℂ := fun n ↦
    Classical.choose (Classical.choose_spec (Classical.choose_spec (stage n)))
  have hStageSpec :
      ∀ n,
        (∀ s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j))) ∧
        (⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)) =
          ⋃ p ∈ T n,
            let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
            let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
            Complex.Rectangle zL zU := by
    intro n
    exact
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (stage n)))
  have hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im := by
    intro n s
    exact (hStageSpec n).1 s
  have hSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K := by
    intro n s
    exact (hStageSpec n).2.1 s
  have hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)) := by
    intro n
    exact (hStageSpec n).2.2.1
  have hUnion :
      ∀ n,
        (⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)) =
          ⋃ p ∈ T n,
            let zL := Complex.mk (p.1.re - p.2 / 4) (p.1.im - p.2 / 4)
            let zU := Complex.mk (p.1.re + p.2 / 4) (p.1.im + p.2 / 4)
            Complex.Rectangle zL zU := by
    intro n
    exact (hStageSpec n).2.2.2
  refine ⟨N, z, w, hOrdered, hSubset, hDisj, ?_⟩
  -- Replace each `Fin`-indexed union by the original finite centered-rectangle stage before using
  -- the already proved omitted-volume convergence.
  refine Filter.Tendsto.congr' ?_ hTvol
  exact Filter.Eventually.of_forall fun n ↦ by
    simp [hUnion n]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once ordered rectangle-boundary
stages inside `interior K` already converge to the two target contour sums, the contour
discrepancies can be recorded as explicit scalar errors tending to `0`. -/
theorem rectangleBoundaryStages_withVanishingErrors_of_asymptotic
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hContourQ :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)))
    (hContourP :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ∃ eQ : ℕ → ℝ,
      ∃ eP : ℕ → ℝ,
        (∀ n,
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
            ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n)) ∧
        Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
        Filter.Tendsto eP Filter.atTop (nhds 0) ∧
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  let contourQ : ℝ :=
    ∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ
  let contourP : ℝ :=
    ∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ
  let stageQ : ℕ → ℝ := fun n ↦
    ∑ s : Fin (N n),
      ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), (((0 : ℂ → ℝ) dx + Q dy)) ζ
  let stageP : ℕ → ℝ := fun n ↦
    ∑ s : Fin (N n),
      ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), (P dx + (0 : ℂ → ℝ) dy) ζ
  let eQ : ℕ → ℝ := fun n ↦ contourQ - stageQ n
  let eP : ℕ → ℝ := fun n ↦ contourP - stageP n
  refine ⟨eQ, eP, ?_, ?_, ?_, hOrdered, hRectSubset, hDisj, hVolume⟩
  · intro n
    constructor
    · -- Package the discrepancy between the target contour sum and the stage contour sum as
      -- the explicit `Q dy` error term.
      dsimp [eQ, contourQ, stageQ]
      ring
    · -- The same contour-difference packaging gives the explicit `P dx` error term.
      dsimp [eP, contourP, stageP]
      ring
  · -- The `Q dy` errors tend to `0` because the stage contour sums converge to the target
    -- contour sum.
    have hStageQ :
        Filter.Tendsto stageQ Filter.atTop (nhds contourQ) := by
      simpa [stageQ, contourQ] using hContourQ
    have hErrorQ :
        Filter.Tendsto (fun n ↦ contourQ - stageQ n) Filter.atTop
          (nhds (contourQ - contourQ)) := by
      exact tendsto_const_nhds.sub hStageQ
    simpa [eQ] using hErrorQ
  · -- The same limit argument turns the `P dx` contour discrepancy into a vanishing error.
    have hStageP :
        Filter.Tendsto stageP Filter.atTop (nhds contourP) := by
      simpa [stageP, contourP] using hContourP
    have hErrorP :
        Filter.Tendsto (fun n ↦ contourP - stageP n) Filter.atTop
          (nhds (contourP - contourP)) := by
      exact tendsto_const_nhds.sub hStageP
    simpa [eP] using hErrorP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: an ordered rectangle exhaustion of
`interior K` already forces the rectangle-boundary stage sums to converge to the corresponding
interior set integrals. -/
theorem orderedRectangleBoundaryStageLimits_onInterior
    {K C : Set ℂ} (hK_compact : IsCompact K) (hKC : K ⊆ C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dQdx ζ)) ∧
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (-∫ ζ in interior K, dPdy ζ)) := by
  let U : ℕ → Set ℂ := fun n ↦ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)
  have hU_subset : ∀ n, U n ⊆ interior K :=
    rectangleStageUnion_subset_interior hRectSubset
  have hU_meas : ∀ n, MeasurableSet (U n) :=
    rectangleStageUnion_measurable z w
  have hRectSubsetC : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C :=
    rectangleStageSubset_domain_of_subset hKC hRectSubset
  have hIntInteriorQ : IntegrableOn dQdx (interior K) :=
    ContinuousOn.integrableOn_interior_of_compact hdQdx_cont hK_compact hKC
  have hIntInteriorP : IntegrableOn dPdy (interior K) :=
    ContinuousOn.integrableOn_interior_of_compact hdPdy_cont hK_compact hKC
  have hSetQ :
      Filter.Tendsto
        (fun n ↦ ∫ ζ in U n, dQdx ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dQdx ζ)) :=
    setIntegral_tendsto_of_volumeInteriorDiff_tendsto_zero
      (K := K) (f := dQdx) (U := U) hIntInteriorQ hU_subset hU_meas hVolume
  have hSetP :
      Filter.Tendsto
        (fun n ↦ ∫ ζ in U n, dPdy ζ)
        Filter.atTop
        (nhds (∫ ζ in interior K, dPdy ζ)) :=
    setIntegral_tendsto_of_volumeInteriorDiff_tendsto_zero
      (K := K) (f := dPdy) (U := U) hIntInteriorP hU_subset hU_meas hVolume
  constructor
  · -- Rewrite each rectangle boundary sum to the set integral over the stage union, then use the
    -- omitted-volume convergence on the resulting measurable exhaustion.
    have hEqQ :
        ∀ n,
          (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
            ∫ ζ in U n, dQdx ζ := by
      intro n
      calc
        (∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
            ∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dQdx ζ := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact
            rectangleQdy_eq_setIntegral_dQdxOrdered
              (hRe := (hOrdered n s).1) (hIm := (hOrdered n s).2) (hRectD := hRectSubsetC n s)
              hQ_cont hdQdx_cont hQ_dx
        _ = ∫ ζ in U n, dQdx ζ := by
          symm
          simpa [U] using
            setIntegral_biUnion_finiteOrderedRectangles
              (s := (Finset.univ : Finset (Fin (N n))))
              (f := dQdx) (z := z n) (w := w n)
              (hMeas := fun s hs ↦ measurableSet_rectangle (z n s) (w n s))
              (hDisj := hDisj n)
              (hInt := fun s hs ↦
                ContinuousOn.integrableOn_rectangle hdQdx_cont (hRectSubsetC n s))
    refine Filter.Tendsto.congr' ?_ hSetQ
    exact Filter.Eventually.of_forall fun n ↦ (hEqQ n).symm
  · -- The horizontal half-form has the same measurable exhaustion, with the sign supplied by the
    -- rectangle Green-Riemann identity.
    have hNegSetP :
        Filter.Tendsto
          (fun n ↦ -(∫ ζ in U n, dPdy ζ))
          Filter.atTop
          (nhds (-∫ ζ in interior K, dPdy ζ)) := by
      simpa using hSetP.neg
    have hEqP :
        ∀ n,
          (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ) =
            -(∫ ζ in U n, dPdy ζ) := by
      intro n
      calc
        (∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ) =
            ∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact
            rectanglePdx_eq_neg_setIntegral_dPdyOrdered
              (hRe := (hOrdered n s).1) (hIm := (hOrdered n s).2) (hRectD := hRectSubsetC n s)
              hP_cont hdPdy_cont hP_dy
        _ = -(∫ ζ in U n, dPdy ζ) := by
          calc
            ∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ) =
                -∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
              calc
                ∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ) =
                    ∑ s : Fin (N n), (-1 : ℝ) * ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  simp
                _ = (-1 : ℝ) * ∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  rw [Finset.mul_sum]
                _ = -∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  simp
            _ = -(∫ ζ in U n, dPdy ζ) := by
              congr 1
              symm
              simpa [U] using
                setIntegral_biUnion_finiteOrderedRectangles
                  (s := (Finset.univ : Finset (Fin (N n))))
                  (f := dPdy) (z := z n) (w := w n)
                  (hMeas := fun s hs ↦ measurableSet_rectangle (z n s) (w n s))
                  (hDisj := hDisj n)
                  (hInt := fun s hs ↦
                    ContinuousOn.integrableOn_rectangle hdPdy_cont (hRectSubsetC n s))
    refine Filter.Tendsto.congr' ?_ hNegSetP
    exact Filter.Eventually.of_forall fun n ↦ (hEqP n).symm

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the total boundary contour
already matches the two interior coordinate integrals, the ordered rectangle stage limits on
`interior K` can be repackaged as explicit vanishing contour-error sequences. -/
theorem orderedRectangleBoundaryStages_withVanishingErrors_of_coordinateHalfFormulasOnInterior
    {ι : Type u} [Fintype ι] {K C : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hK_compact : IsCompact K) (hKC : K ⊆ C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hHalfQ :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ ζ in interior K, dQdx ζ)
    (hHalfP :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        -∫ ζ in interior K, dPdy ζ)
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ∃ eQ : ℕ → ℝ,
      ∃ eP : ℕ → ℝ,
        (∀ n,
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
            ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
              (∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                  (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n)) ∧
        Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
        Filter.Tendsto eP Filter.atTop (nhds 0) ∧
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  obtain ⟨hContourQ, hContourP⟩ :=
    orderedRectangleBoundaryStageLimits_onInterior
      (K := K) (C := C) hK_compact hKC hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx
      hOrdered hRectSubset hDisj hVolume
  -- First retarget the rectangle-stage limits from the interior integrals to the total boundary
  -- contour sums using the supplied half-formulas.
  have hBoundaryContourQ :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) := by
    simpa [hHalfQ] using hContourQ
  have hBoundaryContourP :
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) := by
    simpa [hHalfP] using hContourP
  -- Then package those asymptotic contour identities as explicit error terms tending to zero.
  exact
    rectangleBoundaryStages_withVanishingErrors_of_asymptotic
      (Γ := Γ) (K := K) (P := P) (Q := Q) (N := N) (z := z) (w := w)
      hOrdered hRectSubset hDisj hBoundaryContourQ hBoundaryContourP hVolume

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the remaining connected-open geometry
owner should first produce rectangle stages inside `interior K` whose rectangle boundary integrals
already track the two coordinate half-form contour sums up to vanishing scalar errors. -/
theorem rectangleBoundaryContourTendsto_of_stageErrors
    {ι : Type u} [Fintype ι] {Γ : ι → ClosedPath ℂ}
    {P Q : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ} {eQ eP : ℕ → ℝ}
    (hStage :
      ∀ n,
        ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n))
    (heQ : Filter.Tendsto eQ Filter.atTop (nhds 0))
    (heP : Filter.Tendsto eP Filter.atTop (nhds 0)) :
    Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
      Filter.Tendsto
        (fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) := by
  constructor
  · -- Solve the `Q dy` stage identity for the rectangle-stage contour sum and pass to the limit.
    exact
      tendsto_of_eq_target_add_error
        (stage := fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ)
        (error := eQ)
        (hstage := fun n ↦ (hStage n).1)
        heQ
  · -- Apply the same target-minus-error normalization to the `P dx` half-form.
    exact
      tendsto_of_eq_target_add_error
        (stage := fun n ↦
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ)
        (error := eP)
        (hstage := fun n ↦ (hStage n).2)
        heP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the connected-open geometry
owner produces an exact rectangle stage package with vanishing scalar contour errors, the target
asymptotic rectangle-boundary stage theorem is only a formal limit wrapper. -/
theorem asymptoticRectangleBoundaryStages_of_exactPackage
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q : ℂ → ℝ} {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ} {eQ eP : ℕ → ℝ}
    (hOrdered : ∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im)
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K)
    (hDisj :
      ∀ n,
        Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
          Disjoint (Complex.Rectangle (z n i) (w n i))
            (Complex.Rectangle (z n j) (w n j)))
    (hStage :
      ∀ n,
        ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n))
    (heQ : Filter.Tendsto eQ Filter.atTop (nhds 0))
    (heP : Filter.Tendsto eP Filter.atTop (nhds 0))
    (hVolume :
      Filter.Tendsto
        (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
        Filter.atTop
        (nhds 0)) :
    ∃ N : ℕ → ℕ,
      ∃ z w : ∀ n, Fin (N n) → ℂ,
        (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
        (∀ n,
          Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
            Disjoint (Complex.Rectangle (z n i) (w n i))
              (Complex.Rectangle (z n j) (w n j))) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
        Filter.Tendsto
          (fun n ↦
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ)) ∧
        Filter.Tendsto
          (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
          Filter.atTop
          (nhds 0) := by
  -- Convert the exact stage identities into the two contour limits before repackaging the
  -- unchanged rectangle geometry and omitted-volume convergence.
  rcases
      rectangleBoundaryContourTendsto_of_stageErrors
        (Γ := Γ) (P := P) (Q := Q) (N := N) (z := z) (w := w) (eQ := eQ) (eP := eP)
        hStage heQ heP with
    ⟨hContourQ, hContourP⟩
  exact ⟨N, z, w, hOrdered, hRectSubset, hDisj, hContourQ, hContourP, hVolume⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: an exact rectangle stage package
inside `interior K` converts directly to the measurable set-approximation package used by the
half-formula endgame. -/
theorem directSetApproximationPackage_of_exactRectangleStagePackage
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hK_compact : IsCompact K) (hKC : K ⊆ C)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hdPdy_cont : ContinuousOn dPdy C) (hdQdx_cont : ContinuousOn dQdx C)
    (hP_dy : ∀ z ∈ C, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ C, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hPackage :
      ∃ N : ℕ → ℕ,
        ∃ z w : ∀ n, Fin (N n) → ℂ,
          ∃ eQ : ℕ → ℝ,
            ∃ eP : ℕ → ℝ,
              (∀ n s, (z n s).re < (w n s).re ∧ (z n s).im < (w n s).im) ∧
              (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
              (∀ n,
                Set.Pairwise (↑(Finset.univ : Finset (Fin (N n)))) fun i j ↦
                  Disjoint (Complex.Rectangle (z n i) (w n i))
                    (Complex.Rectangle (z n j) (w n j))) ∧
              (∀ n,
                ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
                    (∑ s : Fin (N n),
                      ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                        (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n) ∧
                  ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
                    (∑ s : Fin (N n),
                      ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                        (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n)) ∧
              Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
              Filter.Tendsto eP Filter.atTop (nhds 0) ∧
              Filter.Tendsto
                (fun n ↦ volume (interior K \ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)))
                Filter.atTop
                (nhds 0)) :
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n, U n ⊆ interior K) ∧
          (∀ n, MeasurableSet (U n)) ∧
          (∀ n,
            ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior K, dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior K, dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  rcases hPackage with ⟨N, z, w, eQ, eP, hOrdered, hRectSubset, hDisj, hStage, heQ, heP, hVolume⟩
  let U : ℕ → Set ℂ := fun n ↦ ⋃ s : Fin (N n), Complex.Rectangle (z n s) (w n s)
  have hU_subset : ∀ n, U n ⊆ interior K :=
    rectangleStageUnion_subset_interior hRectSubset
  have hU_meas : ∀ n, MeasurableSet (U n) :=
    rectangleStageUnion_measurable z w
  have hRectSubsetC : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C :=
    rectangleStageSubset_domain_of_subset hKC hRectSubset
  have hIntInteriorQ : IntegrableOn dQdx (interior K) :=
    ContinuousOn.integrableOn_interior_of_compact hdQdx_cont hK_compact hKC
  have hIntInteriorP : IntegrableOn dPdy (interior K) :=
    ContinuousOn.integrableOn_interior_of_compact hdPdy_cont hK_compact hKC
  refine ⟨U, eQ, eP, hU_subset, hU_meas, ?_, ?_, ?_, heQ, heP⟩
  · intro n
    constructor
    · -- Route correction: first rewrite each rectangle boundary integral to its rectangle set
      -- integral, then collapse the finite disjoint sum to the set integral over the stage union.
      calc
        (∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ) + eQ n := (hStage n).1
        _ =
            (∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dQdx ζ) + eQ n := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact
            rectangleQdy_eq_setIntegral_dQdxOrdered
              (hRe := (hOrdered n s).1) (hIm := (hOrdered n s).2) (hRectD := hRectSubsetC n s)
              hQ_cont hdQdx_cont hQ_dx
        _ = (∫ ζ in U n, dQdx ζ) + eQ n := by
          congr 1
          symm
          simpa [U] using
            setIntegral_biUnion_finiteOrderedRectangles
              (s := (Finset.univ : Finset (Fin (N n))))
              (f := dQdx) (z := z n) (w := w n)
              (hMeas := fun s hs ↦ measurableSet_rectangle (z n s) (w n s))
              (hDisj := hDisj n)
              (hInt := fun s hs ↦
                ContinuousOn.integrableOn_rectangle hdQdx_cont (hRectSubsetC n s))
    · -- Rewrite the horizontal rectangle stages in the same two-step way.
      calc
        (∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ) + eP n := (hStage n).2
        _ = (∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ)) + eP n := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact
            rectanglePdx_eq_neg_setIntegral_dPdyOrdered
              (hRe := (hOrdered n s).1) (hIm := (hOrdered n s).2) (hRectD := hRectSubsetC n s)
              hP_cont hdPdy_cont hP_dy
        _ = -(∫ ζ in U n, dPdy ζ) + eP n := by
          congr 1
          calc
            ∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ) =
                -∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
              calc
                ∑ s : Fin (N n), -(∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ) =
                    ∑ s : Fin (N n), (-1 : ℝ) * ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  simp
                _ = (-1 : ℝ) * ∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  rw [Finset.mul_sum]
                _ = -∑ s : Fin (N n), ∫ ζ in Complex.Rectangle (z n s) (w n s), dPdy ζ := by
                  simp
            _ = -(∫ ζ in U n, dPdy ζ) := by
              congr 1
              symm
              simpa [U] using
                setIntegral_biUnion_finiteOrderedRectangles
                  (s := (Finset.univ : Finset (Fin (N n))))
                  (f := dPdy) (z := z n) (w := w n)
                  (hMeas := fun s hs ↦ measurableSet_rectangle (z n s) (w n s))
                  (hDisj := hDisj n)
                  (hInt := fun s hs ↦
                    ContinuousOn.integrableOn_rectangle hdPdy_cont (hRectSubsetC n s))
  · -- The omitted-volume hypothesis now gives the convergence of the `dQdx` stage set integrals.
    exact
      setIntegral_tendsto_of_volumeInteriorDiff_tendsto_zero
        (K := K) (f := dQdx) (U := U) hIntInteriorQ hU_subset hU_meas hVolume
  · -- Apply the same volume-exhaustion argument to `dPdy`.
    exact
      setIntegral_tendsto_of_volumeInteriorDiff_tendsto_zero
        (K := K) (f := dPdy) (U := U) hIntInteriorP hU_subset hU_meas hVolume


end ConnectedSetApproximationSupport
