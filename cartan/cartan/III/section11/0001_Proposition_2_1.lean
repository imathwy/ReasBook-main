import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0026_Definition_II_1_extra_16»
import cartan.II.section05.«0027_Remark_II_1_extra_17»
import cartan.III.section10.«0002_Definition_III_4_extra_2»
import cartan.II.section06.«0006_Corollary_2»
import cartan.II.section06.«0018_Exercise_3»

-- Semantic recall note: `lean_leansearch` was unavailable here; the statement shape was checked
-- against the owner `Path.closedPathIndexAt` and annulus Laurent-expansion APIs.

noncomputable section

open scoped Topology NNReal unitInterval
open Metric

namespace Path

/-- Helper for Proposition 2.1: a closed path whose image lies in an open ball is null-homotopic
in that ball by straight-line contraction to its base point. -/
lemma null_homotopic_in_ball_of_range_subset
    {R : ℝ} {z : ℂ} {γ : Path z z}
    (hγR : Set.range γ ⊆ Metric.ball (0 : ℂ) R) :
    IsNullHomotopicClosedPathIn (Metric.ball (0 : ℂ) R) γ := by
  -- Contract the loop linearly to the constant loop at its base point; convexity keeps every slice
  -- inside the ball.
  refine ⟨z, hγR ⟨0, by simp⟩, ?_⟩
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := fun p : I × I ↦ (1 - (p.1 : ℝ)) * γ p.2 + (p.1 : ℝ) * z
        continuous_toFun := by
          fun_prop
        map_zero_left := ?_
        map_one_left := ?_ }
    · intro t
      simp
    · intro t
      simp
  · intro s
    refine ⟨?_, ?_⟩
    · -- Every time slice remains a loop because `γ` is closed and the contraction fixes the base
      -- point.
      change (1 - (s : ℝ)) * γ 0 + (s : ℝ) * z = (1 - (s : ℝ)) * γ 1 + (s : ℝ) * z
      simp [γ.source, γ.target]
    · rintro _ ⟨t, rfl⟩
      have hz : z ∈ Metric.ball (0 : ℂ) R := hγR ⟨0, by simp⟩
      have hγt : γ t ∈ Metric.ball (0 : ℂ) R := hγR ⟨t, rfl⟩
      have hseg :
          AffineMap.lineMap (γ t) z (s : ℝ) ∈ Metric.ball (0 : ℂ) R :=
        (convex_ball (0 : ℂ) R).lineMap_mem hγt hz s.2
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using hseg

/-- Helper for Proposition 2.1: on every subdivision piece of a piecewise differentiable path, the
piece still lies in the unit interval. -/
lemma subdivision_piece_subset_unitInterval
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1) :
    ∀ i : Fin (n + 1), Set.Icc (subdiv i.castSucc) (subdiv i.succ) ⊆ I := by
  intro i t ht
  constructor
  · -- The left endpoint of each subdivision piece stays to the right of `0`.
    calc
      0 = subdiv 0 := by symm; exact h0
      _ ≤ subdiv i.castSucc := hsubdiv.monotone (Fin.zero_le _)
      _ ≤ t := ht.1
  · -- The right endpoint of each subdivision piece stays to the left of `1`.
    calc
      t ≤ subdiv i.succ := ht.2
      _ ≤ subdiv (Fin.last (n + 1)) := hsubdiv.monotone i.succ.le_last
      _ = 1 := h1

/-- Helper for Proposition 2.1: on one `C¹` piece, a continuous scalar coefficient produces an
interval-integrable pullback integrand. -/
lemma scalar_pullback_intervalIntegrable_on_piece
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} {l u : ℝ} (hlt : l < u)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc l u)) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (γ.extend '' Set.Icc l u)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume l u := by
  -- Replace the ordinary derivative by the continuous within-derivative on the closed piece.
  have hDerivWithin :
      ContinuousOn (fun t ↦ derivWithin γ.extend (Set.Icc l u) t) (Set.Icc l u) := by
    exact (hγ.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
  have hCoeff : ContinuousOn (fun t ↦ φ (γ.extend t)) (Set.Icc l u) := by
    refine hφ.comp (by fun_prop) ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIntWithin :
      IntervalIntegrable
        (fun t ↦ derivWithin γ.extend (Set.Icc l u) t * φ (γ.extend t))
        MeasureTheory.volume l u :=
    (hDerivWithin.mul hCoeff).intervalIntegrable_of_Icc hlt.le
  -- On the interior of the piece, the within-derivative agrees with the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact by simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Proposition 2.1: interval-integrability on each `C¹` subdivision piece upgrades to
interval-integrability on the whole parameter interval. -/
lemma scalar_pullback_intervalIntegrable_of_subdivision
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv) (h0 : subdiv 0 = 0)
    (h1 : subdiv (Fin.last (n + 1)) = 1)
    (hpieces : ∀ i : Fin (n + 1),
      ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)))
    {φ : ℂ → ℂ}
    (hφ : ∀ i : Fin (n + 1),
      ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ))) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 := by
  let a : ℕ → ℝ := fun k ↦
    if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume
        (a 0) (a (n + 1)) := by
    refine IntervalIntegrable.trans_iterate ?_
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    simpa [a, i, hk0, hk1] using
      scalar_pullback_intervalIntegrable_on_piece (γ := γ) hlt (hpieces i) (hφ i)
  have h0' : a 0 = 0 := by simp [a, h0]
  have h1' : a (n + 1) = 1 := by
    simpa [a] using h1
  simpa [h0', h1'] using hInt

/-- Helper for Proposition 2.1: a continuous scalar field on the image of a piecewise
differentiable path defines a curve-integrable scalar `1`-form along that path. -/
lemma curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
    {D : Set ℂ} {φ : ℂ → ℂ} {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hφ : ContinuousOn φ D) (hγD : Set.range γ ⊆ D) :
    CurveIntegrable (fun z ↦ (φ dz) z) γ := by
  rcases hγ_piecewise with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hCoeff :
      ∀ i : Fin (n + 1),
        ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    refine hφ.mono ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
    simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
  have hInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 :=
    scalar_pullback_intervalIntegrable_of_subdivision hsubdiv h0 h1 hpieces hCoeff
  have hIntForm :
      IntervalIntegrable (fun t ↦ (φ dz) (γ.extend t) (deriv γ.extend t)) MeasureTheory.volume
        0 1 := by
    simpa [Complex.scalarOneForm_apply] using hInt
  -- Replace the ordinary derivative by the within-derivative used in `curveIntegralFun`.
  rw [CurveIntegrable]
  refine hIntForm.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  simp [curveIntegralFun_def,
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Proposition 2.1: a curve integral only depends on the values of the `1`-form along
the image of the path. -/
lemma curveIntegral_eq_of_eqOn_range
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} {ω η : ℂ → ℂ →L[ℂ] ℂ}
    (hωη : Set.EqOn ω η (Set.range γ)) :
    ∫ᶜ w in γ, ω w = ∫ᶜ w in γ, η w := by
  -- Rewrite both curve integrals as interval integrals and use equality along the path image.
  rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hmem : γ.extend t ∈ Set.range γ := by
    refine ⟨⟨t, ht⟩, ?_⟩
    simp [Path.extend_apply, ht]
  exact congrArg (fun ψ ↦ ψ (deriv γ.extend t)) (hωη hmem)

/-- Helper for Proposition 2.1: continuity of a scalar coefficient field yields continuity of the
associated complex-linear scalar `1`-form. -/
lemma scalarOneForm_continuousOn {D : Set ℂ} {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ D) :
    ContinuousOn (fun z ↦ (φ dz) z) D := by
  -- The scalar-one-form constructor is continuous in the scalar coefficient.
  simpa [Complex.scalarOneForm] using
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
      ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hφ)

/-- Helper for Proposition 2.1: each Laurent monomial is continuous on the annulus because annulus
points are nonzero. -/
lemma laurentTerm_continuousOn_annulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (n : ℤ) :
    ContinuousOn (laurentTerm a n) (complexOpenAnnulus ρ₂ ρ₁) := by
  -- The annulus avoids `0`, so `zpow` is continuous there for every integer exponent.
  refine (continuousOn_const.mul (continuousOn_zpow₀ n)).mono ?_
  intro z hz
  have hz_ne : z ≠ 0 := by
    intro hz0
    have : ¬ ((ρ₂ : ENNReal) < 0) := by simp
    exact this (by simpa [complexOpenAnnulus, hz0] using hz.1)
  exact hz_ne

/-- Helper for Proposition 2.1: on the annulus, the nonnegative Laurent tail is pointwise
summable. -/
lemma laurent_nonneg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (n : ℤ) * z ^ n) := by
  -- Restrict the annulus Laurent sum to the nonnegative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective Nat.cast_injective

/-- Helper for Proposition 2.1: on the annulus, the negative Laurent tail is pointwise
summable. -/
lemma laurent_neg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)) := by
  -- Restrict the annulus Laurent sum to the negative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective (@Int.negSucc.inj)

/-- Helper for Proposition 2.1: every point of the smaller disc admits an intermediate circle
that still lies inside the original annulus. -/
lemma exists_intermediate_radius_for_ball_point
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ₁) :
    ∃ R : NNReal, max ρ₂ ‖z‖₊ < R ∧ R < ρ₁ := by
  -- The disc bound puts `‖z‖` below `ρ₁`, so there is room for an intermediate radius.
  have hzlt : ‖z‖₊ < ρ₁ := by
    exact_mod_cast (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz : ‖z‖ < (ρ₁ : ℝ))
  have hmax : max ρ₂ ‖z‖₊ < ρ₁ := max_lt_iff.mpr ⟨hρ, hzlt⟩
  exact exists_between hmax

/-- Helper for Proposition 2.1: the nonnegative Laurent tail is the disc-analytic branch from the
textbook Laurent decomposition. -/
lemma laurent_nonneg_part_analyticOnNhd
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n) (ball (0 : ℂ) ρ₁) := by
  -- Route correction: the main residue reduction below is now explicit, so the only remaining work
  -- here is to port the owner Cauchy-power-series proof of the disc branch into this dependency
  -- closure.
  -- TODO: choose an intermediate circle around each `z`, identify the Cauchy power series with
  -- the nonnegative Laurent coefficients, and transfer analyticity from that circle model to the
  -- whole smaller disc.
  sorry

/-- Helper for Proposition 2.1: on the annulus, the Laurent sum splits into its nonnegative and
negative tails. -/
lemma laurent_split_eqOn_annulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hEq : Set.EqOn f (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus ρ₂ ρ₁)) :
    Set.EqOn f
      (fun z ↦ (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      (complexOpenAnnulus ρ₂ ρ₁) := by
  intro z hz
  have hnonneg := laurent_nonneg_part_summable ha hz
  have hneg := laurent_neg_part_summable ha hz
  let fNat : ℕ → ℂ := fun n ↦ a (n : ℤ) * z ^ n
  let gNeg : ℕ → ℂ := fun n ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)
  have hrec : (fun n : ℤ ↦ Int.rec fNat gNeg n) = fun n : ℤ ↦ a n * z ^ n := by
    -- `Int.rec` is exactly the partition of `ℤ` into nonnegative and negative indices.
    funext n
    cases n <;> rfl
  calc
    f z = ∑' n : ℤ, a n * z ^ n := hEq hz
    _ = ∑' n : ℤ, Int.rec fNat gNeg n := by simpa [hrec]
    _ = (∑' n : ℕ, fNat n) + ∑' n : ℕ, gNeg n := by
          exact tsum_int_rec hnonneg hneg
    _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
          rfl

/-- Helper for Proposition 2.1: the Laurent series splits into the residue term `a (-1) z⁻¹` and
the residue-free remainder. -/
lemma laurent_sum_split_residue_free
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    (∑' n : ℤ, a n * z ^ n) =
      a (-1 : ℤ) * z⁻¹ + ∑' n : ℤ, if n = (-1 : ℤ) then 0 else a n * z ^ n := by
  -- Extract the single index `n = -1` from the Laurent sum.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.tsum_eq_add_tsum_ite (-1 : ℤ)

/-- Helper for Proposition 2.1: the Laurent sum splits into the residue term, the nonnegative
tail, and the residue-free negative tail from the source proof. -/
lemma laurent_sum_split_residue_nonneg_neg_residue_free
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    (∑' n : ℤ, a n * z ^ n) =
      a (-1 : ℤ) * z⁻¹ + (∑' n : ℕ, a (n : ℤ) * z ^ n) +
        ∑' n : ℕ, a (Int.negSucc (n + 1)) * z ^ (Int.negSucc (n + 1)) := by
  -- First split the Laurent series into its nonnegative and negative parts.
  have hsplit :=
    laurent_split_eqOn_annulus (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha
      (f := fun w ↦ ∑' n : ℤ, a n * w ^ n) (by intro w hw; rfl) hz
  let g : ℕ → ℂ := fun n ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)
  have hneg : Summable g := by
    simpa [g] using laurent_neg_part_summable (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha hz
  have htail :
      (∑' n : ℕ, g n) = g 0 + ∑' n : ℕ, g (n + 1) := by
    -- Peel off the `n = 0` term, which is the residue contribution `a (-1) z⁻¹`.
    simpa [g, add_comm, add_left_comm, add_assoc] using (hneg.sum_add_tsum_nat_add 1).symm
  calc
    (∑' n : ℤ, a n * z ^ n)
      = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, g n := by
          simpa [g] using hsplit
    _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + (g 0 + ∑' n : ℕ, g (n + 1)) := by
          rw [htail]
    _ = a (-1 : ℤ) * z⁻¹ + (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, g (n + 1) := by
          simp [g, add_assoc, add_left_comm, add_comm]
    _ = a (-1 : ℤ) * z⁻¹ + (∑' n : ℕ, a (n : ℤ) * z ^ n) +
          ∑' n : ℕ, a (Int.negSucc (n + 1)) * z ^ (Int.negSucc (n + 1)) := by
          rfl

/-- Helper for Proposition 2.1: the compact image of a closed path inside the annulus stays
uniformly away from the inner boundary circle. -/
lemma exists_inner_radius_lt_norm_of_range_subset_annulus
    {ρ₂ ρ₁ : NNReal} {z : ℂ} {γ : Path z z}
    (hγann : Set.range γ ⊆ complexOpenAnnulus ρ₂ ρ₁) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ρ₁ ∧ Set.range γ ⊆ (closedBall (0 : ℂ) (r : ℝ))ᶜ := by
  let K : Set ℂ := Set.range γ
  have hK : IsCompact K := isCompact_range γ.continuous
  obtain ⟨w, hwK, hwMin⟩ :=
    hK.exists_isMinOn ⟨γ 0, ⟨0, rfl⟩⟩ continuous_nnnorm.continuousOn
  have hwann : w ∈ complexOpenAnnulus ρ₂ ρ₁ := hγann hwK
  have hρ₂w : ρ₂ < ‖w‖₊ := by
    exact_mod_cast hwann.1
  have hwρ₁ : ‖w‖₊ < ρ₁ := by
    exact_mod_cast hwann.2
  obtain ⟨r, hρ₂r, hrw⟩ := exists_between hρ₂w
  refine ⟨r, hρ₂r, lt_trans hrw hwρ₁, ?_⟩
  intro u hu
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hwu : ‖w‖₊ ≤ ‖u‖₊ := hwMin hu
  exact_mod_cast not_le_of_gt (lt_of_lt_of_le hrw hwu)

/-- Helper for Proposition 2.1: the nonnegative Laurent tail has zero contour integral because it
extends holomorphically to the whole disc bounded by `ρ₁`. -/
lemma curveIntegral_nonneg_laurent_tail_eq_zero
    {ρ₂ ρ₁ : NNReal} {a : ℤ → ℂ} {z : ℂ} {γ : Path z z}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγann : Set.range γ ⊆ complexOpenAnnulus ρ₂ ρ₁)
    (hρ : ρ₂ < ρ₁)
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    ∫ᶜ w in γ, ((fun z : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n) dz) w = 0 := by
  -- The annulus image lies in the outer disc, so the loop contracts there and the holomorphic
  -- nonnegative tail integrates to zero.
  have hrange_ball : Set.range γ ⊆ Metric.ball (0 : ℂ) ρ₁ := by
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using (hγann hw).2
  have hnull : IsNullHomotopicClosedPathIn (Metric.ball (0 : ℂ) ρ₁) γ :=
    null_homotopic_in_ball_of_range_subset hrange_ball
  have hdiff :
      DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n) (Metric.ball (0 : ℂ) ρ₁) := by
    simpa using
      (laurent_nonneg_part_analyticOnNhd (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) hρ ha).differentiableOn
  exact
    Path.curveIntegral_eq_zero_of_differentiableOn_of_null_homotopic Metric.isOpen_ball
      hγ_piecewise hnull hdiff

/-- Helper for Proposition 2.1: the whole contour integral should reduce to the residue term once
the residue-free Laurent remainder is shown to have zero integral. -/
lemma curveIntegral_eq_residue_term
    {ρ₂ ρ₁ : NNReal} {a : ℤ → ℂ} {z : ℂ} {γ : Path z z}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγann : Set.range γ ⊆ complexOpenAnnulus ρ₂ ρ₁)
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {f : ℂ → ℂ}
    (hf : Set.EqOn f (fun w ↦ ∑' n : ℤ, a n * w ^ n) (complexOpenAnnulus ρ₂ ρ₁)) :
    ∫ᶜ w in γ, (f dz) w =
      ∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w := by
  by_cases hρ : ρ₂ < ρ₁
  · let residue : ℂ → ℂ := fun w ↦ a (-1 : ℤ) * w⁻¹
    let nonneg : ℂ → ℂ := fun w ↦ ∑' n : ℕ, a (n : ℤ) * w ^ n
    let negTail : ℂ → ℂ := fun w ↦ ∑' n : ℕ, a (Int.negSucc (n + 1)) * w ^ (Int.negSucc (n + 1))
    have hsplit :
        Set.EqOn f (fun w ↦ residue w + nonneg w + negTail w) (complexOpenAnnulus ρ₂ ρ₁) := by
      -- Rewrite the Laurent expansion into the source split `a(-1) / z + g_nonneg + g_neg,resfree`.
      intro w hw
      calc
        f w = ∑' n : ℤ, a n * w ^ n := hf hw
        _ = residue w + nonneg w + negTail w := by
              simpa [residue, nonneg, negTail, add_assoc, add_left_comm, add_comm] using
                laurent_sum_split_residue_nonneg_neg_residue_free
                  (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha hw
    have hresidue_cont : ContinuousOn residue (complexOpenAnnulus ρ₂ ρ₁) := by
      -- Annulus points are nonzero, so the logarithmic differential coefficient is continuous.
      refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
      intro w hw
      intro hw0
      have : ¬ ((ρ₂ : ENNReal) < 0) := by simp
      have hnorm0 : ‖w‖₊ = 0 := by simpa [hw0]
      have hlt : (ρ₂ : ENNReal) < 0 := by simpa [hnorm0] using hw.1
      exact this hlt
    have hball :
        complexOpenAnnulus ρ₂ ρ₁ ⊆ Metric.ball (0 : ℂ) ρ₁ := by
      -- The outer annulus bound places every path point inside the disc of radius `ρ₁`.
      intro w hw
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw.2
    have hnonneg_cont : ContinuousOn nonneg (complexOpenAnnulus ρ₂ ρ₁) := by
      -- The nonnegative Laurent tail extends analytically across the inner hole, hence is
      -- continuous on the annulus image.
      exact ((laurent_nonneg_part_analyticOnNhd
        (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) hρ ha).continuousOn).mono hball
    let remainderFromLaurent : ℂ → ℂ :=
      fun w ↦ (∑' n : ℤ, a n * w ^ n) - residue w - nonneg w
    have hlaurent_cont :
        ContinuousOn (fun w : ℂ ↦ ∑' n : ℤ, a n * w ^ n) (complexOpenAnnulus ρ₂ ρ₁) := by
      -- TODO: port the owner section-10 proof that the Laurent sum is analytic, hence continuous,
      -- on the annulus itself.
      sorry
    have hremainder_cont :
        ContinuousOn remainderFromLaurent (complexOpenAnnulus ρ₂ ρ₁) := by
      -- The residue-free remainder is the difference between the full Laurent sum and the already
      -- controlled residue and nonnegative pieces.
      exact (hlaurent_cont.sub hresidue_cont).sub hnonneg_cont
    have hremainder_eq :
        Set.EqOn remainderFromLaurent negTail (complexOpenAnnulus ρ₂ ρ₁) := by
      -- On the annulus the explicit split identifies the remainder with the residue-free negative
      -- Laurent tail.
      intro w hw
      calc
        remainderFromLaurent w = (∑' n : ℤ, a n * w ^ n) - residue w - nonneg w := by
          rfl
        _ = (residue w + nonneg w + negTail w) - residue w - nonneg w := by
          rw [laurent_sum_split_residue_nonneg_neg_residue_free
            (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha hw]
        _ = negTail w := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnegTail_cont : ContinuousOn negTail (complexOpenAnnulus ρ₂ ρ₁) := by
      -- Transfer continuity from the algebraic remainder to the explicit residue-free tail.
      exact hremainder_cont.congr (by
        intro w hw
        exact (hremainder_eq hw).symm)
    have hresidue_int :
        CurveIntegrable (fun w ↦ (residue dz) w) γ := by
      -- Continuous scalar coefficients define curve-integrable scalar one-forms along a piecewise
      -- differentiable path.
      exact curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        hγ_piecewise hresidue_cont hγann
    have hnonneg_int :
        CurveIntegrable (fun w ↦ (nonneg dz) w) γ := by
      -- The disc-holomorphic tail is therefore integrable along the annulus path.
      exact curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        hγ_piecewise hnonneg_cont hγann
    have hresidue_nonneg_int :
        CurveIntegrable (fun w ↦ ((fun w : ℂ ↦ residue w + nonneg w) dz) w) γ := by
      -- We will split the contour integral in two stages, so first record integrability of the
      -- residue plus nonnegative tail.
      exact curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        hγ_piecewise (hresidue_cont.add hnonneg_cont) hγann
    have hnegTail_int :
        CurveIntegrable (fun w ↦ (negTail dz) w) γ := by
      -- The residue-free negative tail is continuous on the annulus, so its scalar one-form is
      -- curve-integrable along `γ`.
      exact curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        hγ_piecewise hnegTail_cont hγann
    have hsplit_residue_nonneg :
        ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w) dz) w =
          ∫ᶜ w in γ, (residue dz) w + ∫ᶜ w in γ, (nonneg dz) w := by
      -- Split the integral of the first two summands by linearity of the curve integral.
      have hform :
          ((fun w : ℂ ↦ residue w + nonneg w) dz) = (residue dz) + (nonneg dz) := by
        ext w
        simp [add_mul]
      rw [hform]
      simpa using
        (curveIntegral_add hresidue_int hnonneg_int :
          curveIntegral ((residue dz) + (nonneg dz)) γ =
            ∫ᶜ w in γ, (residue dz) w + ∫ᶜ w in γ, (nonneg dz) w)
    have hsplit_total :
        ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w + negTail w) dz) w =
          ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w) dz) w +
            ∫ᶜ w in γ, (negTail dz) w := by
      -- Split once more to isolate the residue-free negative tail as the only remaining unknown.
      have hform :
          ((fun w : ℂ ↦ residue w + nonneg w + negTail w) dz) =
            ((fun w : ℂ ↦ residue w + nonneg w) dz) + (negTail dz) := by
        ext w
        simp [add_mul, add_assoc]
      rw [hform]
      simpa using
        (curveIntegral_add hresidue_nonneg_int hnegTail_int :
          curveIntegral (((fun w : ℂ ↦ residue w + nonneg w) dz) + (negTail dz)) γ =
            ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w) dz) w +
              ∫ᶜ w in γ, (negTail dz) w)
    have hnonneg_zero :
        ∫ᶜ w in γ, (nonneg dz) w = 0 := by
      -- The holomorphic disc branch has zero integral on the null-homotopic loop.
      simpa [nonneg] using
        curveIntegral_nonneg_laurent_tail_eq_zero
          (ρ₂ := ρ₂) (ρ₁ := ρ₁) (a := a) (γ := γ) hγ_piecewise hγann hρ ha
    -- TODO: choose `r` with `Set.range γ ⊆ (closedBall 0 r)ᶜ`, build the textbook primitive of
    -- `negTail` on that exterior region, restrict it along `γ`, and conclude by the endpoint
    -- formula for primitives on closed paths.
    have hnegTail_zero :
        ∫ᶜ w in γ, (negTail dz) w = 0 := by
      sorry
    -- After the two source-faithful tail cancellations, only the residue term remains.
    calc
      ∫ᶜ w in γ, (f dz) w
          = ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w + negTail w) dz) w := by
              apply curveIntegral_eq_of_eqOn_range
              intro w hw
              simpa [Complex.scalarOneForm] using
                congrArg (fun c : ℂ ↦ (1 : ℂ →L[ℂ] ℂ).smulRight c) (hsplit (hγann hw))
      _ = ∫ᶜ w in γ, ((fun w : ℂ ↦ residue w + nonneg w) dz) w +
            ∫ᶜ w in γ, (negTail dz) w := hsplit_total
      _ = (∫ᶜ w in γ, (residue dz) w + ∫ᶜ w in γ, (nonneg dz) w) +
            ∫ᶜ w in γ, (negTail dz) w := by
              rw [hsplit_residue_nonneg]
      _ = ∫ᶜ w in γ, (residue dz) w := by
              rw [hnonneg_zero, hnegTail_zero]
              simp
      _ = ∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w := by
              simp [residue]
  · -- If the annulus were empty, the path image could not lie in it; use the point `γ 0`.
    have hpoint : γ 0 ∈ Set.range γ := ⟨0, rfl⟩
    have hmem : γ 0 ∈ complexOpenAnnulus ρ₂ ρ₁ := hγann hpoint
    have hρ' : ρ₂ < ρ₁ := by
      exact_mod_cast (lt_trans hmem.1 hmem.2 : (ρ₂ : ENNReal) < (ρ₁ : ENNReal))
    exact (hρ hρ').elim

/-- Proposition 2.1: if `γ` is a piecewise differentiable closed path contained in the annulus
`ρ₂ < |z| < ρ₁`, and `f` agrees there with the Laurent series `∑' n : ℤ, a n * z ^ n`, then the
normalized contour integral of `f(z) dz` along `γ` is the closed-path index of `γ` about `0`
multiplied by the `(-1)`st Laurent coefficient `a (-1)`. -/
theorem curveIntegral_eq_closedPathIndexAt_zero_mul_laurentCoeff_neg_one
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ} {a : ℤ → ℂ} {z : ℂ} {γ : Path z z}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγann : Set.range γ ⊆ complexOpenAnnulus ρ₂ ρ₁)
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hf : Set.EqOn f (fun w ↦ ∑' n : ℤ, a n * w ^ n) (complexOpenAnnulus ρ₂ ρ₁)) :
    (∫ᶜ w in γ, (f dz) w) / (2 * Real.pi * Complex.I : ℂ) =
      γ.closedPathIndexAt 0
          (γ.not_mem_range_of_range_subset hγann (by simp [complexOpenAnnulus])) *
        a (-1 : ℤ) := by
  let residueCoeff : ℤ → ℂ := fun n ↦ if n = (-1 : ℤ) then a (-1 : ℤ) else 0
  have hnot0 : 0 ∉ Set.range γ :=
    γ.not_mem_range_of_range_subset hγann (by simp [complexOpenAnnulus])
  have hresidueScalar :
      ContinuousOn (fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) (complexOpenAnnulus ρ₂ ρ₁) := by
    -- Annulus points avoid `0`, so the reciprocal is continuous there.
    refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
    intro w hw
    intro hw0
    have : ¬ ((ρ₂ : ENNReal) < 0) := by simp
    have hnorm0 : ‖w‖₊ = 0 := by
      simpa [hw0]
    have hlt : (ρ₂ : ENNReal) < 0 := by
      simpa [hnorm0] using hw.1
    exact this hlt
  have hreduce :
      ∫ᶜ w in γ, (f dz) w =
        ∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w :=
    curveIntegral_eq_residue_term hγ_piecewise hγann ha hf
  have hresidue :
      (∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w) / (2 * Real.pi * Complex.I : ℂ) =
        γ.closedPathIndexAt 0 hnot0 * a (-1 : ℤ) := by
    have hsmul :
        ∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w =
          a (-1 : ℤ) * ∫ᶜ w in γ, indexForm 0 w := by
      -- The residue term is exactly the scalar multiple of the logarithmic form `dz / z`.
      have hEq :
          (fun w : ℂ ↦ ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w) =
            fun w ↦ a (-1 : ℤ) • indexForm 0 w := by
        funext w
        ext
        simp [indexForm, mul_left_comm, mul_comm]
      rw [hEq, curveIntegral_fun_smul]
      simp [smul_eq_mul]
    calc
      (∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w) / (2 * Real.pi * Complex.I : ℂ)
        = a (-1 : ℤ) * ((∫ᶜ w in γ, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ)) := by
            rw [hsmul]
            simp [div_eq_mul_inv, mul_assoc]
      _ = a (-1 : ℤ) * γ.closedPathIndexAt 0 hnot0 := by
            rw [Path.closedPathIndexAt_def, closedPathIndex_def]
      _ = γ.closedPathIndexAt 0 hnot0 * a (-1 : ℤ) := by ring
  -- Finish with the reduced residue-term integral and rewrite it as the closed-path index.
  calc
    (∫ᶜ w in γ, (f dz) w) / (2 * Real.pi * Complex.I : ℂ)
      = (∫ᶜ w in γ, ((fun w : ℂ ↦ a (-1 : ℤ) * w⁻¹) dz) w) / (2 * Real.pi * Complex.I : ℂ) := by
          rw [hreduce]
    _ = γ.closedPathIndexAt 0 hnot0 * a (-1 : ℤ) := hresidue

end Path
