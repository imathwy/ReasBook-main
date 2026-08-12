import Mathlib
import ProbabilityTheory_Klenke_2020.Chap09.Example_9_4
import ProbabilityTheory_Klenke_2020.Chap06.Exercise_6_1_4
import ProbabilityTheory_Klenke_2020.Chap07.Definition_7_2

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology lp

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The symmetric Rademacher law on `ℝ`, assigning mass `1 / 2` to each of the values `-1` and
`1`. -/
abbrev symmetricRademacherRealLaw : Measure ℝ :=
  Measure.map ((↑) : ℤ → ℝ) symmetricRademacherLaw

-- Proof sketch: rewrite the real-valued law as the pushforward of the Chapter 9 Rademacher law
-- along the integer embedding `ℤ → ℝ`, then apply the singleton formula upstream.
/-- The symmetric `{-1, 1}`-valued law on `ℝ` assigns probability `1 / 2` to the value `1`. -/
theorem rademacherRealLaw_apply_singleton_one :
    symmetricRademacherRealLaw ({1} : Set ℝ) = 1 / 2 := by
  rw [symmetricRademacherRealLaw,
    Measure.map_apply (by fun_prop) (measurableSet_singleton (1 : ℝ))]
  have hpreimage : ((↑) : ℤ → ℝ) ⁻¹' ({1} : Set ℝ) = ({1} : Set ℤ) := by
    ext z
    simp
  rw [hpreimage]
  exact _root_.symmetricRademacherLaw_apply_singleton_one

/-- The source-facing subspace `ℓ^f ⊆ ℓ²(ℕ, ℝ)` of finitely supported sequences. -/
def l2FinitelySupported : Submodule ℝ ℓ²(ℕ, ℝ) where
  carrier := { h | Function.HasFiniteSupport h }
  zero_mem' := by
    change (Function.support (0 : ℕ → ℝ)).Finite
    simp
  add_mem' := by
    intro h g hh hg
    exact (hh.union hg).subset (Function.support_add h g)
  smul_mem' := by
    intro c h hh
    exact hh.subset (Function.support_const_smul_subset c h)

private theorem finiteSupport_sum_single_mem (f : ℓ²(ℕ, ℝ)) (s : Finset ℕ) :
    Function.HasFiniteSupport (∑ i ∈ s, lp.single 2 i (f i) : ℓ²(ℕ, ℝ)) := by
  refine (Set.toFinite (↑s : Set ℕ)).subset ?_
  rw [Function.support_subset_iff']
  intro n hn
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hni : n ≠ i := by
    intro h
    apply hn
    simpa [h] using hi
  simp [lp.single_apply, hni]

private theorem denseRange_l2FinitelySupported_subtype :
    DenseRange (l2FinitelySupported.subtypeₗᵢ : l2FinitelySupported → ℓ²(ℕ, ℝ)) := by
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f) ?_
  refine Filter.Eventually.of_forall ?_
  intro s
  refine ⟨⟨∑ i ∈ s, lp.single 2 i (f i), finiteSupport_sum_single_mem f s⟩, rfl⟩

private theorem memLp_two_of_hasLaw_symmetricRademacher
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X symmetricRademacherRealLaw P) :
    MemLp X 2 P := by
  sorry

private def rademacherCoordinate
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).toLp (X n)

private def weightedCoordinate
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    ℕ → Lp ℝ 2 P :=
  fun n ↦ ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n

private theorem weightedCoordinate_hasFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    Function.HasFiniteSupport (weightedCoordinate P X hX_rademacher h) := by
  exact h.2.subset <| by
    simpa [weightedCoordinate] using
      Function.support_smul_subset_left (h : ℓ²(ℕ, ℝ))
        (fun n ↦ rademacherCoordinate P X hX_rademacher n)

private theorem rademacherSeriesOnFiniteSupport_map_add
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h g : l2FinitelySupported) :
    ∑ᶠ n, weightedCoordinate P X hX_rademacher (h + g) n =
      ∑ᶠ n, weightedCoordinate P X hX_rademacher h n +
        ∑ᶠ n, weightedCoordinate P X hX_rademacher g n := by
  sorry

private theorem rademacherSeriesOnFiniteSupport_map_smul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (c : ℝ) (h : l2FinitelySupported) :
    ∑ᶠ n, weightedCoordinate P X hX_rademacher (c • h) n =
      c • ∑ᶠ n, weightedCoordinate P X hX_rademacher h n := by
  sorry

/-- For `h ∈ ℓ^f`, the finite random series `R(h) = ∑ hₙ Xₙ` viewed as an element of
`L²(P)`. -/
def rademacherSeriesOnFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    l2FinitelySupported →ₗ[ℝ] Lp ℝ 2 P where
  toFun := fun h ↦ ∑ᶠ n, weightedCoordinate P X hX_rademacher h n
  map_add' := rademacherSeriesOnFiniteSupport_map_add P X hX_rademacher
  map_smul' := rademacherSeriesOnFiniteSupport_map_smul P X hX_rademacher

/-- On `ℓ^f`, the operator `R` is the finite sum of the coordinates against the Rademacher family
`X`, over any finite set containing the support of `h`. -/
theorem rademacherSeriesOnFiniteSupport_apply
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) {s : Finset ℕ}
    (hs : Function.support (h : ℓ²(ℕ, ℝ)) ⊆ s) :
    rademacherSeriesOnFiniteSupport P X hX_rademacher h =
      Finset.sum s fun n ↦
        ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n := by
  sorry

-- Proof sketch: for finitely supported `h`, the random variable `R(h)` is a finite sum of
-- independent centered `{-1,1}`-valued coordinates. The cross-terms vanish, and each diagonal term
-- contributes `h n ^ 2`, so `‖R(h)‖_{L²(P)}^2 = ∑ h n ^ 2 = ‖h‖_{ℓ²}^2`.
/-- Example 25.1: the source-facing operator `R : ℓ^f → L²(P)` is an isometry on finitely
supported sequences. -/
theorem rademacherSeriesOnFiniteSupport_isometry
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    Isometry (rademacherSeriesOnFiniteSupport P X hX_rademacher) := by
  sorry

private theorem rademacherSeriesOnFiniteSupport_norm_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    ∀ h : l2FinitelySupported,
      ‖rademacherSeriesOnFiniteSupport P X hX_rademacher h‖ ≤
        1 * ‖l2FinitelySupported.subtype h‖ := by
  intro h
  have hnorm :
      ‖rademacherSeriesOnFiniteSupport P X hX_rademacher h‖ = ‖h‖ :=
    ((rademacherSeriesOnFiniteSupport P X hX_rademacher).toLinearIsometry
      (rademacherSeriesOnFiniteSupport_isometry P X hX_indep hX_rademacher)).norm_map h
  simpa using hnorm.le

-- Proof sketch: `ℓ^f` is dense in `ℓ²(ℕ, ℝ)` by the canonical finite-support truncations, and the
-- isometry estimate above gives the norm bound needed for the standard dense-subspace extension
-- theorem.
/-- Example 25.1: the finite-support isometry `R : ℓ^f → L²(P)` has its canonical continuous
extension to all of `ℓ²(ℕ, ℝ)`. -/
def rademacherSeries
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    ℓ²(ℕ, ℝ) →L[ℝ] Lp ℝ 2 P :=
  let _ := rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher
  (rademacherSeriesOnFiniteSupport P X hX_rademacher).extendOfNorm l2FinitelySupported.subtype

/-- The canonical extension `rademacherSeries` agrees with the finite-sum operator `R` on
`ℓ^f`. -/
theorem rademacherSeries_eq_onFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    rademacherSeries P X hX_indep hX_rademacher h =
      rademacherSeriesOnFiniteSupport P X hX_rademacher h := by
  simpa [rademacherSeries] using
    LinearMap.extendOfNorm_eq
      (by simpa using denseRange_l2FinitelySupported_subtype)
      ⟨1, rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher⟩
      h

/-- The canonical extension `rademacherSeries` is the unique continuous linear map on `ℓ²(ℕ, ℝ)`
whose restriction to `ℓ^f` is the finite-sum operator `R`. -/
theorem rademacherSeries_unique
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (R : ℓ²(ℕ, ℝ) →L[ℝ] Lp ℝ 2 P)
    (hR : R.toLinearMap.comp l2FinitelySupported.subtype =
      rademacherSeriesOnFiniteSupport P X hX_rademacher) :
    rademacherSeries P X hX_indep hX_rademacher = R := by
  simpa [rademacherSeries] using
    (LinearMap.extendOfNorm_unique
      (by simpa using denseRange_l2FinitelySupported_subtype)
      1
      (rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher)
      R
      hR)

-- Proof sketch: approximate `h ∈ ℓ²` by the canonical truncations in `ℓ^f`, apply the extension
-- property of `rademacherSeries`, and identify the truncation images with the textbook partial sums
-- `∑_{n < N} h_n X_n`.
/-- For `h ∈ ℓ²(ℕ, ℝ)`, the weighted partial sums converge in `L²(P)` to the extended random
series `R(h)`. -/
theorem rademacherSeries_partialSums_is_l2_limit
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : ℓ²(ℕ, ℝ)) :
    TendstoInLp 2 P
      (fun N ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω)
      (rademacherSeries P X hX_indep hX_rademacher h) := by
  sorry

private theorem memℓp_two_of_summable_sq (h : ℕ → ℝ) (hh_sq : Summable fun n ↦ h n ^ 2) :
    Memℓp h 2 := by
  refine memℓp_gen ?_
  simpa [pow_two, Real.norm_eq_abs, sq_abs] using hh_sq

-- Proof sketch: package the coefficient sequence `h` as an element of `ℓ²(ℕ, ℝ)` and apply
-- `rademacherSeries_partialSums_is_l2_limit`.
/-- Example 25.1: if `X 0, X 1, …` are independent random variables with the symmetric
`{-1, 1}`-valued law on `ℝ` and `∑ (h n)^2 < ∞`, then the weighted partial sums
`S_N(ω) = ∑_{n < N} h n * X n ω` converge in `L²(P)` to a square-integrable random variable.
This existential corollary is the direct consequence of the canonical operator
`rademacherSeries : ℓ²(ℕ, ℝ) → L²(P)`. -/
theorem exists_l2_limit_of_iid_rademacher_series
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (h : ℕ → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (hh_sq : Summable fun n ↦ h n ^ 2) :
    ∃ R : Ω → ℝ,
      TendstoInLp 2 P
        (fun N ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω)
        R := by
  let hL2 : ℓ²(ℕ, ℝ) := ⟨h, memℓp_two_of_summable_sq h hh_sq⟩
  refine ⟨rademacherSeries P X hX_indep hX_rademacher hL2, ?_⟩
  simpa [hL2] using
    rademacherSeries_partialSums_is_l2_limit P X hX_indep hX_rademacher hL2

end ProbabilityTheory
