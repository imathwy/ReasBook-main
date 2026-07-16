import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section10.«0001_Definition_III_4_extra_1»

open scoped Topology
open Metric

noncomputable section

/-- Helper for Proposition 3.1: the radius-`R` circle lies in the degenerate closed annulus
`R ≤ ‖z‖ ≤ R`. This support-file copy keeps the shifted uniform-sum proof dependency-local. -/
lemma sphere_subset_complexClosedAnnulus_eq_radius_support
    {R : NNReal} :
    sphere (0 : ℂ) (R : ℝ) ⊆ complexClosedAnnulus R R := by
  -- Points on the sphere satisfy both closed-annulus inequalities by the exact norm identity.
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simpa using hzR)
  exact ⟨by simp [hzR'], by simp [hzR']⟩

/-- Helper for Proposition 3.1: the Laurent family is uniformly summable on every intermediate
circle by restricting the closed-annulus uniform summability theorem to that sphere. -/
lemma laurent_summableUniformlyOn_sphere_support
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) :
    SummableUniformlyOn (laurentTerm a) (sphere (0 : ℂ) (R : ℝ)) := by
  -- First obtain uniform summability on the degenerate closed annulus `R ≤ ‖z‖ ≤ R`.
  have hclosed :
      SummableUniformlyOn (laurentTerm a) (complexClosedAnnulus R R) :=
    ha.summableUniformlyOn_closedAnnulus (r₂ := R) (r₁ := R)
      (by exact_mod_cast hρ₂R) (by exact_mod_cast hRρ₁)
  -- Then restrict that uniform summability to the circle itself.
  exact hclosed.mono sphere_subset_complexClosedAnnulus_eq_radius_support

/-- Helper for Proposition 3.1: multiplying the Laurent family on a fixed sphere by the fixed
shift `z ^ (Int.negSucc n)` preserves the uniform sum in `UniformOnFun`. -/
lemma shifted_laurent_hasSumUniformlyOn_sphere
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) (n : ℕ) :
    HasSumUniformlyOn
      (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
      (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z)
      (sphere (0 : ℂ) (R : ℝ)) := by
  let s : Set ℂ := sphere (0 : ℂ) (R : ℝ)
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂R
  have hbase :
      HasSumUniformlyOn (laurentTerm a) (fun z ↦ ∑' m : ℤ, laurentTerm a m z) s :=
    (laurent_summableUniformlyOn_sphere_support
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R) ha hρ₂R hRρ₁).hasSumUniformlyOn
  have hbase_tendsto :
      TendstoUniformlyOn
        (fun t : Finset ℤ => fun z : ℂ ↦ ∑ m ∈ t, laurentTerm a m z)
        (fun z ↦ ∑' m : ℤ, laurentTerm a m z) Filter.atTop s := by
    simpa [hasSumUniformlyOn_iff_tendstoUniformlyOn] using hbase
  have hshift_cont : ContinuousOn (fun z : ℂ ↦ z ^ (Int.negSucc n)) s := by
    refine (continuousOn_zpow₀ (m := Int.negSucc n)).mono ?_
    intro z hz
    have hzR : ‖z‖ = (R : ℝ) := by
      simpa using mem_sphere_iff_norm.mp hz
    exact norm_ne_zero_iff.mp <| by
      rw [hzR]
      exact ne_of_gt hR0
  have hcont_partial :
      ∀ t : Finset ℤ, ContinuousOn (fun z : ℂ ↦ ∑ m ∈ t, laurentTerm a m z) s := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) s)
    · intro m t hm ht
      have hmcont : ContinuousOn (laurentTerm a m) s := by
        refine (continuousOn_const.mul (continuousOn_zpow₀ (m := m))).mono ?_
        intro z hz
        have hzR : ‖z‖ = (R : ℝ) := by
          simpa using mem_sphere_iff_norm.mp hz
        exact norm_ne_zero_iff.mp <| by
          rw [hzR]
          exact ne_of_gt hR0
      simpa [Finset.sum_insert, hm] using hmcont.add ht
  have hsum_cont : ContinuousOn (fun z : ℂ ↦ ∑' m : ℤ, laurentTerm a m z) s :=
    hbase_tendsto.continuousOn (Filter.Frequently.of_forall hcont_partial)
  have hconst :
      TendstoUniformlyOn
        (fun _ : Finset ℤ => fun z : ℂ ↦ z ^ (Int.negSucc n))
        (fun z : ℂ ↦ z ^ (Int.negSucc n)) Filter.atTop s := by
    intro u hu
    exact Filter.Eventually.of_forall fun _ z hz ↦ refl_mem_uniformity hu
  have hshifted_loc :
      TendstoLocallyUniformlyOn
        (fun t : Finset ℤ => fun z : ℂ ↦ z ^ (Int.negSucc n) * ∑ m ∈ t, laurentTerm a m z)
        (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z) Filter.atTop s :=
    hconst.tendstoLocallyUniformlyOn.mul₀ hbase_tendsto.tendstoLocallyUniformlyOn
      hshift_cont hsum_cont
  have hscompact : IsCompact s := by
    simpa [s] using isCompact_sphere (0 : ℂ) (R : ℝ)
  have hshifted :
      TendstoUniformlyOn
        (fun t : Finset ℤ => fun z : ℂ ↦ z ^ (Int.negSucc n) * ∑ m ∈ t, laurentTerm a m z)
        (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z) Filter.atTop s :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hscompact).mp hshifted_loc
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  refine hshifted.congr ?_
  exact Filter.Eventually.of_forall fun t z hz ↦ by
    simp [Finset.mul_sum]
