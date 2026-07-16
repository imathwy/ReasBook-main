import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import DifferentialForms_Cartan_1970.cartan.I.section03.«frozen_0008_Definition_I_3_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

/-- Helper for Cartan section03 frozen_0009_Proposition_5_1: two logarithm branches have
pointwise values differing by an integral multiple of `2π i`. -/
lemma branch_eq_add_two_pi_I_mul_int_at
    {f g : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) (hg : IsLogBranchOn g D)
    {z : ℂ} (hz : z ∈ D) :
    ∃ k : ℤ, g z = f z + k * (2 * (Real.pi : ℂ) * I) := by
  -- Compare the two branch identities at the same point.
  have hfz : exp (f z) = z := by
    simpa [Function.comp] using hf.2.2.2 hz
  have hgz : exp (g z) = z := by
    simpa [Function.comp] using hg.2.2.2 hz
  have hExp : exp (g z) = exp (f z) := hgz.trans hfz.symm
  exact Complex.exp_eq_exp_iff_exists_int.1 hExp

/-- Helper for Cartan section03 frozen_0009_Proposition_5_1: the normalized imaginary part of the
branch difference is always an integer on the branch domain. -/
lemma branch_difference_im_div_two_pi_mem_int_cast_range
    {f g : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) (hg : IsLogBranchOn g D)
    {z : ℂ} (hz : z ∈ D) :
    ((g z - f z).im / (2 * Real.pi : ℝ)) ∈ Set.range (fun k : ℤ ↦ (k : ℝ)) := by
  -- Rewrite the pointwise difference using the period relation from the previous helper.
  obtain ⟨k, hk⟩ := branch_eq_add_two_pi_I_mul_int_at hf hg hz
  have hsub : g z - f z = k * (2 * (Real.pi : ℂ) * I) := by
    rw [hk, add_sub_cancel_left]
  have hk_im : (g z - f z).im = (k : ℝ) * (2 * Real.pi) := by
    calc
      (g z - f z).im = (k * (2 * (Real.pi : ℂ) * I)).im := by rw [hsub]
      _ = (((k : ℤ) • (2 * (Real.pi : ℂ) * I)).im) := by rw [zsmul_eq_mul]
      _ = (k : ℤ) • (2 * (Real.pi : ℂ) * I).im := by rw [Complex.im_zsmul]
      _ = (k : ℝ) * (2 * Real.pi) := by simp
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  refine ⟨k, ?_⟩
  exact ((div_eq_iff htwo_pi_ne).2 hk_im).symm

/-- Helper for Cartan section03 frozen_0009_Proposition_5_1: a preconnected subset of the integer
lattice in `ℝ` is a subsingleton. -/
lemma preconnected_subset_int_cast_range_subsingleton
    {s : Set ℝ} (hs : IsPreconnected s)
    (hsub : s ⊆ Set.range (fun k : ℤ ↦ (k : ℝ))) :
    s.Subsingleton := by
  -- Countability of the integer lattice makes it totally disconnected.
  have hcount : (Set.range (fun k : ℤ ↦ (k : ℝ))).Countable := Set.countable_range _
  exact hcount.isTotallyDisconnected s hsub hs

/-- Helper for Cartan section03 frozen_0009_Proposition_5_1: on a connected domain, any two
logarithm branches differ by one fixed integral multiple of `2π i`. -/
lemma eqOn_add_two_pi_I_mul_int_of_isLogBranchOn
    {f g : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) (hg : IsLogBranchOn g D) :
    ∃ k : ℤ, Set.EqOn g (fun z ↦ f z + k * (2 * (Real.pi : ℂ) * I)) D := by
  have hf' := hf
  have hg' := hg
  rcases hf with ⟨_, hConnected, hcontf, hexpf⟩
  rcases hg with ⟨_, _, hcontg, hexpg⟩
  let η : ℂ → ℝ := fun z ↦ (g z - f z).im / (2 * Real.pi : ℝ)
  have hη_cont : ContinuousOn η D := by
    -- The normalized imaginary-part difference is continuous on `D`.
    simpa [η] using
      (Complex.continuous_im.comp_continuousOn (hcontg.sub hcontf)).div_const (2 * Real.pi : ℝ)
  have hη_image_subset : η '' D ⊆ Set.range (fun k : ℤ ↦ (k : ℝ)) := by
    -- Each pointwise branch difference lands in the integer lattice.
    rintro x ⟨z, hz, rfl⟩
    exact branch_difference_im_div_two_pi_mem_int_cast_range hf' hg' hz
  have hη_image_subsingleton : (η '' D).Subsingleton :=
    preconnected_subset_int_cast_range_subsingleton
      (hConnected.image η hη_cont).isPreconnected hη_image_subset
  have hη_const : ∀ ⦃z w : ℂ⦄, z ∈ D → w ∈ D → η z = η w := by
    intro z w hz hw
    exact hη_image_subsingleton ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
  rcases hConnected.nonempty with ⟨z₀, hz₀⟩
  obtain ⟨k₀, hk₀⟩ := branch_eq_add_two_pi_I_mul_int_at hf' hg' hz₀
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hη_eq_int :
      ∀ ⦃z : ℂ⦄ ⦃k : ℤ⦄, g z = f z + k * (2 * (Real.pi : ℂ) * I) → η z = k := by
    intro z k hk
    have hsub : g z - f z = k * (2 * (Real.pi : ℂ) * I) := by
      rw [hk, add_sub_cancel_left]
    have hk_im : (g z - f z).im = (k : ℝ) * (2 * Real.pi) := by
      calc
        (g z - f z).im = (k * (2 * (Real.pi : ℂ) * I)).im := by rw [hsub]
        _ = (((k : ℤ) • (2 * (Real.pi : ℂ) * I)).im) := by rw [zsmul_eq_mul]
        _ = (k : ℤ) • (2 * (Real.pi : ℂ) * I).im := by rw [Complex.im_zsmul]
        _ = (k : ℝ) * (2 * Real.pi) := by simp
    dsimp [η]
    exact (div_eq_iff htwo_pi_ne).2 hk_im
  refine ⟨k₀, ?_⟩
  intro z hz
  -- Compare the integer attached to `z` with the one attached to the base point `z₀`.
  obtain ⟨k, hk⟩ := branch_eq_add_two_pi_I_mul_int_at hf' hg' hz
  have hk_cast : (k : ℝ) = (k₀ : ℝ) := by
    calc
      (k : ℝ) = η z := (hη_eq_int hk).symm
      _ = η z₀ := hη_const hz hz₀
      _ = (k₀ : ℝ) := hη_eq_int hk₀
  have hk_eq : k = k₀ := Int.cast_injective (α := ℝ) hk_cast
  simpa [hk_eq] using hk

-- Proof sketch: if `g` is another branch, then `(f - g) / (2π i)` is a continuous
-- integer-valued function on the connected set `D`, hence is constant with some value
-- `k : ℤ`; conversely, adding `2π i k` preserves continuity and the defining exponential
-- identity because `Complex.exp` is `2π i`-periodic on integer shifts.
/-- Cartan section03 frozen_0009_Proposition_5_1: once `f` is a branch of the logarithm on a
connected open set `D`, a function `g` is another branch on `D` exactly when it differs from
`f` on `D` by a constant integer multiple of `2π i`. -/
theorem IsLogBranchOn.other_iff_eqOn_add_two_pi_I_mul_int
    {f g : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) :
    IsLogBranchOn g D ↔
      ∃ k : ℤ,
        Set.EqOn g (fun z ↦ f z + k * (2 * Real.pi * Complex.I)) D := by
  constructor
  · intro hg
    -- The forward implication is the connectedness argument from the source proof.
    exact eqOn_add_two_pi_I_mul_int_of_isLogBranchOn hf hg
  · rintro ⟨k, hk⟩
    -- Route correction: rather than re-proving connectedness, reuse it from `hf` and
    -- transport the continuous and exponential identities across the fixed period shift.
    refine ⟨hf.1, hf.2.1, ?_, ?_⟩
    · -- Continuity is preserved by adding a constant and using the pointwise equality on `D`.
      refine ContinuousOn.congr (hf.2.2.1.add continuousOn_const) hk
    · -- The defining exponential identity survives because `exp` is `2π i`-periodic.
      intro z hz
      calc
        exp (g z) = exp (f z + k * (2 * (Real.pi : ℂ) * I)) := by rw [hk hz]
        _ = exp (f z) := by simpa using (Complex.exp_periodic.int_mul k) (f z)
        _ = z := by simpa [Function.comp] using hf.2.2.2 hz

end Complex
