import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.III.section10.«0010_Remark_III_4_extra_8»
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.ImageNormalization

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: meromorphicity of the
normalized ratio transports back to meromorphicity of the original map. -/
lemma meromorphicAt_of_normalizedOmittedRatio
    {f : ℂ → ℂ} {ε : ℝ} {a b : ℂ}
    (hε : 0 < ε)
    (hab : a ≠ b)
    (hb : b ∉ f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmer : MeromorphicAt (fun z ↦ (f z - a) / (f z - b)) 0) :
    MeromorphicAt f 0 := by
  let ratio : ℂ → ℂ := fun z ↦ (f z - a) / (f z - b)
  let reconstructed : ℂ → ℂ := fun z ↦ (b * ratio z - a) / (ratio z - 1)
  have hnum : MeromorphicAt (fun z ↦ b * ratio z - a) 0 := by
    -- The numerator is built from the meromorphic ratio by scalar multiplication and subtraction.
    have hmul : MeromorphicAt (fun z ↦ b * ratio z) 0 := by
      simpa [ratio, mul_comm] using
        MeromorphicAt.fun_mul (f := fun _ : ℂ ↦ b) (g := ratio) (x := 0)
          (MeromorphicAt.const b 0) hmer
    exact
      (MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂
        (f := fun z ↦ b * ratio z) (g := fun _ : ℂ ↦ a) (x := 0) (MeromorphicAt.const a 0)).mpr
        hmul
  have hden : MeromorphicAt (fun z ↦ ratio z - 1) 0 := by
    -- The denominator is the same ratio shifted by the constant `1`.
    exact
      (MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂
        (f := ratio) (g := fun _ : ℂ ↦ (1 : ℂ)) (x := 0) (MeromorphicAt.const 1 0)).mpr
        hmer
  have hreconstructed : MeromorphicAt reconstructed 0 := by
    -- Dividing the two meromorphic pieces gives the reconstructed branch.
    simpa [reconstructed] using hnum.div hden
  have hball :
      ball (0 : ℂ) ε \ ({0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    -- Use the punctured ball as the basic neighborhood where the reconstruction identity holds.
    rw [show ball (0 : ℂ) ε \ ({0} : Set ℂ) = ball (0 : ℂ) ε ∩ ({(0 : ℂ)}ᶜ) by
      ext z
      simp [Set.diff_eq]]
    exact Metric.mem_nhdsWithin_iff.mpr ⟨ε, hε, subset_rfl⟩
  have hEq : reconstructed =ᶠ[𝓝[≠] (0 : ℂ)] f := by
    -- The explicit algebraic inverse of the normalized ratio recovers `f` away from the puncture.
    refine Filter.mem_of_superset hball ?_
    intro z hz
    exact (normalizedOmittedRatio_reconstruct hab hz hb).symm
  -- Transport meromorphicity across the eventual equality on the punctured neighborhood.
  exact hreconstructed.congr hEq

