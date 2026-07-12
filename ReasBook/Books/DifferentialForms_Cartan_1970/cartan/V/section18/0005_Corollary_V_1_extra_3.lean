import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- The source-facing compact-majorant hypothesis is bridged to the canonical mathlib owner
-- `SummableLocallyUniformlyOn`, and holomorphicity of the sum is then recovered from
-- `SummableLocallyUniformlyOn.differentiableOn`.

/-- Corollary V.1-extra-3. If a series of holomorphic functions on an open set `D` is normally
convergent on every compact subset of `D`, then its sum is holomorphic on `D`. -/
theorem differentiableOn_tsum_of_normally_convergent_on_compacts
    {D : Set ℂ} (hD : IsOpen D) {f : ℕ → ℂ → ℂ}
    (hf : ∀ n : ℕ, DifferentiableOn ℂ (f n) D)
    (hnorm :
      ∀ K : Set ℂ, K ⊆ D → IsCompact K →
        ∃ u : ℕ → NNReal,
          Summable (fun n : ℕ ↦ (u n : ℝ)) ∧
          ∀ n z, z ∈ K → ‖f n z‖ ≤ (u n : ℝ)) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, f n z) D := by
  let hsum : SummableLocallyUniformlyOn f D :=
    SummableLocallyUniformlyOn_of_locally_bounded hD fun K hKD hK ↦ by
      obtain ⟨u, hu, hbound⟩ := hnorm K hKD hK
      exact ⟨fun n ↦ (u n : ℝ), hu, hbound⟩
  exact hsum.differentiableOn hD fun n z hz ↦ (hf n z hz).differentiableAt (hD.mem_nhds hz)
