import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

-- Proof sketch: since `D` is simply connected, every piecewise differentiable loop in `D` is
-- homotopic in `D` to a constant loop; apply Theorem `2'` to deduce that the integral of `ω`
-- around any such loop vanishes. Then use Proposition `2.1` on the open set `D` to
-- conclude that `ω` admits a global primitive on `D`.
/-- Theorem 3: a continuous closed complex differential form on a simply connected open set admits
a global primitive on that set. -/
theorem hasPrimitiveOn_of_isOpen_of_isSimplyConnected_of_isClosedOn
    {D : Set ℂ} (hD_open : IsOpen D) (hD_sc : IsSimplyConnected D)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω_cont : ContinuousOn ω D)
    (hω_closed : IsClosedOn ω D) :
    HasPrimitiveOn D ω := by
  rw [hasPrimitiveOn_iff_curveIntegral_eq_zero_loops_of_isOpen hD_open hω_cont]
  intro z₀ γ hγ_piecewise hγD
  obtain ⟨F, hF⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hD_sc).2 z₀ γ
      (fun t ↦ hγD ⟨t, rfl⟩)
  have hγ_homotopic : ClosedPathHomotopicIn D γ (Path.refl z₀) := by
    refine ⟨{ toHomotopy := F.toHomotopy, prop' := ?_ }⟩
    intro t
    change IsClosedPathIn D ((F.eval t : Path z₀ z₀) : C(I, ℂ))
    refine ⟨(F.eval t).isClosedPath, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hF (t, s)
  have hγ_integrable : CurveIntegrable ω γ :=
    Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      hω_cont hγ_piecewise hγD
  calc
    ∫ᶜ z in γ, ω z = ∫ᶜ z in Path.refl z₀, ω z := by
      simpa using
        Path.curveIntegral_eq_of_homotopic_closed_paths_of_closed_form hγ_homotopic
          hγ_piecewise (Path.isPiecewiseDifferentiable_refl z₀)
          hγ_integrable (CurveIntegrable.refl ω z₀) hω_closed
    _ = 0 := by
      simp
