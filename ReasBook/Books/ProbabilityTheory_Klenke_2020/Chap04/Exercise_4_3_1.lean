import ProbabilityTheory_Klenke_2020.Chap04.Theorem_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

-- Proof sketch: use the chapter's canonical notion `RiemannIntegrableOnUnitInterval`. For the
-- forward direction, use the classical criterion that a bounded Riemann integrable function is
-- a.e. continuous on `[0,1]`. For the reverse direction, apply
-- `BoxIntegral.integrable_of_bounded_and_ae_continuous` to the lifted function `fun x ↦ f (x 0)`
-- and transport the boundedness and a.e.-continuity hypotheses from `[0,1]` to the canonical
-- one-dimensional box model.
private theorem exists_norm_bound_on_unitInterval {f : ℝ → ℝ}
    (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C := by
  rcases hb.exists_norm_le with ⟨C, hC⟩
  exact ⟨C, fun x hx ↦ hC (f x) (Set.mem_image_of_mem f hx)⟩

/-- Exercise 4.3.1: for a bounded function on `[0,1]`, Riemann integrability on `[0,1]` in the
chapter's canonical one-dimensional box model is equivalent to `volume`-almost everywhere
continuity on `[0,1]`. -/
theorem riemannIntegrableOn_unitInterval_iff_aeContinuousWithinAt
    {f : ℝ → ℝ} (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    RiemannIntegrableOnUnitInterval f ↔
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x := by
  constructor
  · intro hf
    sorry
  · intro hc
    have hb' : ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C :=
      exists_norm_bound_on_unitInterval hb
    sorry
