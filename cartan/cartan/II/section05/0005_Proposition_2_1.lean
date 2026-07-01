import Mathlib
import cartan.II.section05.«0003_Lemma_II_1_extra_3»
import cartan.II.section05.«0004_Definition_II_1_extra_4»
import cartan.II.section05.«0014_Remark_II_1_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

-- Proof sketch: if `ω = dF` on `D`, then the curve integral along any closed path is the endpoint
-- difference `F (γ 1) - F (γ 0)`, hence vanishes. Conversely, on each connected component of the
-- open set `D`, fix a base point, define the componentwise primitive by integrating `ω` along a
-- piecewise differentiable path from that base point, use loop-vanishing to show
-- path-independence, and then glue these componentwise primitives across the clopen connected
-- components of `D`.
/-- Proposition 2.1: for a continuous `G`-valued differential form on an open set `D`, the form
has a primitive on `D` if and only if its integral along every piecewise differentiable closed
path contained in `D` is zero. -/
theorem hasPrimitiveOn_iff_curveIntegral_eq_zero_loops_of_isOpen
    {D : Set E} (hD_open : IsOpen D)
    {ω : E → E →L[ℝ] G} (hω : ContinuousOn ω D) :
    HasPrimitiveOn D ω ↔
      ∀ {z₀ : E} (γ : Path z₀ z₀) (hγ_piecewise : γ.IsPiecewiseDifferentiable)
        (hγD : Set.range γ ⊆ D),
        ∫ᶜ z in γ, ω z = 0 := by
  constructor
  · intro hprimitive z₀ γ hγ_piecewise hγD
    rcases hprimitive with ⟨primitive, hprimitive⟩
    calc
      ∫ᶜ z in γ, ω z = hprimitive.alongPath γ hγD 1 - hprimitive.alongPath γ hγD 0 := by
        simpa using
          (hprimitive.isPrimitiveAlongPath hD_open γ hγD).curveIntegral_eq_endpoint_sub
            hγ_piecewise
      _ = primitive z₀ - primitive z₀ := by
        simp [IsPrimitiveOn.alongPath_apply]
      _ = 0 := sub_self _
  · sorry

end
