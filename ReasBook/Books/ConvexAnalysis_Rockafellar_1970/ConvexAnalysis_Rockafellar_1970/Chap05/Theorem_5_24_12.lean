import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_6

noncomputable section

open scoped RealInnerProductSpace Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace SetRel

/-- Theorem 5.24.12 (1): maximal cyclically monotone relations are exactly the relations that are
the full subdifferential graph of a closed proper convex function, stated at the intrinsic
pairing-parametric owner layer. -/
theorem maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
    (ρ : SetRel E Y) :
    MaxCMon[𝕜](ρ) ↔
      ∃ f : E → WithBotTop 𝕜,
        IsClosedProperConvex[𝕜] f ∧ gph∂[Y](f) = ρ := sorry

end SetRel

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [_root_.FiniteDimensional ℝ E]

/-- Finite-dimensional real inner-product spaces are complete, so the intrinsic pairing-valued
subdifferential graph owner is available in this item file. -/
local instance finiteDimensionalCompleteSpace : CompleteSpace E :=
  _root_.FiniteDimensional.complete ℝ E

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "subgradGraph" =>
  (fun f : E → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ E _ _ _ f E (by infer_instance))

namespace SetRel

-- Proof sketch: compare two closed proper convex functions with the same intrinsic
-- pairing-level subdifferential graph. The source argument first shows, via inclusion of pointwise
-- subdifferentials, that their directional derivatives agree on the relative interior of the
-- effective domain, hence the functions differ there by a constant; conjugation then extends the
-- same constant to the whole space.
/-- Theorem 5.24.12 (2): a closed proper convex function on a finite-dimensional real
inner-product space is uniquely determined by its intrinsic pairing-level subdifferential graph up
to an additive real constant. -/
theorem eq_add_const_of_gphSubdiff_eq_of_isClosedProperConvex
    {f g : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hgraph : subgradGraph f = subgradGraph g) :
    ∃ α : ℝ, g = fun x ↦ f x + α := sorry

end SetRel

end
