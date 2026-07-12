import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.RepresentationTheory.Basic

open MeasureTheory
open scoped ENNReal

noncomputable section

-- Analogue recall: `Representation.ofDistribMulAction` packages the action, while
-- `DomMulAct.smul_Lp_ae_eq` is the formula API for the translated `L²`-functions.

universe u

section

variable {G : Type u} [Group G] [MeasurableSpace G] (μ : Measure G)
  [SMulInvariantMeasure G G μ] [MeasurableConstSMul G G]

/-- The left regular action is obtained from the domain action by sending `g` to
`DomMulAct.mk g⁻¹`. -/
private def regularRepresentationDomActHom : G →* Gᵈᵐᵃ where
  toFun g := DomMulAct.mk g⁻¹
  map_one' := (congrArg DomMulAct.mk inv_one).trans DomMulAct.mk_one
  map_mul' x y := (congrArg DomMulAct.mk (mul_inv_rev x y)).trans (DomMulAct.mk_mul _ _)

/-- Pull back the canonical `Gᵈᵐᵃ`-action on `L²(G)` along inversion to obtain the left-translation
action of `G` itself. -/
instance :
    MulAction G (G →₂[μ] ℂ) :=
  MulAction.compHom (G →₂[μ] ℂ) regularRepresentationDomActHom

/-- The left-translation action of `G` on `L²(G)` is additive and compatible with the complex
scalar action. -/
instance :
    DistribMulAction G (G →₂[μ] ℂ) :=
  DistribMulAction.compHom (G →₂[μ] ℂ) regularRepresentationDomActHom

/-- The transported left-translation action of `G` on `L²(G)` commutes with complex scalars. -/
instance :
    SMulCommClass G ℂ (G →₂[μ] ℂ) :=
  SMul.comp.smulCommClass regularRepresentationDomActHom

/-- Definition 4-23: when `μ` is Haar measure on a compact group `G`, `regularRepresentation` is
the left regular representation of `G` on `L²(G)`. The construction itself only uses the
left-translation invariance of `μ`. -/
def regularRepresentation :
    Representation ℂ G (G →₂[μ] ℂ) :=
  Representation.ofDistribMulAction ℂ G (G →₂[μ] ℂ)

/-- The transported left-translation action on `L²(G)` sends `f` to the class of
`t ↦ f (s⁻¹ * t)` up to `μ`-a.e. equality. -/
theorem regularRepresentation_smul_ae_eq (s : G) (f : G →₂[μ] ℂ) :
    (s • f : G →₂[μ] ℂ) =ᵐ[μ] fun t : G ↦ f (s⁻¹ * t) := by
  simpa [regularRepresentationDomActHom] using
    (DomMulAct.smul_Lp_ae_eq (regularRepresentationDomActHom s) f)

/-- The regular representation acts by the left-translation formula
`(regularRepresentation s f)(t) = f (s⁻¹ * t)` up to `μ`-a.e. equality. -/
theorem regularRepresentation_apply_ae_eq (s : G) (f : G →₂[μ] ℂ) :
    regularRepresentation μ s f =ᵐ[μ] fun t : G ↦ f (s⁻¹ * t) := by
  simpa [regularRepresentation] using regularRepresentation_smul_ae_eq μ s f

end

section

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsTopologicalGroup G] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [SMulInvariantMeasure G G μ] [MeasurableConstSMul G G]

/-- The transported left-translation action of `G` on `L²(G)` is continuous. -/
instance :
    ContinuousSMul G (G →₂[μ] ℂ) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : ContinuousSMul Gᵈᵐᵃ (G →₂[μ] ℂ) := MeasureTheory.Lp.instContinuousSMulDomMulAct
  have h_regularRepresentationDomActHom :
      Continuous (regularRepresentationDomActHom (G := G)) := by
    simpa [regularRepresentationDomActHom] using
      (DomMulAct.continuous_mk.comp continuous_inv : Continuous fun g : G ↦ DomMulAct.mk g⁻¹)
  refine ⟨?_⟩
  simpa [MulAction.compHom_smul_def] using
    (h_regularRepresentationDomActHom.comp continuous_fst).smul continuous_snd

end
