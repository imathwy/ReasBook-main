import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_23
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5

open MeasureTheory
open scoped ENNReal

noncomputable section

section

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [MeasurableMul G] [CompactSpace G]

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

-- Mathlib recall: `Lp.instContinuousSMulDomMulAct` gives continuity for the
-- canonical domain action; this item uses the transported left-translation
-- action packaged by `regularRepresentation`.

/-- Lemma 4-48: for a compact group `G` and `h : L²(G)`, the orbit map
`y ↦ regularRepresentation μG y h`, i.e. `y ↦ (x ↦ h (y⁻¹ * x))`, is continuous as a map from `G`
to `L²(G)`. -/
theorem continuous_regularRepresentation_orbit (h : L²G) :
    Continuous (fun y : G ↦ regularRepresentation μG y h) := by
  simpa [regularRepresentation] using
    (continuous_id.smul continuous_const : Continuous fun y : G ↦ y • h)

end
