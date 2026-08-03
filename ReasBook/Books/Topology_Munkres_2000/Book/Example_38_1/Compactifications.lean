module

public import Topology_Munkres_2000.Book.Lemma_38_1.InducedCompactification
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Compactification.OnePoint.Basic

public section

open Complex Set

namespace OpenUnitInterval

/-- The one-turn parametrization of the unit circle by the open unit interval. -/
noncomputable def circleMap : Ioo (0 : ℝ) 1 → Circle :=
  fun t ↦ Circle.exp (2 * Real.pi * t.1)

/-- The circle parametrization has the textbook cosine-sine coordinate formula. -/
theorem circleMap_apply (t : Ioo (0 : ℝ) 1) :
    (circleMap t : ℂ) =
      Real.cos (2 * Real.pi * t.1) + Real.sin (2 * Real.pi * t.1) * Complex.I := by
  -- Expand the circle exponential into its cosine-sine coordinates.
  rw [circleMap, Circle.coe_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The one-turn circle parametrization embeds the open unit interval. -/
theorem isEmbedding_circleMap : Topology.IsEmbedding circleMap := by
  -- Identify the parametrization with the standard punctured `AddCircle` chart.
  let chart := AddCircle.openPartialHomeomorphCoe (p := (1 : ℝ)) (a := 0)
  have hsource : chart.source = Ioo (0 : ℝ) 1 := by
    norm_num [chart]
  have hchart : Topology.IsEmbedding (chart.source.restrict chart) :=
    chart.isOpenEmbedding_restrict.isEmbedding
  rw [hsource] at hchart
  have hcomposition : Topology.IsEmbedding
      (AddCircle.homeomorphCircle one_ne_zero ∘ (Ioo (0 : ℝ) 1).restrict chart) :=
    (AddCircle.homeomorphCircle one_ne_zero).isEmbedding.comp hchart
  have hfunctions :
      AddCircle.homeomorphCircle one_ne_zero ∘ (Ioo (0 : ℝ) 1).restrict chart =
        circleMap := by
    funext t
    simp only [Function.comp_apply, Set.restrict_apply]
    change AddCircle.homeomorphCircle one_ne_zero (t.1 : AddCircle (1 : ℝ)) = circleMap t
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, circleMap]
    congr 1
    ring_nf
  rwa [hfunctions] at hcomposition

/-- The open unit interval is noncompact. -/
instance instNoncompactSpace : NoncompactSpace (Ioo (0 : ℝ) 1) := by
  -- A nonempty open interval cannot be compact in a densely ordered space.
  rw [← not_compactSpace_iff]
  intro hcompact
  have hinterval : IsCompact (Ioo (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr hcompact
  have hle : (1 : ℝ) ≤ 0 := isCompact_Ioo_iff.mp hinterval
  norm_num at hle

/-- The open unit interval is locally compact. -/
instance instLocallyCompactSpace : LocallyCompactSpace (Ioo (0 : ℝ) 1) :=
  isOpen_Ioo.locallyCompactSpace

/-- The compactification induced by the one-turn circle parametrization. -/
@[expose]
noncomputable def circleCompactification : Compactification (Ioo (0 : ℝ) 1) :=
  InducedCompactification.compactification circleMap isEmbedding_circleMap

/-- The circle compactification uses the canonical map into the closure of the circle image. -/
theorem circleCompactification_apply (t : Ioo (0 : ℝ) 1) :
    circleCompactification t = InducedCompactification.ofMap circleMap t := by
  -- Unpack the map stored by the induced compactification.
  exact InducedCompactification.compactification_apply circleMap isEmbedding_circleMap t

/-- The canonical one-point compactification of the open unit interval. -/
@[expose]
def onePointCompactification : Compactification (Ioo (0 : ℝ) 1) :=
  Compactification.of (OnePoint (Ioo (0 : ℝ) 1)) OnePoint.some
    OnePoint.isDenseEmbedding_coe

/-- The one-point compactification uses the canonical inclusion into `OnePoint`. -/
theorem onePointCompactification_apply (t : Ioo (0 : ℝ) 1) :
    onePointCompactification t = OnePoint.some t := by
  -- Unpack the canonical inclusion stored by `Compactification.of`.
  exact Compactification.of_apply _ _ _ t


end OpenUnitInterval

end
