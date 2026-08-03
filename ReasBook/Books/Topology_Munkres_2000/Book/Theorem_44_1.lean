module

public import Topology_Munkres_2000.Book.Definition_44_1.PeanoSpace
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.MetricSpace.HausdorffAlexandroff

public section

/-- Helper for Theorem 44.1: the canonical inclusion of the ternary Cantor set in the unit
interval. -/
private def cantorSetToUnitInterval (x : cantorSet) : unitInterval :=
  -- Cantor-set membership supplies the required unit-interval bounds.
  ⟨x, cantorSet_subset_unitInterval x.property⟩

/-- Helper for Theorem 44.1: the canonical inclusion of the Cantor set in the unit interval is
continuous. -/
private lemma continuous_cantorSetToUnitInterval : Continuous cantorSetToUnitInterval := by
  -- Continuity is inherited from the two successive subtype inclusions into `ℝ`.
  exact Continuous.subtype_mk continuous_subtype_val
    (fun x ↦ cantorSet_subset_unitInterval x.property)

/-- Helper for Theorem 44.1: the canonical inclusion of the Cantor set in the unit interval is a
closed embedding. -/
private lemma isClosedEmbedding_cantorSetToUnitInterval :
    Topology.IsClosedEmbedding cantorSetToUnitInterval := by
  -- Compactness of the Cantor set upgrades the continuous injection to a closed embedding.
  letI : CompactSpace cantorSet := isCompact_iff_compactSpace.mp isCompact_cantorSet
  apply continuous_cantorSetToUnitInterval.isClosedEmbedding
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : unitInterval ↦ (z : ℝ)) hxy)

/-- Helper for Theorem 44.1: a continuous surjection from the Cantor set to a Tietze extension
space extends to a continuous surjection from the unit interval. -/
private lemma existsContinuousSurjectionUnitIntervalOfCantorSet
    {Y : Type*} [TopologicalSpace Y] [TietzeExtension.{0} Y]
    (g : C(cantorSet, Y)) (hg : Function.Surjective g) :
    ∃ f : C(unitInterval, Y), Function.Surjective f := by
  -- Extend `g` across the closed Cantor-set inclusion.
  obtain ⟨f, hf⟩ := g.exists_extension isClosedEmbedding_cantorSetToUnitInterval
  refine ⟨f, ?_⟩
  intro y
  -- A preimage under `g` remains a preimage because the extension agrees on the Cantor set.
  obtain ⟨x, hx⟩ := hg y
  refine ⟨cantorSetToUnitInterval x, ?_⟩
  have hRestriction :
      (f.comp
        ⟨cantorSetToUnitInterval,
          isClosedEmbedding_cantorSetToUnitInterval.continuous⟩) x = g x := by
    -- Evaluate the bundled restriction identity at the chosen Cantor point.
    exact congrArg (fun k : C(cantorSet, Y) ↦ k x) hf
  exact hRestriction.trans hx

/-- Theorem 44.1. There exists a continuous map from the closed unit interval onto its square. -/
theorem existsContinuousSurjectiveUnitSquare :
    ∃ f : C(unitInterval, unitInterval × unitInterval), Function.Surjective f := by
  -- Hausdorff–Alexandroff replaces the source's explicit polygonal approximants with a
  -- continuous surjection from Cantor space onto the compact metric square.
  obtain ⟨f, hfContinuous, hfSurjective⟩ :=
    exists_nat_bool_continuous_surjective_of_compact (unitInterval × unitInterval)
  have hCantorContinuous :
      Continuous (fun x : cantorSet ↦ f (cantorSetHomeomorphNatToBool x)) :=
    hfContinuous.comp cantorSetHomeomorphNatToBool.continuous
  have hCantorSurjective :
      Function.Surjective (fun x : cantorSet ↦ f (cantorSetHomeomorphNatToBool x)) :=
    hfSurjective.comp cantorSetHomeomorphNatToBool.surjective
  let g : C(cantorSet, unitInterval × unitInterval) :=
    ⟨fun x ↦ f (cantorSetHomeomorphNatToBool x), hCantorContinuous⟩
  -- Tietze extension preserves surjectivity because it agrees with `g` on the Cantor subset.
  exact existsContinuousSurjectionUnitIntervalOfCantorSet g hCantorSurjective

/-- The unit square is a Peano space. -/
instance instPeanoSpaceUnitSquare : PeanoSpace (unitInterval × unitInterval) where
  toT2Space := inferInstance
  exists_surjective := existsContinuousSurjectiveUnitSquare
