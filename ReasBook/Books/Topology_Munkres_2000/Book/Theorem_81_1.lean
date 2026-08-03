module

public import Topology_Munkres_2000.Book.Theorem_81_1.CompactCriterion
public import Topology_Munkres_2000.Book.Theorem_81_1.Instances

public section

open Set

universe u v

/-- Theorem 81.1. A free continuous action on a locally compact Hausdorff space whose
compact subsets meet only finitely many of their translates is properly discontinuous,
and its orbit space is locally compact and Hausdorff. -/
theorem properlyDiscontinuous_and_orbitSpace_locallyCompact_t2
    {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X] [IsCancelSMul G X]
    (hcompact : ∀ {C : Set X}, IsCompact C →
      {g : G | (C ∩ (g • ·) '' C).Nonempty}.Finite) :
    ProperlyDiscontinuousMulAction G X ∧
      LocallyCompactSpace (Quotient (MulAction.orbitRel G X)) ∧
      T2Space (Quotient (MulAction.orbitRel G X)) := by
  have hproper : ProperlyDiscontinuousSMul G X :=
    properlyDiscontinuousSMul_iff_compact_inter_self.mpr hcompact
  -- Local instance justification (proof-local temporary data): conclusion instances use `hproper`.
  letI : ProperlyDiscontinuousSMul G X := hproper
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/- Theorem 81.1 (1): Under the stated compact-translate condition and freeness assumptions,
the action is properly discontinuous in the neighborhood-disjointness sense. -/
#check ProperlyDiscontinuousSMul.toProperlyDiscontinuousMulAction

/- Theorem 81.1 (2): The orbit space of the locally compact space is locally compact. -/
#check MulAction.instLocallyCompactSpaceOrbitRelQuotient

/- Theorem 81.1 (3): The orbit space of the locally compact Hausdorff space is Hausdorff. -/
#check t2Space_of_properlyDiscontinuousSMul_of_t2Space

/- The source's diagonal compact-translate condition is exactly the canonical
`ProperlyDiscontinuousSMul` condition. -/
#check properlyDiscontinuousSMul_iff_compact_inter_self
