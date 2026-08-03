module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Covering.Quotient

public section

/- Theorem 60.3 (1): The real projective plane is compact. -/
#check (inferInstance : CompactSpace RealProjectivePlane)

namespace RealProjectivePlane

/-- Helper for Theorem 60.3: the unit sphere in Euclidean three-space. -/
private abbrev UnitSphereThree :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Helper for Theorem 60.3: `Bool` acts on the unit sphere by the identity and antipode. -/
private noncomputable instance antipodalBoolVAdd : VAdd Bool UnitSphereThree :=
  -- Encode the two transformations by the two Boolean values.
  ⟨fun b x ↦ if b = true then -x else x⟩

/-- Helper for Theorem 60.3: the false Boolean fixes every sphere point. -/
@[simp]
private lemma false_vadd_sphere (x : UnitSphereThree) : false +ᵥ x = x := by
  -- The false branch of the action is the identity.
  rfl

/-- Helper for Theorem 60.3: the true Boolean sends every sphere point to its antipode. -/
@[simp]
private lemma true_vadd_sphere (x : UnitSphereThree) : true +ᵥ x = -x := by
  -- The true branch of the action is negation.
  rfl

/-- Helper for Theorem 60.3: the antipodal Boolean action respects Boolean addition. -/
private lemma antipodalBool_add_vadd (b c : Bool) (x : UnitSphereThree) :
    (b + c) +ᵥ x = b +ᵥ c +ᵥ x := by
  -- Check the four elements of the two-element group directly.
  cases b
  · cases c
    · have hbc : false + false = false := by decide
      rw [hbc]
      simp only [false_vadd_sphere]
    · have hbc : false + true = true := by decide
      rw [hbc]
      simp only [false_vadd_sphere, true_vadd_sphere]
  · cases c
    · have hbc : true + false = true := by decide
      rw [hbc]
      simp only [false_vadd_sphere, true_vadd_sphere]
    · have hbc : true + true = false := by decide
      rw [hbc]
      simp only [false_vadd_sphere, true_vadd_sphere, neg_neg]

/-- Helper for Theorem 60.3: the Boolean identity acts trivially on the sphere. -/
private lemma antipodalBool_zero_vadd (x : UnitSphereThree) : (0 : Bool) +ᵥ x = x := by
  -- Boolean zero is the false deck transformation.
  exact false_vadd_sphere x

/-- Helper for Theorem 60.3: the identity-antipode operation is an additive action. -/
private noncomputable instance antipodalBoolAction : AddAction Bool UnitSphereThree :=
  -- Package the two action laws proved above.
  { add_vadd := antipodalBool_add_vadd
    zero_vadd := antipodalBool_zero_vadd }

/-- Helper for Theorem 60.3: every fixed Boolean deck transformation is continuous. -/
private lemma continuous_antipodalBoolVAdd (b : Bool) :
    Continuous fun x : UnitSphereThree ↦ b +ᵥ x := by
  -- Each action map is either the identity or continuous negation.
  cases b
  · exact continuous_id
  · exact continuous_neg

/-- Helper for Theorem 60.3: the antipodal Boolean action is continuous in the sphere variable. -/
private instance antipodalBoolContinuousConstVAdd : ContinuousConstVAdd Bool UnitSphereThree :=
  -- Supply the pointwise continuity theorem to the action API.
  ⟨continuous_antipodalBoolVAdd⟩

/-- Helper for Theorem 60.3: each Boolean deck transformation is injective. -/
private lemma antipodalBool_left_cancel (b : Bool) (x y : UnitSphereThree)
    (h : b +ᵥ x = b +ᵥ y) : x = y := by
  -- Identity is injective, while injectivity of negation follows by negating both sides.
  cases b
  · simpa using h
  · simpa using congrArg Neg.neg h

/-- Helper for Theorem 60.3: no sphere point makes two Boolean deck transformations agree. -/
private lemma antipodalBool_right_cancel (b c : Bool) (x : UnitSphereThree)
    (h : b +ᵥ x = c +ᵥ x) : b = c := by
  -- Unequal Boolean transformations would identify a unit vector with its antipode.
  cases b
  · cases c
    · rfl
    · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h)
  · cases c
    · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h.symm)
    · rfl

/-- Helper for Theorem 60.3: the antipodal Boolean action is cancellative. -/
private instance antipodalBoolIsCancelVAdd : IsCancelVAdd Bool UnitSphereThree :=
  -- Package injectivity of action maps and freeness of the action.
  { left_cancel' := antipodalBool_left_cancel
    right_cancel' := antipodalBool_right_cancel }

/-- Helper for Theorem 60.3: Boolean orbits are precisely equal-or-antipodal pairs. -/
private lemma mem_antipodalBoolOrbit_iff (x y : UnitSphereThree) :
    x ∈ AddAction.orbit Bool y ↔ y = x ∨ y = -x := by
  -- Expand an orbit witness, then inspect the only two group elements.
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · left
      simpa using hb
    · right
      simpa using congrArg Neg.neg hb
  · rintro (rfl | rfl)
    · use false
      simp
    · use true
      simp

/-- Helper for Theorem 60.3: the sphere projection is the quotient covering associated to the
antipodal Boolean action. -/
private lemma quotientMap_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap quotientMap Bool := by
  -- Match the explicit quotient fibers with Boolean orbits and invoke the finite-action API.
  refine quotientMap_isQuotientMap.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd ?_
  intro x y
  exact (quotientMap_eq_iff x y).trans (mem_antipodalBoolOrbit_iff x y).symm

/-- Theorem 60.3: The quotient projection from `S²` to the real projective plane is a covering
map in mathlib's sense. -/
theorem quotientMap_isCoveringMap : IsCoveringMap quotientMap := by
  -- Forget the deck-group structure from the stronger quotient-covering package.
  exact quotientMap_isAddQuotientCoveringMap.isCoveringMap

/-- Helper for Theorem 60.3: the covering projection transfers the sphere charts to the real
projective plane. -/
noncomputable instance instChartedSpaceOfQuotientMap :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) RealProjectivePlane :=
  quotientMap_isCoveringMap.isLocalHomeomorph.chartedSpace
    quotientMap_isQuotientMap.surjective

/-- Helper for Theorem 60.3: the kernel relation of the sphere projection is closed. -/
private lemma quotientMap_fiberRelation_isClosed :
    IsClosed {q : UnitSphereThree × UnitSphereThree |
      quotientMap q.1 = quotientMap q.2} := by
  -- Split each fiber into its diagonal and antipodal graph, both closed equalizers.
  simpa only [quotientMap_eq_iff, Set.setOf_or, Function.comp_apply] using
    (isClosed_eq continuous_snd continuous_fst).union
      (isClosed_eq continuous_snd (continuous_neg.comp continuous_fst))

/-- The Hausdorff assertion in Theorem 60.3 for the real projective plane. -/
instance instT2Space : T2Space RealProjectivePlane := by
  -- Transfer closedness of the fiber relation across the open quotient map.
  exact (t2Space_iff_of_isOpenQuotientMap
    quotientMap_isAddQuotientCoveringMap.isOpenQuotientMap).mpr
      quotientMap_fiberRelation_isClosed

/-- The countable-basis assertion in Theorem 60.3 for the real projective plane. -/
instance instSecondCountableTopology : SecondCountableTopology RealProjectivePlane := by
  -- Images of a countable basis form a basis under this open quotient projection.
  exact quotientMap_isQuotientMap.secondCountableTopology
    quotientMap_isAddQuotientCoveringMap.isOpenQuotientMap.isOpenMap

/-- The surface assertion in Theorem 60.3 for the real projective plane. -/
instance instTopologicalManifold : TopologicalManifold 2 RealProjectivePlane where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance

/- Theorem 60.3 (4), in the canonical surface API of Definitions 36.2 and 60.1. -/
#check (inferInstance : TopologicalManifold 2 RealProjectivePlane)

/-- The compact-surface assertion of Theorem 60.3. -/
theorem isCompactSurface :
    CompactSpace RealProjectivePlane ∧ TopologicalManifold 2 RealProjectivePlane :=
  ⟨inferInstance, inferInstance⟩

/-- The quotient projection from `S²` to the real projective plane is surjective. -/
theorem quotientMap_surjective : Function.Surjective quotientMap :=
  quotientMap_isQuotientMap.surjective

/-- The surjective covering-map assertion in Theorem 60.3 for the canonical quotient map from
`S²` to the real projective plane. -/
theorem quotientMap_isMunkresCoveringMap :
    IsCoveringMap quotientMap ∧ Function.Surjective quotientMap :=
  ⟨quotientMap_isCoveringMap, quotientMap_surjective⟩

end RealProjectivePlane
