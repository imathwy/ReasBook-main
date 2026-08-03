module

public import Topology_Munkres_2000.Book.Definition_35_3.AbsoluteRetract
public import Topology_Munkres_2000.Book.Definition_35_2.Extension
public import Topology_Munkres_2000.Book.Exercise_35_5.Retract
public import Mathlib.Topology.Separation.CompletelyRegular

public section

universe u v

/-- A characterization used in Exercise 35.6: a normal space is an absolute retract exactly when
every closed subspace of a normal space homeomorphic to it is a retract of the ambient space. -/
theorem absoluteRetract_iff_closedSubspace {Y : Type v} [TopologicalSpace Y] [T4Space Y] :
    AbsoluteRetract.{u, v} Y ↔
      ∀ {Z : Type u} [TopologicalSpace Z] [T4Space Z] (Y₀ : Set Z)
        (_hY₀ : IsClosed Y₀) (_e : Y ≃ₜ Y₀), Set.IsRetract Y₀ := by
  constructor
  · intro hY Z _ _ Y₀ hY₀ e
    -- Compose the given homeomorphism with the closed subtype inclusion.
    let inclusion : Y → Z := fun y ↦ e y
    have hInclusion : Topology.IsClosedEmbedding inclusion :=
      hY₀.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
    have hRange : Set.range inclusion = Y₀ := by
      ext z
      simp only [inclusion, Set.mem_range]
      constructor
      · rintro ⟨y, rfl⟩
        exact (e y).property
      · intro hz
        exact ⟨e.symm ⟨z, hz⟩, congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)⟩
    -- The defining retract of the range is therefore a retract onto the closed copy.
    rw [← hRange]
    exact hY.isRetract_range inclusion hInclusion
  · intro hClosedCopy
    refine ⟨?_⟩
    intro Z _ _ e he
    -- An embedding is homeomorphic to its range, so the closed-copy hypothesis applies.
    exact hClosedCopy (Set.range e) he.isClosed_range he.isEmbedding.toHomeomorph

namespace UniversalExtensionProperty

/-- Part (a) of Exercise 35.6: a normal space with the universal extension property is an
absolute retract. -/
theorem toAbsoluteRetract {Y : Type v} [TopologicalSpace Y] [T4Space Y]
    (hY : UniversalExtensionProperty.{u, v} Y) : AbsoluteRetract.{u, v} Y := by
  rw [absoluteRetract_iff_closedSubspace]
  intro Z _ _ Y₀ hY₀ e
  -- Extend the inverse homeomorphism from the closed copy to the ambient space.
  obtain ⟨g, hg⟩ := hY.exists_restrict_eq Y₀ hY₀ (e.symm : C(Y₀, Y))
  apply (Set.isRetract_iff Y₀).2
  refine ⟨(e : C(Y, Y₀)).comp g, ?_⟩
  intro y
  -- On the closed copy, the extension agrees with the inverse homeomorphism.
  have hgy := ContinuousMap.congr_fun hg y
  change g y = e.symm y at hgy
  change e (g y) = y
  rw [hgy]
  exact e.apply_symm_apply y

/-- The absolute retract structure supplied by the universal extension property. -/
instance absoluteRetract {Y : Type v} [TopologicalSpace Y] [T4Space Y]
    [UniversalExtensionProperty.{u, v} Y] : AbsoluteRetract.{u, v} Y :=
  toAbsoluteRetract inferInstance

end UniversalExtensionProperty

namespace AbsoluteRetract

/-- Helper for Exercise 35.6: every product of closed unit intervals has the universal
extension property. -/
private theorem universalExtensionProperty_piUnitInterval (J : Type v) :
    UniversalExtensionProperty.{u, v} (J → Set.Icc (0 : ℝ) 1) where
  exists_restrict_eq A hA f := by
    classical
    -- Extend every real-valued coordinate while retaining its interval bounds.
    have hCoordinate : ∀ j : J, ∃ g : C(_, ℝ),
        (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
          g.restrict A =
            ⟨fun a ↦ (f a j : ℝ),
              continuous_subtype_val.comp ((continuous_apply j).comp f.continuous)⟩ := by
      intro j
      apply ContinuousMap.exists_restrict_eq_forall_mem_of_closed
      · intro a
        exact (f a j).property
      · exact Set.nonempty_Icc.mpr zero_le_one
      · exact hA
    choose g hgInterval hgRestrict using hCoordinate
    let gInterval : ∀ j : J, C(_, Set.Icc (0 : ℝ) 1) := fun j ↦
      ⟨fun x ↦ ⟨g j x, hgInterval j x⟩, (g j).continuous.subtype_mk _⟩
    -- Assemble the coordinate extensions into one map to the cube.
    refine ⟨ContinuousMap.piEquiv _ _ (gInterval), ?_⟩
    ext a j
    exact ContinuousMap.congr_fun (hgRestrict j) a

/-- Helper for Exercise 35.6: evaluation by all continuous unit-interval-valued functions is a
closed embedding for a compact normal space. -/
private theorem isClosedEmbedding_continuousMapEvaluation_of_compact
    {Y : Type v} [TopologicalSpace Y] [T4Space Y] [CompactSpace Y] :
    Topology.IsClosedEmbedding (fun y (f : C(Y, Set.Icc (0 : ℝ) 1)) ↦ f y) := by
  -- Coordinatewise continuity gives continuity into the product cube.
  have hContinuous : Continuous (fun y (f : C(Y, Set.Icc (0 : ℝ) 1)) ↦ f y) :=
    continuous_pi fun f ↦ f.continuous
  apply hContinuous.isClosedEmbedding
  intro y₁ y₂ hEvaluation
  -- Complete regularity supplies a coordinate separating distinct points.
  by_contra hy
  obtain ⟨f, hf, hSeparate⟩ := separatesPoints_continuous_of_t35Space_Icc hy
  have hEqual := congrFun hEvaluation (⟨f, hf⟩ : C(Y, Set.Icc (0 : ℝ) 1))
  exact hSeparate hEqual

/-- Exercise 35.6. A compact normal absolute retract has the universal extension property. -/
theorem universalExtensionProperty_of_compact {Y : Type v} [TopologicalSpace Y] [T4Space Y]
    [CompactSpace Y] (hY : AbsoluteRetract.{v, v} Y) : UniversalExtensionProperty.{u, v} Y := by
  let evaluation : C(Y, C(Y, Set.Icc (0 : ℝ) 1) → Set.Icc (0 : ℝ) 1) :=
    ContinuousMap.pi fun f ↦ f
  have hEvaluation : Topology.IsClosedEmbedding evaluation :=
    isClosedEmbedding_continuousMapEvaluation_of_compact
  -- The absolute retract hypothesis supplies a retraction from the cube onto the image of `Y`.
  obtain ⟨r, hr⟩ := (Set.isRetract_iff (Set.range evaluation)).1
    (hY.isRetract_range evaluation hEvaluation)
  have hRange : UniversalExtensionProperty.{u, v} (Set.range evaluation) := by
    letI : UniversalExtensionProperty.{u, v}
        (C(Y, Set.Icc (0 : ℝ) 1) → Set.Icc (0 : ℝ) 1) :=
      universalExtensionProperty_piUnitInterval C(Y, Set.Icc (0 : ℝ) 1)
    -- A retract of the cube inherits its universal extension property.
    apply UniversalExtensionProperty.ofRetract
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Set.range evaluation, C(Y, Set.Icc (0 : ℝ) 1) → Set.Icc (0 : ℝ) 1)) r
    exact ContinuousMap.ext hr
  letI : UniversalExtensionProperty.{u, v} (Set.range evaluation) := hRange
  -- Finally transport the extension property across the evaluation homeomorphism onto its range.
  exact UniversalExtensionProperty.ofHomeo hEvaluation.isEmbedding.toHomeomorph

/-- The universal extension property supplied by a compact absolute retract. -/
instance universalExtensionProperty {Y : Type v} [TopologicalSpace Y] [T4Space Y]
    [CompactSpace Y] [AbsoluteRetract.{v, v} Y] : UniversalExtensionProperty.{u, v} Y :=
  universalExtensionProperty_of_compact inferInstance

end AbsoluteRetract
