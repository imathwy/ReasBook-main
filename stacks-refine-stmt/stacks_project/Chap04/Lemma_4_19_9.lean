import stacks_project.Chap04.Lemma_4_19_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I]

section SourceFacing

variable [HasSpanCocones I]

/- Domain-style sampling for Lemma 4.19.9:
- source-facing hypotheses: `HasSpanCocones` and the explicit postcomposition-equalizer
  condition
- core owner declarations: `connected_components_are_filtered`, `CategoryTheory.decomposedEquiv`,
  `preservesLimitsOfShape_colim_grothendieck`, and mathlib's
  `filtered_colim_preservesFiniteLimits_of_types`
- target layer here: `bridge/view`, namely a `PreservesLimitsOfShape` theorem for connected finite
  shapes obtained from the filtered connected-component owner.
-/

/- Companion recalls: the componentwise filtered owner and the Grothendieck gluing theorem are the
canonical upstream ingredients for this bridge file. -/
recall filtered_colim_preservesFiniteLimits_of_types
recall preservesLimitsOfShape_colim_grothendieck

/-- Core bridge theorem: if every connected component of `I` is filtered, then colimits of
`Type`-valued diagrams on `I` preserve finite connected limits. The intended proof factors the
canonical decomposition `CategoryTheory.decomposedEquiv` through the componentwise filtered owner
theorem `filtered_colim_preservesFiniteLimits_of_types`. -/
private theorem componentwiseFiltered_preservesFiniteConnectedLimitsOfTypes
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    [∀ j : ConnectedComponents I, IsFiltered j.Component] :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  sorry

/-- Lemma 4.19.9: assume every span in `I` admits a commuting cocone and every parallel pair in
`I` becomes equal after postcomposition. Then colimits over `I` commute with finite connected
limits in the category of sets. This is the source-faithful statement obtained by combining the
connected-component decomposition from Lemma 4.19.8 with the canonical mathlib result that
filtered colimits in `Type` commute with finite limits. -/
theorem colimit_preserves_finite_connected_limits_of_types
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  let _ (j : ConnectedComponents I) : IsFiltered j.Component :=
    connected_components_are_filtered hMap j
  exact componentwiseFiltered_preservesFiniteConnectedLimitsOfTypes J

-- Proof sketch: specialize the finite-connected-limit statement to the walking cospan.
/-- Under the hypotheses of Lemma 4.19.8, colimits of sets over `I` preserve pullbacks. -/
theorem colimit_preserves_pullbacks_of_types
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) := by
  simpa using colimit_preserves_finite_connected_limits_of_types WalkingCospan hMap

-- Proof sketch: specialize the finite-connected-limit statement to the walking parallel pair.
/-- Under the hypotheses of Lemma 4.19.8, colimits of sets over `I` preserve equalizers. -/
theorem colimit_preserves_equalizers_of_types
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) := by
  simpa using colimit_preserves_finite_connected_limits_of_types WalkingParallelPair hMap

end SourceFacing

section FilteredOrEmpty

variable [IsFilteredOrEmpty I]

/-- If `I` is filtered or empty, then it satisfies the hypotheses of Lemma 4.19.8, so the
source-faithful statement above specializes to the traditional filtered-or-empty formulation. -/
theorem filtered_or_empty_colimit_preserves_finite_connected_limits_of_types
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  let h :
      PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) :=
    colimit_preserves_finite_connected_limits_of_types J
      (fun {_ _} f g ↦ IsFilteredOrEmpty.cocone_maps f g)
  exact h

/-- Filtered-or-empty colimits of sets preserve fibre products. -/
theorem filtered_or_empty_colimit_preserves_pullbacks_of_types :
    PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) := by
  let h :
      PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) :=
    filtered_or_empty_colimit_preserves_finite_connected_limits_of_types WalkingCospan
  exact h

/-- Filtered-or-empty colimits of sets preserve equalizers. -/
theorem filtered_or_empty_colimit_preserves_equalizers_of_types :
    PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) := by
  let h :
      PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) :=
    filtered_or_empty_colimit_preserves_finite_connected_limits_of_types WalkingParallelPair
  exact h

end FilteredOrEmpty

end CategoryTheory.Limits
