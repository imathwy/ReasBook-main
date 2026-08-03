module

public import Topology_Munkres_2000.Book.Theorem_34_2
public import Mathlib.Topology.Separation.CompletelyRegular

public section

open scoped unitInterval

universe u

/-- Helper for Theorem 34.3: the real-valued coercions of all continuous maps to `I`
separate points from closed sets in a completely regular space. -/
private lemma continuousUnitIntervalMapsSeparatePointsFromClosedSets
    {X : Type u} [TopologicalSpace X] [CompletelyRegularSpace X] :
    SeparatesPointsFromClosedSets
      (fun f : C(X, I) ↦ ContinuousMap.comp
        ⟨(Subtype.val : I → ℝ), continuous_subtype_val⟩ f) := by
  -- Reflect a standard complete-regularity separator so it is positive at the point.
  rw [SeparatesPointsFromClosedSets.iff_closedSet]
  intro x A hA hxA
  obtain ⟨g, hg, hgx, hgA⟩ :=
    CompletelyRegularSpace.completely_regular x A hA hxA
  let gMap : C(X, I) := ⟨g, hg⟩
  let reflection : C(I, I) :=
    ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  let separator : C(X, I) := reflection.comp gMap
  refine ⟨separator, ?_, ?_⟩
  · -- Reflection sends the value zero at `x` to the positive value one.
    simp [separator, reflection, gMap, ContinuousMap.comp_apply, hgx]
  · -- Reflection sends the constant value one on `A` to zero.
    intro y hyA
    simp [separator, reflection, gMap, ContinuousMap.comp_apply, hgA hyA]

/-- Evaluation on all continuous unit-interval-valued maps embeds a `T₃.₅` space into their
product. -/
theorem isEmbedding_continuousMapEvaluation (X : Type u) [TopologicalSpace X] [T35Space X] :
    Topology.IsEmbedding (fun x (f : C(X, I)) ↦ f x) := by
  -- Regard every interval-valued coordinate as a bounded real-valued coordinate.
  let intervalInclusion : C(I, ℝ) :=
    ⟨(Subtype.val : I → ℝ), continuous_subtype_val⟩
  let realCoordinates : C(X, I) → C(X, ℝ) :=
    fun f ↦ intervalInclusion.comp f
  have h_range : ∀ f x, realCoordinates f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro f x
    exact (f x).property
  -- Theorem 34.2 packages these coordinates back into the interval product.
  simpa [realCoordinates, intervalInclusion] using
    isEmbedding_piIcc_of_neighborhood_functions realCoordinates
      continuousUnitIntervalMapsSeparatePointsFromClosedSets h_range

/-- Theorem 34.3: In Munkres's convention, a space is completely regular exactly when it embeds
into a product of copies of the unit interval. -/
theorem t35Space_iff_exists_isEmbedding_piUnitInterval (X : Type u) [TopologicalSpace X] :
    T35Space X ↔ ∃ (J : Type u) (F : X → J → I), Topology.IsEmbedding F := by
  constructor
  · -- Evaluate at every continuous interval-valued map to obtain the product embedding.
    intro hX
    letI : T35Space X := hX
    exact ⟨C(X, I), fun x f ↦ f x, isEmbedding_continuousMapEvaluation X⟩
  · -- Pull complete regularity and the separation axiom back along the given embedding.
    rintro ⟨J, F, hF⟩
    exact hF.t35Space

end
