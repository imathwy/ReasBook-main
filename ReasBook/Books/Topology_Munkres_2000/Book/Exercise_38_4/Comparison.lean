module

public import Topology_Munkres_2000.Book.Theorem_38_2.RealExtension
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

universe u v

namespace Compactification

variable {X : Type u} [TopologicalSpace X] [T35Space X]

/-- The canonical continuous map from the Stone–Čech compactification to a compactification
of the same space. -/
noncomputable def stoneCechComparison (C : Compactification.{u, v} X) :
    ContinuousMap (stoneCech X) C :=
  ⟨stoneCechExtend C.isDenseEmbedding.continuous, continuous_stoneCechExtend _⟩

/-- The Stone–Čech comparison map restricts to the identity over the original space. -/
@[simp]
theorem stoneCechComparison_apply (C : Compactification.{u, v} X) (x : X) :
    stoneCechComparison C (stoneCech X x) = C x := by
  rw [stoneCech_apply]
  change stoneCechExtend C.isDenseEmbedding.continuous (stoneCechUnit x) = C x
  exact stoneCechExtend_stoneCechUnit C.isDenseEmbedding.continuous x

/-- The Stone–Čech comparison map onto a compactification is closed. -/
theorem stoneCechComparison_isClosedMap (C : Compactification.{u, v} X) :
    IsClosedMap (stoneCechComparison C) :=
  (stoneCechComparison C).continuous.isClosedMap

/-- The Stone–Čech comparison map onto a compactification is surjective. -/
theorem stoneCechComparison_surjective (C : Compactification.{u, v} X) :
    Function.Surjective (stoneCechComparison C) := by
  rw [← Set.range_eq_univ]
  have hcomp : stoneCechComparison C ∘ stoneCech X = C := by
    funext x
    exact stoneCechComparison_apply C x
  have hdense : DenseRange (stoneCechComparison C) :=
    DenseRange.of_comp (hcomp ▸ C.isDenseEmbedding.toIsDenseInducing.dense)
  rw [← hdense.closure_range]
  exact (stoneCechComparison_isClosedMap C).isClosed_range.closure_eq.symm

/-- The Stone–Čech comparison map presents every compactification as a quotient. -/
theorem stoneCechComparison_isQuotientMap (C : Compactification.{u, v} X) :
    Topology.IsQuotientMap (stoneCechComparison C) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (stoneCechComparison_surjective C) (stoneCechComparison C).continuous

end Compactification

end
