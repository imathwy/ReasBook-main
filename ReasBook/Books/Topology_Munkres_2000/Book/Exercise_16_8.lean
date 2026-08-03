module

public import Topology_Munkres_2000.Book.Exercise_16_8.AffineLine

public section

open SorgenfreyAffineLine

/- Exercise 16.8 (1): A vertical line in `SorgenfreyLine × ℝ` has the usual real topology. -/
#check euclideanVerticalHomeomorph

/- Exercise 16.8 (2): Every nonvertical line in `SorgenfreyLine × ℝ` has the
Sorgenfrey topology. -/
#check euclideanGraphHomeomorph

/- Exercise 16.8 (3): A vertical line in the Sorgenfrey plane has the Sorgenfrey topology. -/
#check verticalHomeomorph

/- Exercise 16.8 (4): A line of nonnegative slope in the Sorgenfrey plane has
the Sorgenfrey topology. -/
#check graphHomeomorphOfNonneg

/- Exercise 16.8 (5): A line of negative slope in the Sorgenfrey plane has the
discrete topology. -/
namespace SorgenfreyAffineLine

/-- Exercise 16.8: A line of negative slope in the Sorgenfrey plane has the discrete topology. -/
theorem graphDiscreteOfNeg (m b : ℝ) (hm : m < 0) : DiscreteTopology (graph m b) := by
  -- Isolate each graph point by a product of unit-width lower-limit intervals.
  rw [discreteTopology_subtype_iff']
  intro point hpoint
  refine ⟨(SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal point.1)
      (SorgenfreyLine.toReal point.1 + 1)) ×ˢ
    (SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal point.2)
      (SorgenfreyLine.toReal point.2 + 1)), ?_, ?_⟩
  · apply IsOpen.prod
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨_, _, lt_add_one _, rfl⟩
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨_, _, lt_add_one _, rfl⟩
  · ext candidate
    constructor
    · intro hcandidate
      rcases hcandidate with ⟨⟨⟨hfirstLower, _⟩, ⟨hsecondLower, _⟩⟩, hgraph⟩
      rw [mem_graph_iff] at hpoint hgraph
      have hfirst : SorgenfreyLine.toReal candidate.1 = SorgenfreyLine.toReal point.1 := by
        nlinarith
      have hsecond : SorgenfreyLine.toReal candidate.2 = SorgenfreyLine.toReal point.2 := by
        nlinarith
      simpa only [Set.mem_singleton_iff] using Prod.ext
        (SorgenfreyLine.toReal.injective hfirst) (SorgenfreyLine.toReal.injective hsecond)
    · intro hcandPoint
      rw [Set.mem_singleton_iff] at hcandPoint
      subst candidate
      refine ⟨⟨?_, ?_⟩, hpoint⟩
      · exact ⟨le_rfl, lt_add_one _⟩
      · exact ⟨le_rfl, lt_add_one _⟩

end SorgenfreyAffineLine
