module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Example_53_4.Covering
import all Topology_Munkres_2000.Book.Example_53_4.Covering
import Topology_Munkres_2000.Book.Theorem_53_2

public section

/- Example 53.5 (1): The basepoint `b₀ = p 0` is `1 : Circle`. -/
#check Circle.turnExp_zero

/- Example 53.5 (2): The two coordinate circles through the basepoint form the figure eight. -/
#check FigureEight

open Set

namespace InfiniteGrid

/-- Helper for Example 53.5: the preimage of the figure eight under the torus covering map. -/
def carrier : Set (ℝ × ℝ) :=
  Torus.cover ⁻¹' FigureEight.carrier

end InfiniteGrid

/-- Helper for Example 53.5: the infinite-grid subspace of `ℝ × ℝ`. -/
abbrev InfiniteGrid := InfiniteGrid.carrier

namespace InfiniteGrid

/-- Helper for Example 53.5: the torus covering map applies the circle exponential in each
coordinate. -/
private theorem torusCover_apply (x : ℝ × ℝ) :
    Torus.cover x = (Circle.turnExp x.1, Circle.turnExp x.2) := by
  -- Expose the coordinatewise definition of the torus covering map.
  rfl

/-- Example 53.5: The preimage of the figure eight is the infinite integer grid. -/
theorem carrier_eq :
    carrier =
      {x : ℝ × ℝ | x.2 ∈ Set.range (Int.cast : ℤ → ℝ)} ∪
        {x : ℝ × ℝ | x.1 ∈ Set.range (Int.cast : ℤ → ℝ)} := by
  -- Reduce both set descriptions to the coordinatewise exponential criterion.
  ext x
  simp only [carrier, Set.mem_preimage, FigureEight.mem_iff, torusCover_apply,
    Circle.turnExp_eq_one_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_range,
    eq_comm]

/-- Helper for Example 53.5: a point is in the grid exactly when one coordinate is integral. -/
theorem mem_iff (x : ℝ × ℝ) :
    x ∈ carrier ↔ (∃ n : ℤ, x.2 = n) ∨ ∃ n : ℤ, x.1 = n := by
  -- Rewrite by the geometric carrier description and unpack the two integer ranges.
  rw [carrier_eq]
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_range, eq_comm]

/-- Helper for Example 53.5: the torus covering map restricted to the infinite grid. -/
noncomputable def cover : InfiniteGrid → FigureEight :=
  FigureEight.carrier.restrictPreimage Torus.cover

/-- Helper for Example 53.5: the grid map agrees with the ambient torus covering map. -/
theorem cover_apply (x : InfiniteGrid) :
    (cover x : Torus) = Torus.cover x := by
  -- Project the canonical restricted-preimage computation to the ambient torus.
  exact congrArg Subtype.val
    (Set.restrictPreimage_mk (t := FigureEight.carrier) (f := Torus.cover) x.property)

/-- Helper for Example 53.5: the restricted grid map is a covering map. -/
theorem cover_isCoveringMap : IsCoveringMap cover := by
  -- Restrict the ambient surjective covering and retain its covering-map component.
  have hambient : IsSurjectiveCoveringMap Torus.cover :=
    (isSurjectiveCoveringMap_iff Torus.cover).2 Torus.cover_isCoveringMap
  have hrestricted := hambient.restrictPreimage FigureEight.carrier
  exact hrestricted.isCoveringMap

/-- Helper for Example 53.5: the restricted grid covering map is surjective. -/
theorem cover_surjective : Function.Surjective cover := by
  -- The restriction theorem also retains surjectivity onto the figure eight.
  have hambient : IsSurjectiveCoveringMap Torus.cover :=
    (isSurjectiveCoveringMap_iff Torus.cover).2 Torus.cover_isCoveringMap
  have hrestricted := hambient.restrictPreimage FigureEight.carrier
  exact hrestricted.surjective

end InfiniteGrid

/- Example 53.5 (4): The restricted product map is a covering map in Munkres's
surjective sense. -/
#check InfiniteGrid.cover_isCoveringMap
#check InfiniteGrid.cover_surjective
