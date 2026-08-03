module

public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Example_53_4.Covering
import all Topology_Munkres_2000.Book.Example_53_4.Covering
import Topology_Munkres_2000.Book.Theorem_53_2

public section

open Set

namespace InfiniteGrid

/-- The preimage of the figure eight under the torus covering map from Example 53.4. -/
def carrier : Set (ℝ × ℝ) :=
  Torus.cover ⁻¹' FigureEight.carrier

end InfiniteGrid

/-- The infinite-grid subspace of `ℝ × ℝ`. -/
abbrev InfiniteGrid := InfiniteGrid.carrier

namespace InfiniteGrid

/-- Helper for Example 53.5: the torus covering map applies the circle exponential in each
coordinate. -/
private theorem torusCover_apply (x : ℝ × ℝ) :
    Torus.cover x = (Circle.turnExp x.1, Circle.turnExp x.2) := by
  -- The implementation import exposes the coordinatewise product map at this bridge.
  rfl

/-- The infinite grid is the union of the horizontal and vertical lines at integer coordinates. -/
theorem carrier_eq :
    carrier =
      {x : ℝ × ℝ | x.2 ∈ Set.range (Int.cast : ℤ → ℝ)} ∪
        {x : ℝ × ℝ | x.1 ∈ Set.range (Int.cast : ℤ → ℝ)} := by
  -- Route correction: isolate the opaque covering map behind its pointwise computation rule,
  -- then reduce both set descriptions to their pointwise membership conditions.
  ext x
  simp only [carrier, Set.mem_preimage, FigureEight.mem_iff, torusCover_apply,
    Circle.turnExp_eq_one_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_range,
    eq_comm]

/-- A point lies in the infinite grid exactly when one coordinate is an integer. -/
theorem mem_iff (x : ℝ × ℝ) :
    x ∈ carrier ↔ (∃ n : ℤ, x.2 = n) ∨ ∃ n : ℤ, x.1 = n := by
  -- Rewrite by the geometric carrier description and unpack membership in each integer range.
  rw [carrier_eq]
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_range, eq_comm]

/-- The restriction of the torus covering map from Example 53.4 to the infinite grid. -/
noncomputable def cover : InfiniteGrid → FigureEight :=
  FigureEight.carrier.restrictPreimage Torus.cover

/-- The grid covering map agrees with the torus covering map from Example 53.4. -/
theorem cover_apply (x : InfiniteGrid) :
    (cover x : Torus) = Torus.cover x := by
  -- Project the canonical restricted-preimage computation to the ambient torus.
  exact congrArg Subtype.val
    (Set.restrictPreimage_mk (t := FigureEight.carrier) (f := Torus.cover) x.property)

/-- The restricted grid map is a covering map of the figure eight. -/
theorem cover_isCoveringMap : IsCoveringMap cover := by
  -- Restrict the ambient surjective covering, then retain its covering-map component.
  have hambient : IsSurjectiveCoveringMap Torus.cover :=
    (isSurjectiveCoveringMap_iff Torus.cover).2 Torus.cover_isCoveringMap
  have hrestricted := hambient.restrictPreimage FigureEight.carrier
  exact hrestricted.isCoveringMap

/-- The restricted grid covering map is surjective. -/
theorem cover_surjective : Function.Surjective cover := by
  -- The same restriction theorem also retains surjectivity onto the figure eight.
  have hambient : IsSurjectiveCoveringMap Torus.cover :=
    (isSurjectiveCoveringMap_iff Torus.cover).2 Torus.cover_isCoveringMap
  have hrestricted := hambient.restrictPreimage FigureEight.carrier
  exact hrestricted.surjective

end InfiniteGrid
