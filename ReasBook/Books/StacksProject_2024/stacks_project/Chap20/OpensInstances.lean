import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Topology.Sheaves.Sheaf

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open TopologicalSpace

universe u

namespace TopologicalSpace

/-- The lattice of opens of a topological space has its canonical top element as an `OrderTop`
instance. This lets APIs such as `Preorder.isTerminalTop (Opens X)` and the induced terminal
object instance for `Opens X` be found by typeclass search without repeated local `letI` blocks. -/
instance Opens.instOrderTop (X : Type u) [TopologicalSpace X] : OrderTop (Opens X) :=
  Opens.instCompleteLattice.toOrderTop

/-- The lattice of opens of a topological space has the canonical finite-limit structure coming
from intersections and the top open. This support instance lets downstream files infer finite
limits on `Opens X` without repeating local scaffolding. -/
instance Opens.instHasFiniteLimits (X : Type u) [TopologicalSpace X] :
    HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The lattice of opens of a topological space therefore has canonical finite products. -/
instance Opens.instHasFiniteProducts (X : Type u) [TopologicalSpace X] :
    HasFiniteProducts (Opens X) :=
  inferInstance

/-- The slice category `Over U` of opens has binary products, computed by pullbacks in
`Opens X`. -/
instance Opens.instHasBinaryProductsOver
    (X : Type u) [TopologicalSpace X] (U : Opens X) :
    HasBinaryProducts (Over U) := by
  let _ : HasPullbacks (Opens X) := by infer_instance
  exact CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The slice category `Over U` of opens therefore has canonical finite products. -/
instance Opens.instHasFiniteProductsOver
    (X : Type u) [TopologicalSpace X] (U : Opens X) :
    HasFiniteProducts (Over U) := by
  letI : HasTerminal (Over U) := CategoryTheory.Over.over_hasTerminal (C := Opens X) U
  exact hasFiniteProducts_of_has_binary_and_terminal

end TopologicalSpace
