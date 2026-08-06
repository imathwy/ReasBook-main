import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup

universe u

open scoped Topology Topology.Homotopy

variable (n : ℕ) {X : Type u} [TopologicalSpace X] (x : X)

-- Semantic recall via `lean_leansearch`: mathlib already packages the positive-degree homotopy
-- group structure by instances, together with the canonical comparisons of `π_ 0` with path
-- components and `π_ 1` with the fundamental group. The repository companion
-- `HomotopyGroup.pi1MulEquivFundamentalGroup` upgrades the `π_ 1` comparison to a multiplicative
-- equivalence used later in Chapter 9 and beyond.

/- Lemma 9.1.2: the based homotopy groups `π_ n X x` already have their canonical algebraic
structure in mathlib: `π_ (n + 1) X x` is a group and `π_ (n + 2) X x` is a commutative group.
The boundary cases agree with the earlier notions via
`HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X` and
`HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x`. -/
#check (inferInstance : Group (π_ (n + 1) X x))
#check (inferInstance : CommGroup (π_ (n + 2) X x))
#check HomotopyGroup.pi0EquivZerothHomotopy
#check HomotopyGroup.pi1EquivFundamentalGroup
#check (HomotopyGroup.pi1MulEquivFundamentalGroup x : π_ 1 X x ≃* FundamentalGroup X x)
