import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Topology.CWComplex.Classical.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology
open Topology.CWComplex

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.cell` is the canonical type of
-- `n`-cells for a chosen classical CW structure, and `FreeAbelianGroup` is the canonical free
-- abelian-group owner in mathlib.

/-- The indexing type of the `n`-cells in the chosen CW structure on `X`. -/
abbrev cellularCell (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :=
  cell (Set.univ : Set X) n

/-- Construction 13.2.1: for a CW complex `X`, the cellular chain group `C_n(X)` is the free
Abelian group on the `n`-cells of the chosen CW structure on `X`. -/
abbrev cellularChainGroup (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) :=
  FreeAbelianGroup (cellularCell X n)

/-- Lean notation for the textbook cellular chain groups `C_n(X)`. -/
scoped[CellularChainGroup] notation "C[" n "](" X ")" => cellularChainGroup X n

open scoped CellularChainGroup

/-- `C[n](X)` is definitionally the free Abelian group on the `n`-cells of `X`. -/
@[simp] theorem cellularChainGroup_def
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) :
    C[n](X) = FreeAbelianGroup (cellularCell X n) :=
  rfl
