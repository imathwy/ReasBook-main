import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

variable (n : ℕ) {X : Type u} [TopologicalSpace X] (x : X)

/- Remark 9.4.14: this sentence is an informal meta-mathematical observation about the current
state of explicit homotopy-group computations, so there is no source-faithful theorem here with a
mathematical predicate formalizing “all homotopy groups are known”. The ambient formal notions it
refers to are the canonical owners `ContractibleSpace`, `SimplyConnectedSpace`, and the based
homotopy groups `HomotopyGroup.Pi`, written `π_ n X x`; the notation surface is the Chapter 9
owner recalled in Definition 9.1.1. -/
recall ContractibleSpace (X : Type u) [TopologicalSpace X] : Prop

recall SimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/- The source also speaks about the based homotopy groups themselves; Definition 9.1.1 already
records the canonical owner `HomotopyGroup.Pi`, with notation `π_ n X x`. -/
#check (π_ n X x)
