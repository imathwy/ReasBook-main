import Mathlib.Tactic.Recall
import Mathlib.Topology.Homotopy.HomotopyGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

variable (n : ℕ) {X : Type u} [TopologicalSpace X] (x : X)

-- Semantic recall via `lean_leansearch`: mathlib's canonical owner for the based `n`th homotopy
-- set/group is `HomotopyGroup.Pi`, written `π_ n X x`. This definition file keeps the source-
-- facing owner and notation only; the positive-degree algebraic structure is recorded separately
-- in Lemma 9.1.2.

/- Definition 9.1.1: for `n : ℕ` and a based space `(X, x)`, mathlib formalizes the `n`th
homotopy set/group as `HomotopyGroup.Pi n X x`, written `π_ n X x`. The source condition `n ≥ 0`
is encoded by taking `n : ℕ`; mathlib models these classes using generalized based `n`-loops. -/
recall HomotopyGroup.Pi (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) : Type u

/- The notation `π_ n X x` is the standard surface for the `n`th based homotopy set/group. -/
#check (π_ n X x)
