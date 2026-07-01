import stacks_project.Chap05.Definition_5_7_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

namespace ConnectedComponentClopenCounterexample

/- Domain-style sampling:
- primary domain: point-set topology, specifically connected components and clopen neighborhoods;
- same-domain declarations inspected:
  `maximal_isConnected_iff_eq_connectedComponent`,
  `connectedComponent`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`;
- best owner abstraction: the canonical owner `connectedComponent x`, with clopen neighborhoods
  expressed through `IsClopen` and the owner theorem
  `connectedComponent_subset_iInter_isClopen`;
- core/canonical: `connectedComponent x`, `IsClopen`, and
  `connectedComponent_subset_iInter_isClopen`;
- source-facing: the explicit Stacks counterexample space from Remark 5.7.4, together with
  the two concrete set computations showing the canonical inclusion can be strict;
- bridge/view layer: the final strict-inclusion theorem is obtained by comparing the source-facing
  computations with the canonical owner theorem above, so no separate local wrapper around that
  owner API is introduced here.

The only primitive data that belongs in this file is the point set and its generated topology; the
connected-component/clopen interface itself is already owned upstream by mathlib. -/

/-- The points of the Stacks counterexample space from Remark 5.7.4. -/
inductive Point where
  | x
  | y
  | z (n : ℕ)
deriving DecidableEq

open Point

/-- The singleton basic open containing only `z n`. -/
private def zSingleton (n : ℕ) : Set Point := {z n}

/-- The tail of all points `z m` with `m ≥ n`. -/
private def zTail (n : ℕ) : Set Point := range fun m ↦ z (n + m)

/-- The basic open `{x, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
private def xTail (n : ℕ) : Set Point := insert x (zTail n)

/-- The basic open `{y, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
private def yTail (n : ℕ) : Set Point := insert y (zTail n)

/-- The canonical topology on the counterexample point set. -/
instance : TopologicalSpace Point :=
  TopologicalSpace.generateFrom
    (range zSingleton ∪ range xTail ∪ range yTail)

/- Canonical owner recall: in any topological space, the connected component of a point is
contained in the intersection of all clopen neighborhoods of that point. This file only supplies a
counterexample showing that the inclusion can be strict. -/
recall connectedComponent_subset_iInter_isClopen {α : Type u} [TopologicalSpace α] {point : α} :
    connectedComponent point ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ point ∈ Z }, Z

/-- The connected component of `x` is the singleton `{x}` in the counterexample space. -/
-- Proof sketch: any connected subset containing `x` cannot contain any `z n`, since `{z n}` is open
-- and closed inside the subset, and `y` is separated from `x` by the basic open tails. Maximality
-- of the connected component then forces `connectedComponent x = {x}`.
theorem connectedComponent_x :
    connectedComponent x = ({x} : Set Point) := sorry

/-- The intersection of all clopen neighborhoods of `x` is `{x, y}` in the counterexample space. -/
-- Proof sketch: show every clopen neighborhood of `x` must also contain `y`, while the set
-- `{x, y}` itself is the intersection of the clopen supersets obtained from the displayed tails.
theorem iInter_isClopen_x :
    (⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point)) = ({x, y} : Set Point) := sorry

/-- Remark 5.7.4: in general the connected component of a point can be strictly smaller than the
intersection of all clopen neighborhoods containing that point; the space defined here is such a
counterexample. -/
-- Proof sketch: combine the explicit computations `connectedComponent_x` and `iInter_isClopen_x`;
-- equivalently, appeal to the canonical inclusion
-- `connectedComponent_subset_iInter_isClopen` and the explicit identifications of the two sets.
theorem connectedComponent_x_ssubset_iInter_isClopen :
    connectedComponent x ⊂ ⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point) := by
  refine ⟨connectedComponent_subset_iInter_isClopen, ?_⟩
  simp [connectedComponent_x, iInter_isClopen_x]

end ConnectedComponentClopenCounterexample
