import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14

noncomputable section

open scoped Rockafellar SetRel InnerProduct

universe u v w z ℓ

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.15 states that process adjunction commutes with relation
  inverse, and that for an actual linear transformation this process adjoint recovers the usual
  Hilbert-space adjoint operator.
- `core/canonical`: the chapter already owns the process adjoint as `SetRel.adjoint` with notation
  `A∗[...]`, the inverse relation as `SetRel.inv` with notation `A⁻¹`, and single-valued maps as
  relation graphs `Function.graph`.
- `bridge/view`: the second clause is a bridge from the relation-level adjoint owner to the
  linear-algebra owner `ContinuousLinearMap.adjoint`.

Primary mathematical domain:
- convex processes and pairing-based adjoint relations.

Domain-style sampling used here:
- `SetRel.adjoint` and `SetRel.mem_adjoint_iff` from `Definition_39_0_14`;
- `SetRel.inv` and `SetRel.mem_inv` from `Definition_26_0_2` / mathlib;
- `Function.graph` from `Mathlib.Data.Rel`;
- `ContinuousLinearMap.adjoint` and `ContinuousLinearMap.adjoint_inner_left` from mathlib's
  inner-product API.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive source operators: inverse and adjoint on relation graphs;
- derived bridge: when `A` is the graph of a linear map, the adjoint relation is again a graph,
  namely the graph of the usual Hilbert-space adjoint operator.

Layer target:
- clause (1) is a direct owner-level identity on relations and pairings;
- clause (2) is a bridge from the source relation owner to the canonical bounded-operator owner.

Redundant-assumption note:
- the source phrases clause (1) for oriented convex processes, but the inverse/adjoint commutation
  law depends only on the relation and the pairing data, so no convex-process hypothesis is kept in
  the public statement.
-/

section InverseAdjoint

variable {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type z} {L : Type ℓ}
variable [LE L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

-- Proof sketch: ext on a dual pair `(u⋆, x⋆)` and rewrite both sides with `SetRel.mem_inv` and
-- `mem_adjoint_iff`. After swapping the graph variables of `A`, the two universal pairing
-- inequalities are definitionally the same.
/-- Proposition 39.0.15 (1): the inverse of the process adjoint equals the adjoint of the inverse
relation. The convex-process hypothesis from the source is redundant for this relation identity, so
the statement is given directly on the canonical relation owner. -/
theorem inv_adjoint_eq_adjoint_inv
    (A : SetRel U X) :
    (A∗[XStar, UStar; L])⁻¹ = (A⁻¹)∗[UStar, XStar; L] := sorry

end InverseAdjoint

section ContinuousLinearMapBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [CompleteSpace F]

-- Proof sketch: ext on a pair `(y, x)` in `F × E`. Membership in the adjoint of
-- `Function.graph A` says that `⟪u, x⟫ ≥ ⟪A u, y⟫` for every `u`; replacing `u` by `-u` forces
-- equality for all `u`. The defining property of `ContinuousLinearMap.adjoint`, via
-- `ContinuousLinearMap.adjoint_inner_left`, then identifies this with `x = (A†) y`.
/-- Proposition 39.0.15 (2): when the process is the graph of a continuous linear map, its process
adjoint is
exactly the graph of the usual Hilbert-space adjoint operator. -/
theorem adjoint_graph_eq_graph_adjoint
    (A : E →L[ℝ] F) :
    (Function.graph A)∗[ℝ] = Function.graph (A†) := sorry

end ContinuousLinearMapBridge

end SetRel
