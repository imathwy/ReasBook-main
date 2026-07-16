import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_5
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_7

noncomputable section

open scoped RealInnerProductSpace

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.5 records that in dimensions `n > 1` monotonicity is strictly
  weaker than cyclic monotonicity, and it says that a linear example already shows the
  distinction.
- `core/canonical`: the chapter already owns these notions as `SetRel.Monotone` and
  `SetRel.CyclicallyMonotone` on graph relations, while single-valued mappings are canonically
  viewed as relations through `Function.graph`.
- `bridge/view`: the source's "linear mapping" is therefore most naturally a linear self-map
  `Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)` together with the relation
  `(Q : _ → _).graph`.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from `Definition_5_24_5`;
- `SetRel.Monotone` from `Definition_5_24_7`;
- `Function.graph` from mathlib's relation API, the canonical bridge from a single-valued map to
  a graph relation;
- `SetRel.maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq` from
  `Theorem_5_24_12`, which confirms that the chapter's owner level for these notions is the graph
  relation itself.

Primitive data vs derived API:
- primitive source-facing data: the dimension parameter `n` with `1 < n`;
- primitive witness data promised by the remark: a linear map `Q`;
- derived owner-level properties: monotonicity and failure of cyclic monotonicity of the graph
  relation of `Q`.

Layer target: `source-facing`. The remark is an existence statement about linear mappings on
`ℝⁿ`, expressed directly through the canonical graph-relation owners already fixed by the chapter.
-/

section

local instance (n : ℕ) :
    HasPairing (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ℝ :=
  instHasPairingOfHasLinearPairing

-- Proof sketch: use the standard quarter-turn on a two-dimensional coordinate plane, whose
-- symmetric part is zero and hence whose graph is monotone, while the map is not symmetric and so
-- fails the linear cyclic-monotonicity criterion. For `n > 1`, extend this `2 × 2` skew block by
-- zero on the remaining coordinates.
/-- Remark 5.24.5: when `n > 1`, there exists a linear self-map of `ℝⁿ` whose graph is monotone
but not cyclically monotone. This gives the source's linear example showing that cyclic
monotonicity is strictly stronger than monotonicity in dimensions greater than one. -/
theorem exists_linearMap_graph_monotone_not_cyclicallyMonotone
    {n : ℕ} (hn : 1 < n) :
    ∃ Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      ((Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)).graph).Monotone ℝ ∧
        ¬ ((Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)).graph).CyclicallyMonotone ℝ :=
  sorry

end
