import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.PairingEqualityOperator
import BauschkeLean.Chap20.Proposition_20_56

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.58 gives the Fitzpatrick lower bound and the corresponding
  contact-set description of a maximally monotone operator.
- `core/canonical`: the owner abstractions are `Maximal IsMonotone A`, the Fitzpatrick function
  owner `F[A]`, and the pairing-contact operator owner `pairingEqualityOperator`.
- `bridge/view`: the recovered operator equality is the main derived owner statement, and the
  graph equality is its source-facing contact-set view.
Semantic recall: `lean_leansearch` returned no item-specific hit, so the owner names and
statement surface were verified directly from `Proposition_20_56` and
`PairingEqualityOperator`. -/

-- Proof sketch: if `(x, u) ∈ gra A`, Proposition 20.56 (1) gives equality
-- `F_A(x, u) = ⟪x, u⟫`. If `(x, u) ∉ gra A`, maximal monotonicity implies that
-- `insert (x, u) (gra A)` is not monotone, and Proposition 20.56 (4) then rules
-- out the inequality `F_A(x, u) ≤ ⟪x, u⟫`, so necessarily `⟪x, u⟫ ≤ F_A(x, u)`.
/-- Helper for Proposition 20.58: if adjoining `(x, u)` to the graph of a maximally monotone
operator preserves monotonicity, then `(x, u)` already belongs to the graph. -/
private theorem mem_graph_of_insert_graph_isMonotone
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x u : H}
    (hinsert : SetRel.IsMonotone (Set.insert (x, u) (gra A))) :
    (x, u) ∈ gra A := by
  rw [SetValuedOperator.mem_graph]
  refine (Maximal.mem_iff hA x u).2 ?_
  intro y v hv
  -- Test the inserted relation against the new point and an arbitrary old graph point.
  have hxu_insert : (x, u) ∈ Set.insert (x, u) (gra A) := Set.mem_insert _ _
  have hyv_insert : (y, v) ∈ Set.insert (x, u) (gra A) := by
    exact Set.mem_insert_iff.mpr <| Or.inr <| by
      simpa [SetValuedOperator.mem_graph] using hv
  exact hinsert hxu_insert hyv_insert

/-- Proposition 20.58 (1): the Fitzpatrick function of a maximally monotone
operator dominates the pairing everywhere. -/
theorem Maximal.inner_le_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    pairing (x, u) ≤ F[A] (x, u) := by
  by_cases hxu : (x, u) ∈ gra A
  · -- On the graph, Proposition 20.56 (1) identifies the Fitzpatrick value with the pairing.
    rw [fitzpatrickFunction_eq_inner_of_mem_graph (A := A) (Maximal.isMonotone hA) hxu]
  · -- Off the graph, a Fitzpatrick value below the pairing would force inserted-graph monotonicity.
    have hnot_le : ¬ F[A] (x, u) ≤ pairing (x, u) := by
      intro hle
      have hinsert :
          SetRel.IsMonotone (Set.insert (x, u) (gra A)) :=
        (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
          (A := A) (Maximal.isMonotone hA) x u).mp hle
      exact hxu (mem_graph_of_insert_graph_isMonotone hA hinsert)
    exact le_of_not_ge hnot_le

/-- Proposition 20.58 (2), owner form: a maximally monotone operator is exactly the
pairing-contact operator of its Fitzpatrick function. -/
theorem Maximal.eq_pairingEqualityOperator_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A = pairingEqualityOperator F[A] := by
  ext x u
  constructor
  · intro hxu
    -- Graph points satisfy the Fitzpatrick contact equality by Proposition 20.56 (1).
    rw [mem_pairingEqualityOperator_iff]
    exact fitzpatrickFunction_eq_inner_of_mem_graph (A := A) (Maximal.isMonotone hA) <| by
      simpa [SetValuedOperator.mem_graph] using hxu
  · intro hcontact
    rw [mem_pairingEqualityOperator_iff] at hcontact
    -- Route correction: use the contact equality only to recover inserted-graph monotonicity,
    -- then apply maximality to deduce graph membership.
    have hinsert :
        SetRel.IsMonotone (Set.insert (x, u) (gra A)) :=
      (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
        (A := A) (Maximal.isMonotone hA) x u).mp (le_of_eq hcontact)
    simpa [SetValuedOperator.mem_graph] using
      (mem_graph_of_insert_graph_isMonotone hA hinsert)

/-- Source-facing graph form of
`Maximal.eq_pairingEqualityOperator_fitzpatrickFunction`: the graph of a maximally monotone
operator is exactly the Fitzpatrick contact set `{(x, u) | F_A (x, u) = ⟪x, u⟫}`. -/
theorem Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.graph = {p | F[A] p = pairing p} := by
  -- Rewrite the owner equality from clause (2) only at the graph level, not inside `F[A]`.
  calc
    A.graph = (pairingEqualityOperator F[A]).graph := by
      simpa using congrArg SetValuedOperator.graph
        (Maximal.eq_pairingEqualityOperator_fitzpatrickFunction (A := A) hA)
    _ = {p | F[A] p = pairing p} := by
      simpa using graph_pairingEqualityOperator_eq (F := F[A])

end SetValuedOperator
