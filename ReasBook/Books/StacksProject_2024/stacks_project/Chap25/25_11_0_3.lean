import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Topology.Category.TopCat.Opens

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

noncomputable section

universe u v w

/- Source/core/bridge triage:
- `source-facing`: the condition that each prescribed finite intersection of level-`n` opens is
  covered by the compatible level-`n + 1` opens;
- `core/canonical`: the `Opens X`-valued owner `HypercoveringIntersectionCondition`;
- `bridge/view`: the `sSup` and finite-inf companion equalities below.

The repeated subtype of compatible level-`n + 1` indices is factored out as
`HypercoveringMatchingIndices` so the source-facing owner and its companions share one stable
surface. -/

variable {X : TopCat.{u}} {n : ℕ} {In : Type v} {In1 : Type w}

/-- The level-`n + 1` indices whose `a`th face agrees with a chosen family of level-`n` indices
for every `a : Fin (n + 2)`. -/
abbrev HypercoveringMatchingIndices
    (d : Fin (n + 2) → In1 → In) (i : Fin (n + 2) → In) :=
  { j : In1 // ∀ a : Fin (n + 2), d a j = i a }

namespace HypercoveringMatchingIndices

/-- The `a`th face of a matching level-`n + 1` index recovers the chosen `a`th level-`n` index. -/
@[simp] theorem face_eq
    {d : Fin (n + 2) → In1 → In} {i : Fin (n + 2) → In}
    (j : HypercoveringMatchingIndices d i) (a : Fin (n + 2)) :
    d a j = i a :=
  j.2 a

/-- For `n = 0`, matching indices are exactly the level-`1` indices whose two faces are the chosen
level-`0` indices. This is the canonical bridge from the generic matching-index owner to the
pairwise source-facing subtype used in `25.11.0.2`. -/
def finTwoEquiv {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0) :
    HypercoveringMatchingIndices ![d0, d1] ![i0, i1] ≃ { j : I1 // d0 j = i0 ∧ d1 j = i1 } where
  toFun j :=
    ⟨j.1, by
      exact ⟨j.2 0, j.2 1⟩⟩
  invFun j :=
    ⟨j.1, by
      simpa [Fin.forall_fin_two] using j.2⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

/-- The forward map of `finTwoEquiv` preserves the underlying level-`1` index. -/
@[simp] theorem finTwoEquiv_val
    {I0 : Type v} {I1 : Type w} (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : HypercoveringMatchingIndices ![d0, d1] ![i0, i1]) :
    (finTwoEquiv d0 d1 i0 i1 j).1 = j.1 :=
  rfl

/-- The inverse map of `finTwoEquiv` preserves the underlying level-`1` index. -/
@[simp] theorem finTwoEquiv_symm_val
    {I0 : Type v} {I1 : Type w} (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : { j : I1 // d0 j = i0 ∧ d1 j = i1 }) :
    ((finTwoEquiv d0 d1 i0 i1).symm j).1 = j.1 :=
  rfl

end HypercoveringMatchingIndices

/-- 25.11.0.3: for every family of `n + 2` level-`n` indices, the corresponding intersection of
opens is covered by the level-`n + 1` opens whose `a`th face is the chosen `a`th index for every
`a : Fin (n + 2)`. -/
@[stacks 01H4]
class HypercoveringIntersectionCondition
    (d : Fin (n + 2) → In1 → In) (Un : In → Opens X) (Un1 : In1 → Opens X) : Prop where
  /-- The intersection indexed by a chosen `(n + 2)`-tuple of level-`n` indices is the supremum
  of the level-`n + 1` opens whose faces recover that tuple. -/
  iInf_eq_iSup (i : Fin (n + 2) → In) :
    (⨅ a, Un (i a)) =
      iSup (fun j : HypercoveringMatchingIndices d i ↦ Un1 j)

namespace HypercoveringIntersectionCondition

/-- The covering equality of `HypercoveringIntersectionCondition` in set-indexed supremum form.
This forgets duplicate level-`n + 1` indices and records only the corresponding opens. -/
theorem iInf_eq_sSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) :
    (⨅ a, Un (i a)) =
      sSup (Set.range (fun j : HypercoveringMatchingIndices d i ↦ Un1 j)) := by
  simpa [sSup_range] using h.iInf_eq_iSup i

/-- Each matching level-`n + 1` open lies in the prescribed finite intersection. -/
theorem matchingOpen_le_iInf
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) (j : HypercoveringMatchingIndices d i) :
    Un1 j ≤ ⨅ a, Un (i a) := by
  rw [h.iInf_eq_iSup i]
  exact le_iSup (fun k : HypercoveringMatchingIndices d i ↦ Un1 k) j

/-- Each matching level-`n + 1` open lies in every factor of the prescribed finite intersection. -/
theorem matchingOpen_le
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) (j : HypercoveringMatchingIndices d i) (a : Fin (n + 2)) :
    Un1 j ≤ Un (i a) :=
  le_trans (h.matchingOpen_le_iInf i j) (iInf_le _ a)

/-- A point lies in the prescribed finite intersection exactly when it lies in one of the matching
level-`n + 1` opens. This is the source-facing union formula attached to
`HypercoveringIntersectionCondition`. -/
theorem mem_iInf_iff_exists
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) (x : X) :
    x ∈ (⨅ a, Un (i a) : Opens X) ↔
      ∃ j : HypercoveringMatchingIndices d i, x ∈ Un1 j := by
  rw [h.iInf_eq_iSup i, Opens.mem_iSup]

/-- The same covering equality in finite-inf notation over `Fin (n + 2)`. -/
theorem eq_iSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) :
    Finset.univ.inf (fun a : Fin (n + 2) ↦ Un (i a)) =
      iSup (fun j : HypercoveringMatchingIndices d i ↦ Un1 j) := by
  simpa [Finset.inf_univ_eq_iInf] using h.iInf_eq_iSup i

/-- The same covering equality in finite-inf and set-indexed supremum notation. -/
theorem eq_sSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    (h : HypercoveringIntersectionCondition d Un Un1)
    (i : Fin (n + 2) → In) :
    Finset.univ.inf (fun a : Fin (n + 2) ↦ Un (i a)) =
      sSup (Set.range (fun j : HypercoveringMatchingIndices d i ↦ Un1 j)) := by
  simpa [sSup_range] using h.eq_iSup i

end HypercoveringIntersectionCondition
