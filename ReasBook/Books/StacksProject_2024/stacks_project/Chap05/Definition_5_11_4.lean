import Mathlib.Data.Set.Card
import Mathlib.Topology.KrullDimension
import StacksProject_2024.Chap05.Definition_5_11_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity on topological spaces:
- earlier chapter owner: `Order.coheight` on `IrreducibleCloseds X`, recalled in
  `Definition_5_11_1`
- mathlib interval bridge: `Order.coheight_bot_eq_krullDim`
- ambient owner for absolute dimension: `topologicalKrullDim`

Layer triage:
- `source-facing`: the relative codimension `codimBetween` and the catenary predicate
  `CatenarySpace`
- `core/canonical`: `coheight` and `krullDim` on the posets `IrreducibleCloseds X` and
  `Set.Icc T T'`
- `bridge/view`: the interval specialization of `Order.coheight_bot_eq_krullDim`

Primitive data belongs to `CatenarySpace`; any derived API should stay atomic. The relative
codimension remains source-facing, but it should be a thin specialization of the chapter owner
`Order.coheight`, not a parallel replacement for it.
-/

/-- The relative codimension of comparable irreducible closed subsets, realized as the thin
interval specialization of `Order.coheight`. -/
noncomputable abbrev codimBetween (T T' : IrreducibleCloseds X) (hTT' : T ≤ T') : ℕ∞ :=
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  coheight (⊥ : Set.Icc T T')

/-- The source-facing relative codimension agrees with the Krull dimension of the interval
`[T, T']`. -/
theorem codimBetween_eq_krullDim {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' = krullDim (Set.Icc T T') := by
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  change coheight (⊥ : Set.Icc T T') = krullDim (Set.Icc T T')
  exact coheight_bot_eq_krullDim

/-- Definition 5.11.4: a topological space is catenary if every comparable pair of irreducible
closed subsets has finite relative codimension; maximal chains in the corresponding interval have
that common length. -/
class CatenarySpace (X : Type u) [TopologicalSpace X] : Prop where
  finite_codimBetween {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' < ⊤
  maximalIrreducibleClosedChainsHaveLength {T T' : IrreducibleCloseds X}
      (hTT' : T ≤ T') (s : Set (Set.Icc T T')) (hs : IsMaxChain (· ≤ ·) s) :
      s.encard = (ENat.toNat (codimBetween T T' hTT') + 1 : ℕ∞)

/-- A catenary-space hypothesis can be supplied through `Fact` when a proposition-valued instance
is the natural interface. -/
instance instFactCatenarySpace [CatenarySpace X] : Fact (CatenarySpace X) := ⟨inferInstance⟩

namespace CatenarySpace

-- Proof sketch: compare maximal chains in `[T, T'']` with the concatenation of their restrictions
-- to `[T, T']` and `[T', T'']`. In a catenary space those maximal chains have lengths prescribed by
-- `codimBetween`, so the common length in the large interval is the sum of the common lengths in
-- the adjacent intervals.
/-- In a catenary space, relative codimension is additive along chains of irreducible closed
subsets. -/
theorem codimBetween_additive [CatenarySpace X] {T T' T'' : IrreducibleCloseds X}
    (hTT' : T ≤ T') (hT'T'' : T' ≤ T'') :
    codimBetween T T'' (hTT'.trans hT'T'') =
      codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := sorry

end CatenarySpace
