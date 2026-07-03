import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_37 (from Items/Chap01) -/
open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

universe u

variable {Ω : Type u}

/- Example 1.37 uses the canonical finite-or-cofinite family from Example 1.11 and the canonical
`∅`-continuity predicate for additive contents from Definition 1.35. -/

/-- The set function used in the finite-cofinite example: finite sets get mass `0`, infinite sets
get mass `∞`. -/
private noncomputable def finiteCofiniteZeroInfiniteContentFun (Ω : Type u) (s : Set Ω) : ENNReal :=
  if s.Finite then (0 : ENNReal) else ∞

private theorem finiteCofiniteZeroInfiniteContentFun_apply (Ω : Type u) (s : Set Ω) :
    finiteCofiniteZeroInfiniteContentFun Ω s = if s.Finite then (0 : ENNReal) else ∞ :=
  rfl

private theorem finiteCofiniteZeroInfiniteContent_empty (Ω : Type u) :
    finiteCofiniteZeroInfiniteContentFun Ω ∅ = 0 := by
  simp [finiteCofiniteZeroInfiniteContentFun]

-- Proof sketch: if the finite disjoint union is finite, then every summand is finite and both sides
-- are `0`; if the union is cofinite, one of the summands is cofinite and forces both sides to be
-- `∞`.
private theorem finiteCofiniteZeroInfiniteContent_sUnion (Ω : Type u) (I : Finset (Set Ω))
    (hI : ↑I ⊆ finiteOrCofiniteFamily Ω)
    (hdis : PairwiseDisjoint (I : Set (Set Ω)) id)
    (hmem : ⋃₀ ↑I ∈ finiteOrCofiniteFamily Ω) :
    finiteCofiniteZeroInfiniteContentFun Ω (⋃₀ ↑I) =
      ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u := sorry

/-- The content on the finite-or-cofinite family that assigns `0` to finite sets and `∞` to
infinite sets. -/
noncomputable def finiteCofiniteZeroInfiniteContent (Ω : Type u) :
    AddContent ENNReal (finiteOrCofiniteFamily Ω) where
  toFun := finiteCofiniteZeroInfiniteContentFun Ω
  empty' := finiteCofiniteZeroInfiniteContent_empty Ω
  sUnion' := finiteCofiniteZeroInfiniteContent_sUnion Ω

/-- The bundled finite-or-cofinite content is given by the stated zero-or-infinity formula. -/
@[simp] theorem finiteCofiniteZeroInfiniteContent_apply (Ω : Type u) (s : Set Ω) :
    finiteCofiniteZeroInfiniteContent Ω s = if s.Finite then (0 : ENNReal) else ∞ := by
  exact finiteCofiniteZeroInfiniteContentFun_apply Ω s

-- Proof sketch: for a decreasing sequence in the finite-or-cofinite family with empty
-- intersection, countability lets one exhaust the remaining points and show that all sufficiently
-- late terms are finite, hence the values are eventually `0` and converge to `0`.
/-- The finite-or-cofinite content is `∅`-continuous on a countably infinite ambient set. -/
instance finiteCofiniteZeroInfiniteContent_isContinuousAtEmpty (Ω : Type u) [Countable Ω]
    [Infinite Ω] :
    AddContent.IsContinuousAtEmpty (finiteCofiniteZeroInfiniteContent Ω) := sorry

-- Proof sketch: apply σ-subadditivity to a partition of the countably infinite ambient space into
-- singletons; the left-hand side is `∞` while the right-hand side is `0`.
/-- The finite-or-cofinite content is not σ-subadditive on a countably infinite ambient set. -/
theorem finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive (Ω : Type u) [Countable Ω]
    [Infinite Ω] :
    ¬ (finiteCofiniteZeroInfiniteContent Ω).IsSigmaSubadditive := sorry

/-- Example 1.37: On a countably infinite set, the content assigning mass `0` to finite sets and
mass `∞` to infinite sets is `∅`-continuous and fails the canonical premeasure predicate
`AddContent.IsSigmaSubadditive`. -/
theorem finiteCofiniteZeroInfiniteContent_continuousAtEmpty_not_premeasure (Ω : Type u)
    [Countable Ω] [Infinite Ω] :
    AddContent.IsContinuousAtEmpty (finiteCofiniteZeroInfiniteContent Ω) ∧
      ¬ (finiteCofiniteZeroInfiniteContent Ω).IsSigmaSubadditive := by
  exact ⟨inferInstance,
    finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive Ω⟩
