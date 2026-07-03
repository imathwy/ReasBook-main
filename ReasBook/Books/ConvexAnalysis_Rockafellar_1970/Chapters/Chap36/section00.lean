

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_36_0_1 (from Chap07) -/
universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.0.1 introduces the two comparison values
  `sup_{u ∈ C} inf_{v ∈ D} K(u, v)` and `inf_{v ∈ D} sup_{u ∈ C} K(u, v)` for a minimax
  problem, and says that when they are equal their common value is the saddle-value.
- `core/canonical`: the owner layer for these values is the set-indexed `iSup`/`iInf` surface
  at the primitive `SupSet`/`InfSet` codomain layer, together with the source-order saddle owner
  `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`.
- `bridge/view`: `Bifunction.IsSaddlePointOn` is itself the canonical owner-side bridge to
  `_root_.IsSaddlePointOn D C (Function.swap K) v u`, so this file can keep theorem surfaces in
  Chapter 36 source variable order.

Domain-style sampling used here:
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- complete-lattice bound lemmas (`iSup₂_le_iff`, `le_iInf₂_iff`, `iInf₂_le_of_le`,
  `le_iSup₂_of_le`);
- `Bifunction.perturbationFunction` from `Chap06.Definition_6_29_1` as the nearby project pattern
  for exposing a genuine source-facing value operator directly through canonical `sInf`/`sSup`
  owners.

Primitive data vs derived API:
- primitive data: the maximizing set `C`, the minimizing set `D`, and the bifunction `K`;
- primitive source-facing value operators: `maximinValueOn C D K` and `minimaxValueOn C D K`;
- derived API: the source-order minimax inequality and the proposition `HasSaddleValueOn C D K`
  asserting equality of those two canonical values, together with value-identification theorems
  from a source-order saddle-point `Bifunction.IsSaddlePointOn C D K u v`.

Layer target: `source-facing`. This file owns the Chapter 36 minimax-value vocabulary, but it does
so directly through the canonical set-indexed owners instead of introducing a parallel package,
wrapper, or duplicate saddle-point abstraction.

Redundant source assumptions:
- the source states `C` and `D` are nonempty, but that nonemptiness is redundant for the defining
  expressions themselves once they are phrased through the canonical set-indexed owners `iSup` and
  `iInf`; later attainment statements can reintroduce nonemptiness where it is mathematically
  needed.

Notation evaluation:
- the source letters `α` and `β` are temporary local names in the prose rather than stable owner
  notation, so no notation is introduced here.
-/

section

variable [SupSet β] [InfSet β]

/-- The maximin value `sup_{u ∈ C} inf_{v ∈ D} K(u, v)` of a bifunction on `C × D`. -/
def maximinValueOn (C : Set E) (D : Set F) (K : E → F → β) : β :=
  ⨆ u ∈ C, ⨅ v ∈ D, K u v

/-- The minimax value `inf_{v ∈ D} sup_{u ∈ C} K(u, v)` of a bifunction on `C × D`. -/
def minimaxValueOn (C : Set E) (D : Set F) (K : E → F → β) : β :=
  ⨅ v ∈ D, ⨆ u ∈ C, K u v

/-- A bifunction has a saddle-value on `C × D` when its maximin and minimax values agree. -/
def HasSaddleValueOn (C : Set E) (D : Set F) (K : E → F → β) : Prop :=
  maximinValueOn C D K = minimaxValueOn C D K

/-- Whole-space bridge for the maximin value owner. -/
abbrev maximinValue (K : E → F → β) : β :=
  maximinValueOn Set.univ Set.univ K

/-- Whole-space bridge for the minimax value owner. -/
abbrev minimaxValue (K : E → F → β) : β :=
  minimaxValueOn Set.univ Set.univ K

/-- Whole-space bridge for the Chapter 36 saddle-value owner. -/
abbrev HasSaddleValue (K : E → F → β) : Prop :=
  HasSaddleValueOn Set.univ Set.univ K

end

section

variable [CompleteLattice β]

/-- The Chapter 36 maximin value is bounded above by the corresponding minimax value. -/
theorem maximin_le_minimax_on
    (C : Set E) (D : Set F) (K : E → F → β) :
    maximinValueOn C D K ≤ minimaxValueOn C D K := by
  rw [maximinValueOn, minimaxValueOn, iSup₂_le_iff]
  intro u hu
  rw [le_iInf₂_iff]
  intro v hv
  exact iInf₂_le_of_le v hv (le_iSup₂_of_le u hu le_rfl)

/-- Whole-space bridge for the Chapter 36 minimax inequality owner. -/
theorem maximin_le_minimax
    (K : E → F → β) :
    maximinValue K ≤ minimaxValue K := by
  simpa [maximinValue, minimaxValue] using
    (maximin_le_minimax_on (C := (Set.univ : Set E)) (D := (Set.univ : Set F)) (K := K))

/-- A source-order saddle-point realizes the Chapter 36 maximin value. -/
theorem IsSaddlePointOn.maximinValueOn_eq
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} {v : F} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    maximinValueOn C D K = K u v := by
  change _root_.IsSaddlePointOn D C (Function.swap K) v u at h
  apply le_antisymm
  · rw [maximinValueOn, iSup₂_le_iff]
    intro x hx
    exact le_trans (iInf₂_le v hv) (by simpa [Function.swap] using h v hv x hx)
  · trans ⨅ y ∈ D, K u y
    · refine le_iInf₂ ?_
      intro y hy
      simpa [Function.swap] using h y hy u hu
    · exact le_iSup₂_of_le u hu le_rfl

/-- A source-order saddle-point realizes the Chapter 36 maximin value. -/
theorem maximinValueOn_eq_of_isSaddlePointOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D)
    (h : IsSaddlePointOn C D K u v) :
    maximinValueOn C D K = K u v :=
  h.maximinValueOn_eq hu hv

/-- A source-order saddle-point realizes the Chapter 36 minimax value. -/
theorem IsSaddlePointOn.minimaxValueOn_eq
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} {v : F} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    minimaxValueOn C D K = K u v := by
  change _root_.IsSaddlePointOn D C (Function.swap K) v u at h
  apply le_antisymm
  · refine le_trans (iInf₂_le v hv) ?_
    rw [iSup₂_le_iff]
    intro x hx
    simpa [Function.swap] using h v hv x hx
  · refine le_iInf₂ ?_
    intro y hy
    exact le_trans (by simpa [Function.swap] using h y hy u hu)
      (le_iSup₂_of_le u hu le_rfl)

/-- A source-order saddle-point realizes the Chapter 36 minimax value. -/
theorem minimaxValueOn_eq_of_isSaddlePointOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D)
    (h : IsSaddlePointOn C D K u v) :
    minimaxValueOn C D K = K u v :=
  h.minimaxValueOn_eq hu hv

/-- A source-order saddle-point gives a saddle value on `C × D`. -/
theorem IsSaddlePointOn.hasSaddleValueOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} {v : F} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    HasSaddleValueOn C D K := by
  rw [HasSaddleValueOn]
  exact (h.maximinValueOn_eq hu hv).trans (h.minimaxValueOn_eq hu hv).symm

/-- Whole-space bridge for maximin-value identification from a source-order saddle-point. -/
theorem IsSaddlePoint.maximinValue_eq
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    maximinValue K = K u v := by
  simpa [maximinValue, IsSaddlePoint] using
    (h.maximinValueOn_eq (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (hu := by simp) (hv := by simp))

/-- Whole-space bridge for maximin-value identification from a source-order saddle-point. -/
theorem maximinValue_eq_of_isSaddlePoint
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    maximinValue K = K u v :=
  h.maximinValue_eq

/-- A source-order saddle-point gives a saddle value on `C × D`. -/
theorem hasSaddleValueOn_of_isSaddlePointOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D)
    (h : IsSaddlePointOn C D K u v) :
    HasSaddleValueOn C D K :=
  h.hasSaddleValueOn hu hv

/-- Existential source-order bridge: an explicit saddle-point witness on `C × D` yields the
Chapter 36 saddle-value owner on `C × D`. -/
theorem hasSaddleValueOn_of_exists_isSaddlePointOn
    {C : Set E} {D : Set F} {K : E → F → β}
    (h : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D K u v) :
    HasSaddleValueOn C D K := by
  rcases h with ⟨u, hu, v, hv, huv⟩
  exact hasSaddleValueOn_of_isSaddlePointOn hu hv huv

/-- Whole-space bridge for minimax-value identification from a source-order saddle-point. -/
theorem IsSaddlePoint.minimaxValue_eq
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    minimaxValue K = K u v := by
  simpa [minimaxValue, IsSaddlePoint] using
    (h.minimaxValueOn_eq (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (hu := by simp) (hv := by simp))

/-- Whole-space bridge for minimax-value identification from a source-order saddle-point. -/
theorem minimaxValue_eq_of_isSaddlePoint
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    minimaxValue K = K u v :=
  h.minimaxValue_eq

/-- Whole-space bridge: a source-order saddle-point yields a Chapter 36 saddle value. -/
theorem IsSaddlePoint.hasSaddleValue
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    HasSaddleValue K := by
  rw [HasSaddleValue]
  exact (h.maximinValue_eq).trans (h.minimaxValue_eq).symm

/-- Whole-space bridge: a source-order saddle-point yields a Chapter 36 saddle value. -/
theorem hasSaddleValue_of_isSaddlePoint
    {K : E → F → β} {u : E} {v : F}
    (h : IsSaddlePoint K u v) :
    HasSaddleValue K :=
  h.hasSaddleValue

end

end Bifunction

end
