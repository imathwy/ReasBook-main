import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Function

/-- Helper for Text 5.5.0.1: the canonical codomain lift views a finite-valued function as
`WithTopBot`-valued. -/
abbrev toWithTopBot {E : Type u} {α : Type v} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Helper for Text 5.5.0.1: backward-compatible spelling for `Function.toWithTopBot`. -/
abbrev toWithBotTop {E : Type u} {α : Type v} (f : E → α) : E → WithBotTop α :=
  f.toWithTopBot

/-- Helper for Text 5.5.0.1: the chapter owner `Function.IsConvex` is convexity of the epigraph
of a `WithTopBot`-valued function. -/
abbrev IsConvex (𝕜 : Type w) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type v} [AddCommMonoid α] [SMul 𝕜 α] [LE α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Text 5.5.0.1: convexity on all of `E` lifts to convexity of the canonical
`WithTopBot` codomain extension. -/
theorem isConvex_coe_of_convexOn_univ {𝕜 : Type w}
    [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {β : Type v} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f.toWithTopBot.IsConvex 𝕜 := by
  simpa [Function.toWithTopBot, Function.IsConvex, epi_univ_eq_setOf_le] using hf.convex_epigraph

/-- Helper for Text 5.5.0.1: coercing a finite coordinatewise supremum into `WithBotTop` equals
the corresponding indexed supremum there. -/
theorem toWithBotTop_sSup_range_eq_iSup {E : Type u} {ι : Type v} {α : Type*}
    [ConditionallyCompleteLattice α] [Nonempty ι]
    (f : E → ι → α) (hf_bddAbove : ∀ x : E, BddAbove (Set.range (f x))) :
    (fun x ↦ ((sSup (Set.range (f x)) : α) : WithBotTop α)) =
      ⨆ i : ι, fun x ↦ (f x i : WithBotTop α) := by
  funext x
  rw [iSup_apply, sSup_range]
  have h_withTop :
      ((((⨆ i : ι, f x i : α) : WithTop α) : WithBotTop α)) =
        (((⨆ i : ι, ((f x i : α) : WithTop α)) : WithTop α) : WithBotTop α) := by
    exact congrArg (fun t : WithTop α ↦ (t : WithBotTop α))
      (WithTop.coe_iSup (f := f x) (hf_bddAbove x))
  have h_bddAbove_withTop : BddAbove (Set.range fun i : ι ↦ ((f x i : α) : WithTop α)) := by
    refine ⟨((sSup (Set.range (f x)) : α) : WithTop α), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact WithTop.coe_le_coe.2 (le_csSup (hf_bddAbove x) (Set.mem_range_self i))
  have h_withBot :
      (((⨆ i : ι, ((f x i : α) : WithTop α)) : WithTop α) : WithBotTop α) =
        ⨆ i : ι, ((((f x i : α) : WithTop α) : WithBotTop α)) := by
    exact WithBot.coe_iSup (f := fun i : ι ↦ ((f x i : α) : WithTop α)) h_bddAbove_withTop
  exact h_withTop.trans h_withBot

end Function

/-- The function on a finite-coordinate space sending `x` to the supremum of its coordinates.
This owner is index-finite and scalar-agnostic; concrete coordinate models are downstream
specializations. -/
def greatestCoordinate {ι : Type u} {α : Type v} [SupSet α]
    [Finite ι] [Nonempty ι] : (ι → α) → α :=
  fun x ↦ sSup (Set.range x)

section

variable {ι : Type u} {α : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item asserts convexity of the finite nonempty-coordinate function sending
  `x` to the greatest of its coordinates.
- `core/canonical`: the owner abstractions are the chapter convexity predicate
  `Function.IsConvex`, the closure theorem `Function.IsConvex.iSup` for pointwise suprema, and
  the linear coordinate projections `LinearMap.proj i`.
- `bridge/view`: the textbook greatest-coordinate function is the finite supremum
  `sSup (Set.range x)` of the coordinates of `x`, and after coercion to `WithTopBot α` it is the
  indexed supremum of the coordinate projections `x ↦ x i`.
- Primitive data vs derived API: `greatestCoordinate` is the primitive source-facing owner, with
  nonemptiness of the index type included in the owner layer (so no empty-index sentinel value is
  encoded in the definition). The canonical convexity theorem is stated directly on the indexed
  `iSup` owner; the finite-owner `greatestCoordinate` convexity theorem is derived through the
  `toWithTopBot` bridge.
- Domain-style sampling used here: the project bridge `Function.toWithTopBot`,
  `Function.toWithBotTop_sSup_range_eq_iSup` (compatibility theorem name),
  `Function.IsConvex.iSup`,
  `Function.isConvex_coe_of_convexOn_univ`, `LinearMap.proj`, `LinearMap.convexOn`, and
  `Finite.bddAbove_range`.
- Assumption layer for the convexity theorem:
  scalar assumptions come from the convexity API (`Function.IsConvex.iSup` and
  `Function.isConvex_coe_of_convexOn_univ`), while codomain assumptions come from finite `sSup`
  and order-compatible scalar monotonicity; the scalar and codomain are kept decoupled.
- Layer target: `source-facing`, with the owner defined once at the finite-index level and reused
  by the later positive-homogeneity and simplex-support-function items.
-/

section finiteIndex

variable [Finite ι]

@[simp] theorem greatestCoordinate_apply [SupSet α] [Nonempty ι] (x : ι → α) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

theorem greatestCoordinate_toWithBotTop_eq_iSup [ConditionallyCompleteLattice α]
    [Nonempty ι] :
    greatestCoordinate.toWithBotTop =
      ⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α) := by
  simpa [greatestCoordinate] using
    (Function.toWithBotTop_sSup_range_eq_iSup
      (f := fun x : ι → α ↦ fun i : ι ↦ x i)
      (hf_bddAbove := fun x : ι → α ↦ Finite.bddAbove_range x))

/-- Canonical owner bridge: coercing `greatestCoordinate` to `WithTopBot` is the pointwise
coordinate supremum. This is definitionally equivalent to
`greatestCoordinate_toWithBotTop_eq_iSup`. -/
theorem greatestCoordinate_toWithTopBot_eq_iSup [ConditionallyCompleteLattice α]
    [Nonempty ι] :
    greatestCoordinate.toWithTopBot =
      ⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α) := by
  simpa using (greatestCoordinate_toWithBotTop_eq_iSup (ι := ι) (α := α))

end finiteIndex

/-- Helper for Text 5.5.0.1: each coordinate is bounded above by the greatest coordinate. -/
private theorem coordinate_le_greatestCoordinate [ConditionallyCompleteLattice α]
    [Finite ι] [Nonempty ι] (x : ι → α) (i : ι) :
    x i ≤ greatestCoordinate x := by
  -- The `i`-th coordinate is one of the values appearing in the finite range supremum.
  rw [greatestCoordinate_apply]
  exact le_csSup (Finite.bddAbove_range x) (Set.mem_range_self i)

/-- Helper for Text 5.5.0.1: the finite supremum of the coordinate projections satisfies Jensen's
inequality on `Set.univ`. -/
private theorem convexOn_univ_greatestCoordinate {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α]
    [Finite ι] [Nonempty ι] :
    ConvexOn R (Set.univ : Set (ι → α)) (greatestCoordinate : (ι → α) → α) := by
  -- Route correction: prove Jensen directly on the finite supremum owner, then lift to
  -- `toWithBotTop`; the chapter `iSup` closure theorem is exposed on the dual `WithTopBot` owner.
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Compare each coordinate of the convex combination to the same convex combination of the
  -- coordinate suprema, then take the supremum over all coordinates.
  rw [greatestCoordinate_apply, greatestCoordinate_apply, greatestCoordinate_apply]
  refine csSup_le (Set.range_nonempty (a • x + b • y)) ?_
  rintro z ⟨i, rfl⟩
  change a • x i + b • y i ≤ a • sSup (Set.range x) + b • sSup (Set.range y)
  exact add_le_add
    (smul_le_smul_of_nonneg_left
      (coordinate_le_greatestCoordinate (ι := ι) (α := α) x i) ha)
    (smul_le_smul_of_nonneg_left
      (coordinate_le_greatestCoordinate (ι := ι) (α := α) y i) hb)

section finiteIndex

variable [Finite ι]

/-- Text 5.5.0.1: the greatest-coordinate function is convex. -/
theorem greatestCoordinate_isConvex {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α] [Nonempty ι] :
    ((greatestCoordinate : (ι → α) → α).toWithBotTop).IsConvex R := by
  -- Lift the finite-valued Jensen proof to the chapter extended-value owner.
  exact Function.isConvex_coe_of_convexOn_univ
    (convexOn_univ_greatestCoordinate (ι := ι) (α := α) (R := R))

/-- Canonical owner form behind Text 5.5.0.1: the `WithBotTop`-valued coordinate supremum is
convex. -/
theorem iSup_coordinate_isConvex {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α] [Nonempty ι] :
    (⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α)).IsConvex R := by
  -- Rewrite the indexed-supremum bridge back to `greatestCoordinate`.
  rw [← greatestCoordinate_toWithBotTop_eq_iSup]
  exact greatestCoordinate_isConvex (ι := ι) (α := α) (R := R)

end finiteIndex

end
