import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {X : Type u} {ι : Sort v} {Y : Type*}
variable [Bornology Y]

open Bornology

/-!
Source/core/bridge triage:
- `source-facing`: Definition 10.5.6 names the condition that a family of `Y`-valued functions is
  bounded at each point of a subset `S`.
- `core/canonical`: the intrinsic owner abstraction is the set-family predicate
  `Set.PointwiseBoundedOn F S`, defined by applying the canonical bornology owner
  `Bornology.IsBounded` to the restricted family in `S → Y`, so pointwise boundedness is expressed
  in the Pi-space bornology independently of any indexing model.
- `bridge/view`: the intrinsic subtype-indexed fiberwise and order-bounded reformulations
  `Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype` and
  `Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype`; the chapter indexed owner
  `PointwiseBoundedOn f S` is a thin bridge through `Set.range`.

Domain-style sampling used here:
- `Bornology.IsBounded`;
- `Bornology.forall_isBounded_image_eval_iff`;
- `Function.eval`;
- `isBounded_iff_bddBelow_bddAbove`;
- `Bornology.IsBounded.bddBelow`;
- `Bornology.IsBounded.bddAbove`.

Primitive data vs derived API:
- primitive data: a subset `S` and a family set `F : Set (X → Y)`;
- derived API: the chapter predicate `PointwiseBoundedOn f S`, obtained canonically as
  `(Set.range f).PointwiseBoundedOn S`, with subtype-indexed and ambient companion reformulations.

Layer target: `source-facing`; the textbook indexed-family predicate is kept as chapter
vocabulary, now stated directly on the canonical bornology owner on the restricted function space
`S → Y`, with fiberwise and order-theoretic reformulations kept as thin bridges.
-/

/-- Intrinsic owner for pointwise boundedness on `S`: a family set `F` is pointwise bounded on `S`
when the restricted family in `S → Y` is bounded in the canonical function-space bornology. -/
def Set.PointwiseBoundedOn (F : Set (X → Y)) (S : Set X) : Prop :=
  IsBounded ((fun g : X → Y ↦ fun x : S ↦ g x) '' F)

/-- Intrinsic fiberwise bridge for family sets: pointwise boundedness on `S` is equivalent to
boundedness of each evaluation image over subtype points `x : S`. -/
theorem Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype
    {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x : S, IsBounded ((fun g : X → Y ↦ g x) '' F) := by
  have hEval (x : S) :
      Function.eval x '' ((fun g : X → Y ↦ fun y : S ↦ g y) '' F) =
        (fun g : X → Y ↦ g x) '' F := by
    ext y
    constructor
    · rintro ⟨h, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(fun y : S ↦ g y), ⟨g, hg, rfl⟩, rfl⟩
  rw [Set.PointwiseBoundedOn, ← forall_isBounded_image_eval_iff]
  constructor
  · intro h x
    simpa [hEval x] using h x
  · intro h x
    simpa [hEval x] using h x

/-- Owner-elimination lemma on subtype points: from `F.PointwiseBoundedOn S`, each subtype
evaluation image `((fun g ↦ g x) '' F)` is bounded. -/
theorem Set.PointwiseBoundedOn.isBounded_image_eval_subtype
    {S : Set X} {F : Set (X → Y)} (h : F.PointwiseBoundedOn S) (x : S) :
    IsBounded ((fun g : X → Y ↦ g x) '' F) :=
  (Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype.mp h) x

/-- Textbook ambient bridge for family sets: pointwise boundedness on `S` is equivalent to
boundedness of each evaluation image at points `x ∈ S`. -/
theorem Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x ∈ S, IsBounded ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Owner-elimination lemma on ambient points: from `F.PointwiseBoundedOn S`, each evaluation
image at `x ∈ S` is bounded. -/
theorem Set.PointwiseBoundedOn.isBounded_image_eval
    {S : Set X} {F : Set (X → Y)} (h : F.PointwiseBoundedOn S) {x : X} (hx : x ∈ S) :
    IsBounded ((fun g : X → Y ↦ g x) '' F) :=
  (Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval.mp h) x hx

/-- Intrinsic order bridge for family sets: for an order-bornology codomain, pointwise
boundedness on `S` is equivalent to two-sided order bounds on each subtype-indexed evaluation
image. -/
theorem Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype
    [Preorder Y] [IsOrderBornology Y] {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x : S, BddBelow ((fun g : X → Y ↦ g x) '' F) ∧
        BddAbove ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  simp [isBounded_iff_bddBelow_bddAbove]

/-- Textbook ambient order bridge for family sets: for an order-bornology codomain, pointwise
boundedness on `S` is equivalent to two-sided order bounds on each evaluation image at points
`x ∈ S`. -/
theorem Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval
    [Preorder Y] [IsOrderBornology Y] {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x ∈ S,
        BddBelow ((fun g : X → Y ↦ g x) '' F) ∧
          BddAbove ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Definition 10.5.6 (source-facing indexed bridge): an indexed family is pointwise bounded on
`S` when its range family set is pointwise bounded on `S` in the intrinsic owner layer. -/
def PointwiseBoundedOn (f : ι → X → Y) (S : Set X) : Prop :=
  (Set.range f).PointwiseBoundedOn S

/-- Intrinsic fiberwise bridge for indexed families: pointwise boundedness on `S` is equivalent to
boundedness of each fiber over subtype points `x : S`. -/
theorem pointwiseBoundedOn_iff_forall_isBounded_range_subtype {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x : S, IsBounded (Set.range fun i ↦ f i x) := by
  rw [PointwiseBoundedOn, Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  have hRange (x : S) :
      (fun g : X → Y ↦ g x) '' Set.range f = Set.range (fun i ↦ f i x) := by
    ext y
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  constructor
  · intro h x
    simpa [hRange x] using h x
  · intro h x
    simpa [hRange x] using h x

/-- Owner-elimination lemma on subtype points: from `PointwiseBoundedOn f S`, each subtype fiber
`Set.range (fun i ↦ f i x)` is bounded. -/
theorem PointwiseBoundedOn.isBounded_range_subtype {S : Set X} {f : ι → X → Y}
    (h : PointwiseBoundedOn f S) (x : S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  (pointwiseBoundedOn_iff_forall_isBounded_range_subtype.mp h) x

/-- Textbook ambient bridge: pointwise boundedness on `S` is equivalent to boundedness of each
fiber at points `x ∈ S`. -/
theorem pointwiseBoundedOn_iff_forall_isBounded_range {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x ∈ S, IsBounded (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_forall_isBounded_range_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Owner-elimination lemma on ambient points: from `PointwiseBoundedOn f S`, each fiber at
`x ∈ S` is bounded. -/
theorem PointwiseBoundedOn.isBounded_range {S : Set X} {f : ι → X → Y}
    (h : PointwiseBoundedOn f S) {x : X} (hx : x ∈ S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  (pointwiseBoundedOn_iff_forall_isBounded_range.mp h) x hx

/-- Intrinsic order bridge: for an order-bornology codomain, pointwise boundedness on `S` is
equivalent to two-sided order bounds on each subtype-indexed fiber. -/
theorem pointwiseBoundedOn_iff_bddBelow_bddAbove_subtype [Preorder Y] [IsOrderBornology Y]
    {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x : S, BddBelow (Set.range fun i ↦ f i x) ∧ BddAbove (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_forall_isBounded_range_subtype]
  simp [isBounded_iff_bddBelow_bddAbove]

/-- Textbook ambient order bridge: for an order-bornology codomain, pointwise boundedness on `S`
is equivalent to two-sided order bounds on each fiber at points `x ∈ S`. -/
theorem pointwiseBoundedOn_iff_bddBelow_bddAbove [Preorder Y] [IsOrderBornology Y]
    {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x ∈ S, BddBelow (Set.range fun i ↦ f i x) ∧ BddAbove (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_bddBelow_bddAbove_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

end
