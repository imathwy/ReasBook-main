import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open Bornology

variable {X : Type u} {ι : Sort v} {α : Type w}
variable [Bornology α]

/-
Source/core/bridge triage:
- `source-facing`: the textbook phrase "uniformly bounded on `S`" is one common two-sided
  scalar bound for all values `f i x` with `x ∈ S`.
- `core/canonical`: the owner is the canonical bornology primitive `Bornology.IsBounded` on the
  canonical evaluation image `Set.image2 (fun g x ↦ g x) (Set.range f) S`.
- `bridge/view`: `uniformlyBoundedOn_iff_exists_bounds` and
  `uniformlyBoundedOn_iff_exists_bounds_mapsTo` are textbook quantifier and `MapsTo` bridges from
  that canonical owner surface.
- Domain-style sampling used here:
  `Bornology.IsBounded`, `isBounded_iff_bddBelow_bddAbove`,
  `bddBelow_bddAbove_iff_subset_Icc`.
- Primitive data vs derived API:
  primitive data: the subset `S` and the indexed family `f : ι → X → α`;
  derived API: the chapter owner `UniformlyBoundedOn f S` and its order-bounded reformulations.
- Layer target: `source-facing`; the chapter predicate is retained, but now directly exposes the
  canonical owner primitive rather than introducing an additional set-family owner wrapper.
-/

/-- Definition 10.5.7 (owner layer): a family of `α`-valued functions is uniformly bounded on `S`
when the common value set of all pairs `(i, x)` with `x ∈ S` is bounded in the ambient bornology
on `α`. -/
def UniformlyBoundedOn (f : ι → X → α) (S : Set X) : Prop :=
  IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S)

/-- Monotonicity in the subset variable: if `f` is uniformly bounded on `S`, then it is uniformly
bounded on every `T ⊆ S`. -/
theorem UniformlyBoundedOn.mono {f : ι → X → α} {S T : Set X}
    (h : UniformlyBoundedOn f S) (hTS : T ⊆ S) :
    UniformlyBoundedOn f T := by
  refine (show IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S) from h).subset ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact Set.mem_image2_of_mem hg (hTS hx)

/-- Owner-elimination lemma on subtype points: from `UniformlyBoundedOn f S`, each subtype fiber
`Set.range (fun i ↦ f i x)` is bounded. -/
theorem UniformlyBoundedOn.isBounded_range_subtype {f : ι → X → α} {S : Set X}
    (h : UniformlyBoundedOn f S) (x : S) :
    IsBounded (Set.range fun i ↦ f i x) := by
  refine (show IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S) from h).subset ?_
  rintro y ⟨i, rfl⟩
  exact Set.mem_image2_of_mem ⟨i, rfl⟩ x.2

/-- Owner-elimination lemma on ambient points: from `UniformlyBoundedOn f S`, each fiber
`Set.range (fun i ↦ f i x)` at `x ∈ S` is bounded. -/
theorem UniformlyBoundedOn.isBounded_range {f : ι → X → α} {S : Set X}
    (h : UniformlyBoundedOn f S) {x : X} (hx : x ∈ S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  h.isBounded_range_subtype ⟨x, hx⟩

/-- Intrinsic subtype bridge for families: `f` is uniformly bounded on `S` iff two common bounds
work for every index at every subtype point `x : S`. -/
theorem uniformlyBoundedOn_iff_exists_bounds_subtype [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ x : S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂ := by
  let T : Set α := Set.image2 (fun g x ↦ g x) (Set.range f) S
  rw [UniformlyBoundedOn, isBounded_iff_bddBelow_bddAbove, bddBelow_bddAbove_iff_subset_Icc]
  change (∃ α₁ α₂ : α, T ⊆ Set.Icc α₁ α₂) ↔
    ∃ α₁ α₂ : α, ∀ x : S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂
  constructor
  · rintro ⟨α₁, α₂, hT⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x i
    have hmem : f i x ∈ T := Set.mem_image2_of_mem ⟨i, rfl⟩ x.2
    simpa [Set.mem_Icc] using hT hmem
  · rintro ⟨α₁, α₂, hT⟩
    refine ⟨α₁, α₂, ?_⟩
    rintro y ⟨g, hg, x, hx, rfl⟩
    rcases hg with ⟨i, rfl⟩
    simpa [Set.mem_Icc] using hT ⟨x, hx⟩ i

/-- A family of `α`-valued functions is uniformly bounded on `S` exactly when there are two
bounds `α₁` and `α₂` satisfying `α₁ ≤ f i x ≤ α₂` for every `x ∈ S` and every index `i`. -/
theorem uniformlyBoundedOn_iff_exists_bounds [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ x ∈ S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂ := by
  rw [uniformlyBoundedOn_iff_exists_bounds_subtype]
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x hx i
    exact h ⟨x, hx⟩ i
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x i
    exact h x x.2 i

/-- Intrinsic bridge for indexed families: `f` is uniformly bounded on `S` iff each `f i` maps
`S` into one common interval `Set.Icc α₁ α₂`. -/
theorem uniformlyBoundedOn_iff_exists_bounds_mapsTo [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ i, Set.MapsTo (f i) S (Set.Icc α₁ α₂) := by
  rw [uniformlyBoundedOn_iff_exists_bounds]
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro i x hx
    exact h x hx i
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x hx i
    exact h i hx

end
