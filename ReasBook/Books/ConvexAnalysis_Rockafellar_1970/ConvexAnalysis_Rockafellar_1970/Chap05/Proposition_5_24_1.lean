import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_4

noncomputable section

open scoped SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.1 starts with geometric prose about a complete
  non-decreasing curve in `ℝ²`; that descriptive first sentence is already the content of the
  Chapter 5 owner `SetRel.IsCompleteNondecreasingCurve`. The new precise mathematical content is
  the claim that the coordinate-sum parameter `T(x, x⋆) = x + x⋆` identifies the curve
  homeomorphically with `ℝ`.
- `core/canonical`: graph-like multivalued objects in this chapter are organized as relations
  `SetRel`; the coordinate-sum bridge itself uses only the additive structure of endpoint types,
  while the canonical topology owner for “continuous in both directions, one-to-one, and onto” is
  mathlib's `IsHomeomorph`.
- `bridge/view`: this file adds only the explicit coordinate-sum map on the subtype `Γ` and states
  the proposition on that map, rather than introducing a second packaged notion of “true curve”.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` and `Function.completeNondecreasingCurve` from
  `Items/Chap05/Definition_5_24_4.lean`;
- `IsHomeomorph` from `Mathlib/Topology/Homeomorph/Defs.lean`;
- order-boundedness owners `BddAbove` and `BddBelow` from mathlib's order API.

Primitive data vs derived API:
- primitive bridge data introduced here: for any additive relation `Γ : SetRel X Y`, the
  coordinate-sum map `Γ.coordinateSumMap : Γ → Z`, i.e. the restriction of `x + y` to the
  relation subtype `Γ`;
- primitive relation-side owner: the coordinate-sum value set `Γ.coordinateSums`;
- primitive range bridge data: generic order-theoretic lemmas saying surjective maps have
  unbounded range in codomains without top/bottom elements, used as bridge lemmas;
- derived conclusion here: if the coordinate-sum map is surjective (in particular if it is an
  `IsHomeomorph`), then `Γ.coordinateSums` is unbounded above and below.

Layer target: `bridge/view`. The first sentence of the source proposition is geometric
interpretation of the owner from Definition 5.24.4, while the formal theorem content here is the
Minty-style coordinate-sum bridge at the canonical API layer.
-/

namespace SetRel

section

variable {X Y Z : Type*} [HAdd X Y Z]

/-- The coordinate-sum parameter on a relation with additive coordinates. -/
abbrev coordinateSumMap (Γ : SetRel X Y) : Γ → Z :=
  fun p ↦ p.1.1 + p.1.2

/-- Evaluating the coordinate-sum map on a point of the graph returns the sum of its two
coordinates. -/
@[simp]
theorem coordinateSumMap_apply {Γ : SetRel X Y} {x : X} {xStar : Y}
    (h : x ~[Γ] xStar) :
    Γ.coordinateSumMap ⟨(x, xStar), h⟩ = x + xStar := rfl

/-- Intrinsic owner for the coordinate-sum values of a relation:
`{x + x⋆ | x ~[Γ] x⋆}`. -/
abbrev coordinateSums (Γ : SetRel X Y) : Set Z :=
  Set.range Γ.coordinateSumMap

/-- Membership in `Γ.coordinateSums` is exactly representability as `x + x⋆` along `Γ`. -/
@[simp]
theorem mem_coordinateSums_iff {Γ : SetRel X Y} {z : Z} :
    z ∈ Γ.coordinateSums ↔ ∃ x : X, ∃ xStar : Y, x ~[Γ] xStar ∧ z = x + xStar := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1, p.1.2, p.2, rfl⟩
  · rintro ⟨x, xStar, h, rfl⟩
    exact ⟨⟨(x, xStar), h⟩, rfl⟩

end

end SetRel

namespace Function

section

variable {α β : Type*} [LE β]

/- Primitive order-level range bridge: surjectivity already forces the range to be all of the
codomain, so unboundedness follows as soon as the codomain has no top element. -/
namespace Surjective

/-- A surjective function into a type with `≤` and no top element has unbounded-above range. -/
theorem not_bddAbove_range [NoTopOrder β] {f : α → β} (hf : Function.Surjective f) :
    ¬ BddAbove (Set.range f) := by
  rw [hf.range_eq]
  intro h
  rcases h with ⟨a, ha⟩
  rcases NoTopOrder.exists_not_le a with ⟨b, hb⟩
  exact hb (ha (by simp))

/- Dual primitive range bridge for lower bounds. -/
/-- A surjective function into a type with `≤` and no bottom element has unbounded-below range. -/
theorem not_bddBelow_range [NoBotOrder β] {f : α → β} (hf : Function.Surjective f) :
    ¬ BddBelow (Set.range f) := by
  rw [hf.range_eq]
  intro h
  rcases h with ⟨a, ha⟩
  rcases NoBotOrder.exists_not_ge a with ⟨b, hb⟩
  exact hb (ha (by simp))

end Surjective

end

end Function

section

variable {X Y Z : Type*} [HAdd X Y Z] [LE Z]
variable {Γ : SetRel X Y}

namespace Function
namespace Surjective

-- Proof sketch: this is the coordinate-sum specialization of the generic function-level
-- surjective-range bridge above.
/-- If the coordinate-sum map on `Γ` is surjective and the codomain has no top element, then
`Γ.coordinateSums` is unbounded above. -/
theorem not_bddAbove_coordinateSums [NoTopOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddAbove Γ.coordinateSums :=
  hT.not_bddAbove_range

-- Proof sketch: same specialization as above, now for lower bounds.
/-- If the coordinate-sum map on `Γ` is surjective and the codomain has no bottom element, then
`Γ.coordinateSums` is unbounded below. -/
theorem not_bddBelow_coordinateSums [NoBotOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddBelow Γ.coordinateSums :=
  hT.not_bddBelow_range

/-- Bridge form: unboundedness of `Γ.coordinateSums` stated as unboundedness of the subtype-map
range. -/
theorem not_bddAbove_range_coordinateSumMap [NoTopOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddAbove (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddAbove_coordinateSums

/-- Bridge form: lower-unboundedness of `Γ.coordinateSums` stated on the subtype-map range. -/
theorem not_bddBelow_range_coordinateSumMap [NoBotOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddBelow (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddBelow_coordinateSums

end Surjective
end Function

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsHomeomorph

/-- Homeomorphic coordinate-sum parametrizations are automatically unbounded above in codomains
without top element. -/
theorem not_bddAbove_coordinateSums [NoTopOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddAbove Γ.coordinateSums :=
  hT.surjective.not_bddAbove_coordinateSums

/-- Homeomorphic coordinate-sum parametrizations are automatically unbounded below in codomains
without bottom element. -/
theorem not_bddBelow_coordinateSums [NoBotOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddBelow Γ.coordinateSums :=
  hT.surjective.not_bddBelow_coordinateSums

/-- Bridge form of `IsHomeomorph.not_bddAbove_coordinateSums` on the subtype-map range. -/
theorem not_bddAbove_range_coordinateSumMap [NoTopOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddAbove (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddAbove_coordinateSums

/-- Bridge form of `IsHomeomorph.not_bddBelow_coordinateSums` on the subtype-map range. -/
theorem not_bddBelow_range_coordinateSumMap [NoBotOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddBelow (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddBelow_coordinateSums

end IsHomeomorph

end
