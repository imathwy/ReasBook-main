import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.5.10 identifies convex cones in `ℝ^n` as subsets that are both
  cones and convex, so the primary public surface is the unbundled subset predicate
  `Set.IsConvexCone R K`.
- `core/canonical`: the bundled owner abstraction is `ConvexCone R E`, and its canonical owner
  construction on subsets is `ConvexCone.hull R K`.
- `bridge/view`: `Set.IsCone.hull_eq` and `Set.IsConvexCone.hull_eq_iff` connect the
  source-facing subset predicate to the bundled owner.
- Primitive data vs derived API: the source-facing owner is `Set.IsConvexCone R K`, while the
  primitive bridge into the bundled owner uses the raw cone data `Set.IsCone R K` together with
  additive closure. The convex-facing hull fixed-point statements are then derived API.
- Domain-style sampling used here: the chapter owner `Set.IsCone` from Definition 2.5.9 together
  with mathlib's `ConvexCone R E`, `ConvexCone.hull`, `ConvexCone.hull_le_iff`,
  `ConvexCone.convex`, and the chapter bridge `ConvexCone.isCone`. These confirm that there is no
  upstream set-level owner beyond the conjunction itself, while the bundled owner remains the
  right target for companion bridge lemmas.
- Layer target: `source-facing` for the numbered item itself, with `bridge/view` companion lemmas
  for the bundled hull.
-/

section SourceFacing

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

/-- Definition 2.5.10: a subset is a convex cone if it is both a cone and convex. This keeps the
textbook subset-level notion as the main public surface with a short owner name. -/
def IsConvexCone (R : Type v) [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [SMul R E] (K : Set E) : Prop :=
  Set.IsCone R K ∧ Convex R K

@[simp] theorem isConvexCone_iff (K : Set E) :
    IsConvexCone R K ↔ Set.IsCone R K ∧ Convex R K :=
  Iff.rfl

namespace IsConvexCone

theorem isCone {K : Set E} (hK : Set.IsConvexCone R K) : Set.IsCone R K :=
  hK.1

theorem convex {K : Set E} (hK : Set.IsConvexCone R K) : Convex R K :=
  hK.2

end IsConvexCone
end Set

end SourceFacing

section PrimitiveHullBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set.IsCone

/-- A cone with additive closure is fixed by the canonical owner hull. This is the primitive
set-level bridge to the bundled `ConvexCone` owner. -/
theorem hull_eq {K : Set E} (hK : Set.IsCone R K)
    (hadd : K + K ⊆ K) :
    (ConvexCone.hull R K : Set E) = K := by
  let C : ConvexCone R E := {
    carrier := K
    smul_mem' := fun _ hc _ hx ↦ hK.smul_mem hc hx
    add_mem' := fun {_} hx {_} hy ↦ hadd (Set.add_mem_add hx hy)
  }
  simpa [C] using
    congrArg (fun D : ConvexCone R E ↦ (D : Set E)) (ConvexCone.gi.l_u_eq C)

/-- Primitive owner-level fixed-point criterion for `ConvexCone.hull`: a set is fixed by the hull
exactly when it is both a cone and closed under pointwise set addition. -/
theorem hull_eq_iff (K : Set E) :
    (ConvexCone.hull R K : Set E) = K ↔ Set.IsCone R K ∧ K + K ⊆ K := by
  constructor
  · intro hHull
    refine ⟨by simpa [hHull] using (ConvexCone.hull R K).isCone, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hxHull : x ∈ (ConvexCone.hull R K : Set E) := by simpa [hHull] using hx
    have hyHull : y ∈ (ConvexCone.hull R K : Set E) := by simpa [hHull] using hy
    have hzHull : x + y ∈ (ConvexCone.hull R K : Set E) :=
      (ConvexCone.hull R K).add_mem hxHull hyHull
    simpa [hHull] using hzHull
  · intro hK
    exact hK.1.hull_eq hK.2

end Set.IsCone

end PrimitiveHullBridge

section PrimitiveSourceBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set.IsConvexCone

/-- Primitive source-facing bridge: if a source-facing convex cone is also known to be closed under
set addition, then it is fixed by the canonical owner hull. This keeps the hull fixed-point API at
the weaker semiring layer when additive closure is available as primitive data. -/
theorem hull_eq_of_add_subset {K : Set E} (hK : Set.IsConvexCone R K)
    (hadd : K + K ⊆ K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.isCone.hull_eq hadd

end Set.IsConvexCone

end PrimitiveSourceBridge

section BundledBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace ConvexCone

/-- Every bundled convex cone is source-facing convex after forgetting to its carrier set. -/
theorem isConvexCone (C : ConvexCone R E) : Set.IsConvexCone R (C : Set E) := by
  refine ⟨C.isCone, ?_⟩
  refine C.isCone.convex_of_add_subset ?_
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact C.add_mem hx hy

end ConvexCone

end BundledBridge

section WeakHullBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace Set.IsConvexCone

/-- Any set fixed by the canonical owner hull is source-facing convex-cone valued. This direction
works at the weaker semiring/action layer, without the division-semiring assumptions used in
`Set.IsConvexCone.hull_eq`. -/
theorem of_hull_eq {K : Set E} (hK : (ConvexCone.hull R K : Set E) = K) :
    Set.IsConvexCone R K := by
  rcases (Set.IsCone.hull_eq_iff (R := R) K).1 hK with ⟨hCone, hAdd⟩
  exact ⟨hCone, hCone.convex_of_add_subset hAdd⟩

end Set.IsConvexCone

end WeakHullBridge

section Bridge

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set.IsConvexCone

/-- A source-facing convex cone is closed under addition. -/
theorem add_mem {K : Set E} (hK : Set.IsConvexCone R K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ K := by
  exact (hK.isCone.convex_iff_add_subset.mp hK.convex) (Set.add_mem_add hx hy)

/-- A source-facing convex cone is closed under set addition. -/
theorem add_subset {K : Set E} (hK : Set.IsConvexCone R K) :
    K + K ⊆ K := by
  exact hK.isCone.convex_iff_add_subset.mp hK.convex

/-- A source-facing convex cone is fixed by the canonical owner hull. -/
theorem hull_eq {K : Set E} (hK : Set.IsConvexCone R K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.hull_eq_of_add_subset hK.add_subset

/-- Owner-level canonical bridge: a subset is a convex cone exactly when it is fixed by the
`ConvexCone` hull. -/
theorem hull_eq_iff (K : Set E) :
    Set.IsConvexCone R K ↔ (ConvexCone.hull R K : Set E) = K := by
  constructor
  · intro hK
    exact hK.hull_eq
  · intro hK
    exact Set.IsConvexCone.of_hull_eq hK

end Set.IsConvexCone

namespace Set.IsCone

/-- A convex cone is closed under addition. -/
theorem add_mem {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ K := by
  exact (hK.convex_iff_add_subset.mp hconv) (Set.add_mem_add hx hy)

/-- A cone that is convex is closed under set addition. -/
theorem add_subset {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K) :
    K + K ⊆ K := by
  exact hK.convex_iff_add_subset.mp hconv

/-- A cone that is convex is fixed by the canonical owner hull. -/
theorem hull_eq_of_convex {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.hull_eq (hK.add_subset hconv)

end Set.IsCone

end Bridge
