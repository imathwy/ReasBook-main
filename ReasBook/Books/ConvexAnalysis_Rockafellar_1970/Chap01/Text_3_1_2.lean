import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.2 characterizes convex cones through the short source owner
  `Set.IsConvexCone R K` by positive-scalar closure and closure under set addition.
  Coordinate-model textbook statements are obtained as downstream specializations.
- `core/canonical`: the owner-side criteria already live upstream as
  `Set.isCone_iff_pos_smul_subset` (canonical setwise form) together with
  `Set.isCone_iff_forall_pos_smul_subset` (pointwise bridge form) for the cone part, and
  `Set.IsCone.convex_iff_add_subset` for the convexity part under a cone hypothesis.
- `bridge/view`: the source-facing pointwise closure statement
  `(∀ c > 0, c • K ⊆ K)` is a bridge restatement of the owner predicate `Set.IsCone R K`.
- Primitive data vs derived API: the primitive source predicate is `Set.IsCone R K`; pointwise
  scalar-closure inclusion is derived via `Set.isCone_iff_forall_pos_smul_subset`.
- Domain-style sampling: this refinement reuses `Set.IsCone`,
  `Set.isCone_iff_forall_pos_smul_subset`, and `Set.IsCone.convex_iff_add_subset`.
- Layer target: `source-facing` with a primitive bridge theorem at the weaker
  `Set.IsConvexCone`-definition layer and Text 3.1.2 as the stronger additive bridge.
-/

/- Canonicalization audit (this pass):
- Codomain/ambient layer check: no `EReal`/`ℝ`-specific codomain appears; keep the semiring layer.
- Scalar/ambient structure check: the positive-scalar/convex bridge stays at the weak
  `Semiring`/`SMul` layer; additive-closure equivalence keeps the division layer required by
  `Set.IsCone.convex_iff_add_subset`.
- Owner check: keep the short source owner `Set.IsConvexCone` and expose owner-prefixed bridge
  constructors/projections.
- Topology check: not applicable in this item.
- Notation check: reuse existing pointwise notation `c • K` and `K + K`; no new notation layer.
-/

section PrimitiveBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

namespace IsConvexCone

/-- A source-facing convex cone is closed under every positive scalar action on its carrier set. -/
theorem pos_smul_subset {K : Set E} (hK : IsConvexCone R K) :
    ∀ c : R, 0 < c → c • K ⊆ K := by
  intro c hc
  exact hK.isCone.smul_set_subset hc

/-- Constructor bridge from positive-scalar set closure and convexity to the source owner
`Set.IsConvexCone`. -/
theorem of_pos_smul_subset_and_convex {K : Set E}
    (hsmul : ∀ c : R, 0 < c → c • K ⊆ K) (hconv : Convex R K) :
    IsConvexCone R K := by
  exact ⟨(isCone_iff_forall_pos_smul_subset K).2 hsmul, hconv⟩

end IsConvexCone

/-- Primitive owner-level bridge: a subset is a convex cone iff it is closed under positive scalar
set multiplication and is convex. This theorem stays at the weak structure layer of
`Set.IsConvexCone` and `Set.isCone_iff_forall_pos_smul_subset`. -/
theorem IsConvexCone.iff_pos_smul_subset_and_convex (K : Set E) :
    IsConvexCone R K ↔ (∀ c : R, 0 < c → c • K ⊆ K) ∧ Convex R K := by
  constructor
  · intro hK
    exact ⟨hK.pos_smul_subset, hK.convex⟩
  · rintro ⟨hsmul, hconv⟩
    exact IsConvexCone.of_pos_smul_subset_and_convex hsmul hconv

end Set

end PrimitiveBridge

section WeakAdditiveConstructor

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace Set

namespace IsConvexCone

/-- Weak-layer constructor bridge from conehood and additive closure to the source owner
`Set.IsConvexCone`. -/
theorem of_isCone_and_add_subset {K : Set E} (hcone : IsCone R K)
    (hadd : K + K ⊆ K) : IsConvexCone R K := by
  refine ⟨hcone, convex_iff_add_mem.2 ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by simpa [ha0] using hab
    simpa [ha0, hb1] using hy
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      simpa [hb0, ha1] using hx
    · have ha_pos : (0 : R) < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : (0 : R) < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact hadd (Set.add_mem_add (hcone.smul_mem ha_pos hx) (hcone.smul_mem hb_pos hy))

end IsConvexCone

end Set

end WeakAdditiveConstructor

section AdditiveBridge

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set

/-- Owner-level canonical form of Text 3.1.2: a subset is a convex cone iff it is a cone and is
closed under set addition. -/
theorem IsConvexCone.iff_isCone_and_add_subset (K : Set E) :
    IsConvexCone R K ↔ IsCone R K ∧ K + K ⊆ K := by
  constructor
  · intro hK
    exact ⟨hK.isCone, hK.add_subset⟩
  · rintro ⟨hcone, hadd⟩
    exact IsConvexCone.of_isCone_and_add_subset hcone hadd

/-- Text 3.1.2 in source-facing pointwise form: a subset of a module over a partially ordered
division semiring is a convex cone iff every positive scalar multiple `c • K` is contained in `K`
and the sum set `K + K` is contained in `K`. -/
theorem IsConvexCone.iff_pos_smul_subset_and_add_subset (K : Set E) :
    IsConvexCone R K ↔ (∀ c : R, 0 < c → c • K ⊆ K) ∧ K + K ⊆ K := by
  simpa [isCone_iff_forall_pos_smul_subset K] using
    (IsConvexCone.iff_isCone_and_add_subset (K := K))

end Set

end AdditiveBridge
