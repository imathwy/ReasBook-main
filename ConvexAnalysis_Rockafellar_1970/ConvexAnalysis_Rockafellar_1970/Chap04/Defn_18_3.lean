import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped Pointwise

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 18.3 introduces extreme rays of a convex cone.
- `core/canonical`: the primitive owner is ray-indexed extremeness
  `ConvexCone.IsExtremeRay` on `Module.Ray R E` directions, with `originRay` providing the
  canonical subset realization.
- `bridge/view`: the textbook nonnegative half-line `R≥0 • ({x} : Set E)` is exactly
  the singleton-direction realization `originRay (rayOfNeZero R x hx)` over any ordered semifield
  with order-compatible multiplication reflection; the source-facing subset owner `IsExtremeRay`
  and its vector-generated characterization stay as bridge surfaces.

Domain-style sampling used here:
- `Module.Ray R E`;
- `originRay`;
- `mem_originRay_iff`;
- `IsExtreme R (K : Set E)`.

Primitive data vs derived API:
- primitive data: the ambient cone `K` and a direction ray `r : Module.Ray R E`;
- source-facing bridge data: a subset `S` identified with `originRay r`;
- derived API: the textbook vector-generated half-line criterion over an ordered semifield.

Layer target: ray-owner primitive API plus source-facing subset bridge statements.
-/

namespace ConvexCone

/-- Primitive owner for Defn 18.3: a direction `r` is extreme in `K` when its canonical origin
half-line is an extreme subset of `K`. -/
def IsExtremeRay (K : ConvexCone R E) (r : Module.Ray R E) : Prop :=
  IsExtreme R K (originRay r)

/-- Primitive owner-facing surface for `ConvexCone.IsExtremeRay`. -/
@[simp] theorem isExtremeRay_iff (K : ConvexCone R E) (r : Module.Ray R E) :
    K.IsExtremeRay r ↔ IsExtreme R K (originRay r) :=
  Iff.rfl

end ConvexCone

/-- Defn 18.3, source-facing bridge surface: an extreme ray subset of a convex cone is an extreme
subset with an origin-ray realization. -/
def IsExtremeRay (K : ConvexCone R E) (S : Set E) : Prop :=
  IsExtreme R K S ∧ ∃ r : Module.Ray R E, S = originRay r

/- Source-facing bridge surface for `IsExtremeRay`. -/
@[simp] theorem isExtremeRay_iff (K : ConvexCone R E) (S : Set E) :
    IsExtremeRay K S ↔ IsExtreme R K S ∧ ∃ r : Module.Ray R E, S = originRay r :=
  Iff.rfl

/-- Source-facing/primitive bridge for `IsExtremeRay`: the subset owner is equivalent to
realizability by an extreme direction ray. -/
theorem isExtremeRay_iff_exists_direction (K : ConvexCone R E) (S : Set E) :
    IsExtremeRay K S ↔ ∃ r : Module.Ray R E, K.IsExtremeRay r ∧ S = originRay r := by
  constructor
  · rintro ⟨hS, ⟨r, rfl⟩⟩
    exact ⟨r, hS, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hr, ⟨r, rfl⟩⟩

namespace IsExtremeRay

/-- Owner projection: every extreme ray subset is an extreme subset of the ambient cone. -/
theorem isExtreme {K : ConvexCone R E} {S : Set E} (hS : IsExtremeRay K S) :
    IsExtreme R K S :=
  hS.1

/-- Owner projection: every extreme ray subset is realized by some direction-origin ray. -/
theorem exists_eq_originRay {K : ConvexCone R E} {S : Set E} (hS : IsExtremeRay K S) :
    ∃ r : Module.Ray R E, S = originRay r :=
  hS.2

end IsExtremeRay

/- On the source-facing subset surface `originRay r`, `IsExtremeRay` agrees with the primitive
direction owner. -/
@[simp] theorem isExtremeRay_originRay_iff (K : ConvexCone R E) (r : Module.Ray R E) :
    IsExtremeRay K (originRay r) ↔ K.IsExtremeRay r := by
  constructor
  · intro h
    exact h.isExtreme
  · intro h
    exact ⟨h, ⟨r, rfl⟩⟩

end

section

variable {R : Type v} [Zero R] [Preorder R]
variable {E : Type u} [SMul R E]

local notation "R≥0" => Set.Ici (0 : R)

private theorem mem_nonnegative_smul_singleton_iff {x y : E} :
    y ∈ R≥0 • ({x} : Set E) ↔ ∃ a : R, 0 ≤ a ∧ y = a • x := by
  constructor
  · intro hy
    rcases Set.mem_smul.mp hy with ⟨a, ha, z, hz, hEq⟩
    have hz' : z = x := by
      simpa using hz
    subst hz'
    exact ⟨a, ha, hEq.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact Set.mem_smul.mpr ⟨a, ha, x, Set.mem_singleton x, rfl⟩

end

section

variable {R : Type v} [Semifield R] [PartialOrder R] [PosMulReflectLT R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

local notation "R≥0" => Set.Ici (0 : R)

/-- The singleton-direction realization of a nonzero vector is exactly its textbook nonnegative
scalar ray. -/
theorem originRay_eq_nonnegative_smul_singleton {x : E} (hx : x ≠ 0) :
    originRay (rayOfNeZero R x hx) = R≥0 • ({x} : Set E) := by
  ext y
  rw [mem_originRay_iff, mem_nonnegative_smul_singleton_iff]
  constructor
  · intro hy
    rcases hy with rfl | ⟨hy0, hyMem⟩
    · exact ⟨0, le_rfl, by simp⟩
    · rcases ((ray_eq_iff hy0 hx).1 hyMem).exists_pos hy0 hx with ⟨a, b, ha, hb, hEq⟩
      refine ⟨a⁻¹ * b, mul_nonneg (inv_nonneg.mpr ha.le) hb.le, ?_⟩
      calc
        y = a⁻¹ • (a • y) := by rw [inv_smul_smul₀ ha.ne']
        _ = a⁻¹ • (b • x) := by rw [hEq]
        _ = (a⁻¹ * b) • x := by rw [smul_smul]
  · intro hy
    rcases hy with ⟨a, ha, hEq⟩
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · refine Or.inr ⟨hy0, ?_⟩
      apply (ray_eq_iff hy0 hx).2
      rw [hEq]
      exact SameRay.sameRay_nonneg_smul_left x ha

/-- The textbook vector-generated half-line condition is exactly existence of a direction ray whose
singleton realization is the given set. -/
theorem exists_eq_originRay_iff {S : Set E} :
    (∃ r : Module.Ray R E, S = originRay r) ↔
      ∃ x : E, x ≠ 0 ∧ S = R≥0 • ({x} : Set E) := by
  constructor
  · rintro ⟨r, rfl⟩
    refine Module.Ray.ind (R := R) (M := E)
      (C := fun r ↦ ∃ x : E, x ≠ 0 ∧ originRay r = R≥0 • ({x} : Set E)) ?_ r
    intro x hx
    exact ⟨x, hx, originRay_eq_nonnegative_smul_singleton hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rayOfNeZero R x hx, (originRay_eq_nonnegative_smul_singleton hx).symm⟩

/-- Primitive-owner bridge: for a nonzero generator `x`, extremeness of the direction
`rayOfNeZero R x hx` is exactly extremeness of its textbook nonnegative scalar ray. -/
@[simp] theorem ConvexCone.isExtremeRay_rayOfNeZero_iff
    (K : ConvexCone R E) {x : E} (hx : x ≠ 0) :
    K.IsExtremeRay (rayOfNeZero R x hx) ↔ IsExtreme R K (R≥0 • ({x} : Set E)) := by
  rw [ConvexCone.isExtremeRay_iff, originRay_eq_nonnegative_smul_singleton hx]

/-- Source-facing singleton bridge: for a nonzero generator `x`, the textbook nonnegative scalar
ray is an extreme ray subset exactly when the corresponding direction ray is extreme. -/
@[simp] theorem isExtremeRay_nonnegative_smul_singleton_iff
    (K : ConvexCone R E) {x : E} (hx : x ≠ 0) :
    IsExtremeRay K (R≥0 • ({x} : Set E)) ↔ K.IsExtremeRay (rayOfNeZero R x hx) := by
  rw [← originRay_eq_nonnegative_smul_singleton hx, isExtremeRay_originRay_iff]

/-- A subset of a convex cone is an extreme ray exactly when it is an extreme subset and equals the
nonnegative scalar ray generated by some nonzero vector. -/
theorem isExtremeRay_iff_exists_nonnegative_smul_singleton (K : ConvexCone R E) (S : Set E) :
    IsExtremeRay K S ↔
      IsExtreme R K S ∧ ∃ x : E, x ≠ 0 ∧ S = R≥0 • ({x} : Set E) := by
  rw [isExtremeRay_iff, exists_eq_originRay_iff]

end
