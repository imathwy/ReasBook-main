import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_18_0_6

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Defn 18.5 introduces exposed faces by maximizer slices of a supporting
  functional, then defines exposed directions as directions of exposed half-line faces and exposed
  rays as exposed half-line faces of a cone issuing from the origin.
- `core/canonical`: mathlib's owner abstraction for exposed faces is `IsExposed R C F`; the
  chapter owners for ray geometry are `affineHalfLine` from Definition 18.4 and `originRay` from
  Definition 18.3.
- `bridge/view`: the source's directional notions are packaged below by quantifying over exposed
  affine half-lines or origin rays built from the exposed-face owner predicate.

Domain-style sampling used here:
- `IsExposed`;
- `IsExposed.isFace_of_convex`;
- `affineHalfLine`;
- `originRay`;
- `exists_eq_originRay_iff`.

Primitive data vs derived API:
- exposed-face status itself is already canonical and should be recalled directly;
- exposed directions are source-facing derived notions built from the chapter owner
  `affineHalfLine` and the canonical exposed-face predicate rather than a second local half-line
  definition;
- exposed rays use the primitive direction owner `ConvexCone.IsExposedRay`, with the source-facing
  subset owner `IsExposedRay` as the direct bridge through `originRay`.
- ambient minimization: `Set.exposedDirections` only reuses `IsExposed` and `affineHalfLine`, so
  it lives over `[AddCommMonoid E]`; additive inverses are only needed later for the exposed-ray
  characterization over vector-generated origin rays.
-/

/- Defn 18.5: an exposed face of a convex set is the canonical owner notion `IsExposed R C F`,
meaning that `F` is the maximizer set of some continuous linear functional on `C`. -/
recall IsExposed

universe u v

open Set

section ExposedDirections

/-- The exposed directions of `C` are the direction rays of exposed affine half-line faces of
`C`. The scalar owner parameter is explicit, matching `Set.extremeDirections`. -/
def Set.exposedDirections (𝕜 : Type v) [TopologicalSpace 𝕜] [CommSemiring 𝕜] [PartialOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    (C : Set E) : Set (Module.Ray 𝕜 E) :=
  {r | ∃ x : E, IsExposed 𝕜 C (affineHalfLine x r)}

/-- A ray is an exposed direction of `C` exactly when some affine half-line of that direction is an
exposed subset of `C`. -/
@[simp] theorem Set.mem_exposedDirections_iff
    {𝕜 : Type v} [TopologicalSpace 𝕜] [CommSemiring 𝕜] [PartialOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {C : Set E} {r : Module.Ray 𝕜 E} :
    r ∈ C.exposedDirections 𝕜 ↔ ∃ x : E, IsExposed 𝕜 C (affineHalfLine x r) :=
  Iff.rfl

end ExposedDirections

section ExposedDirectionBridge

variable {𝕜 : Type v} [TopologicalSpace 𝕜] [CommSemiring 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]

/-- Companion bridge: every exposed direction of `C` is carried by an affine half-line face of
`C`. -/
theorem Set.mem_extremeDirections_of_mem_exposedDirections {C : Set E}
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    r ∈ C.extremeDirections 𝕜 := by
  rcases hr with ⟨x, hx⟩
  exact ⟨x, hx.isFace_of_convex (convex_affineHalfLine x r)⟩

/-- Every exposed direction is an extreme direction. -/
theorem Set.exposedDirections_subset_extremeDirections (C : Set E) :
    C.exposedDirections 𝕜 ⊆ C.extremeDirections 𝕜 := by
  intro r hr
  exact Set.mem_extremeDirections_of_mem_exposedDirections hr

/-- Companion bridge: every exposed direction of `C` is carried by an affine half-line face of
`C`. -/
theorem Set.exists_isFace_of_mem_exposedDirections {C : Set E}
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    ∃ x : E, (affineHalfLine x r).IsFace 𝕜 C := by
  rcases hr with ⟨x, hx⟩
  exact ⟨x, hx.isFace_of_convex (convex_affineHalfLine x r)⟩

end ExposedDirectionBridge

section ExposedRays

open Pointwise

variable {R : Type v} [TopologicalSpace R] [CommSemiring R] [PartialOrder R]
  [IsStrictOrderedRing R]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module R E]

namespace ConvexCone

/-- Primitive owner for Defn 18.5: a direction `r` is exposed in `K` when its canonical origin
half-line is exposed in `K`. -/
def IsExposedRay (K : ConvexCone R E) (r : Module.Ray R E) : Prop :=
  IsExposed R K (originRay r)

/-- Primitive owner-facing surface for `ConvexCone.IsExposedRay`. -/
@[simp] theorem isExposedRay_iff (K : ConvexCone R E) (r : Module.Ray R E) :
    K.IsExposedRay r ↔ IsExposed R K (originRay r) :=
  Iff.rfl

end ConvexCone

/-- Source-facing bridge owner: an exposed ray subset of a convex cone is an exposed subset with
an origin-ray realization. -/
def IsExposedRay (K : ConvexCone R E) (S : Set E) : Prop :=
  IsExposed R K S ∧ ∃ r : Module.Ray R E, S = originRay r

end ExposedRays

section ExposedRayCharacterization

open Pointwise

section Primitive

variable {R : Type v} [TopologicalSpace R] [CommSemiring R] [PartialOrder R]
  [IsStrictOrderedRing R]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module R E]

/-- Source-facing bridge surface for `IsExposedRay`. -/
@[simp] theorem isExposedRay_iff (K : ConvexCone R E) (S : Set E) :
    IsExposedRay K S ↔ IsExposed R K S ∧ ∃ r : Module.Ray R E, S = originRay r :=
  Iff.rfl

/-- On the source-facing subset surface `originRay r`, `IsExposedRay` agrees with the primitive
direction owner. -/
@[simp] theorem isExposedRay_originRay_iff (K : ConvexCone R E) (r : Module.Ray R E) :
    IsExposedRay K (originRay r) ↔ K.IsExposedRay r := by
  constructor
  · intro h
    simpa [ConvexCone.IsExposedRay] using h.1
  · intro hr
    exact ⟨by simpa [ConvexCone.IsExposedRay] using hr, ⟨r, rfl⟩⟩

end Primitive

section NonnegativeSmulSingleton

variable {R : Type v} [TopologicalSpace R] [Semifield R] [PartialOrder R] [PosMulReflectLT R]
  [IsStrictOrderedRing R]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module R E]

local notation "R≥0" => Set.Ici (0 : R)

/-- Primitive-owner bridge: for a nonzero generator `x`, exposedness of the direction
`rayOfNeZero R x hx` is exactly exposedness of its textbook nonnegative scalar ray. -/
@[simp] theorem ConvexCone.isExposedRay_rayOfNeZero_iff
    (K : ConvexCone R E) {x : E} (hx : x ≠ 0) :
    K.IsExposedRay (rayOfNeZero R x hx) ↔ IsExposed R K (R≥0 • ({x} : Set E)) := by
  rw [ConvexCone.isExposedRay_iff, originRay_eq_nonnegative_smul_singleton hx]

/-- Source-facing singleton bridge: for a nonzero generator `x`, the textbook nonnegative scalar
ray is an exposed ray subset exactly when the corresponding direction ray is exposed. -/
@[simp] theorem isExposedRay_nonnegative_smul_singleton_iff
    (K : ConvexCone R E) {x : E} (hx : x ≠ 0) :
    IsExposedRay K (R≥0 • ({x} : Set E)) ↔ K.IsExposedRay (rayOfNeZero R x hx) := by
  rw [← originRay_eq_nonnegative_smul_singleton hx, isExposedRay_originRay_iff]

/-- A subset of a convex cone is an exposed ray exactly when it is an exposed subset and equals the
nonnegative scalar ray generated by some nonzero vector. -/
theorem isExposedRay_iff_exists_nonnegative_smul_singleton (K : ConvexCone R E) (S : Set E) :
    IsExposedRay K S ↔
      IsExposed R K S ∧ ∃ x : E, x ≠ 0 ∧ S = R≥0 • ({x} : Set E) := by
  rw [isExposedRay_iff, exists_eq_originRay_iff]

end NonnegativeSmulSingleton

end ExposedRayCharacterization

section ExposedRayBridge

variable {R : Type v} [TopologicalSpace R] [CommSemiring R] [LinearOrder R]
  [IsStrictOrderedRing R]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module R E]

namespace IsExposedRay

/-- Owner projection: every exposed ray subset is exposed in the ambient cone. -/
theorem isExposed {K : ConvexCone R E} {S : Set E} (hS : IsExposedRay K S) :
    IsExposed R K S :=
  hS.1

/-- Owner projection: every exposed ray subset is realized by some direction-origin ray. -/
theorem exists_eq_originRay {K : ConvexCone R E} {S : Set E} (hS : IsExposedRay K S) :
    ∃ r : Module.Ray R E, S = originRay r :=
  hS.2

/-- Owner bridge: an exposed ray is exactly an exposed subset that is an extreme ray. -/
theorem iff_isExposed_and_isExtremeRay (K : ConvexCone R E) (S : Set E) :
    IsExposedRay K S ↔ IsExposed R K S ∧ IsExtremeRay K S := by
  constructor
  · rintro ⟨hS_exposed, ⟨r, rfl⟩⟩
    exact ⟨hS_exposed, ⟨(hS_exposed.isFace K.convex).isExtreme, ⟨r, rfl⟩⟩⟩
  · rintro ⟨hS_exposed, hS_extremeRay⟩
    exact ⟨hS_exposed, hS_extremeRay.exists_eq_originRay⟩

/-- Every exposed ray of a convex cone is a face of that cone. -/
theorem isFace {K : ConvexCone R E} {S : Set E} (hS : IsExposedRay K S) :
    S.IsFace R K :=
  hS.isExposed.isFace K.convex

/-- Every exposed ray of a convex cone is an extreme ray of that cone. -/
theorem isExtremeRay {K : ConvexCone R E} {S : Set E} (hS : IsExposedRay K S) :
    IsExtremeRay K S :=
  (iff_isExposed_and_isExtremeRay K S).1 hS |>.2

end IsExposedRay

namespace ConvexCone

/-- Primitive owner bridge: every exposed direction ray of a convex cone is an extreme direction
ray. -/
theorem IsExposedRay.isExtremeRay {K : ConvexCone R E} {r : Module.Ray R E}
    (hr : K.IsExposedRay r) : K.IsExtremeRay r := by
  have hS : _root_.IsExposedRay K (originRay r) := (isExposedRay_originRay_iff K r).2 hr
  have hE : _root_.IsExtremeRay K (originRay r) := _root_.IsExposedRay.isExtremeRay hS
  exact (isExtremeRay_originRay_iff K r).1 hE

end ConvexCone

end ExposedRayBridge
