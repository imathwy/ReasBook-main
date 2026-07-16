import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped Pointwise

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-!
Source/core/bridge triage:
- `source-facing`: Definition 18.4 names the directions of half-line faces of a convex set.
- `core/canonical`: the owner abstractions are mathlib's `Set.vaddSet` for translation,
  `Set.IsFace R F C` for face ownership, `Module.Ray R E` for directions, and the chapter owner
  `originRay` for the half-line through the origin with direction `r`.
- `bridge/view`: a half-line with initial point `x` and direction `r` is rendered as the
  translate `x +ᵥ originRay r`; the canonical extremeness view is then recovered from
  `Set.IsFace` via `IsFace.isExtreme`.
- Layer target: `source-facing`.

Domain-style sampling used here:
- `Set.vaddSet`;
- `mem_vadd_set_iff_neg_vadd_mem`;
- `originRay`;
- `mem_originRay_iff`;
- `IsExtreme`;
- `Set.IsFace`;
- `Module.Ray`.

Primitive data vs derived API:
- primitive source-facing data: a base point `x` and a direction ray `r`;
- core/canonical bridge owners: the translation owner `Set.vaddSet`, the origin half-line
  `originRay r`, and the face owner `Set.IsFace`;
- derived API: the extremeness-only criterion for `Set.extremeDirections`, obtained from
  `Set.IsFace` and the derived convexity of `affineHalfLine x r`;
- ambient minimization: neither `originRay`, `Set.IsFace`, nor the convexity of translated rays
  uses additive inverses or real-specific structure, so the owner API lives over the
  ordered-semiring scalar layer already used for directions in Definition 18.3; only the
  displacement-membership bridge lemmas below need an additive group.
-/

private theorem sameRay_someVector_of_mem_originRay {r : Module.Ray R E} {y : E}
    (hy : y ∈ originRay r) : SameRay R y r.someVector := by
  rw [mem_originRay_iff] at hy
  rcases hy with rfl | ⟨hy0, hyr⟩
  · exact SameRay.zero_left _
  · exact (ray_eq_iff hy0 r.someVector_ne_zero).1 (hyr.trans r.someVector_ray.symm)

/-- The origin half-line in a fixed ray direction is convex. -/
theorem convex_originRay (r : Module.Ray R E) : Convex R (originRay r) := by
  rw [convex_iff_pointwise_add_subset]
  intro a b ha hb hab y hy
  rcases hy with ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  have hau : SameRay R (a • u) r.someVector :=
    (sameRay_someVector_of_mem_originRay hu).nonneg_smul_left ha
  have hbv : SameRay R (b • v) r.someVector :=
    (sameRay_someVector_of_mem_originRay hv).nonneg_smul_left hb
  have habuv : SameRay R (a • u + b • v) r.someVector := hau.add_left hbv
  rw [mem_originRay_iff]
  by_cases hzero : a • u + b • v = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero, by simpa using (ray_eq_iff hzero r.someVector_ne_zero).2 habuv⟩

/-- The affine half-line with initial point `x` and direction ray `r`. -/
abbrev affineHalfLine (x : E) (r : Module.Ray R E) : Set E :=
  x +ᵥ originRay r

/-- Every nonnegative multiple of the direction vector of `r`, translated from the initial point
`x`, lies on the affine half-line of direction `r` through `x`. -/
theorem add_smul_someVector_mem_affineHalfLine (x : E) (r : Module.Ray R E) {a : R}
    (ha : 0 ≤ a) :
    x + a • r.someVector ∈ affineHalfLine x r := by
  rw [affineHalfLine, Set.mem_vadd_set]
  refine ⟨a • r.someVector, ?_, by simp [vadd_eq_add]⟩
  rw [mem_originRay_iff]
  by_cases hzero : a • r.someVector = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero,
      ((ray_eq_iff hzero r.someVector_ne_zero).2 <|
        SameRay.sameRay_nonneg_smul_left r.someVector ha).trans r.someVector_ray⟩

/-- An affine half-line is convex. -/
theorem convex_affineHalfLine (x : E) (r : Module.Ray R E) : Convex R (affineHalfLine x r) := by
  simpa [affineHalfLine] using (convex_originRay r).vadd x

end

/-- Defn 18.4: the extreme directions of a convex set `C` are the direction rays of its half-line
faces. The scalar owner parameter is explicit, matching the canonical owner surface
`Set.extremePoints 𝕜 C`. -/
def Set.extremeDirections (𝕜 : Type v) [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {E : Type u} [AddCommMonoid E] [Module 𝕜 E] (C : Set E) : Set (Module.Ray 𝕜 E) :=
  {r | ∃ x : E, (affineHalfLine x r).IsFace 𝕜 C}

/-- A ray is an extreme direction of `C` exactly when some affine half-line of that direction is a
face of `C`. This is the primitive owner-facing surface of the definition. -/
@[simp] theorem Set.mem_extremeDirections_iff
    {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {E : Type u} [AddCommMonoid E] [Module 𝕜 E] {C : Set E} {r : Module.Ray 𝕜 E} :
    r ∈ C.extremeDirections 𝕜 ↔ ∃ x : E, (affineHalfLine x r).IsFace 𝕜 C :=
  Iff.rfl

/-- Companion bridge: an extreme direction is equivalently carried by an affine half-line that is
an extreme subset of `C`. -/
theorem Set.mem_extremeDirections_iff_exists_isExtreme
    {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {E : Type u} [AddCommMonoid E] [Module 𝕜 E] {C : Set E} {r : Module.Ray 𝕜 E} :
    r ∈ C.extremeDirections 𝕜 ↔ ∃ x : E, IsExtreme 𝕜 C (affineHalfLine x r) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.isExtreme⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, ⟨convex_affineHalfLine x r, hx⟩⟩

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Membership in an affine half-line means that the displacement from the initial point lies on
the translated origin half-line. -/
@[simp] theorem mem_affineHalfLine_iff {x y : E} {r : Module.Ray R E} :
    y ∈ affineHalfLine x r ↔ y - x ∈ originRay r := by
  simpa [affineHalfLine, vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (mem_vadd_set_iff_neg_vadd_mem : y ∈ x +ᵥ originRay r ↔ -x +ᵥ y ∈ originRay r)

/-- Membership in an affine half-line means either being the initial point or having displacement
with the prescribed direction ray. -/
theorem mem_affineHalfLine_iff_eq_or_exists {x y : E} {r : Module.Ray R E} :
    y ∈ affineHalfLine x r ↔
      y = x ∨ ∃ hy : y - x ≠ 0, rayOfNeZero R (y - x) hy = r := by
  rw [mem_affineHalfLine_iff, mem_originRay_iff]
  constructor
  · rintro (hzero | ⟨hy, hyRay⟩)
    · left
      exact sub_eq_zero.mp hzero
    · right
      simpa using ⟨hy, hyRay⟩
  · rintro (rfl | ⟨hy, hyRay⟩)
    · left
      simp
    · right
      simpa using ⟨hy, hyRay⟩

end

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCancelCommMonoid E] [Module R E]

/-- A nonzero recession direction of an affine half-line has the same ray direction as that
half-line. -/
theorem rayOfNeZero_eq_of_mem_recessionCone_affineHalfLine
    {x v : E} {r : Module.Ray R E} (hv : v ∈ 0⁺[R](affineHalfLine x r)) (hv0 : v ≠ 0) :
    rayOfNeZero R v hv0 = r := by
  have hx : x ∈ affineHalfLine x r := by
    convert add_smul_someVector_mem_affineHalfLine x r (show (0 : R) ≤ 0 from le_rfl) using 1
    simp
  have hxv : x + v ∈ affineHalfLine x r := by
    simpa using (Set.mem_recessionCone_iff.mp hv) x hx 1 zero_le_one
  have hvRay : v ∈ originRay r := by
    rw [affineHalfLine, Set.mem_vadd_set] at hxv
    rcases hxv with ⟨u, hu, hxu⟩
    have huv : u = v := add_left_cancel hxu
    simpa [huv] using hu
  rw [mem_originRay_iff] at hvRay
  rcases hvRay with hzero | ⟨_, hvr⟩
  · exact (hv0 hzero).elim
  · exact hvr

end

section

open Bornology

variable {K : Type v} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
variable [NormSMulClass ℤ K]
variable {E : Type u} [NormedAddCommGroup E] [Module K E] [NormSMulClass K E]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem not_isBounded_range_add_natCast_smul (x y : E) (hy : y ≠ 0) :
    ¬ IsBounded (Set.range fun n : ℕ ↦ x + (n : K) • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + (n : K) • y‖ ≤ R := by
    have hxR : x + (n : K) • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  have hny : ‖(n : K)‖ * ‖y‖ ≤ R + ‖x‖ := by
    calc
      ‖(n : K)‖ * ‖y‖ = ‖(n : K) • y‖ := by
        simpa using (norm_smul (n : K) y).symm
      _ = ‖(x + (n : K) • y) - x‖ := by simp
      _ ≤ ‖x + (n : K) • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x‖ < ‖(n : K)‖ * ‖y‖ := by
    calc
      R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : K)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

/-- An affine half-line is unbounded. -/
theorem not_isBounded_affineHalfLine (x : E) (r : Module.Ray K E) :
    ¬ IsBounded (affineHalfLine x r) := by
  intro hbounded
  have hrange :
      Set.range (fun n : ℕ ↦ x + (n : K) • r.someVector) ⊆ affineHalfLine x r := by
    rintro _ ⟨n, rfl⟩
    exact add_smul_someVector_mem_affineHalfLine x r
      (show (0 : K) ≤ (n : K) from Nat.cast_nonneg n)
  exact not_isBounded_range_add_natCast_smul x r.someVector r.someVector_ne_zero <|
    hbounded.subset hrange

end

section

open scoped Convex Rockafellar

namespace Set

/-- `C` is a closed half of its affine hull when it is the intersection of `affineSpan 𝕜 C` with an
intrinsic closed linear half-space. This keeps the owner independent of an auxiliary pairing side
type. -/
def IsClosedHalfAffineHull (𝕜 : Type*) [Ring 𝕜] [Preorder 𝕜]
    {E : Type u} [AddCommGroup E] [Module 𝕜 E] (C : Set E) : Prop :=
  ∃ s : Set E, (closedLinearHalfSpace[𝕜] s) ∧
    C = (affineSpan 𝕜 C : Set E) ∩ s

end Set

end
