

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_3 (from Chap03) -/
universe u

open scoped Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 3.3 is `source-facing` in the Chapter 3 convex-analysis API: it introduces the normal
cone of a set at a point. The `core/canonical` owner declaration for this notion in the project is
Chapter 2's `polar_cone`, applied to the translated set `S -ᵥ {x}`. The only primitive data here
is the set-valued map `normal_cone`; membership and the feasible-point identification with
`polar_cone` are derived API.
-/

/-- Definition 3.3: the normal cone of a set `S ⊆ E` at `x` consists of the dual vectors that are
nonpositive on every displacement `z - x` with `z ∈ S`; when `x ∉ S`, the normal cone is empty.
This source-facing cone is the Chapter 2 owner `polar_cone` of the translated set `S -ᵥ {x}`. -/
def normal_cone (S : Set E) (x : E) : Set (Module.Dual ℝ E) :=
  { y | x ∈ S ∧ y ∈ polar_cone (S -ᵥ ({x} : Set E)) }

-- Proof sketch: if `x ∈ S`, the extra feasibility guard in the definition of `normal_cone` is
-- redundant, so the source-facing cone is exactly the owner `polar_cone` of the translated set.
/-- At a feasible point, the normal cone is the polar cone of the translated feasible-displacement
set. -/
@[simp] lemma normal_cone_eq_polar_cone_of_mem (S : Set E) {x : E} (hx : x ∈ S) :
    normal_cone S x = polar_cone (S -ᵥ ({x} : Set E)) := by
  ext y
  simp [normal_cone, hx]

-- Proof sketch: rewrite `normal_cone` to the owner `polar_cone` of the translated set `S -ᵥ {x}`;
-- using `Set.vsub_singleton`, membership in that polar cone is exactly the textbook inequality on
-- the displacements `z - x` with `z ∈ S`.
/-- At a point `x ∈ S`, membership in the normal cone means being nonpositive on every feasible
displacement `z - x` with `z ∈ S`. -/
lemma mem_normal_cone (S : Set E) {x : E} (hx : x ∈ S) (y : Module.Dual ℝ E) :
    y ∈ normal_cone S x ↔ ∀ z ∈ S, y (z - x) ≤ 0 := by
  rw [normal_cone_eq_polar_cone_of_mem S hx, mem_polar_cone, Set.vsub_singleton]
  constructor
  · intro hy z hz
    exact hy (z - x) ⟨z, hz, rfl⟩
  · intro hy
    rintro _ ⟨z, hz, rfl⟩
    exact hy z hz

-- Proof sketch: the owner-derived definition is explicitly empty when `x ∉ S`.
/-- Outside the set, the normal cone is empty. -/
lemma normal_cone_eq_empty_of_not_mem (S : Set E) {x : E} (hx : x ∉ S) :
    normal_cone S x = ∅ := by
  ext y
  simp [normal_cone, hx]

end

/-! ### Lemma_3_3 (from Chap03) -/
noncomputable section

open Matrix

section

variable {m n p : ℕ}

local notation "PrimalSpace" => EuclideanSpace ℝ (Fin n)
local notation "IneqPerturbationSpace" => EuclideanSpace ℝ (Fin m)
local notation "EqPerturbationSpace" => EuclideanSpace ℝ (Fin p)

/- Lemma 3.3 is a `bridge/view` item in the perturbation-value-function API. The owner
declarations are `value_function` and the derived antitonicity theorem
`value_function_antitone_u` from `Lemma_3_4`, specialized to
`E = EuclideanSpace ℝ (Fin n)` and to the matrix linear map `A.toEuclideanLin`. The source writes
the affine constraint as `A *ᵥ x = b + t`, while the owner uses `A x + c = t`, so the faithful
specialization here is obtained by taking `c = -b`. -/
recall value_function
recall value_function_antitone_u

/-- Lemma 3.3: the perturbation value function is monotone with respect to relaxing the
coordinatewise inequality bounds, equivalently antitone in the bound parameter itself. In the
source convention `A *ᵥ x = b + t`, this is the specialization of the owner value function to the
offset `-b`. -/
theorem value_function_monotone
    (X : Set PrimalSpace) (f : PrimalSpace → EReal) (g : Fin m → PrimalSpace → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EqPerturbationSpace)
    {u w : IneqPerturbationSpace} {t : EqPerturbationSpace}
    (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function X f g A.toEuclideanLin (-b) (u, t) ≥
      value_function X f g A.toEuclideanLin (-b) (w, t) :=
  value_function_antitone_u X f g A.toEuclideanLin (-b) huw

end

/-! ### Proposition_3_3 (from Chap03) -/
universe u

open Metric

/- Proposition 3.3 is a `bridge/view` specialization in the chapter convex-analysis API. The
owner declarations are `normal_cone`, Proposition 3.2's
`subdifferential_extended_indicator_eq_normal_cone`, and Chapter 1's canonical `dualNorm`
interface together with `exists_dualNorm_eq_apply`. The only primitive data here are the closed
unit ball and the point `x`; the dual-norm inequality description is derived API. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: this is the closed-unit-ball specialization of the owner theorem
-- `subdifferential_extended_indicator_eq_normal_cone`.
/-- Proposition 3.3: the subdifferential of the indicator of the closed unit ball is its normal
cone. -/
theorem subdifferential_extended_indicator_closed_unit_ball_eq_normal_cone (x : E) :
    subdifferential (extendedIndicator (closedBall (0 : E) 1)) x =
      normal_cone (closedBall (0 : E) 1) x := by
  simpa using
    subdifferential_extended_indicator_eq_normal_cone (closedBall (0 : E) 1) x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: if `‖x‖ ≤ 1`, rewrite membership in `normal_cone (closedBall (0 : E) 1) x`
-- as `∀ z, ‖z‖ ≤ 1 → y z ≤ y x`, then use `exists_dualNorm_eq_apply` to realize the chapter owner
-- dual norm on the closed unit ball and `abs_apply_le_dual_norm_mul_norm` for the converse
-- bound. If `‖x‖ > 1`, then `x ∉ closedBall (0 : E) 1`, so the normal cone is empty by
-- definition.
/-- The normal cone of the closed unit ball is described by the chapter dual-norm inequality
`dualNorm y ≤ y x` on the ball and is empty outside the ball. -/
theorem normal_cone_closed_unit_ball_eq_if_dualNorm_le_apply (x : E) :
    normal_cone (closedBall (0 : E) 1) x =
      if ‖x‖ ≤ 1 then { y : Module.Dual ℝ E | dualNorm y ≤ y x } else ∅ := by
  let B : Set E := closedBall (0 : E) 1
  by_cases hx : ‖x‖ ≤ 1
  · have hxB : x ∈ B := by
      simpa [B] using hx
    rw [if_pos hx]
    ext y
    constructor
    · intro hy
      have hy' := (mem_normal_cone B hxB y).1 (by simpa [B] using hy)
      obtain ⟨z, hz, hdual⟩ := exists_dualNorm_eq_apply y
      calc
        dualNorm y = y z := hdual
        _ ≤ y x := by
          have hz' : y (z - x) ≤ 0 := hy' z (by simpa [B] using hz)
          exact sub_nonpos.mp (by simpa using hz')
    · intro hy
      refine (mem_normal_cone B hxB y).2 ?_
      intro z hz
      have hznorm : ‖z‖ ≤ 1 := by
        simpa [B] using hz
      have hdual_nonneg : 0 ≤ dualNorm y := by
        simp [dualNorm]
      have hyz_le_dual : y z ≤ dualNorm y := by
        calc
          y z ≤ |y z| := le_abs_self _
          _ ≤ dualNorm y * ‖z‖ := abs_apply_le_dual_norm_mul_norm y z
          _ ≤ dualNorm y * 1 := by
            exact mul_le_mul_of_nonneg_left hznorm hdual_nonneg
          _ = dualNorm y := by simp
      have hyz_le_x : y z ≤ y x := hyz_le_dual.trans hy
      have : y z - y x ≤ 0 := sub_nonpos.mpr hyz_le_x
      simpa using this
  · have hxball : x ∉ closedBall (0 : E) 1 := by
      simpa using hx
    rw [normal_cone_eq_empty_of_not_mem (closedBall (0 : E) 1) hxball, if_neg hx]

end

/-! ### Theorem_3_3 (from Chap03) -/
universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
Theorem 3.3 is `source-facing` at the chapter owner `subdifferential : Set (Module.Dual ℝ E)`.
Its boundedness conclusion lives naturally on the normed continuous-dual view, so the file reuses
the existing bridge `strongDualSubdifferential` instead of introducing a second `StrongDual`-valued
owner. Domain sampling shows that the stronger chapter existence theorem is
`subdifferential_nonempty_at_relativeInterior_point`; part (1) below is only its finite-dimensional
interior specialization, while part (2) stays on the same owner/bridge surface.
-/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential
recall subdifferential_nonempty_at_relativeInterior_point

-- Proof sketch: this is the finite-dimensional interior specialization of the stronger owner
-- theorem `subdifferential_nonempty_at_relativeInterior_point`, using the canonical inclusion
-- `interior (effective_domain f) ⊆ intrinsicInterior ℝ (effective_domain f)`.
/-- Theorem 3.3 (1): for a convex extended-real-valued function, the subdifferential at an
interior point of the effective domain is nonempty. -/
theorem subdifferential_nonempty_at_interior_point
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    (subdifferential f x).Nonempty :=
  subdifferential_nonempty_at_relativeInterior_point f x hconvex
    (interior_subset_intrinsicInterior hx)

-- Proof sketch: use local Lipschitz continuity on a closed ball centered at `x` and contained in
-- `effective_domain f`. For any `g ∈ ∂ f(x)`, evaluate the subgradient inequality at a point of
-- the form `x + εu`, where `u` is a unit vector realizing the dual norm of `g`, to obtain a
-- uniform norm bound `‖g‖ ≤ L`; hence `∂ f(x)` is contained in a closed ball of the dual space.
/-- Theorem 3.3 (2): for a convex extended-real-valued function that never takes the value `⊥`,
the continuous-dual view of the subdifferential at an interior point of the effective domain is
bounded in the dual norm. -/
theorem subdifferential_bounded_at_interior_point
    (f : E → EReal) (x : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    IsBounded (strongDualSubdifferential f x) := sorry

end
