import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_26 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.26 lies in the Euclidean ellipsoid / positive-definite dual-norm domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the textbook unit-radius
  ellipsoid;
- `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the exact membership companion theorem for
  that owner;
- `positiveDefMatrixNorm` in `Definition_7_23`, the source-facing owner for the primal norm
  induced by a positive-definite matrix;
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Definition_7_23`, the canonical bridge
  from the dual norm to the inverse-matrix quadratic formula.

Best owner abstraction:
- source-facing: the radius-parametrized ellipsoid `matrixEllipsoid G v r`;
- core/canonical owners: the unit ellipsoid `affineEllipsoid` and the dual norm
  `positiveDefMatrixNorm`;
- bridge/view: the unit-radius identification and the positive-definite dual-norm membership
  theorem.

Primitive data:
- a matrix `G : Mat`;
- a center `v : E`;
- a radius `r : ℝ`.

Derived API:
- the centered specialization `centeredMatrixEllipsoid G r`;
- exact membership lemmas;
- the radius-`1` bridge to `affineEllipsoid`;
- the positive-definite dual-norm reformulation.

Source/core/bridge triage:
- source-facing: `matrixEllipsoid`, `centeredMatrixEllipsoid`;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`;
- bridge/view: the companion equivalences below.

The source genuinely carries the extra radius parameter, so this file keeps that source-facing
owner. The duplicate wheel is only the unit-radius surface, which is refined back to the chapter
owner `affineEllipsoid`; under positive-definiteness the defining inequality is further refined to
the canonical dual-norm API from `Definition_7_23`.
-/

/-- Definition 7.26: the ellipsoid `W_r(v, G)` is the set of points `s` in `ℝⁿ` whose
`G`-dual distance from the center `v` is at most `r`, namely
`⟪G⁻¹ (s - v), s - v⟫ ^ (1 / 2) ≤ r`. -/
def matrixEllipsoid (G : Mat) (v : E) (r : ℝ) : Set E :=
  {s | Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - v)) (s - v)) ≤ r}

/-- The centered ellipsoid `W_r(G)`, obtained from `W_r(v, G)` by taking `v = 0`. -/
abbrev centeredMatrixEllipsoid (G : Mat) (r : ℝ) : Set E :=
  matrixEllipsoid G 0 r

namespace EllipsoidNotation

scoped notation:max "W[" r:arg "](" v:arg ", " G:arg ")" => matrixEllipsoid G v r

scoped notation:max "W[" r:arg "](" G:arg ")" => centeredMatrixEllipsoid G r

end EllipsoidNotation

open scoped EllipsoidNotation

/-- Membership in `W[r](v, G)` is exactly the defining quadratic-inequality bound. -/
theorem mem_matrixEllipsoid_iff
    {G : Mat} {v s : E} {r : ℝ} :
    s ∈ W[r](v, G) ↔
      Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - v)) (s - v)) ≤ r :=
  Iff.rfl

/-- Membership in the centered ellipsoid `W[r](G)` is the defining inequality with center `0`. -/
theorem mem_centeredMatrixEllipsoid_iff
    {G : Mat} {s : E} {r : ℝ} :
    s ∈ W[r](G) ↔
      Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) s) s) ≤ r := by
  have hmem :
      s ∈ W[r]((0 : E), G) ↔
        Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - (0 : E))) (s - (0 : E))) ≤ r :=
    mem_matrixEllipsoid_iff
  simpa [centeredMatrixEllipsoid] using
    hmem

/-- At radius `1`, `W[1](v, G)` is exactly the chapter's unit-radius ellipsoid owner `E(G, v)`. -/
theorem matrixEllipsoid_one_eq_affineEllipsoid
    (G : Mat) (v : E) :
    W[1](v, G) = E(G, v) := by
  ext s
  rw [mem_matrixEllipsoid_iff, mem_affineEllipsoid_iff, Real.sqrt_le_iff]
  simp

/-- At radius `1`, the centered ellipsoid is exactly the chapter's centered unit ellipsoid owner
`E(G, 0)`. -/
theorem centeredMatrixEllipsoid_one_eq_affineEllipsoid
    (G : Mat) :
    W[1](G) = E(G, 0) := by
  simpa [centeredMatrixEllipsoid] using
    matrixEllipsoid_one_eq_affineEllipsoid G (0 : E)

/-- For a positive-definite matrix, membership in `W[r](v, G)` is exactly the dual-norm bound
`‖s - v‖[⟨G, hG⟩,*] ≤ r`. -/
theorem mem_matrixEllipsoid_iff_dualNorm_le
    {G : Mat} (hG : G.PosDef) {v s : E} {r : ℝ} :
    s ∈ W[r](v, G) ↔ ‖s - v‖[⟨G, hG⟩,*] ≤ r := by
  rw [mem_matrixEllipsoid_iff, positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
  simp [LinearMap.map_sub, real_inner_comm]

/-- For a positive-definite matrix, membership in the centered ellipsoid `W[r](G)` is exactly the
dual-norm bound `‖s‖[⟨G, hG⟩,*] ≤ r`. -/
theorem mem_centeredMatrixEllipsoid_iff_dualNorm_le
    {G : Mat} (hG : G.PosDef) {s : E} {r : ℝ} :
    s ∈ W[r](G) ↔ ‖s‖[⟨G, hG⟩,*] ≤ r := by
  have hmem :
      s ∈ W[r]((0 : E), G) ↔ ‖s - (0 : E)‖[⟨G, hG⟩,*] ≤ r :=
    mem_matrixEllipsoid_iff_dualNorm_le hG
  simpa [centeredMatrixEllipsoid] using
    hmem

end

/-! ### Proposition_7_26 (from Chap07) -/
noncomputable section

universe u

section

variable {Q : Type u}

/- Proposition 7.26 lies in Chapter 7's relative-accuracy / stagewise gap-conversion domain.

Sampled owner-style declarations:
- `IsRelativeAccuracy` in `Definition_7_1`, the chapter owner for two-sided relative accuracy;
- `subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_2`,
  the sibling one-shot conversion from a stagewise gap bound to a `(1 + δ) fStar` upper bound;
- `direct_structure_iterate_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_4`, the same
  owner-level conversion pattern for a different coefficient profile;
- `iterativeSmoothing_outputPoint_value_le` in `Theorem_7_11`, showing the local chapter style:
  the one-sided upper bound is source-facing, while `IsRelativeAccuracy` is a companion bridge
  once the lower bound is available.

Best owner abstraction:
- source-facing: Proposition 7.26's one-sided value estimate
  `f_p (x_k) ≤ (1 + δ) f_p^*` at an iteration index satisfying the explicit lower bound;
- core/canonical: `IsRelativeAccuracy fStar δ (f_p (x k))`;
- bridge/view: the passage from the explicit coefficient
  `16 (1 + δ) r log r / (δ k (k + 1))` to `δ`.

Primitive data:
- the objective `f_p`, iterate sequence `x`, and scalars `δ`, `r`, `fStar`;
- the stagewise gap estimate;
- the explicit lower bound on the chosen index `k`;
- the nonnegativity of `fStar`, which is exactly what the one-sided upper bound uses.

Derived API:
- the source-facing upper bound below;
- the companion `IsRelativeAccuracy` statement obtained by supplying the missing lower bound
  `fStar ≤ f_p (x k)` and the stronger positivity input needed by the chapter owner.

Source/core/bridge triage:
- source-facing: `fp_relative_accuracy_of_iteration_gap_bound`;
- core/canonical: `IsRelativeAccuracy`;
- bridge/view: `fp_iterate_isRelativeAccuracy_of_iteration_gap_bound`.

The main theorem remains the source-facing upper bound because the current proposition does not
assume the lower inequality `fStar ≤ f_p (x k)`. Replacing it by `IsRelativeAccuracy` would change
the source semantics. The canonical owner is therefore added only as the minimal companion bridge.
-/

-- Proof sketch: for the chosen iterate `k`, rewrite the assumed gap estimate as
-- `f_p (x k) ≤ (1 + C_k) fStar` with
-- `C_k = 16 (1 + δ) r log r / (δ k (k + 1))`. The lower bound on `k` implies
-- `k (k + 1) ≥ k^2 ≥ 16 (1 + δ) r log r / δ^2`, so `C_k ≤ δ`. Substituting this into the
-- previous inequality and using `0 ≤ fStar` gives `f_p (x k) ≤ (1 + δ) fStar`.
/-- Proposition 7.26: if the iterates `x_k` satisfy the displayed gap estimate
`f_p(x_k) - f_p^* ≤ 16 (1 + δ) r log r / (δ k (k + 1)) * f_p^*`, `f_p^*` is nonnegative, and
every iterate with
`k ≥ (4 / δ) * sqrt ((1 + δ) r log r)` satisfies the relative-accuracy bound
`f_p(x_k) ≤ (1 + δ) f_p^*`. -/
theorem fp_relative_accuracy_of_iteration_gap_bound
    (f_p : Q → ℝ) (δ r fStar : ℝ) (x : ℕ → Q) {k : ℕ}
    (hδ : 0 < δ) (hr : 1 < r) (hfStar_nonneg : 0 ≤ fStar)
    (hgap :
      ∀ n : ℕ,
        1 ≤ n →
          f_p (x n) - fStar ≤
            ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (n : ℝ) * (n + 1)) * fStar)
    (hk : (4 / δ) * Real.sqrt ((1 + δ) * r * Real.log r) ≤ (k : ℝ)) :
    f_p (x k) ≤ (1 + δ) * fStar := by
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hOne_add_δ_pos : 0 < 1 + δ := by linarith
  have hr_pos : 0 < r := lt_trans zero_lt_one hr
  have hlogr_pos : 0 < Real.log r := Real.log_pos hr
  set A : ℝ := (1 + δ) * r * Real.log r
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hsqrt_pos : 0 < Real.sqrt A := by
    apply Real.sqrt_pos.2
    have hA_pos : 0 < A := by
      dsimp [A]
      positivity
    exact hA_pos
  have hleft_pos : 0 < (4 / δ) * Real.sqrt A := by
    positivity
  have hk_pos : 0 < (k : ℝ) := lt_of_lt_of_le hleft_pos hk
  have hk_nat_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.cast_pos.mp hk_pos)
  have hgapk := hgap k hk_nat_pos
  have hscaled :
      4 * Real.sqrt A ≤ δ * (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hk hδ_nonneg
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ
    simpa [A, div_eq_mul_inv, hδ_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hmain :
      (16 : ℝ) * A ≤ δ ^ (2 : ℕ) * (k : ℝ) ^ (2 : ℕ) := by
    have hsq :
        (4 * Real.sqrt A) ^ (2 : ℕ) ≤ (δ * (k : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hscaled]
    nlinarith [hsq, Real.sq_sqrt hA_nonneg]
  have hk_sq_le :
      (k : ℝ) ^ (2 : ℕ) ≤ (k : ℝ) * (k + 1) := by
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  have hmain' :
      (16 : ℝ) * A ≤ δ ^ (2 : ℕ) * ((k : ℝ) * (k + 1)) := by
    exact hmain.trans <| by
      gcongr
  have hden_pos : 0 < δ * (k : ℝ) * (k + 1) := by
    positivity
  have hcoeff_le :
      ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1)) ≤ δ := by
    apply (div_le_iff₀ hden_pos).2
    simpa [A, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain'
  have hcoeff_mul_le :
      (((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1))) * fStar ≤
        δ * fStar := by
    exact mul_le_mul_of_nonneg_right hcoeff_le hfStar_nonneg
  calc
    f_p (x k) = (f_p (x k) - fStar) + fStar := by ring
    _ ≤
        (((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1))) * fStar + fStar := by
      linarith
    _ ≤ δ * fStar + fStar := by
      gcongr
    _ = (1 + δ) * fStar := by ring

/-- Proposition 7.26 upgrades to the chapter owner `IsRelativeAccuracy` once the missing lower
bound `f_p^* ≤ f_p(x_k)` is supplied explicitly. -/
theorem fp_iterate_isRelativeAccuracy_of_iteration_gap_bound
    (f_p : Q → ℝ) (δ r fStar : ℝ) (x : ℕ → Q) {k : ℕ}
    (hδ : 0 < δ) (hr : 1 < r) (hfStar_pos : 0 < fStar)
    (hgap :
      ∀ n : ℕ,
        1 ≤ n →
          f_p (x n) - fStar ≤
            ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (n : ℝ) * (n + 1)) * fStar)
    (hk : (4 / δ) * Real.sqrt ((1 + δ) * r * Real.log r) ≤ (k : ℝ))
    (hfStar_le : fStar ≤ f_p (x k)) :
    IsRelativeAccuracy fStar δ (f_p (x k)) := by
  refine ⟨hfStar_pos, hfStar_le, ?_⟩
  exact
    fp_relative_accuracy_of_iteration_gap_bound f_p δ r fStar x hδ hr
      (le_of_lt hfStar_pos) hgap hk

end
