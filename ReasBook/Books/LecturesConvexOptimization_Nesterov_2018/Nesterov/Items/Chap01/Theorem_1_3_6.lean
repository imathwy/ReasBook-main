import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Theorem_1_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 1.3.6 lies in the finite-dimensional box-constrained midpoint-grid optimization
domain.

Relevant owner-style declarations sampled before refining:
* `uniformGridPoint` in `Nesterov/Chap01/Theorem_1_3_6.lean`, the chapter owner of the midpoint
  grid points;
* `uniformGrid` in the same file, the chapter owner of the midpoint grid itself;
* `isMinOn_iff` in mathlib, the canonical owner-style elimination rule for the minimizer
  hypothesis `IsMinOn f (uniformGrid n p) xBar`;
* `SetConstrainedMinimizationProblem.optimalValue` in `Nesterov/Chap01/Definition_1_3_7.lean`,
  the canonical owner of the constrained optimal value.

Best owner abstraction:
* source-facing: the midpoint grid `uniformGrid n p` and the textbook value-gap conclusion;
* core/canonical: `IsMinOn f (uniformGrid n p) xBar` together with
  `(zeroOneBoxProblem n f).optimalValue`;
* bridge/view: the explicit value inequality derived directly from the grid minimizer hypothesis
  and the canonical optimal-value owner.

Primitive data:
* the dimension `n`;
* the mesh parameter `p : ℕ+`;
* the midpoint-grid minimizer hypothesis `IsMinOn f (uniformGrid n p) xBar`.

Derived API:
* the coordinate formula for midpoint-grid points;
* feasibility of midpoint-grid points and grid approximation inside `zeroOneBox n`;
* the explicit objective-value inequality against the canonical constrained optimal value.

This item therefore reuses the exact chapter owners directly and keeps only the source-facing
value-gap theorem as a thin bridge from the canonical optimal-value owner, rather than
redefining the box, `ℓ∞` norm, Lipschitz class, grid, or optimal-value API locally. -/

/- The midpoint grid point of mesh `1 / p` is the chapter owner `uniformGridPoint n p α`. -/
recall uniformGridPoint (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) :
    EuclideanSpace ℝ (Fin n)

/- The midpoint grid of mesh `1 / p` is the chapter owner `uniformGrid n p`. -/
recall uniformGrid (n : ℕ) (p : ℕ+) : Set (EuclideanSpace ℝ (Fin n))

/- The coordinates of a midpoint grid point are given by the midpoint formula. -/
recall uniformGridPoint_apply
    (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) (i : Fin n) :
    uniformGridPoint n p α i = (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)

/- Each midpoint grid point lies in the textbook box `B_n = [0,1]^n`. -/
recall uniformGridPoint_mem_zeroOneBox
    (p : ℕ+) (α : Fin n → Fin p) :
    uniformGridPoint n p α ∈ zeroOneBox n

/- The midpoint grid is contained in the textbook box `B_n = [0,1]^n`. -/
recall uniformGrid_subset_zeroOneBox (p : ℕ+) :
    uniformGrid n p ⊆ zeroOneBox n

/- Every point of `B_n = [0,1]^n` is within `ℓ∞`-distance `1 / (2p)` of some midpoint grid
point. -/
recall exists_uniformGrid_linfty_close
    (p : ℕ+) {x : E} (hx : x ∈ zeroOneBox n) :
    ∃ y ∈ uniformGrid n p, ‖x - y‖∞ ≤ 1 / (2 * (p : ℝ))

/- The canonical chapter theorem expresses Theorem 1.3.6 as approximate optimality for the box
problem owner `zeroOneBoxProblem n f`. -/
recall uniformGrid_isApproximateMinimizer_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hxBar : xBar ∈ uniformGrid n p)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (zeroOneBoxProblem n f).IsApproximateMinimizer ((L : ℝ) / (2 * (p : ℝ))) xBar

/-- Theorem 1.3.6: if `f ∈ 𝒫∞[n, L]` and the value `f xBar` is minimal on the midpoint grid of
mesh `1 / p`, then `f xBar` is at most `L / (2p)` above the canonical optimal value of the box
problem `min_{x ∈ B_n} f(x)`. -/
theorem uniformGrid_value_le_optimalValue_add_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (f xBar : EReal) ≤ (zeroOneBoxProblem n f).optimalValue + (L : ℝ) / (2 * (p : ℝ)) := by
  let ε : ℝ := (L : ℝ) / (2 * (p : ℝ))
  have hxBar_le_add {x : E} (hx : x ∈ zeroOneBox n) :
      (f xBar : EReal) ≤ (f x : EReal) + ε := by
    rcases exists_uniformGrid_linfty_close p hx with ⟨y, hy_grid, hxy⟩
    have hxBar_le_y : f xBar ≤ f y := by
      rw [isMinOn_iff] at hxBar_min
      exact hxBar_min y hy_grid
    have hy_box : y ∈ zeroOneBox n :=
      uniformGrid_subset_zeroOneBox p hy_grid
    have hyx_dist :
        (L : ℝ) * ‖y - x‖∞ ≤ ε := by
      have hxy' : ‖y - x‖∞ ≤ 1 / (2 * (p : ℝ)) := by
        simpa [norm_sub_rev] using hxy
      have hL_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast L.2
      calc
        (L : ℝ) * ‖y - x‖∞ ≤ (L : ℝ) * (1 / (2 * (p : ℝ))) := by
          gcongr
        _ = ε := by
          simp [ε, div_eq_mul_inv]
    have hy_dist :
        |f y - f x| ≤ ε := by
      exact (abs_sub_le_mul_linftyNorm hf_lipschitz hy_box hx).trans hyx_dist
    have hy_le_x : f y ≤ f x + ε := by
      have hy_sub_x : f y - f x ≤ ε := (abs_sub_le_iff.mp hy_dist).1
      linarith
    have hxBar_le_x : f xBar ≤ f x + ε :=
      le_trans hxBar_le_y hy_le_x
    exact_mod_cast hxBar_le_x
  by_contra h
  have hgap : (zeroOneBoxProblem n f).optimalValue + ε < (f xBar : EReal) := by
    simpa [ε] using h
  have hopt_lt : (zeroOneBoxProblem n f).optimalValue < (f xBar : EReal) - ε := by
    exact (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot ε)) (.inl (EReal.coe_ne_top ε))).2 hgap
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image] at hopt_lt
  have himage_nonempty :
      ((fun x ↦ (zeroOneBoxProblem n f x : EReal)) '' (zeroOneBoxProblem n f).feasibleSet).Nonempty := by
    refine ⟨(f 0 : EReal), ?_⟩
    refine ⟨0, ?_, by simp⟩
    change (0 : E) ∈ zeroOneBox n
    exact zeroOneBox_zero_mem n
  rcases exists_lt_of_csInf_lt himage_nonempty hopt_lt with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  have hxBar_le : (f xBar : EReal) ≤ (f x : EReal) + ε := by
    simpa [ε] using hxBar_le_add (by simpa using hx)
  have hlt : (f x : EReal) + ε < (f xBar : EReal) := by
    exact EReal.add_lt_of_lt_sub (by simpa [ε] using hvlt)
  exact (not_lt_of_ge hxBar_le hlt)
