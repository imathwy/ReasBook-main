import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifoldsLee.Chap01.Sec01_04.Example_1_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Lee's alternate smooth real line from Example 1.23 is `CubicRealLine`.

/-- Helper for Problem 2-5: the alternate real line is presented in this file by the cubic
embedding into the standard real line. -/
def cubic_real_line_embedding : CubicRealLine → ℝ :=
  cubicMap

/-- Helper for Problem 2-5: a smooth real-valued function on the standard line, viewed as a map
into the alternate smooth real line. -/
def std_to_cubic (f : ℝ → ℝ) : ℝ → CubicRealLine :=
  f

/-- Helper for Problem 2-5: a real-valued function on the alternate smooth real line, viewed as an
ordinary function on `ℝ`. -/
def cubic_to_std (f : ℝ → ℝ) : CubicRealLine → ℝ :=
  f

/-- Helper for Problem 2-5: the inverse cubic chart, viewed as a map from the standard line to the
alternate smooth real line. -/
noncomputable def cubic_chart_symm_to_cubic : ℝ → CubicRealLine :=
  cubicChart.symm

/-- Helper for Problem 2-5: the defining cubic embedding of the alternate real line is an open
embedding. -/
lemma cubic_real_line_embedding_isOpenEmbedding :
    Topology.IsOpenEmbedding cubic_real_line_embedding :=
  show Topology.IsOpenEmbedding cubicMap from cubicMap_isOpenEmbedding

/-- Helper for Problem 2-5: the alternate real line is nonempty. -/
local instance cubicRealLineNonempty : Nonempty CubicRealLine :=
  ⟨show CubicRealLine from (0 : ℝ)⟩

/-- Helper for Problem 2-5: inside this file, use the singleton cubic chart as the charted-space
structure on the alternate real line. -/
noncomputable local instance cubicRealLineChartedSpace : ChartedSpace ℝ CubicRealLine :=
  cubic_real_line_embedding_isOpenEmbedding.singletonChartedSpace

/-- Helper for Problem 2-5: the local singleton cubic chart defines a smooth manifold structure on
the alternate real line. -/
noncomputable local instance cubicRealLineIsManifold : IsManifold (𝓘(ℝ)) ∞ CubicRealLine :=
  cubic_real_line_embedding_isOpenEmbedding.isManifold_singleton (I := 𝓘(ℝ)) (n := ∞)

/-- Helper for Problem 2-5: the inverse cubic chart is a left inverse to the cubic map. -/
lemma cubicChart_symm_cubicMap_eq (x : ℝ) : cubicChart.symm (cubicMap x) = x := by
  -- Injectivity of the cubic map identifies the unique preimage of `x ^ 3`.
  apply cubicMap_isOpenEmbedding.injective
  simpa [cubicMap] using cubicChart_symm_cube_eq (cubicMap x)

/-- Problem 2-5 (1): every function `f : ℝ → ℝ` that is smooth in the usual sense is also smooth
as a map from the standard smooth real line to Lee's alternate smooth structure `\widetilde{ℝ}`
from Example 1.23. -/
theorem contMDiff_std_to_cubic_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (std_to_cubic f) := by
  -- Compose `f` with the defining cubic embedding to reach the Euclidean model space.
  have hcomp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (cubic_real_line_embedding ∘ std_to_cubic f) := by
    -- The composite is the cubic polynomial applied to `f`, hence ordinarily smooth.
    rw [contMDiff_iff_contDiff]
    simpa [cubic_real_line_embedding, std_to_cubic, cubicMap, Function.comp] using
      ((contDiff_id.pow (3 : ℕ)).comp hf)
  -- The open-embedding API lifts Euclidean smoothness back to manifold smoothness.
  exact ContMDiff.of_comp_isOpenEmbedding
    (h' := cubic_real_line_embedding_isOpenEmbedding) hcomp

/-- Helper for Problem 2-5: if every block of an ordered finpartition has size `3`, then the
ambient order is divisible by `3`. -/
lemma OrderedFinpartition.three_dvd_of_all_partSize_eq_three {n : ℕ} (c : OrderedFinpartition n)
    (hpart : ∀ j : Fin c.length, c.partSize j = 3) : 3 ∣ n := by
  -- Count the sigma-type parametrizing the blocks to recover the total order `n`.
  have hcard : ∑ j : Fin c.length, c.partSize j = n := by
    simpa only [Fintype.card_fin, Fintype.card_sigma] using Fintype.card_congr c.equivSigma
  refine ⟨c.length, ?_⟩
  calc
    n = ∑ j : Fin c.length, c.partSize j := by simpa using hcard.symm
    _ = ∑ _j : Fin c.length, 3 := by simp [hpart]
    _ = c.length * 3 := by simp
    _ = 3 * c.length := by ring

/-- Helper for Problem 2-5: after composing a smooth function with the cubic chart, every
iterated derivative at `0` of order not divisible by `3` vanishes. -/
lemma iteratedDeriv_comp_cubic_eq_zero_of_not_three_dvd {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n (g ∘ cubicMap) 0 = 0 := by
  intro n hn
  have hcubic : ContDiffAt ℝ ∞ cubicMap 0 := by
    -- The cubic map is an ordinary smooth polynomial map.
    simpa [cubicMap] using
      ((contDiff_id.pow (3 : ℕ)) : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ (3 : ℕ))).contDiffAt
  have hnle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) by exact le_top)
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (x := 0) (i := n) hg.contDiffAt hcubic hnle]
  classical
  refine Finset.sum_eq_zero ?_
  intro c hc
  by_cases hprod : ∏ j, iteratedDeriv (c.partSize j) cubicMap 0 = 0
  · -- If the product of cubic derivatives vanishes, the whole Faà di Bruno term vanishes.
    simp [hprod]
  · -- Otherwise each block contributes a nonzero derivative, forcing all block sizes to be `3`.
    have hpart : ∀ j : Fin c.length, c.partSize j = 3 := by
      intro j
      have hfactor :
          iteratedDeriv (c.partSize j) cubicMap 0 ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
      have hpow :
          iteratedDeriv (c.partSize j) cubicMap 0 =
            (if c.partSize j = 3 then ((3 : ℕ).factorial : ℝ) else 0) := by
        calc
          iteratedDeriv (c.partSize j) cubicMap 0
              = iteratedDeriv (c.partSize j) (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 := by
                  rfl
          _ = (if c.partSize j = 3 then ((3 : ℕ).factorial : ℝ) else 0) := by
                simpa using
                  (iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := c.partSize j) (m := 3))
      by_contra hj
      have hzero : iteratedDeriv (c.partSize j) cubicMap 0 = 0 := by
        rw [hpow, if_neg hj]
      exact hfactor hzero
    have hdiv : 3 ∣ n := c.three_dvd_of_all_partSize_eq_three hpart
    exact (hn hdiv).elim

/-- Helper for Problem 2-5: away from the origin, the inverse cubic chart is ordinarily smooth. -/
lemma contDiffAt_cubicChart_symm_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ cubicChart.symm y := by
  -- The inverse function theorem applies because the derivative of `x ↦ x ^ 3` is nonzero away
  -- from the singular point.
  have hsymm_ne_zero : cubicChart.symm y ≠ 0 := by
    intro hzero
    apply hy
    simpa [hzero] using (cubicChart_symm_cube_eq y).symm
  have hderiv_ne_zero : (3 : ℝ) * cubicChart.symm y ^ (2 : ℕ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    exact pow_ne_zero 2 hsymm_ne_zero
  have hy_mem : y ∈ cubicChart.target := by
    rw [cubicChart_target_eq_univ]
    exact Set.mem_univ y
  have hderiv :
      HasDerivAt cubicChart ((3 : ℝ) * cubicChart.symm y ^ (2 : ℕ)) (cubicChart.symm y) := by
    -- The cubic chart has the same derivative as the polynomial `x ↦ x ^ 3`.
    simpa [cubicChart, cubicMap] using hasDerivAt_pow 3 (cubicChart.symm y)
  have hcubic : ContDiffAt ℝ ∞ cubicChart (cubicChart.symm y) := by
    -- Ordinary polynomial smoothness controls the chart itself.
    simpa [cubicChart, cubicMap] using
      ((contDiff_id.pow (3 : ℕ)) : ContDiff ℝ ∞ cubicChart).contDiffAt
  exact cubicChart.contDiffAt_symm_deriv hderiv_ne_zero hy_mem hderiv hcubic

/-- Helper for Problem 2-5: away from the origin, precomposing a smooth function with the inverse
cubic chart remains ordinarily smooth. -/
lemma contDiffAt_comp_cubicChart_symm_of_ne_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {y : ℝ}
    (hy : y ≠ 0) : ContDiffAt ℝ ∞ (f ∘ cubicChart.symm) y := by
  -- Off the singular point, the cube-root chart is smooth, so ordinary composition applies.
  exact ContDiffAt.comp y hf.contDiffAt (contDiffAt_cubicChart_symm_of_ne_zero hy)

/-- Helper for Problem 2-5: the three reciprocal factors added between degrees `3m` and
`3(m+1)` combine with `((3m)!)⁻¹` to give `((3(m+1))!)⁻¹`. -/
lemma cubic_taylor_inverse_factorial_step (m : ℕ) :
    (((3 * m).factorial : ℝ)⁻¹) *
        ((((3 * m + 1 : ℕ) : ℝ)⁻¹) *
          ((((3 * m + 2 : ℕ) : ℝ)⁻¹) * (((3 * m + 3 : ℕ) : ℝ)⁻¹))) =
      (((3 * (m + 1)).factorial : ℝ)⁻¹) := by
  -- Expand `((3 * (m + 1))!)` three times so the denominator matches the three new reciprocal
  -- factors inserted between `3m` and `3(m + 1)`.
  have hfactorial :
      (((3 * (m + 1)).factorial : ℝ)) =
        (((3 * m).factorial : ℝ) * (((3 * m + 1 : ℕ) : ℝ) *
          (((3 * m + 2 : ℕ) : ℝ) * (((3 * m + 3 : ℕ) : ℝ))))) := by
    calc
      (((3 * (m + 1)).factorial : ℝ))
          = (((3 * m + 3).factorial : ℕ) : ℝ) := by
              congr 1
      _ = (((3 * m + 3 : ℕ) : ℝ) * (((3 * m + 2).factorial : ℕ) : ℝ)) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m + 3 : ℕ) : ℝ) * (((3 * m + 2 : ℕ) : ℝ) *
            (((3 * m + 1).factorial : ℕ) : ℝ))) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m + 3 : ℕ) : ℝ) * ((((3 * m + 2 : ℕ) : ℝ) *
            (((3 * m + 1 : ℕ) : ℝ) * (((3 * m).factorial : ℕ) : ℝ))))) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m).factorial : ℝ) * (((3 * m + 1 : ℕ) : ℝ) *
            (((3 * m + 2 : ℕ) : ℝ) * (((3 * m + 3 : ℕ) : ℝ))))) := by
            ring_nf
  -- Inverting the explicit factorial factorization produces exactly the reciprocal chain on the
  -- left-hand side.
  simpa [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
    (congrArg Inv.inv hfactorial).symm

/-- Helper for Problem 2-5: Taylor polynomials at `0` compress to the terms whose degrees are
multiples of `3` when all other iterated derivatives vanish at `0`. -/
lemma taylorWithinEval_eq_cubic_polynomial_of_vanishing {f : ℝ → ℝ}
    (hvanish : ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0) :
    ∀ m : ℕ, ∀ x : ℝ,
      taylorWithinEval f (3 * m) Set.univ 0 x =
        Finset.sum (Finset.range (m + 1)) fun j =>
          (iteratedDeriv (3 * j) f 0 / ((3 * j).factorial : ℝ)) * x ^ (3 * j) := by
  -- TODO: iterate `taylorWithinEval_succ` three times, use `iteratedDerivWithin_univ`,
  -- kill the degrees `3m+1` and `3m+2` with `hvanish`, and normalize the last factorial
  -- coefficient using `cubic_taylor_inverse_factorial_step`.
  sorry

/-- Helper for Problem 2-5: substituting the inverse cubic chart turns a polynomial in powers
`(cubicChart.symm y)^(3j)` into the corresponding ordinary polynomial in `y`. -/
lemma cubic_polynomial_comp_cubicChart_symm (a : ℕ → ℝ) :
    ∀ m : ℕ, ∀ y : ℝ,
      Finset.sum (Finset.range (m + 1)) (fun j => a j * (cubicChart.symm y) ^ (3 * j)) =
        Finset.sum (Finset.range (m + 1)) fun j => a j * y ^ j := by
  intro m y
  -- Rewrite each monomial through `(cubicChart.symm y)^3 = y`.
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [pow_mul, cubicChart_symm_cube_eq]

/-- Helper for Problem 2-5: vanishing of the non-`3`-divisible derivatives of `f` at `0`
forces the Euclidean representative in the cubic source chart to be smooth. -/
lemma contDiff_comp_cubic_chart_symm_of_vanishing {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hvanish : ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0) :
    ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) := by
  -- Route correction: the zero-point argument must first be solved in Euclidean coordinates,
  -- then translated back to manifolds through the cubic singleton atlas.
  -- TODO: use `taylorWithinEval_eq_cubic_polynomial_of_vanishing`,
  -- `cubic_polynomial_comp_cubicChart_symm`, and the Taylor remainder estimate at `0` to prove
  -- `ContDiffAt ℝ m (cubic_to_std f ∘ cubic_chart_symm_to_cubic) 0` for every `m : ℕ`, combine
  -- this with `contDiffAt_comp_cubicChart_symm_of_ne_zero`, and finish via `contDiff_infty`.
  sorry

/-- Problem 2-5 (2): for a function `f : ℝ → ℝ` that is smooth in the usual sense, smoothness as a
map from Lee's alternate smooth real line `\widetilde{ℝ}` to the standard smooth real line is
equivalent to vanishing of every derivative at `0` whose order is not a multiple of `3`. -/
theorem contMDiff_cubic_to_std_iff_iteratedDeriv_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (cubic_to_std f) ↔
      ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0 := by
  -- Route correction: lock the cubic singleton atlas locally, then pass between manifold
  -- smoothness and ordinary smoothness by composing with the inverse cubic chart.
  constructor
  · intro hmdiff n hn
    have hsymm : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ cubic_chart_symm_to_cubic := by
      -- The inverse of the defining open embedding is manifold-smooth on its image, which is all
      -- of `ℝ` because the cubic map is surjective.
      rw [← contMDiffOn_univ, ← cubicMap_surjective.range_eq]
      simpa [cubic_real_line_embedding, cubic_chart_symm_to_cubic, cubicChart] using
        (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ))
          (h := cubic_real_line_embedding_isOpenEmbedding) (n := ∞))
    have hg : ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) := by
      -- Composing the manifold-smooth map with the manifold-smooth inverse chart gives an
      -- ordinary smooth function on `ℝ`.
      simpa [contMDiff_iff_contDiff] using hmdiff.comp hsymm
    have hrewrite : ((cubic_to_std f ∘ cubic_chart_symm_to_cubic) ∘ cubicMap) = f := by
      -- The cubic chart inverse cancels the cubic map pointwise.
      funext x
      simp [cubic_to_std, cubic_chart_symm_to_cubic, Function.comp, cubicChart_symm_cubicMap_eq]
    -- Apply the Faà di Bruno vanishing lemma to the Euclidean representative.
    simpa [hrewrite] using
      iteratedDeriv_comp_cubic_eq_zero_of_not_three_dvd hg n hn
  · intro hvanish
    have hg : ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) :=
      contDiff_comp_cubic_chart_symm_of_vanishing hf hvanish
    intro x
    -- Translate the manifold-smoothness claim to the Euclidean representative in the source
    -- cubic chart, where `hg` applies directly.
    rw [contMDiffAt_iff_source_of_mem_source (I := 𝓘(ℝ)) (I' := 𝓘(ℝ))
      (x := x) (x' := x) (f := cubic_to_std f) (mem_chart_source _ x)]
    simpa [cubic_to_std, cubic_chart_symm_to_cubic, cubic_real_line_embedding, Function.comp,
      extChartAt_coe, extChartAt_coe_symm, extChartAt_model_space_eq_id,
      Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq,
      contMDiffWithinAt_iff_contDiffWithinAt] using
      (hg.contDiffAt.contDiffWithinAt : ContDiffWithinAt ℝ ∞
        (cubic_to_std f ∘ cubic_chart_symm_to_cubic) Set.univ (cubic_real_line_embedding x))
