import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_4 (from Chap03) -/
/-
Definition 3.4 lies in the finite convex-combination domain over an ordered scalar ring, with the
extra source-facing requirement that every coefficient be strictly positive.

Sampled owner-style declarations:
- `StdSimplex`
- `StdSimplex.IsStrict`
- `is_convex_combination_of`
- `StdSimplex.map`
- `ConvexSpace.convexCombination`
- `convexCombination_eq_sum`

Best owner abstraction:
- `convexCombination (w.1.map points)` for `w : StdSimplex.Strict R ι`

Primitive data:
- a strict simplex weight vector `w : StdSimplex.Strict R ι`
- a finite family `points : ι → E`

Derived API:
- the owner predicate `StdSimplex.IsStrict`
- the reusable strict subtype view `StdSimplex.Strict`
- the derived finiteness lemma `StdSimplex.Strict.finite`
- the source-facing strict-convex-combination predicate
- the bridge to the earlier owner predicate `is_convex_combination_of`
- the coefficient bridge theorem

Source/core/bridge triage:
- source-facing: `is_strict_convex_combination_of R points x`
- core/canonical: `w : StdSimplex.Strict R ι` and `convexCombination (w.1.map points)`
- bridge/view:
  `is_strict_convex_combination_of.is_convex_combination_of`
  and
  `is_strict_convex_combination_of_iff_exists_coefficients`

The earlier chapter file `Definition_3_1_1_4` already owns the finite convex-combination notion,
so this file reuses that finite-family owner directly, with `StdSimplex.IsStrict` as the
strictness predicate and `StdSimplex.Strict` as the corresponding strict owner view. The strict
simplex witness already forces `ι` to be finite, so the source-facing predicate derives finiteness
internally instead of storing it as separate public data. Later files with strictly positive
simplex data should reuse this owner-based API instead of reintroducing a parallel top-level
alias. -/

namespace StdSimplex

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- A simplex weight vector is strict when every coefficient is strictly positive. -/
def IsStrict {ι : Type*} (w : StdSimplex R ι) : Prop :=
  ∀ i, 0 < w.weights i

/-- The subtype of strict simplex weight vectors. -/
abbrev Strict (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] (ι : Type*) :=
  {w : StdSimplex R ι // w.IsStrict}

theorem Strict.finite {ι : Type*} (w : StdSimplex.Strict R ι) : Finite ι := by
  classical
  let f : ι ↪ {i // i ∈ w.1.weights.support} :=
    ⟨fun i ↦ ⟨i, by
        rw [Finsupp.mem_support_iff]
        exact ne_of_gt (w.2 i)⟩,
      fun _ _ h ↦ Subtype.mk.inj h⟩
  exact Finite.of_injective f f.injective

end StdSimplex

section Owner

variable (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable {ι : Type v}
variable {E : Type w} [ConvexSpace R E]

/-- Definition 3.4: a point is a strict convex combination of a finite family of points when it is
the canonical convex combination associated to a strict simplex weight vector. -/
def is_strict_convex_combination_of (points : ι → E) (x : E) : Prop :=
  ∃ w : StdSimplex.Strict R ι, x = convexCombination (w.1.map points)

/-- A strict convex combination is, in particular, an ordinary convex combination of the same
family. -/
theorem is_strict_convex_combination_of.is_convex_combination_of
    {points : ι → E} {x : E}
    (h : is_strict_convex_combination_of R points x) :
    is_convex_combination_of R points x := by
  rcases h with ⟨w, hw⟩
  letI : Finite ι := w.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  exact ⟨w, hw⟩

end Owner

section Module

variable {ι : Type v} [Fintype ι]
variable {R : Type u} [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {E : Type w} [AddCommGroup E] [Module R E]

/-- Unpacking a strict convex combination into coefficient data gives exactly the textbook formula
with positive coefficients summing to `1`. -/
-- Proof sketch: unpack a strict `StdSimplex` weight vector into its coefficient function, read off
-- normalization from the underlying `StdSimplex`, rewrite the canonical convex combination by
-- `StdSimplex.convexCombination_map_eq_sum`, and read strict positivity from `w.IsStrict`;
-- conversely,
-- package the coefficient family into a `StdSimplex`, prove it strict using the positivity
-- hypothesis, and then recover the canonical convex combination.
theorem is_strict_convex_combination_of_iff_exists_coefficients
    (points : ι → E) (x : E) :
    is_strict_convex_combination_of R points x ↔
      ∃ α : ι → R, (∀ i, 0 < α i) ∧ (∑ i, α i) = 1 ∧ x = ∑ i, α i • points i := by
  unfold is_strict_convex_combination_of
  constructor
  · rintro ⟨w, hwx⟩
    refine ⟨w.1.weights, w.2, ?_, ?_⟩
    · simpa [Finsupp.sum_fintype] using w.1.total
    · simpa [StdSimplex.convexCombination_map_eq_sum R w.1 points] using hwx
  · rintro ⟨α, hα_pos, hα_sum, rfl⟩
    let w : StdSimplex.Strict R ι :=
      ⟨⟨Finsupp.equivFunOnFinite.symm α,
          by simpa using fun i ↦ (hα_pos i).le,
          by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hα_sum⟩,
        hα_pos⟩
    refine ⟨w, ?_⟩
    simpa [w] using (StdSimplex.convexCombination_map_eq_sum R w.1 points).symm

end Module

/-! ### Lemma_3_4 (from Chap03) -/
noncomputable section

open Filter
open scoped Topology
open scoped WithTopConvexAnalysis

private theorem convexOn_right_secant_bound
    {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    {x z t : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxt : x ≤ t) (htz : t < z) :
    g t ≤ g x + ((t - x) / (z - x)) * (g z - g x) := by
  rcases eq_or_lt_of_le hxt with rfl | hxt
  · simp
  have hxz : x < z := lt_trans hxt htz
  have hzx0 : 0 < z - x := sub_pos.mpr hxz
  have hsec :
      (z - x) * g t ≤ (z - t) * g x + (t - x) * g z :=
    hg.secant_mono_aux1 hx hz hxt htz
  refine le_of_mul_le_mul_left ?_ hzx0
  calc
    (z - x) * g t ≤ (z - t) * g x + (t - x) * g z := hsec
    _ = (z - x) * (g x + ((t - x) / (z - x)) * (g z - g x)) := by
      field_simp [hzx0.ne']
      ring

private theorem convexOn_left_secant_bound
    {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    {z x t : ℝ} (hz : z ∈ s) (hx : x ∈ s) (hzt : z < t) (htx : t ≤ x) :
    g t ≤ g x + ((x - t) / (x - z)) * (g z - g x) := by
  rcases eq_or_lt_of_le htx with rfl | htx
  · simp
  have hzx : z < x := lt_trans hzt htx
  have hxz0 : 0 < x - z := sub_pos.mpr hzx
  have hsec :
      (x - z) * g t ≤ (x - t) * g z + (t - z) * g x :=
    hg.secant_mono_aux1 hz hx hzt htx
  refine le_of_mul_le_mul_left ?_ hxz0
  calc
    (x - z) * g t ≤ (x - t) * g z + (t - z) * g x := hsec
    _ = (x - z) * (g x + ((x - t) / (x - z)) * (g z - g x)) := by
      field_simp [hxz0.ne']
      ring

private theorem coeff_mul_abs_lt_half
    {num den diff ε : ℝ}
    (hnum_nonneg : 0 ≤ num) (hden_pos : 0 < den)
    (hnum_lt : num < den * ε / (2 * (|diff| + 1))) (hε : 0 < ε) :
    (num / den) * |diff| < ε / 2 := by
  let A : ℝ := |diff| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hcoeff_nonneg : 0 ≤ num / den := div_nonneg hnum_nonneg hden_pos.le
  have hcoeff_lt : num / den < ε / (2 * A) := by
    have h' : num < (ε / (2 * A)) * den := by
      simpa [A, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hnum_lt
    exact (div_lt_iff₀ hden_pos).2 h'
  have hle : (num / den) * |diff| ≤ (num / den) * A := by
    have habs_le : |diff| ≤ A := by
      dsimp [A]
      nlinarith
    exact mul_le_mul_of_nonneg_left habs_le hcoeff_nonneg
  have hlt : (num / den) * A < ε / 2 := by
    have hmul := mul_lt_mul_of_pos_right hcoeff_lt hApos
    have hEq : (ε / (2 * A)) * A = ε / 2 := by
      field_simp [A, hApos.ne']
    simpa [hEq] using hmul
  exact lt_of_le_of_lt hle hlt

/-
Lemma 3.4 lies in the chapter's univariate closed-convex continuity domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `dom f`, `withTopRealPart` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- mathlib `continuousWithinAt_iff_continuousAt_restrict`
- mathlib `continuous_iff_seqContinuous`
- mathlib `ConvexOn.continuousOn`

Best owner abstraction:
- `ClosedConvexFunction`, with `dom f` and `withTopRealPart f` as the canonical derived
  domain/view data.

Primitive data:
- the effective domain `dom f`
- the finite real representative `withTopRealPart f`
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: continuity of the finite-value representative on the effective domain
- core/canonical: `ClosedConvexFunction`
- bridge/view: restriction to the effective-domain subtype used to express relative continuity

The source-facing continuity theorem is the main public entry in this file. The sequential limit
reformulation carried no downstream use in the chapter, so the file keeps only the owner theorem
instead of exporting a second bridge statement.
-/

/-- Lemma 3.4: any univariate closed convex function is continuous on its effective domain. -/
-- Proof sketch: restrict `withTopRealPart f` to the effective-domain subtype. The one-dimensional
-- closed-convex argument gives sequential continuity there, and metric-space sequential continuity
-- upgrades to continuity on the subtype. Translating back yields continuity on the effective
-- domain.
theorem ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
    {f : ℝ → WithTop ℝ} (hf : ClosedConvexFunction f) :
    ContinuousOn (withTopRealPart f) (dom f) := by
  let g : ℝ → ℝ := withTopRealPart f
  have hconv : ConvexOn ℝ (dom f) g := hf.convexOn_withTopRealPart
  have hclosed :
      IsClosed {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2} := by
    rw [← constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom f ⊆ dom f)]
    exact hf.isClosed_constrainedEpigraph
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous]
  intro u x hu
  have hu_real : Tendsto (fun n ↦ ((u n : dom f) : ℝ)) atTop (𝓝 (x : ℝ)) :=
    tendsto_subtype_rng.1 hu
  have hnear :
      ∀ {δ : ℝ}, 0 < δ →
        ∀ᶠ n in atTop, |((u n : dom f) : ℝ) - (x : ℝ)| < δ := by
    intro δ hδ
    have hball : Metric.ball (x : ℝ) δ ∈ 𝓝 (x : ℝ) :=
      Metric.ball_mem_nhds _ hδ
    simpa [Metric.mem_ball, Real.dist_eq] using hu_real hball
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlower : ∀ᶠ n in atTop, g x - ε / 2 < g (u n) := by
    have hpair :
        Tendsto (fun n ↦ (((u n : dom f) : ℝ), g x - ε / 2)) atTop
          (𝓝 ((x : ℝ), g x - ε / 2)) :=
      hu_real.prodMk_nhds tendsto_const_nhds
    have hnot :
        ((x : ℝ), g x - ε / 2) ∉ {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2} := by
      have : ¬ g x ≤ g x - ε / 2 := by
        nlinarith [hε]
      rintro ⟨_, hx⟩
      exact this hx
    have hmem :
        {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2}ᶜ ∈
          𝓝 ((x : ℝ), g x - ε / 2) :=
      hclosed.isOpen_compl.mem_nhds hnot
    filter_upwards [hpair hmem] with n hn
    have hu_mem : ((u n : dom f) : ℝ) ∈ dom f := (u n).2
    exact not_le.mp (fun hle ↦ hn ⟨hu_mem, hle⟩)
  have hupper : ∀ᶠ n in atTop, g (u n) < g x + ε / 2 := by
    by_cases hleft : ∃ z : dom f, (z : ℝ) < (x : ℝ)
    · by_cases hright : ∃ z : dom f, (x : ℝ) < (z : ℝ)
      · rcases hleft with ⟨zl, hzl⟩
        rcases hright with ⟨zr, hzr⟩
        have hxl_pos : 0 < (x : ℝ) - (zl : ℝ) := sub_pos.mpr hzl
        have hxr_pos : 0 < (zr : ℝ) - (x : ℝ) := sub_pos.mpr hzr
        let δl : ℝ :=
          min (((x : ℝ) - (zl : ℝ)) / 2)
            ((((x : ℝ) - (zl : ℝ)) * ε) /
              (2 * (|g zl - g x| + 1)))
        let δr : ℝ :=
          min (((zr : ℝ) - (x : ℝ)) / 2)
            ((((zr : ℝ) - (x : ℝ)) * ε) /
              (2 * (|g zr - g x| + 1)))
        let δ : ℝ := min δl δr
        have hδl_pos : 0 < δl := by
          dsimp [δl]
          apply lt_min
          · exact half_pos hxl_pos
          · positivity
        have hδr_pos : 0 < δr := by
          dsimp [δr]
          apply lt_min
          · exact half_pos hxr_pos
          · positivity
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          exact lt_min hδl_pos hδr_pos
        filter_upwards [hnear hδ_pos] with n hn
        rcases le_or_gt ((u n : dom f) : ℝ) (x : ℝ) with hux | hxu
        · have hzl_un : (zl : ℝ) < ((u n : dom f) : ℝ) := by
            have habs := abs_lt.1 hn
            have hδ_le_δl : δ ≤ δl := by
              dsimp [δ]
              exact min_le_left _ _
            have hδl_half : δl ≤ (((x : ℝ) - (zl : ℝ)) / 2) := by
              dsimp [δl]
              exact min_le_left _ _
            nlinarith
          let coeff : ℝ := (((x : ℝ) - (u n : dom f)) / ((x : ℝ) - (zl : ℝ)))
          have hcoeff_nonneg : 0 ≤ coeff := by
            dsimp [coeff]
            exact div_nonneg (sub_nonneg.mpr hux) (sub_nonneg.mpr hzl.le)
          have hxu_lt_δ : (x : ℝ) - (u n : dom f) < δ := by
            have habs := abs_lt.1 hn
            nlinarith
          have hδ_num :
              (x : ℝ) - (u n : dom f) <
                (((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1)) := by
            have hδ_le_δl : δ ≤ δl := by
              dsimp [δ]
              exact min_le_left _ _
            have hδl_le :
                δl ≤ ((((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1))) := by
              dsimp [δl]
              exact min_le_right _ _
            exact lt_of_lt_of_le hxu_lt_δ (le_trans hδ_le_δl hδl_le)
          have hmul_lt : coeff * |g zl - g x| < ε / 2 := by
            dsimp [coeff]
            exact coeff_mul_abs_lt_half
              (sub_nonneg.mpr hux) hxl_pos hδ_num hε
          have hsec :
              g (u n) ≤ g x + coeff * (g zl - g x) := by
            simpa [g, coeff] using
              convexOn_left_secant_bound hconv zl.2 x.2 hzl_un hux
          have hbound : g (u n) ≤ g x + coeff * |g zl - g x| := by
            have : coeff * (g zl - g x) ≤ coeff * |g zl - g x| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
            nlinarith
          nlinarith
        · let coeff : ℝ := ((((u n : dom f) : ℝ) - (x : ℝ)) / ((zr : ℝ) - (x : ℝ)))
          have huzr : ((u n : dom f) : ℝ) < (zr : ℝ) := by
            have habs := abs_lt.1 hn
            have hδ_le_δr : δ ≤ δr := by
              dsimp [δ]
              exact min_le_right _ _
            have hδr_half : δr ≤ (((zr : ℝ) - (x : ℝ)) / 2) := by
              dsimp [δr]
              exact min_le_left _ _
            nlinarith
          have hcoeff_nonneg : 0 ≤ coeff := by
            dsimp [coeff]
            exact div_nonneg (sub_nonneg.mpr hxu.le) (sub_nonneg.mpr hzr.le)
          have hxu_lt_δ : ((u n : dom f) : ℝ) - (x : ℝ) < δ := by
            have habs := abs_lt.1 hn
            nlinarith
          have hδ_num :
              ((u n : dom f) : ℝ) - (x : ℝ) <
                (((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1)) := by
            have hδ_le_δr : δ ≤ δr := by
              dsimp [δ]
              exact min_le_right _ _
            have hδr_le :
                δr ≤ ((((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1))) := by
              dsimp [δr]
              exact min_le_right _ _
            exact lt_of_lt_of_le hxu_lt_δ (le_trans hδ_le_δr hδr_le)
          have hmul_lt : coeff * |g zr - g x| < ε / 2 := by
            dsimp [coeff]
            exact coeff_mul_abs_lt_half
              (sub_nonneg.mpr hxu.le) hxr_pos hδ_num hε
          have hsec :
              g (u n) ≤ g x + coeff * (g zr - g x) := by
            simpa [g, coeff] using
              convexOn_right_secant_bound hconv x.2 zr.2 hxu.le huzr
          have hbound : g (u n) ≤ g x + coeff * |g zr - g x| := by
            have : coeff * (g zr - g x) ≤ coeff * |g zr - g x| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
            nlinarith
          nlinarith
      · rcases hleft with ⟨zl, hzl⟩
        have hx_max : ∀ {y : ℝ}, y ∈ dom f → y ≤ (x : ℝ) := by
          intro y hy
          by_contra hyx
          exact hright ⟨⟨y, hy⟩, lt_of_not_ge hyx⟩
        have hxl_pos : 0 < (x : ℝ) - (zl : ℝ) := sub_pos.mpr hzl
        let δ : ℝ :=
          min (((x : ℝ) - (zl : ℝ)) / 2)
            ((((x : ℝ) - (zl : ℝ)) * ε) /
              (2 * (|g zl - g x| + 1)))
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          apply lt_min
          · exact half_pos hxl_pos
          · positivity
        filter_upwards [hnear hδ_pos] with n hn
        have hux : ((u n : dom f) : ℝ) ≤ (x : ℝ) := hx_max (u n).2
        have hzl_un : (zl : ℝ) < ((u n : dom f) : ℝ) := by
          have habs := abs_lt.1 hn
          have hδ_half : δ ≤ (((x : ℝ) - (zl : ℝ)) / 2) := by
            dsimp [δ]
            exact min_le_left _ _
          nlinarith
        let coeff : ℝ := (((x : ℝ) - (u n : dom f)) / ((x : ℝ) - (zl : ℝ)))
        have hcoeff_nonneg : 0 ≤ coeff := by
          dsimp [coeff]
          exact div_nonneg (sub_nonneg.mpr hux) (sub_nonneg.mpr hzl.le)
        have hxu_lt_δ : (x : ℝ) - (u n : dom f) < δ := by
          have habs := abs_lt.1 hn
          nlinarith
        have hδ_num :
            (x : ℝ) - (u n : dom f) <
              (((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1)) := by
          have hδ_le :
              δ ≤ ((((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1))) := by
            dsimp [δ]
            exact min_le_right _ _
          exact lt_of_lt_of_le hxu_lt_δ hδ_le
        have hmul_lt : coeff * |g zl - g x| < ε / 2 := by
          dsimp [coeff]
          exact coeff_mul_abs_lt_half
            (sub_nonneg.mpr hux) hxl_pos hδ_num hε
        have hsec :
            g (u n) ≤ g x + coeff * (g zl - g x) := by
          simpa [g, coeff] using
            convexOn_left_secant_bound hconv zl.2 x.2 hzl_un hux
        have hbound : g (u n) ≤ g x + coeff * |g zl - g x| := by
          have : coeff * (g zl - g x) ≤ coeff * |g zl - g x| := by
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
          nlinarith
        nlinarith
    · by_cases hright : ∃ z : dom f, (x : ℝ) < (z : ℝ)
      · rcases hright with ⟨zr, hzr⟩
        have hx_min : ∀ {y : ℝ}, y ∈ dom f → (x : ℝ) ≤ y := by
          intro y hy
          by_contra hyx
          exact hleft ⟨⟨y, hy⟩, lt_of_not_ge hyx⟩
        have hxr_pos : 0 < (zr : ℝ) - (x : ℝ) := sub_pos.mpr hzr
        let δ : ℝ :=
          min (((zr : ℝ) - (x : ℝ)) / 2)
            ((((zr : ℝ) - (x : ℝ)) * ε) /
              (2 * (|g zr - g x| + 1)))
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          apply lt_min
          · exact half_pos hxr_pos
          · positivity
        filter_upwards [hnear hδ_pos] with n hn
        have hxu : (x : ℝ) ≤ ((u n : dom f) : ℝ) := hx_min (u n).2
        have huzr : ((u n : dom f) : ℝ) < (zr : ℝ) := by
          have habs := abs_lt.1 hn
          have hδ_half : δ ≤ (((zr : ℝ) - (x : ℝ)) / 2) := by
            dsimp [δ]
            exact min_le_left _ _
          nlinarith
        let coeff : ℝ := ((((u n : dom f) : ℝ) - (x : ℝ)) / ((zr : ℝ) - (x : ℝ)))
        have hcoeff_nonneg : 0 ≤ coeff := by
          dsimp [coeff]
          exact div_nonneg (sub_nonneg.mpr hxu) (sub_nonneg.mpr hzr.le)
        have hxu_lt_δ : ((u n : dom f) : ℝ) - (x : ℝ) < δ := by
          have habs := abs_lt.1 hn
          nlinarith
        have hδ_num :
            ((u n : dom f) : ℝ) - (x : ℝ) <
              (((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1)) := by
          have hδ_le :
              δ ≤ ((((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1))) := by
            dsimp [δ]
            exact min_le_right _ _
          exact lt_of_lt_of_le hxu_lt_δ hδ_le
        have hmul_lt : coeff * |g zr - g x| < ε / 2 := by
          dsimp [coeff]
          exact coeff_mul_abs_lt_half
            (sub_nonneg.mpr hxu) hxr_pos hδ_num hε
        have hsec :
            g (u n) ≤ g x + coeff * (g zr - g x) := by
          simpa [g, coeff] using
            convexOn_right_secant_bound hconv x.2 zr.2 hxu huzr
        have hbound : g (u n) ≤ g x + coeff * |g zr - g x| := by
          have : coeff * (g zr - g x) ≤ coeff * |g zr - g x| := by
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
          nlinarith
        nlinarith
      · have hsingle : ∀ {y : ℝ}, y ∈ dom f → y = (x : ℝ) := by
          intro y hy
          by_cases hxy : y = (x : ℝ)
          · exact hxy
          · rcases lt_or_gt_of_ne hxy with hyx | hxy'
            · exact False.elim <| hleft ⟨⟨y, hy⟩, hyx⟩
            · exact False.elim <| hright ⟨⟨y, hy⟩, hxy'⟩
        filter_upwards [Filter.Eventually.of_forall fun n ↦ hsingle (u n).2] with n hn
        have : g x < g x + ε / 2 := by
          nlinarith
        simpa [g, hn] using this
  have hfinal :
      ∀ᶠ n in atTop,
        dist (((dom f).restrict (withTopRealPart f) ∘ u) n)
          (((dom f).restrict (withTopRealPart f)) x) < ε := by
    filter_upwards [hlower, hupper] with n hn_lower hn_upper
    have : |g (u n) - g x| < ε := by
      rw [abs_sub_lt_iff]
      constructor <;> nlinarith
    simpa [g, Real.dist_eq] using this
  simpa [Filter.eventually_atTop] using hfinal

end

/-! ### Proposition_3_4 (from Chap03) -/
/- Proposition 3.4 lies in the chapter's closed-convex `WithTop`-valued convex-analysis domain.

Primary domain:
- continuous convex real-valued functions viewed through the owner predicate
  `ClosedConvexFunction`.

Sampled owner-style declarations:
- `closedConvexFunction_coe_of_convexOn_continuous` in `Proposition_3_1_1_3`, the existing
  chapter theorem with the same mathematical content at the intrinsic real topological-module
  level;
- `ClosedConvexFunction` and `ClosedConvexOn` in `Definition_3_1_1_5`, the source-facing owners
  for closed convex extended-real-valued functions;
- mathlib `ConvexOn.convex_epigraph`;
- mathlib `IsClosed.epigraph`.

Best owner abstraction:
- `closedConvexFunction_coe_of_convexOn_continuous`.

Primitive data:
- a real-valued function `f`;
- its convexity on `Set.univ`;
- its continuity.

Derived API:
- the closed-convex owner statement for the `WithTop ℝ` coercion of `f`.

Source/core/bridge triage:
- source-facing: Proposition 3.4 as the Euclidean `ℝⁿ` statement;
- core/canonical: `ClosedConvexFunction` together with `ConvexOn` and closed epigraphs;
- bridge/view: the already-proved intrinsic theorem
  `closedConvexFunction_coe_of_convexOn_continuous`.

This file is therefore recall-only. Keeping a second Euclidean theorem shell here would duplicate
an existing owner-level declaration instead of reusing the chapter's canonical abstraction. -/

recall closedConvexFunction_coe_of_convexOn_continuous

/-! ### Theorem_3_4 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.4 lies in the chapter's `WithTop` convex-sublevel-set domain.

Primary domain:
- convex sublevel sets for `WithTop ℝ`-valued functions on an `ℝ`-module.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- mathlib `ConvexOn.convex_lt`
- chapter `withTopRealPart` in `Definition_3_3`
- chapter `constrainedSublevelSet` in `Definition_3_3`

Best owner abstraction:
- core/canonical: `ConvexOn.convex_le`, specialized to
  `ConvexOn ℝ (dom f) (withTopRealPart f)`

Primitive data:
- `dom f`
- `withTopRealPart f`

Derived API:
- `constrainedSublevelSet (dom f) f β`
- the bridge `withTopRealPart_le_iff`
- the source-facing convexity theorem below

Source/core/bridge triage:
- source-facing: `constrainedSublevelSet (dom f) f β`
- core/canonical: `ConvexOn.convex_le`
- bridge/view: `constrainedSublevelSet_dom_eq`, identifying the chapter sublevel-set owner with
  the owner surface `{x ∈ dom f | withTopRealPart f x ≤ β}`

The textbook states the result on `ℝⁿ`, but both the owner theorem and the chapter bridge use
only the ambient `ℝ`-module structure. This file therefore keeps the source-facing `WithTop`
sublevel-set theorem on the public surface and derives it directly from the canonical owner
theorem.
-/

/-- Helper for Theorem 3.4: on the effective domain, the chapter's constrained sublevel set is
exactly the owner sublevel set of the finite real part. -/
theorem constrainedSublevelSet_dom_eq {X : Type u} (f : X → WithTop ℝ) (β : ℝ) :
    constrainedSublevelSet (dom f) f β = {x ∈ dom f | withTopRealPart f x ≤ β} := by
  -- Identify both sets pointwise using the domain membership bridge from Definition 3.3.
  ext x
  constructor
  · rintro ⟨hx, hxβ⟩
    -- Inside the effective domain, the `WithTop` inequality is equivalent to the owner real one.
    exact ⟨hx, (withTopRealPart_le_iff hx).2 hxβ⟩
  · rintro ⟨hx, hxβ⟩
    -- Reversing the same bridge recovers the chapter-facing sublevel-set condition.
    exact ⟨hx, (withTopRealPart_le_iff hx).1 hxβ⟩

namespace ConvexOn

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable {f : X → WithTop ℝ}

/-- Theorem 3.4: if `f` is convex on its effective domain, then each constrained sublevel set of
`f` over that domain is convex. -/
theorem convex_constrainedSublevelSet
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) (β : ℝ) :
    Convex ℝ (constrainedSublevelSet (dom f) f β) := by
  -- Rewrite the chapter sublevel set to the owner surface and apply `ConvexOn.convex_le`.
  simpa [constrainedSublevelSet_dom_eq f β] using hf.convex_le β

end Convexity

end ConvexOn
