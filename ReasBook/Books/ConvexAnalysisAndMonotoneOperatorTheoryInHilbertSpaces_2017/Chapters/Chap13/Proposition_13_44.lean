import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Lemma_1_32
import BauschkeLean.Chap01.Text_1_0_31
import BauschkeLean.Chap08.Proposition_8_4
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Corollary_9_10
import BauschkeLean.Chap09.Proposition_9_6
import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Theorem_13_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Filter

universe u

namespace ERealFunction

section BasicConjugationHelpers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 44: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex
    {f : H → EReal} (hconv : IsConvex f) :
    Convex ℝ (epigraph f) := by
  -- Rewrite epigraph convexity through the Jensen criterion already stored in `IsConvex`.
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy a ha ha_lt_one
  exact hconv ha.le ha_lt_one.le

/-- Helper for Proposition 13 44: every affine defect is bounded above by the Fenchel conjugate
at the same dual point. -/
private theorem affine_defect_le_conjugate
    (f : H → EReal) (x u : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ u := by
  -- Evaluate the defining supremum of `f∗ u` at the chosen primal point `x`.
  rw [conjugate_apply]
  exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Helper for Proposition 13 44: every function dominates its Fenchel biconjugate pointwise. -/
private theorem biconjugate_le_local
    (f : H → EReal) :
    f∗∗ ≤ f := by
  -- This is exactly Proposition 13.16(i).
  exact biconjugate_le f

/-- Helper for Proposition 13 44: Fenchel conjugation reverses the pointwise order. -/
private theorem conjugate_antitone_local :
    Antitone (conjugate : (H → EReal) → H → EReal) := by
  intro f g hfg u
  -- Compare the affine defects pointwise and then take suprema.
  rw [conjugate_apply, conjugate_apply]
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - g x)
        ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) := by
          exact EReal.sub_le_sub le_rfl (hfg x)
    _ ≤ ⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) := by
          exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Helper for Proposition 13 44: the triple Fenchel conjugate equals the single conjugate. -/
private theorem triple_conjugate_eq_conjugate_local
    (f : H → EReal) :
    f∗∗∗ = f∗ := by
  -- This is exactly Proposition 13.16(iv).
  simpa using triple_conjugate_eq_conjugate (f := f)

/-- Helper for Proposition 13 44: the Fenchel biconjugate lies below the lower semicontinuous
convex envelope. -/
private theorem biconjugate_le_lowerSemicontinuousConvexEnvelope
    (f : H → EReal) :
    f∗∗ ≤ lowerSemicontinuousConvexEnvelope f := by
  have hbiconj_gamma : f∗∗ ∈ gamma H := conjugate_mem_gamma (f := f∗)
  have hbiconj_data : IsConvex (f∗∗) ∧ LowerSemicontinuous (f∗∗) :=
    (mem_gamma_iff (f∗∗)).mp hbiconj_gamma
  -- Proposition 9.8 makes the envelope the maximal lower semicontinuous convex minorant.
  exact
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hbiconj_data.2
      (convex_epigraph_of_isConvex hbiconj_data.1)
      (biconjugate_le f)

/-- Helper for Proposition 13 44: passing to the lower semicontinuous convex envelope preserves
the Fenchel conjugate. -/
private theorem conjugate_lowerSemicontinuousConvexEnvelope_eq_local
    (f : H → EReal) :
    (lowerSemicontinuousConvexEnvelope f)∗ = f∗ := by
  -- This is exactly Proposition 13.16(iv) specialized to the convex envelope.
  simpa using conjugate_lowerSemicontinuousConvexEnvelope_eq (f := f)

/-- Helper for Proposition 13 44: a point outside the domain has value `⊤`. -/
private theorem value_eq_top_of_not_mem_dom
    {X : Type u} {f : X → EReal} {x : X} (hx : x ∉ dom f) :
    f x = ⊤ := by
  -- This is the complement form of domain membership.
  exact (not_mem_dom_iff f x).mp hx

/-- Helper for Proposition 13 44: a lower semicontinuous function with convex epigraph and one
finite point cannot take the value `⊥` anywhere on its domain. -/
private theorem ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ y : H} (hx₀ : x₀ ∈ effectiveDom g) (hy : y ∈ dom g) :
    g y ≠ ⊥ := by
  intro hy_bot
  have hx₀_fin := (mem_effectiveDom_iff (f := g) (x := x₀)).mp hx₀
  have hx₀_dom : x₀ ∈ dom g := (mem_dom_iff_ne_top g x₀).2 hx₀_fin.1
  let u : ℕ → H := fun n ↦ (1 / (n + 2 : ℝ)) • y + (1 - 1 / (n + 2 : ℝ)) • x₀
  have hu_tendsto : Tendsto u atTop (nhds x₀) :=
    tendsto_reciprocal_convex_combination_to_right y x₀
  have hu_bot : ∀ n : ℕ, g (u n) = ⊥ := by
    intro n
    have hα_pos : 0 < 1 / (n + 2 : ℝ) := by
      exact one_div_pos.mpr (by positivity : (0 : ℝ) < n + 2)
    have hα_lt_one : 1 / (n + 2 : ℝ) < 1 := by
      have h : 1 / (n + 2 : ℝ) < 1 / (1 : ℝ) := by
        refine (one_div_lt_one_div (α := ℝ) ?_ ?_).2 ?_
        · positivity
        · norm_num
        · exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
      simpa using h
    have hineq :
        g (u n) ≤
          ((1 / (n + 2 : ℝ) : ℝ) : EReal) * g y +
            (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := by
      simpa [u] using
        (convex_epigraph_iff_jensen_on_dom g).1 hconv hy hx₀_dom hα_pos hα_lt_one
    have hαE : 0 < (((1 / (n + 2 : ℝ) : ℝ) : EReal)) := EReal.coe_pos.mpr hα_pos
    have hineq_bot : g (u n) ≤ ⊥ := by
      calc
        g (u n)
            ≤ ((1 / (n + 2 : ℝ) : ℝ) : EReal) * g y +
                (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := hineq
        _ = ⊥ + (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := by
          rw [hy_bot, EReal.mul_bot_of_pos hαE]
        _ = ⊥ := by
          rw [EReal.bot_add]
    exact le_bot_iff.mp hineq_bot
  have hseq :
      g x₀ ≤ Filter.liminf (g ∘ u) atTop := by
    calc
      g x₀ ≤ Filter.liminf g (nhds x₀) := hlsc.le_liminf x₀
      _ ≤ Filter.liminf g (Filter.map u atTop) := Filter.liminf_le_liminf_of_le hu_tendsto
      _ = Filter.liminf (g ∘ u) atTop := by
        rw [Filter.liminf_comp]
  have hconst : (g ∘ u) = fun _ : ℕ ↦ (⊥ : EReal) := by
    funext n
    exact hu_bot n
  rw [hconst, Filter.liminf_const] at hseq
  exact hx₀_fin.2 (le_bot_iff.mp hseq)

/-- Helper for Proposition 13 44: once a lower semicontinuous function with convex epigraph is
finite somewhere, convexity of the epigraph upgrades to Jensen convexity. -/
private theorem isConvex_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDom g) :
    IsConvex g := by
  intro x y a ha₀ ha₁
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    rw [hcoef_eq]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha₀ (Ne.symm ha_zero)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha₁ ha_one
  by_cases hx : x ∈ dom g
  · by_cases hy : y ∈ dom g
    · -- On two domain points, Proposition 8.4 provides the strict-convex-combination inequality.
      rw [hcoef_eq]
      exact (convex_epigraph_iff_jensen_on_dom g).1 hconv hx hy ha_pos ha_lt_one
    · have hy_top : g y = ⊤ := value_eq_top_of_not_mem_dom (f := g) hy
      have hx_term_ne_bot : (a : EReal) * g x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), ?_, Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha₀)⟩
        exact Or.inr
          (ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
            hconv hlsc hx₀ hx)
      have hrhs_top :
          (a : EReal) * g x + (1 - (a : EReal)) * g y = ⊤ := by
        rw [hcoef_eq, hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
        exact EReal.add_top_of_ne_bot hx_term_ne_bot
      rw [hrhs_top]
      exact le_top
  · have hx_top : g x = ⊤ := value_eq_top_of_not_mem_dom (f := g) hx
    have hy_term_ne_bot : (((1 - a : ℝ) : EReal) * g y) ≠ ⊥ := by
      by_cases hy : y ∈ dom g
      · rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - a)), ?_, Or.inl (EReal.coe_ne_top (1 - a)),
          Or.inl (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha₁))⟩
        exact Or.inr
          (ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
            hconv hlsc hx₀ hy)
      · have hy_top : g y = ⊤ := value_eq_top_of_not_mem_dom (f := g) hy
        rw [hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
        simp
    have hrhs_top :
        (a : EReal) * g x + (1 - (a : EReal)) * g y = ⊤ := by
      rw [hx_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
      exact EReal.top_add_of_ne_bot hy_term_ne_bot
    simp [hrhs_top]

/-- Helper for Proposition 13 44: a lower semicontinuous function with convex epigraph and one
finite point is proper. -/
private theorem isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDom g) :
    IsProper g := by
  have hx₀_fin := (mem_effectiveDom_iff (f := g) (x := x₀)).mp hx₀
  refine ⟨?_, ⟨x₀, (mem_dom_iff_ne_top g x₀).2 hx₀_fin.1⟩⟩
  intro y
  by_cases hy : y ∈ dom g
  · -- Domain points cannot be `⊥` once one finite point exists.
    exact
      ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
        hconv hlsc hx₀ hy
  · -- Outside the domain the value is `⊤`, hence certainly not `⊥`.
    simp [value_eq_top_of_not_mem_dom (f := g) hy]

end BasicConjugationHelpers

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 13 44: at a finite lower-semicontinuity point of a convex function, the
lower semicontinuous convex envelope coincides globally with the Fenchel biconjugate. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    lowerSemicontinuousConvexEnvelope f = f∗∗ := by
  let g : H → EReal := lowerSemicontinuousConvexEnvelope f
  have hg_lsc : LowerSemicontinuous g := by
    -- Proposition 9.8 already packages the envelope as lower semicontinuous.
    simpa [g] using lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f
  have hg_conv_epi : Convex ℝ (epigraph g) := by
    -- Proposition 9.8 also packages convexity of the envelope epigraph.
    simpa [g] using convex_epigraph_lowerSemicontinuousConvexEnvelope f
  have henv_eq_hull :
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
      f (convex_epigraph_of_isConvex hconv)
  have hg_eq_fx : g x = f x := by
    -- The source route rewrites lower semicontinuity at `x` as equality with the lsc hull.
    calc
      g x = lowerSemicontinuousConvexEnvelope f x := rfl
      _ = lowerSemicontinuousEnvelope f x := by
        simpa using congrArg (fun h : H → EReal ↦ h x) henv_eq_hull
      _ = f x := (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).mp hlsc
  have hxg : x ∈ effectiveDom g := by
    -- Equality at the finite point transports effective-domain membership to the envelope.
    rw [mem_effectiveDom_iff] at hx ⊢
    simpa [hg_eq_fx] using hx
  have hg_proper : IsProper g :=
    isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom hg_conv_epi hg_lsc hxg
  have hg_gamma : g ∈ Γ(H) := by
    rw [mem_gamma_iff]
    exact
      ⟨isConvex_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
          hg_conv_epi hg_lsc hxg,
        hg_lsc⟩
  have hconj : g∗ = f∗ := by
    -- Proposition 13.16(iv) says the convex envelope preserves the Fenchel conjugate.
    simpa [g] using conjugate_lowerSemicontinuousConvexEnvelope_eq (f := f)
  have hbiconj : g∗∗ = f∗∗ := congrArg conjugate hconj
  calc
    lowerSemicontinuousConvexEnvelope f = g := rfl
    _ = g∗∗ := by
      exact ((mem_gamma_iff_eq_biconjugate_of_is_proper hg_proper).mp hg_gamma).symm
    _ = f∗∗ := hbiconj

-- Proof sketch: Lemma 1.32 rewrites lower semicontinuity at `x` as
-- `lowerSemicontinuousEnvelope f x = f x`, while Corollary 9.10 identifies
-- `lowerSemicontinuousConvexEnvelope f` with `lowerSemicontinuousEnvelope f` for convex `f`.
/-- Helper: for a convex extended-real-valued function, lower semicontinuity at `x` is
equivalent to the lower semicontinuous convex envelope agreeing with `f` at `x`. -/
private theorem lscAt_iff_lowerSemicontinuousConvexEnvelope_eq_self_of_convex
    {f : H → EReal} (hconv : IsConvex f) {x : H} :
    LowerSemicontinuousAt f x ↔ lowerSemicontinuousConvexEnvelope f x = f x := by
  have henv_eq_hull :
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
      f (convex_epigraph_of_isConvex hconv)
  constructor
  · intro hlsc
    -- Lemma 1.32 identifies the lsc hull with `f` at every lsc point.
    calc
      lowerSemicontinuousConvexEnvelope f x = lowerSemicontinuousEnvelope f x := by
        simpa using congrArg (fun h : H → EReal ↦ h x) henv_eq_hull
      _ = f x := (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).mp hlsc
  · intro hEq
    -- Conversely, the envelope-hull identification reduces the claim to Lemma 1.32.
    refine (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).2 ?_
    calc
      lowerSemicontinuousEnvelope f x = lowerSemicontinuousConvexEnvelope f x := by
        simpa using congrArg (fun h : H → EReal ↦ h x) henv_eq_hull.symm
      _ = f x := hEq

-- Proof sketch: Lemma 1.32 rewrites lower semicontinuity at `x` as
-- `lowerSemicontinuousEnvelope f x = f x`, Corollary 9.10 identifies
-- `lowerSemicontinuousConvexEnvelope f` with `lowerSemicontinuousEnvelope f` for convex `f`,
-- and membership of `x` in `effectiveDom f` gives the needed finite-point hypothesis.
/-- Proposition 13.44 (1): clause `(ii)` says that for a convex extended-real-valued function
on a real Hilbert space, at a point `x` of the effective domain lower semicontinuity is
equivalent to the textbook chain
`f∗∗ x = lowerSemicontinuousConvexEnvelope f x = lowerSemicontinuousEnvelope f x = f x`. -/
theorem lscAt_iff_biconjugate_chain_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f) :
    LowerSemicontinuousAt f x ↔
      f∗∗ x = lowerSemicontinuousConvexEnvelope f x ∧
        lowerSemicontinuousConvexEnvelope f x = lowerSemicontinuousEnvelope f x ∧
        lowerSemicontinuousEnvelope f x = f x := by
  have henv_eq_hull :
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
      f (convex_epigraph_of_isConvex hconv)
  constructor
  · intro hlsc
    have henv_eq_biconj :
        lowerSemicontinuousConvexEnvelope f = f∗∗ :=
      lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
        hconv hx hlsc
    have hhull_eq_self :
        lowerSemicontinuousEnvelope f x = f x :=
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).mp hlsc
    -- The source proof's global equalities specialize at `x` to the textbook chain.
    refine ⟨?_, ?_, hhull_eq_self⟩
    · simpa using congrArg (fun h : H → EReal ↦ h x) henv_eq_biconj.symm
    · simpa using congrArg (fun h : H → EReal ↦ h x) henv_eq_hull
  · rintro ⟨_, henv_eq_hull_x, hhull_eq_self⟩
    -- Only the hull endpoint matters for recovering lower semicontinuity at `x`.
    exact
      (lscAt_iff_lowerSemicontinuousConvexEnvelope_eq_self_of_convex hconv).2
        (henv_eq_hull_x.trans hhull_eq_self)

-- Proof sketch: clause `(ii)` already contains the full pointwise chain, so clause `(iii)` is its
-- endpoint equality.
/-- Proposition 13.44 (2): clause `(iii)` says that for a convex extended-real-valued function
on a real Hilbert space, at a point `x` of the effective domain the function is lower
semicontinuous if and only if its Fenchel biconjugate agrees with `f` at `x`. -/
theorem lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f) :
    LowerSemicontinuousAt f x ↔ f∗∗ x = f x := by
  constructor
  · intro hlsc
    rcases
      (lscAt_iff_biconjugate_chain_of_convex_at_finite_point hconv hx).mp hlsc with
      ⟨hbiconj_env, henv_hull, hhull_self⟩
    -- Collapse the textbook chain to its endpoint equality.
    exact hbiconj_env.trans (henv_hull.trans hhull_self)
  · intro hEq
    have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma (f := f∗)
    have hbiconj_lsc : LowerSemicontinuous (f∗∗) :=
      (mem_gamma_iff (f∗∗)).mp hbiconj_gamma |>.2
    have hbiconj_le_hull :
        f∗∗ ≤ lowerSemicontinuousEnvelope f :=
      (lowerSemicontinuousHull_isGreatest f).2 ⟨hbiconj_lsc, biconjugate_le f⟩
    -- Since `f**` is an lsc minorant below `f`, equality `f** x = f x` forces hull equality.
    refine (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).2 ?_
    apply le_antisymm
    · exact (lowerSemicontinuousHull_isGreatest f).1.2 x
    · calc
        f x = f∗∗ x := hEq.symm
        _ ≤ lowerSemicontinuousEnvelope f x := hbiconj_le_hull x

-- Proof sketch: clause `(iii)` provides a finite point of `f∗∗`, Proposition 13.13 places
-- `f∗∗` in `Γ(H)`, and Proposition 9.6 rules out the `⊥` branch globally for any member of
-- `Γ(H)` that is finite somewhere.
/-- Companion bridge: under the hypotheses of Proposition 13.44, the Fenchel biconjugate is a
proper extended-real-valued function. -/
theorem biconjugate_isProper_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    IsProper (f∗∗) := by
  have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma (f := f∗)
  have hbiconj_data := (mem_gamma_iff (f∗∗)).mp hbiconj_gamma
  have hx_biconj : x ∈ effectiveDom (f∗∗) := by
    have hEq := (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconv hx).mp hlsc
    rw [mem_effectiveDom_iff] at hx ⊢
    constructor
    · rw [hEq]
      exact hx.1
    · rw [hEq]
      exact hx.2
  -- The biconjugate lies in `Γ(H)` and is finite at `x`, so the finite-point bridge gives
  -- properness.
  exact
    isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
      (convex_epigraph_of_isConvex hbiconj_data.1) hbiconj_data.2 hx_biconj

-- Proof sketch: apply the generic implication `Γ(H) → Γ₀(H)` for proper functions to the
-- canonical Chapter 9 owner `properIoi` of the proper function `f∗∗`.
/-- Companion bridge: the canonical `Γ₀(H)`-valued representative of the Fenchel biconjugate
belongs to `Γ₀(H)` under the hypotheses of Proposition 13.44. -/
theorem biconjugate_mem_gammaZero_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    properIoi (f∗∗)
      (biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc) ∈ Γ₀(H) := by
  have hbiconj_proper :
      IsProper (f∗∗) :=
    biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc
  have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma (f := f∗)
  -- Package the raw `Γ(H)` biconjugate into the Chapter 9 `Γ₀(H)` owner.
  exact properIoi_mem_gammaZero_of_mem_gamma hbiconj_proper hbiconj_gamma

-- Chapter 9 defines `Γ₀(H)` for `]-∞,+∞]`-valued owners, so the main labeled statement stays on
-- the raw `EReal` side as `IsProper (f∗∗) ∧ f∗∗ ∈ Γ(H)`, with the packaging kept in the companion
-- theorem `biconjugate_mem_gammaZero_of_lscAt_of_convex_at_finite_point`.
/-- Proposition 13.44 (3): moreover, if a convex extended-real-valued function is lower
semicontinuous at a point `x` of the effective domain, then globally
`f ≥ lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f = f∗∗`, and the
Fenchel biconjugate is proper and belongs to `Γ(H)`. -/
theorem convexEnvelope_hull_biconjugate_chain_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    f∗∗ ≤ f ∧
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f ∧
      lowerSemicontinuousEnvelope f = f∗∗ ∧
      IsProper (f∗∗) ∧
      f∗∗ ∈ Γ(H) := by
  have henv_eq_hull :
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
      f (convex_epigraph_of_isConvex hconv)
  have henv_eq_biconj :
      lowerSemicontinuousConvexEnvelope f = f∗∗ :=
    lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
      hconv hx hlsc
  have hbiconj_proper :
      IsProper (f∗∗) :=
    biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc
  have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma (f := f∗)
  -- Combine the global inequalities and equalities supplied by the source proof.
  refine ⟨biconjugate_le f, henv_eq_hull, henv_eq_hull.symm.trans henv_eq_biconj,
    hbiconj_proper, hbiconj_gamma⟩

end Conjugation

end ERealFunction
