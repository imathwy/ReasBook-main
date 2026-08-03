import Mathlib
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap03.Corollary_3_38
import BauschkeLean.Chap10.Definition_10_27
import BauschkeLean.Chap11.Proposition_11_21
import BauschkeLean.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: reindexing a minimizing sequence by a strictly monotone map
preserves the minimizing-sequence property. -/
theorem IsMinimizingSequence.comp_strictMono
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsMinimizingSequence f (fun n ↦ xₙ (φ n)) := by
  -- The subsequence stays in the domain termwise, and its values keep the same limit.
  constructor
  · intro n
    exact hxₙ.mem_dom (φ n)
  · simpa [Function.comp] using hxₙ.tendsto.comp hφ.tendsto_atTop

end

section

omit [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: if a minimizing sequence eventually falls into one bounded lower
level set, then its whole range is bounded. -/
theorem IsMinimizingSequence.isBounded_range_of_bounded_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ)) :
    Bornology.IsBounded (Set.range xₙ) := by
  -- The convergence of `f (xₙ n)` to the infimum places a tail inside the chosen lower level set.
  have htail : ∀ᶠ n in atTop, xₙ n ∈ lowerLevelSet f ξ := by
    have hle : ∀ᶠ n in atTop, f (xₙ n) ≤ (ξ : EReal) :=
      hxₙ.tendsto.eventually (Iic_mem_nhds hξ)
    simpa [lowerLevelSet, Function.comp] using hle
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s₀ : Set H := xₙ '' {n : ℕ | n < N}
  have hs₀_finite : s₀.Finite := by
    classical
    simpa [s₀] using (Set.finite_lt_nat N).image xₙ
  have hrange_subset : Set.range xₙ ⊆ s₀ ∪ lowerLevelSet f ξ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr (hN n (Nat.le_of_not_lt hn))
  exact (hs₀_finite.isBounded.union hlevel_bounded).subset hrange_subset

end

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: every real lower level set strictly above the infimum is
nonempty. -/
theorem lowerLevelSet_nonempty_of_sInf_lt
    {f : H → EReal} {ξ : ℝ} (hξ : sInf (Set.range f) < (ξ : EReal)) :
    (lowerLevelSet f ξ).Nonempty := by
  -- Otherwise `ξ` would be a lower bound for the whole range, contradicting maximality of `sInf`.
  by_contra hnonempty
  rw [Set.not_nonempty_iff_eq_empty] at hnonempty
  have hbound : ∀ z ∈ Set.range f, (ξ : EReal) ≤ z := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hxnot : x ∉ lowerLevelSet f ξ := by
      simp [hnonempty]
    exact (by
      have hxlt : (ξ : EReal) < f x := by
        simpa [mem_lowerLevelSet_iff, not_le] using hxnot
      exact hxlt.le)
  exact (not_le_of_gt hξ) ((isGLB_sInf (Set.range f)).2 hbound)

end

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: if the indicator augmentation has no `⊥ + ⊤` ambiguity outside
`C`, then its lower level sets are exactly the feasible lower level sets. -/
theorem lowerLevelSet_add_indicator_eq_inter
    {f : H → EReal} {C : Set H} (hbot : ∀ x ∉ C, f x ≠ ⊥) {η : ℝ} :
    lowerLevelSet (f + (ι[C]).asEReal) η = C ∩ lowerLevelSet f η := by
  ext x
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using hx
    · have hxle : (f + (ι[C]).asEReal) x ≤ (η : EReal) :=
        (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).1 hx
      have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have : ¬ ((⊤ : EReal) ≤ (η : EReal)) := by
        simp
      rw [htop] at hxle
      exact False.elim <| this hxle
  · rintro ⟨hxC, hxlevel⟩
    refine (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).2 ?_
    simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using
      (mem_lowerLevelSet_iff f η x).1 hxlevel

end

section

omit [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: adding the indicator of a closed set preserves lower
semicontinuity once `⊥ + ⊤` is excluded outside the set. -/
theorem lowerSemicontinuous_add_indicator_of_isClosed
    {f : H → EReal} {C : Set H} (hf_lsc : LowerSemicontinuous f) (hC_closed : IsClosed C)
    (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    LowerSemicontinuous (f + (ι[C]).asEReal) := by
  -- Lower semicontinuity is equivalent to closed lower level sets, and the indicator objective
  -- turns those level sets into intersections with `C`.
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro η
  rw [lowerLevelSet_add_indicator_eq_inter hbot]
  exact hC_closed.inter ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc η)

end

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: on a lower level set strictly above the infimum, adding the
indicator does not change the infimum of the objective. -/
theorem sInf_range_add_indicator_lowerLevelSet_eq
    {f : H → EReal} {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥) :
    sInf (Set.range (f + (ι[lowerLevelSet f ξ]).asEReal)) = sInf (Set.range f) := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hfg : ∀ x, f x ≤ g x := by
    intro x
    by_cases hxC : x ∈ C
    · simp [g, C, indicator_apply, hxC]
    · have htop : g x = ⊤ := by
        simp [g, C, indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      rw [htop]
      exact le_top
  apply le_antisymm
  · -- If `sInf (range g)` were strictly larger, a value of `f` below that gap would lie in `C`
    -- and still be a value of `g`, contradicting minimality of `sInf (range g)`.
    by_contra hsInf_gt
    have hsInf_lt : sInf (Set.range f) < sInf (Set.range g) := lt_of_not_ge hsInf_gt
    have hmin_lt : sInf (Set.range f) < min (sInf (Set.range g)) (ξ : EReal) :=
      lt_min hsInf_lt hξ
    rcases EReal.lt_iff_exists_real_btwn.mp hmin_lt with ⟨η, hη_left, hη_right⟩
    have hη_lt_sInf_g : (η : EReal) < sInf (Set.range g) :=
      lt_of_lt_of_le hη_right (min_le_left _ _)
    have hη_lt_ξ : (η : EReal) < (ξ : EReal) :=
      lt_of_lt_of_le hη_right (min_le_right _ _)
    rcases lowerLevelSet_nonempty_of_sInf_lt hη_left with ⟨x, hxη⟩
    have hxC : x ∈ C := by
      exact
        (mem_lowerLevelSet_iff f ξ x).2 <|
          le_trans ((mem_lowerLevelSet_iff f η x).1 hxη) hη_lt_ξ.le
    have hxg : g x ≤ (η : EReal) := by
      simpa [g, C, add_indicator_apply, indicator_apply, hxC] using
        (mem_lowerLevelSet_iff f η x).1 hxη
    have hsInf_le : sInf (Set.range g) ≤ g x :=
      (isGLB_sInf (Set.range g)).1 (Set.mem_range_self x)
    exact (not_le_of_gt hη_lt_sInf_g) (le_trans hsInf_le hxg)
  · -- Every value of `g` dominates the infimum of `f`, so `sInf (range f)` is a lower bound for
    -- the range of `g`.
    exact (isGLB_sInf (Set.range g)).2 <| by
      intro z hz
      rcases hz with ⟨x, rfl⟩
      exact le_trans ((isGLB_sInf (Set.range f)).1 (Set.mem_range_self x)) (hfg x)

end

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: a global minimizer of the indicator objective over the lower
level set is already a global minimizer of the original objective. -/
theorem mem_argmin_of_mem_argmin_indicator_lowerLevelSet
    {f : H → EReal} {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥) {x : H}
    (hx : x ∈ Argmin (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  have hC_nonempty : C.Nonempty := lowerLevelSet_nonempty_of_sInf_lt hξ
  obtain ⟨y, hyC⟩ := hC_nonempty
  have hxmin : IsMinOn (f + (ι[C]).asEReal) Set.univ x := (mem_argmin_iff).1 hx
  have hxle : (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) y :=
    (isMinOn_univ_iff.mp hxmin) y
  have hxC : x ∈ C := by
    by_cases hxC : x ∈ C
    · exact hxC
    · have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [C, indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have hytop : (f + (ι[C]).asEReal) y < ⊤ := by
        simpa [C, add_indicator_apply, indicator_apply, hyC] using
          lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ y).1 hyC) (EReal.coe_lt_top ξ)
      have : ¬ ((⊤ : EReal) ≤ (f + (ι[C]).asEReal) y) := not_le_of_gt hytop
      exact False.elim <| this <| by simpa [htop] using hxle
  have hx_on : x ∈ Argmin[C] f := by
    rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
    exact ⟨hxC, hx⟩
  rcases (mem_argminOn_iff.mp hx_on) with ⟨hxC, hxminC⟩
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro z
  by_cases hzC : z ∈ C
  · exact (isMinOn_iff.mp hxminC) z hzC
  · have hx_level : f x ≤ (ξ : EReal) := (mem_lowerLevelSet_iff f ξ x).1 hxC
    have hz_gt : (ξ : EReal) < f z := by
      simpa [C, mem_lowerLevelSet_iff, not_le] using hzC
    exact le_trans hx_level hz_gt.le

end

/-- Helper for Proposition 11 29: a uniformly quasiconvex objective is automatically strictly
quasiconvex. -/
theorem UniformlyQuasiconvex.strictlyQuasiconvex
    {f : H → EReal} {φ : NNReal → EReal} (hf : UniformlyQuasiconvex f φ) :
    StrictlyQuasiconvex f := by
  -- The uniform gap term is positive at distinct points, so the weak max inequality becomes strict.
  refine ⟨hf.isProper, ?_⟩
  intro x y hx hy hxy α hα0 hα1
  let m : H := α • x + (1 - α) • y
  have hαterm_pos : (0 : EReal) < (((α * (1 - α) : ℝ) : EReal)) := by
    exact_mod_cast show 0 < α * (1 - α) by nlinarith
  have hdist_pos : (0 : NNReal) < ‖x - y‖₊ := by
    exact_mod_cast norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    rw [← (hf.modulus_eq_zero_iff 0).2 rfl]
    exact hf.monotone bot_le
  have hφ_ne_zero : φ ‖x - y‖₊ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hdist_pos) ((hf.modulus_eq_zero_iff ‖x - y‖₊).1 hzero)
  have hφ_pos : (0 : EReal) < φ ‖x - y‖₊ :=
    lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
  have hterm_pos :
      (0 : EReal) < (((α * (1 - α) : ℝ) : EReal)) * φ ‖x - y‖₊ :=
    EReal.mul_pos hαterm_pos hφ_pos
  have hineq := hf.ineq hx hy hα0 hα1
  have hmax_top : max (f x) (f y) < ⊤ := by
    exact max_lt_iff.mpr ⟨(mem_dom_iff f x).1 hx, (mem_dom_iff f y).1 hy⟩
  have hm_ne_top : f m ≠ ⊤ := by
    intro hm_top
    have hsum_top :
        f m + ((((α * (1 - α) : ℝ) : EReal)) * φ ‖x - y‖₊) = ⊤ := by
      simpa [m, hm_top] using
        EReal.top_add_of_ne_bot (by
          intro hterm_bot
          have hbot_pos : (0 : EReal) < ⊥ := by
            simp [hterm_bot] at hterm_pos
          exact (not_lt_of_ge (bot_le : (⊥ : EReal) ≤ 0)) hbot_pos)
    have : ¬ (f m + ((((α * (1 - α) : ℝ) : EReal)) * φ ‖x - y‖₊) < ⊤) := by
      simpa [hsum_top]
    exact this (lt_of_le_of_lt hineq hmax_top)
  have hm_ne_bot : f m ≠ ⊥ := hf.isProper.1 m
  have hlt :
      f m < f m + (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) := by
    simpa [m, add_comm] using
      EReal.add_lt_add_of_lt_of_le hterm_pos le_rfl hm_ne_bot hm_ne_top
  exact lt_of_lt_of_le hlt hineq

/-- Helper for Proposition 11 29: a strictly quasiconvex indicator-augmented objective has at
most one constrained minimizer. -/
theorem argminOn_subsingleton_of_indicator_objective_strictlyQuasiconvex
    {f : H → EReal} {C : Set H}
    (hstrict : StrictlyQuasiconvex (f + (ι[C]).asEReal)) :
    (Argmin[C] f).Subsingleton := by
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    have hg : (f + (ι[C]).asEReal) x ≠ ⊥ := hstrict.isProper.1 x
    exact hg <| by simp [hxC, hfx]
  rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxmin : ∀ z, (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hx.2)
  have hymin : ∀ z, (f + (ι[C]).asEReal) y ≤ (f + (ι[C]).asEReal) z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hy.2)
  rcases hstrict.isProper.2 with ⟨z, hz_dom⟩
  have hx_dom : x ∈ dom (f + (ι[C]).asEReal) := by
    rw [mem_dom_iff_ne_top]
    intro hxtop
    have : (⊤ : EReal) ≤ (f + (ι[C]).asEReal) z := by
      simpa [hxtop] using hxmin z
    exact (not_lt_of_ge this) ((mem_dom_iff (f + (ι[C]).asEReal) z).mp hz_dom)
  have hy_dom : y ∈ dom (f + (ι[C]).asEReal) := by
    rw [mem_dom_iff_ne_top]
    intro hytop
    have : (⊤ : EReal) ≤ (f + (ι[C]).asEReal) z := by
      simpa [hytop] using hymin z
    exact (not_lt_of_ge this) ((mem_dom_iff (f + (ι[C]).asEReal) z).mp hz_dom)
  let z : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hstrict_z :
      (f + (ι[C]).asEReal) z <
        max ((f + (ι[C]).asEReal) x) ((f + (ι[C]).asEReal) y) :=
    hstrict.ineq hx_dom hy_dom hxy (by norm_num) (by norm_num)
  have hx_z : (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) z := hxmin z
  have hy_z : (f + (ι[C]).asEReal) y ≤ (f + (ι[C]).asEReal) z := hymin z
  have hmax_z :
      max ((f + (ι[C]).asEReal) x) ((f + (ι[C]).asEReal) y) ≤
        (f + (ι[C]).asEReal) z :=
    max_le hx_z hy_z
  exact (not_lt_of_ge hmax_z hstrict_z).elim

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: `hxₙ.tendsto` makes the minimizing sequence eventually enter every lower level set
-- strictly above `sInf (Set.range f)`. Once the tail lies in the bounded set `lowerLevelSet f ξ`,
-- put that set inside a closed ball and apply
-- `exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex` to obtain a weakly
-- convergent subsequence, hence a weak sequential cluster point.
/-- Proposition 11 29 (1): clause (i). If some lower level set strictly above the infimum of `f`
is bounded, then every minimizing sequence of `f` has a weak sequential cluster point. -/
theorem IsMinimizingSequence.exists_weakSequentialClusterPoint_of_bounded_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ)) :
    ∃ x : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
  -- First bound the full range of the minimizing sequence from the bounded lower-level tail.
  have hrange_bounded :
      Bornology.IsBounded (Set.range xₙ) :=
    hxₙ.isBounded_range_of_bounded_lowerLevelSet hξ hlevel_bounded
  obtain ⟨r, hrange_subset⟩ := hrange_bounded.subset_closedBall (0 : H)
  obtain ⟨x, -, φ, hφ, hφx⟩ :=
    exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex
      Metric.isBounded_closedBall Metric.isClosed_closedBall (convex_closedBall (0 : H) r) xₙ
      (fun n ↦ hrange_subset (Set.mem_range_self n))
  exact ⟨x, ⟨φ, hφ, by simpa [Function.comp] using hφx⟩⟩

end CompleteSpace

-- Proof sketch: `hx.exists_subseq_tendsto` supplies a weakly convergent subsequence. A
-- subsequence of a minimizing sequence is still minimizing, so
-- `mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ` from Proposition
-- 11.21 applies to that subsequence.
/-- Proposition 11 29 (2): clause (i). Every weak sequential cluster point of a minimizing
sequence of a lower semicontinuous quasiconvex function is a global minimizer. -/
theorem IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x))
    (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    (hxₙ : IsMinimizingSequence f xₙ) :
    x ∈ Argmin f := by
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  -- Apply Proposition 11.21 to the weakly convergent minimizing subsequence.
  exact
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
      hf_quasi hf_lsc (hxₙ.comp_strictMono hφ) <| by
        simpa [Function.comp] using hφx

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: choose an arbitrary minimizing sequence of `f`. Part (1) supplies a weak
-- sequential cluster point. Apply Proposition 11.21 to the indicator-augmented objective
-- `f + (ι[lowerLevelSet f ξ]).asEReal`, whose strict quasiconvexity already gives the needed
-- quasiconvexity, and then use that this objective agrees with `f` on `lowerLevelSet f ξ`.
-- Uniqueness comes from `argminOn_subsingleton_of_indicator_strictlyQuasiconvex`.
/-- Proposition 11 29 (3): clause (ii). If `f + ι_C` is strictly quasiconvex for
`C = lowerLevelSet f ξ`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃! x : H, x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    exact (hstrict.isProper.1 x) <| by simp [C, hxC, hfx]
  have hC_closed : IsClosed C := by
    simpa [C] using (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hlevel_nonempty : (lowerLevelSet g ξ).Nonempty := by
    rcases lowerLevelSet_nonempty_of_sInf_lt hξ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [lowerLevelSet_add_indicator_eq_inter hbot]
    exact ⟨hx, hx⟩
  have hlevel_bounded_g : Bornology.IsBounded (lowerLevelSet g ξ) := by
    rw [lowerLevelSet_add_indicator_eq_inter hbot]
    simpa [C, Set.inter_self] using hlevel_bounded
  have hg_lsc : LowerSemicontinuous g :=
    lowerSemicontinuous_add_indicator_of_isClosed hf_lsc hC_closed hbot
  have hg_arg_nonempty : (Argmin g).Nonempty := by
    simpa [g] using
      argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
        (f := g) (C := Set.univ) hstrict.quasiconvexOn hg_lsc isClosed_univ convex_univ ξ
        (by simpa using hlevel_nonempty) (by simpa using hlevel_bounded_g)
  rcases hg_arg_nonempty with ⟨x, hxg⟩
  have hx_argmin : x ∈ Argmin f :=
    mem_argmin_of_mem_argmin_indicator_lowerLevelSet hξ hbot hxg
  refine ⟨x, hx_argmin, ?_⟩
  intro y hy
  have hyC : y ∈ C := by
    exact
      (mem_lowerLevelSet_iff f ξ y).2 <| by
        calc
          f y = sInf (Set.range f) := (mem_argmin_iff_eq_sInf).1 hy
          _ ≤ (ξ : EReal) := hξ.le
  have hy_on : y ∈ Argmin[C] f := by
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨hyC, ?_⟩
    intro z hz
    exact (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hy)) z
  have hx_on : x ∈ Argmin[C] f := by
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨?_, ?_⟩
    · exact
        (mem_lowerLevelSet_iff f ξ x).2 <|
          le_trans ((mem_argmin_iff_eq_sInf).1 hx_argmin).le hξ.le
    · intro z hz
      exact (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx_argmin)) z
  exact
    (argminOn_subsingleton_of_indicator_objective_strictlyQuasiconvex
      (f := f) (C := C) hstrict)
    hy_on hx_on

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 11 29: a subsequence that stays inside the lower level set is a
minimizing sequence for the indicator-augmented objective. -/
theorem IsMinimizingSequence.comp_add_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hφC : ∀ n, xₙ (φ n) ∈ lowerLevelSet f ξ) :
    IsMinimizingSequence (f + (ι[lowerLevelSet f ξ]).asEReal) (fun n ↦ xₙ (φ n)) := by
  let g : H → EReal := f + (ι[lowerLevelSet f ξ]).asEReal
  have hsub : IsMinimizingSequence f (fun n ↦ xₙ (φ n)) :=
    hxₙ.comp_strictMono hφ
  constructor
  · intro n
    -- On the feasible lower level set, the indicator objective agrees with `f`.
    rw [mem_dom_iff]
    simpa [g, indicator_apply, hφC n] using hsub.lt_top n
  · -- The reindexed values of the indicator objective share the same limit infimum as `f`.
    have hEq :
        (fun n ↦ g (xₙ (φ n))) = fun n ↦ f (xₙ (φ n)) := by
      funext n
      simp [g, indicator_apply, hφC n]
    rw [show (g ∘ fun n ↦ xₙ (φ n)) = fun n ↦ g (xₙ (φ n)) by rfl, hEq]
    simpa [g, Function.comp, sInf_range_add_indicator_lowerLevelSet_eq hξ hbot] using hsub.tendsto

end

section

omit [CompleteSpace H]

/-- Helper for Proposition 11 29: every weak sequential cluster point of a minimizing sequence is
already a global minimizer once the indicator-augmented objective is strictly quasiconvex on the
relevant lower level set. -/
theorem
    IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x))
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hxₙ : IsMinimizingSequence f xₙ)
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hbot : ∀ y ∉ C, f y ≠ ⊥ := by
    intro y hyC hfy
    exact (hstrict.isProper.1 y) <| by simp [C, hyC, hfy]
  have hC_closed : IsClosed C := by
    simpa [C] using (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hg_lsc : LowerSemicontinuous g :=
    lowerSemicontinuous_add_indicator_of_isClosed hf_lsc hC_closed hbot
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have htailC : ∀ᶠ n in atTop, xₙ n ∈ C := by
    -- Minimizing values eventually lie below every real level strictly above the infimum.
    have hle : ∀ᶠ n in atTop, f (xₙ n) ≤ (ξ : EReal) :=
      hxₙ.tendsto.eventually (Iic_mem_nhds hξ)
    simpa [C, lowerLevelSet, Function.comp] using hle
  have hsubtailC : ∀ᶠ n in atTop, xₙ (φ n) ∈ C :=
    hφ.tendsto_atTop.eventually htailC
  rcases eventually_atTop.mp hsubtailC with ⟨N, hN⟩
  let ψ : ℕ → ℕ := fun n ↦ φ (n + N)
  have hadd : StrictMono (fun n : ℕ ↦ n + N) := by
    intro m n hmn
    exact Nat.add_lt_add_right hmn N
  have hψ : StrictMono ψ := hφ.comp hadd
  have hψx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ (ψ n))) atTop (𝓝 (toWeakSpace ℝ H x)) := by
    -- Shifting along the convergent subsequence preserves the same weak limit.
    simpa [ψ, Function.comp] using hφx.comp (tendsto_add_atTop_nat N)
  have hψC : ∀ n, xₙ (ψ n) ∈ C := by
    intro n
    simpa [ψ] using hN (n + N) (Nat.le_add_left N n)
  have hψ_min : IsMinimizingSequence g (fun n ↦ xₙ (ψ n)) :=
    hxₙ.comp_add_indicator_lowerLevelSet hξ hbot hψ hψC
  have hxg : x ∈ Argmin g :=
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
      hstrict.quasiconvexOn hg_lsc hψ_min hψx
  -- The indicator objective agrees with `f` at minimizers inside the lower level set.
  exact mem_argmin_of_mem_argmin_indicator_lowerLevelSet hξ hbot hxg

end

-- Proof sketch: part (1) yields boundedness of the weak-image sequence through a weakly
-- convergent subsequence, and Proposition 11.21 applied to
-- `f + (ι[lowerLevelSet f ξ]).asEReal` shows that
-- every weak sequential cluster point is a minimizer. Part (3) makes that minimizer unique, so
-- `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` upgrades the bounded
-- sequence to weak convergence of the whole minimizing sequence.
namespace IsMinimizingSequence

/-- Proposition 11 29 (4): clause (ii). Under the same strict quasiconvexity hypothesis, the
minimizing sequence converges weakly to a global minimizer of `f`. -/
theorem exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃ x ∈ Argmin f,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  -- Route correction: the convergence upgrade is the only remaining structural step, so the
  -- earlier existence and indicator-bridge work is kept explicit and stable.
  have hbounded :
      Bornology.IsBounded (Set.range xₙ) :=
    hxₙ.isBounded_range_of_bounded_lowerLevelSet hξ hlevel_bounded
  obtain ⟨x₀, hx₀_argmin, hx₀_unique⟩ :=
    existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf_lsc hξ hlevel_bounded hstrict
  have hunique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) →
        y = z := by
    intro y z hy hz
    have hy_arg : y ∈ Argmin f := by
      exact
        IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
          hy hf_lsc hξ hxₙ hstrict
    have hz_arg : z ∈ Argmin f := by
      exact
        IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
          hz hf_lsc hξ hxₙ hstrict
    calc
      y = x₀ := hx₀_unique y hy_arg
      _ = z := (hx₀_unique z hz_arg).symm
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
      ⟨hbounded, hunique⟩ with ⟨x, hx_tendsto⟩
  have hx_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
    -- The convergent full sequence is its own witnessing subsequence.
    refine ⟨fun n ↦ n, fun _ _ h ↦ h, ?_⟩
    simpa [Function.comp] using hx_tendsto
  have hx_arg : x ∈ Argmin f := by
    exact
      IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
        hx_cluster hf_lsc hξ hxₙ hstrict
  exact ⟨x, hx_arg, hx_tendsto⟩

end IsMinimizingSequence

-- Proof sketch: choose an arbitrary minimizing sequence of `f`. Uniform quasiconvexity of
-- `f + (ι[lowerLevelSet f ξ]).asEReal` already provides the relevant quasiconvexity and the same
-- uniqueness mechanism as in clause (ii), while part (1) and Proposition 11.21 again provide
-- existence of a minimizer through weak sequential cluster points.
/-- Proposition 11 29 (5): clause (iii). If `f + ι_C` is uniformly quasiconvex for
`C = lowerLevelSet f ξ`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_uniformlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal) φ) :
    ∃! x : H, x ∈ Argmin f := by
  -- Uniform quasiconvexity already yields the strict quasiconvexity needed by clause (ii).
  exact
    existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf_lsc hξ hlevel_bounded huniform.strictlyQuasiconvex

section

omit [CompleteSpace H]

/-- Helper for Proposition 11 29: uniform quasiconvexity on the indicator-augmented objective
forces a fixed positive objective gap once a point in the lower level set stays a definite distance
away from a global minimizer. -/
theorem argmin_value_add_uniform_gap_le_of_mem_lowerLevelSet
    {f : H → EReal} {ξ : ℝ} {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal) φ)
    (hξ : sInf (Set.range f) < (ξ : EReal))
    {x y : H} (hx : x ∈ Argmin f) (hy : y ∈ lowerLevelSet f ξ)
    {ε : NNReal} (hε : ε ≤ ‖y - x‖₊) :
    f x + (((1 / 4 : ℝ) : EReal) * φ ε) ≤ f y := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hbot : ∀ z ∉ C, f z ≠ ⊥ := by
    intro z hz hfz
    exact (huniform.isProper.1 z) <| by simp [C, hz, hfz]
  have hxC : x ∈ C := by
    exact
      (mem_lowerLevelSet_iff f ξ x).2 <| by
        calc
          f x = sInf (Set.range f) := (mem_argmin_iff_eq_sInf).1 hx
          _ ≤ (ξ : EReal) := hξ.le
  have hx_dom : x ∈ dom g := by
    -- The minimizer value lies below the chosen finite real level `ξ`.
    rw [mem_dom_iff]
    have hxtop : f x < ⊤ := by
      calc
        f x = sInf (Set.range f) := (mem_argmin_iff_eq_sInf).1 hx
        _ < (ξ : EReal) := hξ
        _ < ⊤ := EReal.coe_lt_top ξ
    simpa [g, C, indicator_apply, hxC] using hxtop
  have hy_dom : y ∈ dom g := by
    -- Any feasible point in the lower level set also has finite indicator-augmented value.
    rw [mem_dom_iff]
    have hytop : f y < ⊤ := by
      exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ y).1 hy) (EReal.coe_lt_top ξ)
    simpa [g, C, indicator_apply, hy] using hytop
  have hnorm_rev : ‖x - y‖₊ = ‖y - x‖₊ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (nnnorm_neg (x - y)).symm
  have hε' : ε ≤ ‖x - y‖₊ := by
    simpa [hnorm_rev] using hε
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hmid_ge : f x ≤ g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) := by
    -- The midpoint value of `g` dominates the global minimum value of `f`.
    by_cases hmidC : m ∈ C
    · have hmid_f :
          f x ≤ f m :=
        (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx)) _
      have hmid_eq :
          g m = f m := by
        simpa [g] using
          add_indicator_eqOn f C hmidC
      calc
        f x ≤ f m := hmid_f
        _ = g m := hmid_eq.symm
    · have htop : g m = ⊤ := by
        have hindicator :
            Cᶜ.indicator (fun _ : H ↦ (⊤ : EReal)) m = ⊤ := by
          simp [hmidC]
        calc
          g m = f m + Cᶜ.indicator (fun _ : H ↦ (⊤ : EReal)) m := by
            simp [g, indicator_apply]
          _ = f m + ⊤ := by rw [hindicator]
          _ = ⊤ := EReal.add_top_of_ne_bot (hbot _ hmidC)
      rw [show g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) = g m by simp [m], htop]
      exact le_top
  have hmax :
      max (g x) (g y) = f y := by
    -- Since `x` is a global minimizer of `f`, the maximum of the two feasible endpoint values is
    -- the value at `y`.
    have hxy : f x ≤ f y := (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx)) y
    rw [show g x = f x by simp [g, C, indicator_apply, hxC]]
    rw [show g y = f y by simp [g, C, indicator_apply, hy]]
    exact max_eq_right hxy
  have hmidpoint_gap :
      f x + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤ f y := by
    have hineq :=
      huniform.ineq hx_dom hy_dom (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hquarter :
        ((((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊) =
          (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) := by
      norm_num
    have hineq' :
        g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) +
            (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤
          f y := by
      -- Specializing the uniform inequality at the midpoint fixes the coefficient to `1 / 4`.
      calc
        g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) +
            (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) =
          g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) +
            ((((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊) := by
          rw [hquarter]
        _ ≤
          max (g x) (g y) := hineq
        _ = f y := hmax
    calc
      f x + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤
          g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) +
            (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hmid_ge ((((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊))
      _ ≤ f y := hineq'
  have hcoef_nonneg : (0 : EReal) ≤ (((1 / 4 : ℝ) : EReal)) := by
    norm_num
  have hmon :
      (((1 / 4 : ℝ) : EReal) * φ ε) ≤
        (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) :=
    mul_le_mul_of_nonneg_left (huniform.monotone hε') hcoef_nonneg
  -- Replace the distance term by the smaller prescribed radius `ε`.
  exact
    le_trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hmon (f x))
      hmidpoint_gap

end

-- Proof sketch: after clause (iii) gives uniqueness of the minimizer, the uniform quasiconvexity
-- inequality for `f + ι_{lev≤ξ f}` controls `φ ‖xₙ - x‖₊` by `f (xₙ) - f x`; since the right-hand
-- side tends to `0` along the minimizing sequence, the modulus forces `‖xₙ - x‖ → 0`.
namespace IsMinimizingSequence

/-- Proposition 11 29 (6): clause (iii). Under the same uniform quasiconvexity hypothesis, the
minimizing sequence converges strongly to a global minimizer of `f`. -/
theorem exists_mem_argmin_and_tendsto_of_uniformlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal) φ) :
    ∃ x ∈ Argmin f, Tendsto xₙ atTop (𝓝 x) := by
  rcases
      hxₙ.exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
        hf_lsc hξ hlevel_bounded huniform.strictlyQuasiconvex with
    ⟨x, hx_arg, _⟩
  refine ⟨x, hx_arg, ?_⟩
  by_contra hstrong
  rw [Metric.tendsto_atTop] at hstrong
  push Not at hstrong
  rcases hstrong with ⟨ε, hε, hbad⟩
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (xₙ n) x := by
    rw [frequently_atTop]
    intro N
    rcases hbad N with ⟨n, hnN, hndist⟩
    exact ⟨n, hnN, hndist⟩
  rcases extraction_of_frequently_atTop hfreq with ⟨φbad, hφbad_mono, hφbad_dist⟩
  have htailC : ∀ᶠ n in atTop, xₙ n ∈ lowerLevelSet f ξ := by
    -- The minimizing sequence eventually enters the chosen lower level set.
    have hle : ∀ᶠ n in atTop, f (xₙ n) ≤ (ξ : EReal) :=
      hxₙ.tendsto.eventually (Iic_mem_nhds hξ)
    simpa [lowerLevelSet, Function.comp] using hle
  have hsubtailC : ∀ᶠ n in atTop, xₙ (φbad n) ∈ lowerLevelSet f ξ :=
    hφbad_mono.tendsto_atTop.eventually htailC
  rcases eventually_atTop.mp hsubtailC with ⟨N, hN⟩
  let ψ : ℕ → ℕ := fun n ↦ φbad (n + N)
  have hadd : StrictMono (fun n : ℕ ↦ n + N) := by
    intro m n hmn
    exact Nat.add_lt_add_right hmn N
  have hψ_mono : StrictMono ψ := hφbad_mono.comp hadd
  have hψ_level : ∀ n, xₙ (ψ n) ∈ lowerLevelSet f ξ := by
    intro n
    simpa [ψ] using hN (n + N) (Nat.le_add_left N n)
  have hψ_dist : ∀ n, ε ≤ dist (xₙ (ψ n)) x := by
    intro n
    simpa [ψ] using hφbad_dist (n + N)
  let εNN : NNReal := ⟨ε, hε.le⟩
  let cε : EReal := (((1 / 4 : ℝ) : EReal) * φ εNN)
  have hφ_nonneg : (0 : EReal) ≤ φ εNN := by
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hφ_ne_zero : φ εNN ≠ 0 := by
    intro hzero
    have : εNN = 0 := (huniform.modulus_eq_zero_iff εNN).1 hzero
    exact (ne_of_gt hε) <| by
      simpa [εNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) this
  have hφ_pos : (0 : EReal) < φ εNN :=
    lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
  have hcε_pos : (0 : EReal) < cε := by
    -- The modulus is strictly positive away from the origin, and the midpoint coefficient is
    -- positive.
    exact EReal.mul_pos (by exact_mod_cast (show (0 : ℝ) < 1 / 4 by norm_num)) hφ_pos
  have hpointwise :
      ∀ n, f x + cε ≤ f (xₙ (ψ n)) := by
    intro n
    have hεNN :
        εNN ≤ ‖xₙ (ψ n) - x‖₊ := by
      exact_mod_cast (by simpa [dist_eq_norm] using hψ_dist n)
    -- The fixed distance lower bound turns uniform quasiconvexity into a fixed objective gap.
    simpa [cε] using
      argmin_value_add_uniform_gap_le_of_mem_lowerLevelSet
        huniform hξ hx_arg (hψ_level n) hεNN
  have hψ_min : IsMinimizingSequence f (fun n ↦ xₙ (ψ n)) :=
    hxₙ.comp_strictMono hψ_mono
  have hψ_tendsto :
      Tendsto (fun n ↦ f (xₙ (ψ n))) atTop (𝓝 (f x)) := by
    -- Every subsequence of a minimizing sequence still converges to the global infimum.
    simpa [Function.comp, (mem_argmin_iff_eq_sInf).1 hx_arg] using hψ_min.tendsto
  have hconst : Tendsto (fun _ : ℕ ↦ f x + cε) atTop (𝓝 (f x + cε)) :=
    tendsto_const_nhds
  have hle_fx : f x + cε ≤ f x :=
    le_of_tendsto_of_tendsto' hconst hψ_tendsto hpointwise
  have hlt_fx : f x < f x + cε := by
    have hxC : x ∈ lowerLevelSet f ξ := by
      exact
        (mem_lowerLevelSet_iff f ξ x).2 <| by
          calc
            f x = sInf (Set.range f) := (mem_argmin_iff_eq_sInf).1 hx_arg
            _ ≤ (ξ : EReal) := hξ.le
    have hfx_ne_top : f x ≠ ⊤ := by
      exact
        ((lt_of_eq_of_lt (mem_argmin_iff_eq_sInf.1 hx_arg) hξ).trans (EReal.coe_lt_top ξ)).ne
    have hfx_ne_bot : f x ≠ ⊥ := by
      intro hfx_bot
      have hg_ne_bot :
          (f + (ι[lowerLevelSet f ξ]).asEReal) x ≠ ⊥ :=
        huniform.isProper.1 x
      have : (f + (ι[lowerLevelSet f ξ]).asEReal) x = ⊥ := by
        simp [indicator_apply, hxC, hfx_bot]
      exact hg_ne_bot this
    simpa [add_comm] using
      EReal.add_lt_add_of_lt_of_le hcε_pos le_rfl hfx_ne_bot hfx_ne_top
  exact (not_le_of_gt hlt_fx) hle_fx

end IsMinimizingSequence

end CompleteSpace

end ERealFunction
