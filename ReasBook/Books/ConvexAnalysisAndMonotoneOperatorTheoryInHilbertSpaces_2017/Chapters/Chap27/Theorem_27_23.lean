import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap09.Theorem_9_1
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap11.Corollary_11_16
import BauschkeLean.Chap11.Corollary_11_30
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_12
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap14.Proposition_14_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u

namespace ERealFunction

section Regularization

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem add_posReal_smul_mem_gammaZero_of_argmin_inter_effectiveDomain_nonempty
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty) (ε : PosReal) :
    f + ε • g ∈ Γ₀(H) := by
  rcases hfeas with ⟨x, hxarg, hxg⟩
  have hxf : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hxarg
  have hxεg : x ∈ effectiveDomain (ε • g) := by
    have hxg_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxg)
    rw [mem_effectiveDomain_iff, posReal_smul_apply, lt_top_iff_ne_top, EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot (ε : ℝ)), Or.inl (EReal.coe_nonneg.mpr ε.2.le),
      Or.inl (EReal.coe_ne_top (ε : ℝ)), Or.inr hxg_top⟩
  exact pointwiseAdd_mem_gammaZero f (ε • g) hf (smul_mem_gammaZero g hg ε) ⟨x, hxf, hxεg⟩

omit [CompleteSpace H] in
/-- Helper for Theorem 27.23: the indicator of a nonempty closed convex set belongs to `Γ₀(H)`.
-/
private theorem indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Theorem 27.23: positive scaling preserves the effective domain. -/
private theorem mem_effectiveDomain_posReal_smul_iff
    {g : H → Set.Ioi (⊥ : EReal)} (ε : PosReal) (x : H) :
    x ∈ effectiveDomain (ε • g) ↔ x ∈ effectiveDomain g := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, posReal_smul_apply, lt_top_iff_ne_top,
    lt_top_iff_ne_top]
  constructor
  · intro hx htop
    exact hx (by simpa [htop] using EReal.coe_mul_top_of_pos ε.2)
  · intro hx
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot (ε : ℝ)), Or.inl (EReal.coe_nonneg.mpr ε.2.le),
      Or.inl (EReal.coe_ne_top (ε : ℝ)), Or.inr hx⟩

/-- Helper for Theorem 27.23: the finite weighted sum of two effective-domain values is the cast
of the corresponding real weighted sum of their `toReal` values. -/
private theorem weighted_value_sum_eq_coe_two_points_local
    (g : H → Set.Ioi (⊥ : EReal))
    {x y : H} (hx : x ∈ effectiveDomain g) (hy : y ∈ effectiveDomain g) (α : ℝ) :
    (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) =
      ((α * (g x : EReal).toReal + (1 - α) * (g y : EReal).toReal : ℝ) : EReal) := by
  -- Effective-domain membership lets us rewrite both endpoint values as finite real casts.
  have hx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
  have hy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (g y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
  rw [← EReal.coe_toReal hx_top hx_bot,
    show (1 - α : EReal) = ((1 - α : ℝ) : EReal) by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
    ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simp

/-- Helper for Theorem 27.23: on the effective domain, positive scaling commutes with `toReal`.
-/
private theorem toReal_posReal_smul
    {g : H → Set.Ioi (⊥ : EReal)} (ε : PosReal) {x : H} (hx : x ∈ effectiveDomain g) :
    (((ε • g) x : EReal).toReal) = (ε : ℝ) * (g x : EReal).toReal := by
  -- Finite values stay finite after positive scaling, so `toReal` sees ordinary real
  -- multiplication.
  have hx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
  simp [EReal.toReal_mul, EReal.toReal_coe]

/-- Helper for Theorem 27.23: the indicator of `Argmin f` belongs to `Γ₀(H)` once a feasible
minimizer is available. -/
private theorem argmin_indicator_mem_gammaZero_of_feasible
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty) :
    ι[Argmin f.asEReal] ∈ Γ₀(H) := by
  rcases hfeas with ⟨x, hxarg, _⟩
  have harg_nonempty : (Argmin f.asEReal).Nonempty := ⟨x, hxarg⟩
  have harg_convex : Convex ℝ (Argmin f.asEReal) := by
    have hf_quasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
      rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ]
      intro ξ
      exact convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ
    simpa [argmin_eq_setOf_le_sInf_range] using hf_quasi (sInf (Set.range f.asEReal))
  have harg_closed : IsClosed (Argmin f.asEReal) := by
    have hxmin : IsMinOn f.asEReal Set.univ x := (mem_argmin_iff).mp hxarg
    have hxdom : x ∈ effectiveDomain f := by
      simpa [effectiveDomain, dom] using
        mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hxarg
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxdom)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
    have hx_real : (((f.asEReal x).toReal : ℝ) : EReal) = f.asEReal x :=
      EReal.coe_toReal hx_top hx_bot
    have hargmin_eq_level :
        Argmin f.asEReal = lowerLevelSet f.asEReal (f.asEReal x).toReal := by
      ext y
      constructor
      · intro hy
        rw [mem_lowerLevelSet_iff]
        have hy_le : f.asEReal y ≤ f.asEReal x := by
          exact (isMinOn_univ_iff.mp (mem_argmin_iff.mp hy)) x
        simpa [hx_real] using hy_le
      · intro hy
        rw [mem_argmin_iff, isMinOn_univ_iff]
        intro z
        have hy_le_x : f.asEReal y ≤ f.asEReal x := by
          simpa [mem_lowerLevelSet_iff, hx_real] using hy
        exact le_trans hy_le_x ((isMinOn_univ_iff.mp hxmin) z)
    rw [hargmin_eq_level]
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1 _
  exact
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local harg_nonempty harg_closed
      harg_convex

/-- Helper for Theorem 27.23: positive scaling preserves coercivity of the underlying
`EReal`-valued function. -/
private theorem coercive_posReal_smul_asEReal
    {g : H → Set.Ioi (⊥ : EReal)} (ε : PosReal) (hg_coe : Coercive g.asEReal) :
    Coercive (ε • g).asEReal := by
  -- Compare the scaled lower level set with the lower level set of `g` at the divided height.
  refine (coercive_iff_bounded_lowerLevelSet (ε • g).asEReal).2 ?_
  intro ξ
  have hg_bounded :
      Bornology.IsBounded (lowerLevelSet g.asEReal (ξ / (ε : ℝ))) :=
    (coercive_iff_bounded_lowerLevelSet g.asEReal).1 hg_coe (ξ / (ε : ℝ))
  refine hg_bounded.subset ?_
  intro x hx
  rw [mem_lowerLevelSet_iff] at hx ⊢
  have hxε_dom : x ∈ effectiveDomain (ε • g) := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hx (EReal.coe_lt_top ξ)
  have hxg : x ∈ effectiveDomain g :=
    (mem_effectiveDomain_posReal_smul_iff ε x).1 hxε_dom
  have hxg_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxg)
  have hxg_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
  have hscaled_bot : ((ε : EReal) * (g x : EReal)) ≠ ⊥ := by
    exact (EReal.mul_ne_bot _ _).2
      ⟨Or.inl (EReal.coe_ne_bot (ε : ℝ)), Or.inr hxg_bot,
        Or.inl (EReal.coe_ne_top (ε : ℝ)), Or.inl (EReal.coe_nonneg.mpr ε.2.le)⟩
  have hscaled_real : (ε : ℝ) * (g x : EReal).toReal ≤ ξ := by
    -- Move the finite extended-real inequality back to a real inequality before dividing by `ε`.
    have htoReal :=
      EReal.toReal_le_toReal hx hscaled_bot (EReal.coe_ne_top ξ)
    simpa [posReal_smul_apply, EReal.toReal_mul, EReal.toReal_coe, hxg_top, hxg_bot] using htoReal
  have hreal : (g x : EReal).toReal ≤ ξ / (ε : ℝ) := by
    exact (le_div_iff₀ ε.2).2 (by simpa [mul_comm] using hscaled_real)
  have hcoer : (g x : EReal) ≤ (((ξ / (ε : ℝ) : ℝ) : EReal)) := by
    rw [← EReal.coe_toReal hxg_top hxg_bot]
    exact_mod_cast hreal
  simpa [Function.asEReal] using hcoer

/-- Helper for Theorem 27.23: positive scaling preserves strict convexity. -/
private theorem strictlyConvex_posReal_smul
    {g : H → Set.Ioi (⊥ : EReal)} (ε : PosReal) (hg_strict : StrictlyConvex g) :
    StrictlyConvex (ε • g) := by
  intro x hx y hy hxy α hα0 hα1
  have hxg : x ∈ effectiveDomain g := (mem_effectiveDomain_posReal_smul_iff ε x).1 hx
  have hyg : y ∈ effectiveDomain g := (mem_effectiveDomain_posReal_smul_iff ε y).1 hy
  let z : H := α • x + (1 - α) • y
  have hstrict :
      (g z : EReal) <
        (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) :=
    hg_strict.ineq hxg hyg hxy hα0 hα1
  have hsum_eq :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) =
        ((α * (g x : EReal).toReal + (1 - α) * (g y : EReal).toReal : ℝ) : EReal) :=
    weighted_value_sum_eq_coe_two_points_local g hxg hyg α
  have hsum_lt_top :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) < ⊤ := by
    rw [hsum_eq]
    exact EReal.coe_lt_top _
  have hzg_top : (g z : EReal) ≠ ⊤ := ne_of_lt (lt_trans hstrict hsum_lt_top)
  have hzg_bot : (g z : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g z : EReal) from (g z).2)
  have hzg : z ∈ effectiveDomain g := by
    rw [mem_effectiveDomain_iff]
    exact lt_top_iff_ne_top.mpr hzg_top
  have hreal :
      (g z : EReal).toReal <
        α * (g x : EReal).toReal + (1 - α) * (g y : EReal).toReal := by
    -- Rewrite the strict Jensen inequality for `g` as an ordinary real inequality.
    rw [hsum_eq, ← EReal.coe_toReal hzg_top hzg_bot] at hstrict
    exact_mod_cast hstrict
  have hscaled_real :
      (ε : ℝ) * (g z : EReal).toReal <
        α * ((ε : ℝ) * (g x : EReal).toReal) +
          (1 - α) * ((ε : ℝ) * (g y : EReal).toReal) := by
    -- Positive real scaling preserves the strict real inequality.
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hreal ε.2
  have hzε : z ∈ effectiveDomain (ε • g) :=
    (mem_effectiveDomain_posReal_smul_iff ε z).2 hzg
  have hzε_top : (((ε • g) z : EReal)) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzε)
  have hzε_bot : (((ε • g) z : EReal)) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < ((ε • g) z : EReal) from ((ε • g) z).2)
  have hsum_scaled_eq :
      (α : EReal) * (((ε • g) x : EReal)) + (1 - α : EReal) * (((ε • g) y : EReal)) =
        ((α * (((ε • g) x : EReal).toReal) + (1 - α) * (((ε • g) y : EReal).toReal : ℝ) :
            EReal)) :=
    weighted_value_sum_eq_coe_two_points_local (ε • g) hx hy α
  have hscaled_real' :
      (((ε • g) z : EReal).toReal) <
        α * (((ε • g) x : EReal).toReal) +
          (1 - α) * (((ε • g) y : EReal).toReal) := by
    -- Rewrite the scaled values via `toReal_posReal_smul`, then reuse the strict real inequality.
    rw [toReal_posReal_smul ε hzg, toReal_posReal_smul ε hxg, toReal_posReal_smul ε hyg]
    exact hscaled_real
  have hscaled_ereal :
      (((ε • g) z : EReal)) <
        (α : EReal) * (((ε • g) x : EReal)) + (1 - α : EReal) * (((ε • g) y : EReal)) := by
    -- Return to `EReal` after the scalar multiplication has been handled in `ℝ`.
    rw [hsum_scaled_eq, ← EReal.coe_toReal hzε_top hzε_bot]
    exact_mod_cast hscaled_real'
  simpa [z] using hscaled_ereal

omit [CompleteSpace H] in
/-- Helper for Theorem 27.23: members of `Γ₀(H)` are weakly sequentially lower
semicontinuous. -/
private theorem weak_seq_tendsto_le_liminf_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {x : H} {u : ℕ → H}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (nhds (toWeakSpace ℝ H x))) :
    φ.asEReal x ≤ liminf (φ.asEReal ∘ u) atTop := by
  -- Read the weak-sequential clause directly from Theorem 9.1 using the convex epigraph of `φ`.
  have htfae :
      List.TFAE
        [ (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (nhds (toWeakSpace ℝ H x)) →
                φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop),
          (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
              Tendsto xₙ atTop (nhds x) →
                φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop),
          LowerSemicontinuous φ.asEReal,
          WeaklyLowerSemicontinuous φ.asEReal ] := by
    exact convex_lowerSemicontinuity_tfae
      (convex_epigraph_asEReal_of_mem_gammaZero hφ)
  have hweak_seq :
      (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
          Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (nhds (toWeakSpace ℝ H x)) →
            φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop) := by
    exact (List.TFAE.out htfae 0 2).2 hφ.1
  exact hweak_seq hu


-- The provided source text duplicates the convergence clause in (i) and (iii); the proof text
-- identifies (i) as weak convergence and (iii) as strong convergence. The split statements below
-- follow that source-consistent reading.

/-- Theorem 27.23 (1): if `f, g ∈ Γ₀(H)`, if `Argmin f ∩ dom g` is nonempty, and if `g` is
coercive and strictly convex, then `g` has a unique minimizer over `Argmin f`. -/
theorem existsUnique_mem_argminOn_argmin_of_inter_nonempty_of_coercive_of_strictlyConvex
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    (hg_coe : Coercive g.asEReal) (hg_strict : StrictlyConvex g) :
    ∃! x0 : H, x0 ∈ Argmin[Argmin f.asEReal] g.asEReal := by
  let S := Argmin f.asEReal
  have hindicator : ι[S] ∈ Γ₀(H) :=
    argmin_indicator_mem_gammaZero_of_feasible hf hfeas
  have hsum : g + ι[S] ∈ Γ₀(H) := by
    rcases hfeas with ⟨x, hxarg, hxg⟩
    -- Encode the constrained problem over `Argmin f` as a global indicator-augmented objective.
    exact pointwiseAdd_mem_gammaZero g (ι[S]) hg hindicator
      ⟨x, hxg, by simpa [S, effectiveDomain_indicator] using hxarg⟩
  have hindicator_bddBelow : BddBelow (Set.range (ι[S])) := by
    refine ⟨(⟨0, by simp⟩ : Set.Ioi (⊥ : EReal)), ?_⟩
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ S <;> simp [ERealFunction.indicator, hx]
  have hdom : (effectiveDomain g ∩ effectiveDomain (ι[S])).Nonempty := by
    rcases hfeas with ⟨x, hxarg, hxg⟩
    exact ⟨x, hxg, by simpa [S, effectiveDomain_indicator] using hxarg⟩
  have hsum_nonempty : (Argmin (g + ι[S]).asEReal).Nonempty := by
    -- Existence comes from coercivity of `g` and bounded-below geometry of the indicator.
    exact
      pointwiseAdd_argmin_nonempty_of_supercoercive_or_coercive_bddBelow
        (f := g) (g := ι[S]) hindicator hg (Or.inr ⟨hg_coe, hindicator_bddBelow⟩)
  have hsum_subsingleton : (Argmin (g + ι[S]).asEReal).Subsingleton := by
    -- Uniqueness comes from strict convexity of `g` on the same augmented objective.
    exact
      pointwiseAdd_argmin_subsingleton_of_inter_nonempty_of_strictlyConvex
        (f := g) (g := ι[S]) hindicator hg hdom (Or.inl hg_strict)
  rcases hsum_nonempty with ⟨x0, hx0⟩
  have hx0_dom : x0 ∈ effectiveDomain (g + ι[S]) := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hsum) hx0
  have hx0S : x0 ∈ S := by
    exact
      (by
        simpa [S, effectiveDomain_indicator] using
          ((mem_effectiveDomain_pointwiseAdd_iff g (ι[S]) x0).1 hx0_dom).2)
  have hbot : ∀ y ∉ S, g.asEReal y ≠ ⊥ := by
    intro y hyS
    exact ne_of_gt (show (⊥ : EReal) < g.asEReal y from (g y).2)
  have hx0_on : x0 ∈ Argmin[S] g.asEReal := by
    -- Once the indicator minimizer is known feasible, the textbook constrained argmin follows.
    rw [argminOn_eq_inter_argmin_add_indicator g.asEReal S hbot]
    exact ⟨hx0S, by simpa [S] using hx0⟩
  refine ⟨x0, hx0_on, ?_⟩
  intro y hy
  have hy_global : y ∈ Argmin (g + ι[S]).asEReal := by
    rw [argminOn_eq_inter_argmin_add_indicator g.asEReal S hbot] at hy
    exact hy.2
  exact hsum_subsingleton hy_global hx0

/-- Theorem 27.23 (2): for every `ε ∈ ]0,1[`, the regularized problem
`minimize f + ε g` has a unique minimizer. -/
theorem existsUnique_mem_argmin_add_posReal_smul_of_inter_nonempty_of_coercive_of_strictlyConvex
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    (hg_coe : Coercive g.asEReal) (hg_strict : StrictlyConvex g)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃! xε : H, xε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal := by
  let epsPos : PosReal := ⟨ε, hε.1⟩
  have hf_bddBelow : BddBelow (Set.range f) := by
    rcases hfeas with ⟨x, hxarg, _⟩
    refine ⟨f x, ?_⟩
    rintro y ⟨z, rfl⟩
    -- A global minimizer of `f` gives the lower bound needed for Corollary 11.16.
    simpa using (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hxarg)) z
  have hsum_nonempty : (Argmin (f + epsPos • g).asEReal).Nonempty := by
    -- Commute the sum so Corollary 11.16 sees the coercive regularizer first.
    simpa [add_comm] using
      pointwiseAdd_argmin_nonempty_of_supercoercive_or_coercive_bddBelow
        (f := epsPos • g) (g := f) hf (smul_mem_gammaZero g hg epsPos)
        (Or.inr ⟨coercive_posReal_smul_asEReal epsPos hg_coe, hf_bddBelow⟩)
  have hsum_subsingleton : (Argmin (f + epsPos • g).asEReal).Subsingleton := by
    -- Strict convexity of `ε g` is the source of uniqueness for the regularized problem.
    exact
      pointwiseAdd_argmin_subsingleton_of_inter_nonempty_of_strictlyConvex
        (f := f) (g := epsPos • g) (smul_mem_gammaZero g hg epsPos) hf
        (by
          rcases hfeas with ⟨x, hxarg, hxg⟩
          have hxεg : x ∈ effectiveDomain (epsPos • g) :=
            (mem_effectiveDomain_posReal_smul_iff epsPos x).2 hxg
          have hxf : x ∈ effectiveDomain f := by
            simpa [effectiveDomain, dom] using
              mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hxarg
          exact ⟨x, hxf, hxεg⟩)
        (Or.inr (strictlyConvex_posReal_smul epsPos hg_strict))
  rcases hsum_nonempty with ⟨xε, hxε⟩
  exact ⟨xε, hxε, fun y hy ↦ hsum_subsingleton hy hxε⟩

/-- Helper for Theorem 27.23: comparing the regularized minimizer against the constrained
minimizer `x₀` yields the fixed source bound `g(y) ≤ g(x₀)`. -/
private theorem regularized_g_le_argminOn_value
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    {x0 y : H} {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    (hy : y ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal) :
    g.asEReal y ≤ g.asEReal x0 := by
  let epsPos : PosReal := ⟨ε, hε.1⟩
  have hx0_argf : x0 ∈ Argmin f.asEReal := (mem_argminOn_iff.mp hx0).1
  have hx0_dom_f : x0 ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hx0_argf
  have hx0_dom_g : x0 ∈ effectiveDomain g := by
    rcases hfeas with ⟨z, hz_argf, hz_dom_g⟩
    have hx0_min_g : IsMinOn g.asEReal (Argmin f.asEReal) x0 :=
      (mem_argminOn_iff.mp hx0).2
    -- Compare `x₀` with one feasible finite point of `Argmin f`.
    rw [mem_effectiveDomain_iff]
    exact
      lt_of_le_of_lt ((isMinOn_iff.mp hx0_min_g) z hz_argf)
        (mem_effectiveDomain_iff.mp hz_dom_g)
  have hy_dom_sum : y ∈ effectiveDomain (f + epsPos • g) := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper
        (isProper_of_mem_gammaZero
          (add_posReal_smul_mem_gammaZero_of_argmin_inter_effectiveDomain_nonempty
            hf hg hfeas epsPos))
        hy
  have hy_dom_f : y ∈ effectiveDomain f :=
    ((mem_effectiveDomain_pointwiseAdd_iff f (epsPos • g) y).1 hy_dom_sum).1
  have hy_dom_epsg : y ∈ effectiveDomain (epsPos • g) :=
    ((mem_effectiveDomain_pointwiseAdd_iff f (epsPos • g) y).1 hy_dom_sum).2
  have hy_dom_g : y ∈ effectiveDomain g :=
    (mem_effectiveDomain_posReal_smul_iff epsPos y).1 hy_dom_epsg
  have hy_min : IsMinOn (f + epsPos • g).asEReal Set.univ y := (mem_argmin_iff.mp hy)
  have hsum_compare_x0 :
      (f y : EReal) + ((epsPos • g) y : EReal) ≤
        (f x0 : EReal) + ((epsPos • g) x0 : EReal) := by
    -- Regularized optimality gives the first comparison in the source proof.
    simpa [Function.asEReal] using (isMinOn_univ_iff.mp hy_min) x0
  have hx0_le_fy : (f x0 : EReal) ≤ (f y : EReal) := by
    -- Since `x₀ ∈ Argmin f`, its `f`-value is a global lower bound.
    exact (isMinOn_univ_iff.mp ((mem_argmin_iff.mp hx0_argf))) y
  have hsum_compare :
      (f y : EReal) + ((epsPos • g) y : EReal) ≤
        (f y : EReal) + ((epsPos • g) x0 : EReal) := by
    exact le_trans hsum_compare_x0 <| by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hx0_le_fy (((epsPos • g) x0 : EReal))
  have hyf_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_f)
  have hyf_bot : (f y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hx0f_top : (f x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_f)
  have hx0f_bot : (f x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f x0 : EReal) from (f x0).2)
  have hyg_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_g)
  have hyg_bot : (g y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
  have hx0g_top : (g x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_g)
  have hx0g_bot : (g x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (g x0 : EReal) from (g x0).2)
  have hyepsg_top : ((epsPos • g) y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_epsg)
  have hyepsg_bot : ((epsPos • g) y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < ((epsPos • g) y : EReal) from ((epsPos • g) y).2)
  have hx0epsg_dom : x0 ∈ effectiveDomain (epsPos • g) :=
    (mem_effectiveDomain_posReal_smul_iff epsPos x0).2 hx0_dom_g
  have hx0epsg_top : ((epsPos • g) x0 : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hx0epsg_dom)
  have hx0epsg_bot : ((epsPos • g) x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < ((epsPos • g) x0 : EReal) from ((epsPos • g) x0).2)
  have hsum_compare_real :
      (f y : EReal).toReal + ((epsPos • g) y : EReal).toReal ≤
        (f y : EReal).toReal + ((epsPos • g) x0 : EReal).toReal := by
    -- Move the finite regularized-value comparison back to `ℝ`.
    have hsum_compare_coe := hsum_compare
    rw [show (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hyf_top hyf_bot).symm,
      show (((epsPos • g) y : EReal)) = ((((epsPos • g) y : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hyepsg_top hyepsg_bot).symm,
      show (((epsPos • g) x0 : EReal)) = ((((epsPos • g) x0 : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hx0epsg_top hx0epsg_bot).symm,
      ← EReal.coe_add, ← EReal.coe_add] at hsum_compare_coe
    exact EReal.coe_le_coe_iff.mp hsum_compare_coe
  have hscaled_compare_real :
      (ε : ℝ) * (g y : EReal).toReal ≤ (ε : ℝ) * (g x0 : EReal).toReal := by
    -- Cancel the common `f(y)` term after rewriting the scaled values in `ℝ`.
    rw [toReal_posReal_smul epsPos hy_dom_g, toReal_posReal_smul epsPos hx0_dom_g] at hsum_compare_real
    linarith
  have hg_compare_real : (g y : EReal).toReal ≤ (g x0 : EReal).toReal := by
    -- Divide by the positive regularization parameter.
    nlinarith [hε.1, hscaled_compare_real]
  -- Return from `ℝ` to `EReal` now that both endpoint values are known finite.
  change (g y : EReal) ≤ (g x0 : EReal)
  rw [← EReal.coe_toReal hyg_top hyg_bot, ← EReal.coe_toReal hx0g_top hx0g_bot]
  exact_mod_cast hg_compare_real

/-- Helper for Theorem 27.23: local uniform convexity on every nonempty closed-ball slice implies
global strict convexity. -/
private theorem strictlyConvex_of_closedBall_uniformlyConvex_local
    {g : H → Set.Ioi (⊥ : EReal)}
    (hball_uniform :
      ∀ ⦃c : H⦄ ⦃r : ℝ⦄, 0 ≤ r →
        (Metric.closedBall c r ∩ effectiveDomain g).Nonempty →
        ∃ φ : NNReal → EReal,
          UniformlyConvexOn g (Metric.closedBall c r ∩ effectiveDomain g) φ) :
    StrictlyConvex g := by
  intro x hx y hy hxy α hα0 hα1
  let C : Set H := Metric.closedBall x ‖y - x‖ ∩ effectiveDomain g
  have hxC : x ∈ C := by
    refine ⟨?_, hx⟩
    simpa [Metric.mem_closedBall, dist_eq_norm]
  have hyC : y ∈ C := by
    refine ⟨?_, hy⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using le_rfl
  obtain ⟨φ, huniform⟩ := hball_uniform (c := x) (r := ‖y - x‖) (norm_nonneg _) ⟨x, hxC⟩
  let z : H := α • x + (1 - α) • y
  have hweighted_eq :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) =
        ((α * (g x : EReal).toReal + (1 - α) * (g y : EReal).toReal : ℝ) : EReal) :=
    weighted_value_sum_eq_coe_two_points_local g hx hy α
  have hweighted_ne_top :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) ≠ ⊤ := by
    rw [hweighted_eq]
    exact EReal.coe_ne_top _
  have hdist_pos : (0 : NNReal) < ‖x - y‖₊ := by
    exact_mod_cast norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hφ_ne_zero : φ ‖x - y‖₊ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hdist_pos) ((huniform.modulus_eq_zero_iff ‖x - y‖₊).1 hzero)
  have hφ_pos : (0 : EReal) < φ ‖x - y‖₊ :=
    lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
  have hαterm_pos : (0 : EReal) < ((α * (1 - α) : ℝ) : EReal) := by
    exact_mod_cast show 0 < α * (1 - α) by nlinarith
  have hterm_pos :
      (0 : EReal) < ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
    EReal.mul_pos hαterm_pos hφ_pos
  have hterm_ne_bot :
      ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hterm_pos
    simp at hterm_pos
  have hz_ne_top : (g z : EReal) ≠ ⊤ := by
    intro hz_top
    have htop_le :
        (⊤ : EReal) ≤
          (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) := by
      have hineq := huniform.ineq hxC hyC hα0 hα1
      have hleft_top :
          (g z : EReal) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ = ⊤ := by
        rw [hz_top, EReal.top_add_of_ne_bot hterm_ne_bot]
      calc
        (⊤ : EReal) =
            (g z : EReal) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := hleft_top.symm
        _ ≤ (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) := by
              simpa [z] using hineq
    exact hweighted_ne_top (top_unique htop_le)
  have hz_ne_bot : (g z : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g z : EReal) from (g z).2)
  have hz_lt_gap :
      (g z : EReal) <
        (g z : EReal) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := by
    simpa [add_comm, z] using
      EReal.add_lt_add_of_lt_of_le hterm_pos le_rfl hz_ne_bot hz_ne_top
  have hineq := huniform.ineq hxC hyC hα0 hα1
  exact lt_of_lt_of_le hz_lt_gap (by simpa [z] using hineq)

/-- Helper for Theorem 27.23: specializing uniform convexity at the midpoint produces the fixed
quarter-gap inequality used in the source proof. -/
private theorem midpoint_gap_le_of_uniformlyConvexOn
    {g : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (huniform : UniformlyConvexOn g C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    g.asEReal (midpoint ℝ x y) + ((((1 / 4 : ℝ) : EReal)) * φ ‖x - y‖₊) ≤
      (((1 / 2 : ℝ) : EReal) * g.asEReal x + ((1 / 2 : ℝ) : EReal) * g.asEReal y) := by
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  have hhalf_ereal : (1 - (1 / 2 : ℝ) : EReal) = (((1 / 2 : ℝ) : EReal)) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    norm_num
  have hquarter_ereal :
      (((1 / 2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal))) = (((1 / 4 : ℝ) : EReal)) := by
    rw [← EReal.coe_mul]
    norm_num
  -- Route correction: isolate the midpoint coefficient bookkeeping once, instead of rebuilding
  -- the `α = 1 / 2` simplification inside the final contradiction proof.
  have hineq :=
    huniform.ineq (x := x) (y := y) hx hy hhalf_pos hhalf_lt_one
  norm_num at hineq
  rw [hhalf_ereal] at hineq
  simpa [midpoint_eq_smul_add] using hineq

/-- Helper for Theorem 27.23: if a sequence fails to converge strongly to `0`, then some
subsequence stays uniformly away from `0`. -/
private theorem exists_strictMono_subseq_norm_ge_of_not_tendsto_zero
    (u : ℕ → H) (hnot : ¬ Tendsto u atTop (𝓝 (0 : H))) :
    ∃ c > 0, ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ n, c ≤ ‖u (k n)‖ := by
  rcases Filter.not_tendsto_iff_exists_frequently_notMem.1 hnot with ⟨s, hs0, hfreq⟩
  obtain ⟨c, hcpos, hcball⟩ := Metric.mem_nhds_iff.1 hs0
  rcases Filter.extraction_of_frequently_atTop hfreq with ⟨k, hkmono, hkout⟩
  refine ⟨c, hcpos, k, hkmono, ?_⟩
  intro n
  have hnot_ball : u (k n) ∉ Metric.ball (0 : H) c := by
    intro hkball
    exact hkout n (hcball hkball)
  have hdist : c ≤ dist (u (k n)) 0 := by
    by_contra hlt
    exact hnot_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hlt)
  simpa [dist_eq_norm] using hdist

/-- Helper for Theorem 27.23: the source estimate `(27.70)` bounds the `f`-value of a regularized
minimizer by the infimum of `f` plus an `ε`-scaled `g`-gap. -/
private theorem regularized_f_le_sInf_add_eps_mul_gap
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    {x0 xg y : H} {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    (hxg : xg ∈ Argmin g.asEReal)
    (hy : y ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal) :
    f.asEReal y ≤
      sInf (Set.range f.asEReal) +
        (((ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal) : ℝ) : EReal)) := by
  let epsPos : PosReal := ⟨ε, hε.1⟩
  have hx0_argf : x0 ∈ Argmin f.asEReal := (mem_argminOn_iff.mp hx0).1
  have hy_dom_sum : y ∈ effectiveDomain (f + epsPos • g) := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper
        (isProper_of_mem_gammaZero
          (add_posReal_smul_mem_gammaZero_of_argmin_inter_effectiveDomain_nonempty
            hf hg hfeas epsPos))
        hy
  have hy_dom_f : y ∈ effectiveDomain f :=
    ((mem_effectiveDomain_pointwiseAdd_iff f (epsPos • g) y).1 hy_dom_sum).1
  have hx0_dom_f : x0 ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hx0_argf
  have hx0_dom_g : x0 ∈ effectiveDomain g := by
    rcases hfeas with ⟨z, hz_argf, hz_dom_g⟩
    have hx0_min_g : IsMinOn g.asEReal (Argmin f.asEReal) x0 :=
      (mem_argminOn_iff.mp hx0).2
    -- Compare `x₀` with one feasible finite point of `Argmin f`.
    rw [mem_effectiveDomain_iff]
    exact
      lt_of_le_of_lt ((isMinOn_iff.mp hx0_min_g) z hz_argf)
        (mem_effectiveDomain_iff.mp hz_dom_g)
  have hxg_dom_g : xg ∈ effectiveDomain g := by
    simpa [effectiveDomain, dom] using
      mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hg) hxg
  have hy_min : IsMinOn (f + epsPos • g).asEReal Set.univ y := (mem_argmin_iff.mp hy)
  have hxg_min : IsMinOn g.asEReal Set.univ xg := (mem_argmin_iff.mp hxg)
  have hsum_compare_x0 :
      (f y : EReal) + ((epsPos • g) y : EReal) ≤
        (f x0 : EReal) + ((epsPos • g) x0 : EReal) := by
    -- Regularized optimality compares the regularized minimizer `y` with the constrained minimizer
    -- `x₀`.
    simpa [Function.asEReal] using (isMinOn_univ_iff.mp hy_min) x0
  have hscaled_xg_le_y :
      ((epsPos • g) xg : EReal) ≤ ((epsPos • g) y : EReal) := by
    -- The global minimizer `xg` of `g` provides the uniform lower bound from the source proof.
    have hxg_le_y : (g xg : EReal) ≤ (g y : EReal) :=
      (isMinOn_univ_iff.mp hxg_min) y
    simpa [posReal_smul_apply] using
      mul_le_mul_of_nonneg_left hxg_le_y (by exact_mod_cast hε.1.le : (0 : EReal) ≤ (ε : ℝ))
  have hsum_compare :
      (f y : EReal) + ((epsPos • g) xg : EReal) ≤
        (f x0 : EReal) + ((epsPos • g) x0 : EReal) := by
    -- Insert the lower bound `ε g(xg) ≤ ε g(y)` before returning to ordinary real arithmetic.
    exact le_trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hscaled_xg_le_y (f y : EReal))
      hsum_compare_x0
  have hyf_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_f)
  have hyf_bot : (f y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hx0f_top : (f x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_f)
  have hx0f_bot : (f x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f x0 : EReal) from (f x0).2)
  have hxgg_top : (g xg : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxg_dom_g)
  have hxgg_bot : (g xg : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (g xg : EReal) from (g xg).2)
  have hx0g_top : (g x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_g)
  have hx0g_bot : (g x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (g x0 : EReal) from (g x0).2)
  have hxgepsg_dom : xg ∈ effectiveDomain (epsPos • g) :=
    (mem_effectiveDomain_posReal_smul_iff epsPos xg).2 hxg_dom_g
  have hx0epsg_dom : x0 ∈ effectiveDomain (epsPos • g) :=
    (mem_effectiveDomain_posReal_smul_iff epsPos x0).2 hx0_dom_g
  have hxgepsg_top : ((epsPos • g) xg : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hxgepsg_dom)
  have hxgepsg_bot : ((epsPos • g) xg : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < ((epsPos • g) xg : EReal) from ((epsPos • g) xg).2)
  have hx0epsg_top : ((epsPos • g) x0 : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hx0epsg_dom)
  have hx0epsg_bot : ((epsPos • g) x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < ((epsPos • g) x0 : EReal) from ((epsPos • g) x0).2)
  have hsum_compare_real :
      (f y : EReal).toReal + ((epsPos • g) xg : EReal).toReal ≤
        (f x0 : EReal).toReal + ((epsPos • g) x0 : EReal).toReal := by
    -- Every term in the comparison is finite, so the source inequality can be read in `ℝ`.
    have hsum_compare_coe := hsum_compare
    rw [show (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hyf_top hyf_bot).symm,
      show (((epsPos • g) xg : EReal)) = ((((epsPos • g) xg : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hxgepsg_top hxgepsg_bot).symm,
      show (f x0 : EReal) = (((f x0 : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hx0f_top hx0f_bot).symm,
      show (((epsPos • g) x0 : EReal)) = ((((epsPos • g) x0 : EReal).toReal : ℝ) : EReal) by
        exact (EReal.coe_toReal hx0epsg_top hx0epsg_bot).symm,
      ← EReal.coe_add, ← EReal.coe_add] at hsum_compare_coe
    exact EReal.coe_le_coe_iff.mp hsum_compare_coe
  have hreal :
      (f y : EReal).toReal ≤
        (f x0 : EReal).toReal +
          (ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal)) := by
    -- Rewrite the scaled terms as ordinary real products and cancel `ε g(xg)`.
    rw [toReal_posReal_smul epsPos hxg_dom_g, toReal_posReal_smul epsPos hx0_dom_g] at hsum_compare_real
    linarith
  -- Return from `ℝ` to `EReal`, then rewrite `f x0` as `sInf (Set.range f.asEReal)`.
  have hereal :
      (f y : EReal) ≤
        (f x0 : EReal) + (((ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal) : ℝ) : EReal)) := by
    have hcoe :
        ((((f y : EReal).toReal : ℝ) : EReal)) ≤
          ((((f x0 : EReal).toReal +
              (ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal)) : ℝ) : EReal)) := by
      exact_mod_cast hreal
    calc
      (f y : EReal) = ((((f y : EReal).toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal hyf_top hyf_bot]
      _ ≤ ((((f x0 : EReal).toReal +
            (ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal)) : ℝ) : EReal)) := hcoe
      _ = (f x0 : EReal) + (((ε * ((g.asEReal x0).toReal - (g.asEReal xg).toReal) : ℝ) : EReal)) := by
        rw [EReal.coe_add, EReal.coe_toReal hx0f_top hx0f_bot]
  simpa [(mem_argmin_iff_eq_sInf.mp hx0_argf)] using hereal

/-- Helper for Theorem 27.23: a vanishing positive-parameter sequence sends the corresponding
regularized minimizers to a minimizing sequence for `f`. -/
private theorem regularized_sequence_isMinimizingSequence_f
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    {x0 xg : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    (hxg : xg ∈ Argmin g.asEReal)
    {ε : ℕ → ℝ} (hε_mem : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) 1)
    (hε_tendsto : Tendsto ε atTop (𝓝 (0 : ℝ)))
    {y : ℕ → H}
    (hy :
      ∀ n, y n ∈ Argmin (f + (⟨ε n, (hε_mem n).1⟩ : PosReal) • g).asEReal) :
    IsMinimizingSequence f.asEReal y := by
  rw [isMinimizingSequence_iff_lt_top]
  refine ⟨?_, ?_⟩
  · intro n
    let epsPos : PosReal := ⟨ε n, (hε_mem n).1⟩
    have hy_dom_sum : y n ∈ effectiveDomain (f + epsPos • g) := by
      simpa [effectiveDomain, dom] using
        mem_dom_of_mem_argmin_of_isProper
          (isProper_of_mem_gammaZero
            (add_posReal_smul_mem_gammaZero_of_argmin_inter_effectiveDomain_nonempty
              hf hg hfeas epsPos))
          (hy n)
    have hy_dom_f : y n ∈ effectiveDomain f :=
      ((mem_effectiveDomain_pointwiseAdd_iff f (epsPos • g) (y n)).1 hy_dom_sum).1
    simpa using (mem_effectiveDomain_iff.mp hy_dom_f)
  · have hx0_argf : x0 ∈ Argmin f.asEReal := (mem_argminOn_iff.mp hx0).1
    have hx0_dom_f : x0 ∈ effectiveDomain f := by
      simpa [effectiveDomain, dom] using
        mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hx0_argf
    have hx0f_top : (f.asEReal x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_f)
    have hx0f_bot : (f.asEReal x0 : EReal) ≠ ⊥ :=
      ne_of_gt (show (⊥ : EReal) < f.asEReal x0 from (f x0).2)
    let gap : ℝ := (g.asEReal x0).toReal - (g.asEReal xg).toReal
    have hgap_tendsto_real :
        Tendsto (fun n ↦ ε n * gap) atTop (𝓝 (0 : ℝ)) := by
      simpa [gap, mul_comm] using hε_tendsto.const_mul gap
    have hgap_tendsto :
        Tendsto (fun n ↦ (((ε n * gap : ℝ) : EReal))) atTop (𝓝 (0 : EReal)) :=
      EReal.tendsto_coe.2 hgap_tendsto_real
    have hupp :
        Tendsto
          (fun n ↦ sInf (Set.range f.asEReal) + (((ε n * gap : ℝ) : EReal)))
          atTop
          (𝓝 (sInf (Set.range f.asEReal) + 0)) := by
      have hsInf_ne_top : sInf (Set.range f.asEReal) ≠ ⊤ := by
        rw [(mem_argmin_iff_eq_sInf.mp hx0_argf).symm]
        exact hx0f_top
      have hsInf_ne_bot : sInf (Set.range f.asEReal) ≠ ⊥ := by
        rw [(mem_argmin_iff_eq_sInf.mp hx0_argf).symm]
        exact hx0f_bot
      have hadd :
          ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
            (sInf (Set.range f.asEReal), 0) :=
        EReal.continuousAt_add (.inl hsInf_ne_top) (.inl hsInf_ne_bot)
      exact hadd.tendsto.comp
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ sInf (Set.range f.asEReal)) atTop
            (nhds (sInf (Set.range f.asEReal)))).prodMk_nhds hgap_tendsto)
    have hupp' :
        Tendsto
          (fun n ↦ sInf (Set.range f.asEReal) + (((ε n * gap : ℝ) : EReal)))
          atTop
          (𝓝 (sInf (Set.range f.asEReal))) := by
      simpa using hupp
    have hlower : ∀ n, sInf (Set.range f.asEReal) ≤ f.asEReal (y n) := by
      intro n
      exact (isGLB_sInf (Set.range f.asEReal)).1 (Set.mem_range_self (y n))
    have hupper :
        ∀ n,
          f.asEReal (y n) ≤
            sInf (Set.range f.asEReal) + (((ε n * gap : ℝ) : EReal)) := by
      intro n
      simpa [gap] using
        regularized_f_le_sInf_add_eps_mul_gap hf hg hfeas (hε_mem n) hx0 hxg (hy n)
    -- The source estimate squeezes `f (yₙ)` between the infimum and an error term that vanishes.
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupp' (fun n ↦ hlower n) (fun n ↦ hupper n)

/-- Helper for Theorem 27.23: a weak sequential cluster point of the regularized minimizer
sequence lies in the constrained argmin set `Argmin[Argmin f] g`. -/
private theorem weakSequentialClusterPt_mem_argminOn_of_regularized_sequence
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x0 : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    {y : ℕ → H} (hymin : IsMinimizingSequence f.asEReal y)
    (hyg : ∀ n, g.asEReal (y n) ≤ g.asEReal x0)
    {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H x)) :
    x ∈ Argmin[Argmin f.asEReal] g.asEReal := by
  have hx_argf : x ∈ Argmin f.asEReal :=
    mem_argmin_of_weakSequentialClusterPoint_of_mem_gammaZero hf hymin hx
  have hx0_min : IsMinOn g.asEReal (Argmin f.asEReal) x0 :=
    (mem_argminOn_iff.mp hx0).2
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have hg_liminf :
      g.asEReal x ≤ liminf (g.asEReal ∘ fun n ↦ y (φ n)) atTop := by
    -- Weak lower semicontinuity of `g` gives the source liminf inequality on the witnessing
    -- subsequence.
    simpa [Function.comp] using
      weak_seq_tendsto_le_liminf_of_mem_gammaZero (φ := g) hg hφx
  have hliminf_le :
      liminf (g.asEReal ∘ fun n ↦ y (φ n)) atTop ≤ g.asEReal x0 := by
    -- The fixed source bound `g (yₙ) ≤ g x₀` forces the subsequential liminf below `g x₀`.
    refine Filter.liminf_le_of_frequently_le' ?_
    exact Filter.Frequently.of_forall fun n ↦ by
      simpa [Function.comp] using hyg (φ n)
  have hx_le_x0 : g.asEReal x ≤ g.asEReal x0 := le_trans hg_liminf hliminf_le
  refine ⟨hx_argf, ?_⟩
  -- Once `x` is a minimizer of `f`, compare `g x` with the constrained minimizer `x₀`.
  rw [isMinOn_iff]
  intro z hz
  exact le_trans hx_le_x0 ((isMinOn_iff.mp hx0_min) z hz)

/-- Theorem 27.23 (3): along `ε ↓ 0` with `ε ∈ ]0,1[`, the unique minimizers of the regularized
problems converge weakly to the unique minimizer of `g` over `Argmin f`. -/
theorem tendsto_toWeakSpace_argmin_add_posReal_smul_of_inter_nonempty_of_coercive_of_strictlyConvex
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    (hg_coe : Coercive g.asEReal) (hg_strict : StrictlyConvex g)
    {x0 : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    {xε : ℝ → H}
    (hxε :
      ∀ {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        xε ε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal) :
    Tendsto
      (fun ε : ℝ ↦ toWeakSpace ℝ H (xε ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (𝓝 (toWeakSpace ℝ H x0)) := by
  obtain ⟨xg, hxg, _⟩ :=
    existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex hg hg_coe hg_strict
  have hargmin_subsingleton : (Argmin[Argmin f.asEReal] g.asEReal).Subsingleton := by
    intro y hy z hz
    obtain ⟨w, hw, huniq⟩ :=
      existsUnique_mem_argminOn_argmin_of_inter_nonempty_of_coercive_of_strictlyConvex
        hf hg hfeas hg_coe hg_strict
    have hy_eq : y = w := huniq y hy
    have hz_eq : z = w := huniq z hz
    exact hy_eq.trans hz_eq.symm
  have hx0_dom_g : x0 ∈ effectiveDomain g := by
    rcases hfeas with ⟨z, hz_argf, hz_dom_g⟩
    have hx0_min_g : IsMinOn g.asEReal (Argmin f.asEReal) x0 :=
      (mem_argminOn_iff.mp hx0).2
    -- A feasible argmin point bounds the constrained minimizer `x₀` inside the effective domain.
    rw [mem_effectiveDomain_iff]
    exact
      lt_of_le_of_lt ((isMinOn_iff.mp hx0_min_g) z hz_argf)
        (mem_effectiveDomain_iff.mp hz_dom_g)
  have hx0g_top : (g.asEReal x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_g)
  have hx0g_bot : (g.asEReal x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < g.asEReal x0 from (g x0).2)
  -- Route correction: package the source estimate into a minimizing-sequence helper before using
  -- the bounded-range plus unique-cluster-point criterion.
  apply Filter.tendsto_of_seq_tendsto
  intro εseq hεseq
  have hεseq_zero : Tendsto εseq atTop (𝓝 (0 : ℝ)) :=
    hεseq.mono_right inf_le_left
  have hεseq_mem :
      ∀ᶠ n in atTop, εseq n ∈ Set.Ioo (0 : ℝ) 1 := hεseq.eventually self_mem_nhdsWithin
  rcases eventually_atTop.mp hεseq_mem with ⟨N, hN⟩
  let εtail : ℕ → ℝ := fun n ↦ εseq (n + N)
  have hεtail_mem : ∀ n, εtail n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    exact hN (n + N) (by simpa [Nat.add_comm] using Nat.le_add_left N n)
  have hεtail_zero : Tendsto εtail atTop (𝓝 (0 : ℝ)) := by
    simpa [εtail, Function.comp] using hεseq_zero.comp (Filter.tendsto_add_atTop_nat N)
  let y : ℕ → H := fun n ↦ xε (εtail n)
  have hy_argmin :
      ∀ n,
        y n ∈ Argmin (f + (⟨εtail n, (hεtail_mem n).1⟩ : PosReal) • g).asEReal := by
    intro n
    simpa [y, εtail] using hxε (hεtail_mem n)
  have hy_min : IsMinimizingSequence f.asEReal y :=
    regularized_sequence_isMinimizingSequence_f
      hf hg hfeas hx0 hxg hεtail_mem hεtail_zero hy_argmin
  have hyg : ∀ n, g.asEReal (y n) ≤ g.asEReal x0 := by
    intro n
    exact regularized_g_le_argminOn_value hf hg hfeas (hεtail_mem n) hx0 (hy_argmin n)
  have hy_mem_level :
      ∀ n, y n ∈ lowerLevelSet g.asEReal (g.asEReal x0).toReal := by
    intro n
    rw [mem_lowerLevelSet_iff]
    simpa [EReal.coe_toReal hx0g_top hx0g_bot] using hyg n
  have hy_bounded : Bornology.IsBounded (Set.range y) := by
    -- The fixed lower level set from the source proof bounds the whole regularized tail.
    exact
      ((coercive_iff_bounded_lowerLevelSet g.asEReal).1 hg_coe ((g.asEReal x0).toReal)).subset
        (fun z hz ↦ by
          rcases hz with ⟨n, rfl⟩
          exact hy_mem_level n)
  have hunique :
      ∀ u v : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H u) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H v) →
        u = v := by
    intro u v hu hv
    have hu_arg :
        u ∈ Argmin[Argmin f.asEReal] g.asEReal :=
      weakSequentialClusterPt_mem_argminOn_of_regularized_sequence hf hg hx0 hy_min hyg hu
    have hv_arg :
        v ∈ Argmin[Argmin f.asEReal] g.asEReal :=
      weakSequentialClusterPt_mem_argminOn_of_regularized_sequence hf hg hx0 hy_min hyg hv
    exact hargmin_subsingleton hu_arg hv_arg
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint y).2
        ⟨hy_bounded, hunique⟩ with
    ⟨x, hxweak⟩
  have hxcluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H x) := by
    -- The weakly convergent full sequence is its own witnessing subsequence.
    refine ⟨fun n ↦ n, fun _ _ h ↦ h, ?_⟩
    simpa [Function.comp] using hxweak
  have hx_arg :
      x ∈ Argmin[Argmin f.asEReal] g.asEReal :=
    weakSequentialClusterPt_mem_argminOn_of_regularized_sequence hf hg hx0 hy_min hyg hxcluster
  have hxx0 : x = x0 := hargmin_subsingleton hx_arg hx0
  have htail :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (xε (εseq (n + N))))
        atTop
        (𝓝 (toWeakSpace ℝ H x0)) := by
    simpa [y, εtail, hxx0, Nat.add_comm] using hxweak
  exact (Filter.tendsto_add_atTop_iff_nat N).1 htail

/-- Theorem 27.23 (4): along `ε ↓ 0` with `ε ∈ ]0,1[`, the values `g (x_ε)` converge to
`g (x₀)`. -/
theorem tendsto_argmin_add_posReal_smul_value_of_inter_nonempty_of_coercive_of_strictlyConvex
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    (hg_coe : Coercive g.asEReal) (hg_strict : StrictlyConvex g)
    {x0 : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    {xε : ℝ → H}
    (hxε :
      ∀ {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        xε ε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal) :
    Tendsto
      (fun ε : ℝ ↦ g.asEReal (xε ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (𝓝 (g.asEReal x0)) := by
  have hweak :=
    tendsto_toWeakSpace_argmin_add_posReal_smul_of_inter_nonempty_of_coercive_of_strictlyConvex
      hf hg hfeas hg_coe hg_strict hx0 hxε
  apply Filter.tendsto_of_seq_tendsto
  intro εseq hεseq
  have hεseq_mem :
      ∀ᶠ n in atTop, εseq n ∈ Set.Ioo (0 : ℝ) 1 := hεseq.eventually self_mem_nhdsWithin
  rcases eventually_atTop.mp hεseq_mem with ⟨N, hN⟩
  let εtail : ℕ → ℝ := fun n ↦ εseq (n + N)
  have hεtail_mem : ∀ n, εtail n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    exact hN (n + N) (by simpa [Nat.add_comm] using Nat.le_add_left N n)
  have hεtail_within :
      Tendsto εtail atTop (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [εtail, Function.comp] using hεseq.comp (Filter.tendsto_add_atTop_nat N)
  have hy_weak :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (xε (εtail n)))
        atTop
        (𝓝 (toWeakSpace ℝ H x0)) := by
    simpa [Function.comp, εtail] using hweak.comp hεtail_within
  have hliminf :
      g.asEReal x0 ≤ liminf (fun n ↦ g.asEReal (xε (εtail n))) atTop := by
    -- Weak lower semicontinuity gives the lower half of the source squeeze.
    exact weak_seq_tendsto_le_liminf_of_mem_gammaZero (φ := g) hg hy_weak
  have hlimsup :
      limsup (fun n ↦ g.asEReal (xε (εtail n))) atTop ≤ g.asEReal x0 := by
    -- The regularized-value bound supplies the upper half of the source squeeze.
    refine Filter.limsup_le_of_le (hf := by isBoundedDefault) ?_
    exact Filter.Eventually.of_forall fun n ↦
      regularized_g_le_argminOn_value hf hg hfeas (hεtail_mem n) hx0 <|
        by simpa [εtail] using hxε (hεtail_mem n)
  have htail :
      Tendsto
        (fun n ↦ g.asEReal (xε (εseq (n + N))))
        atTop
        (𝓝 (g.asEReal x0)) := by
    have hy_tendsto :
        Tendsto (fun n ↦ g.asEReal (xε (εtail n))) atTop (𝓝 (g.asEReal x0)) :=
      tendsto_of_le_liminf_of_limsup_le hliminf hlimsup
    simpa [εtail, Nat.add_comm] using hy_tendsto
  exact (Filter.tendsto_add_atTop_iff_nat N).1 htail

/-- Theorem 27.23 (5): if every nonempty slice `Metric.closedBall c r ∩ dom g` carries a modulus
witnessing uniform convexity of `g`, then the regularized minimizers converge strongly to the
unique minimizer of `g` over `Argmin f` as `ε ↓ 0`. -/
theorem tendsto_argmin_add_posReal_smul_of_closedBall_uniformlyConvex
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfeas : (Argmin f.asEReal ∩ effectiveDomain g).Nonempty)
    (hg_coe : Coercive g.asEReal)
    (hball_uniform :
      ∀ ⦃c : H⦄ ⦃r : ℝ⦄, 0 ≤ r →
        (Metric.closedBall c r ∩ effectiveDomain g).Nonempty →
        ∃ φ : NNReal → EReal,
          UniformlyConvexOn g (Metric.closedBall c r ∩ effectiveDomain g) φ)
    {x0 : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] g.asEReal)
    {xε : ℝ → H}
    (hxε :
      ∀ {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        xε ε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • g).asEReal) :
    Tendsto xε (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) (𝓝 x0) := by
  have hg_strict : StrictlyConvex g :=
    strictlyConvex_of_closedBall_uniformlyConvex_local hball_uniform
  have hweak :=
    tendsto_toWeakSpace_argmin_add_posReal_smul_of_inter_nonempty_of_coercive_of_strictlyConvex
      hf hg hfeas hg_coe hg_strict hx0 hxε
  have hval :=
    tendsto_argmin_add_posReal_smul_value_of_inter_nonempty_of_coercive_of_strictlyConvex
      hf hg hfeas hg_coe hg_strict hx0 hxε
  have hx0_argf : x0 ∈ Argmin f.asEReal := (mem_argminOn_iff.mp hx0).1
  have hx0_dom_g : x0 ∈ effectiveDomain g := by
    rcases hfeas with ⟨z, hz_argf, hz_dom_g⟩
    have hx0_min_g : IsMinOn g.asEReal (Argmin f.asEReal) x0 :=
      (mem_argminOn_iff.mp hx0).2
    -- A feasible comparison point keeps the constrained minimizer inside `dom g`.
    rw [mem_effectiveDomain_iff]
    exact
      lt_of_le_of_lt ((isMinOn_iff.mp hx0_min_g) z hz_argf)
        (mem_effectiveDomain_iff.mp hz_dom_g)
  have hx0g_top : (g.asEReal x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom_g)
  have hx0g_bot : (g.asEReal x0 : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < g.asEReal x0 from (g x0).2)
  apply Filter.tendsto_of_seq_tendsto
  intro εseq hεseq
  have hεseq_mem :
      ∀ᶠ n in atTop, εseq n ∈ Set.Ioo (0 : ℝ) 1 := hεseq.eventually self_mem_nhdsWithin
  rcases eventually_atTop.mp hεseq_mem with ⟨N, hN⟩
  let εtail : ℕ → ℝ := fun n ↦ εseq (n + N)
  have hεtail_mem : ∀ n, εtail n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    exact hN (n + N) (by simpa [Nat.add_comm] using Nat.le_add_left N n)
  have hεtail_within :
      Tendsto εtail atTop (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [εtail, Function.comp] using hεseq.comp (Filter.tendsto_add_atTop_nat N)
  let y : ℕ → H := fun n ↦ xε (εtail n)
  have hy_argmin :
      ∀ n,
        y n ∈ Argmin (f + (⟨εtail n, (hεtail_mem n).1⟩ : PosReal) • g).asEReal := by
    intro n
    simpa [y, εtail] using hxε (hεtail_mem n)
  have hy_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (y n)) atTop (𝓝 (toWeakSpace ℝ H x0)) := by
    simpa [Function.comp, y, εtail] using hweak.comp hεtail_within
  have hy_val :
      Tendsto (fun n ↦ g.asEReal (y n)) atTop (𝓝 (g.asEReal x0)) := by
    simpa [Function.comp, y, εtail] using hval.comp hεtail_within
  have hy_level :
      ∀ n, g.asEReal (y n) ≤ g.asEReal x0 := by
    intro n
    exact regularized_g_le_argminOn_value hf hg hfeas (hεtail_mem n) hx0 (hy_argmin n)
  have hy_mem_level :
      ∀ n, y n ∈ lowerLevelSet g.asEReal (g.asEReal x0).toReal := by
    intro n
    rw [mem_lowerLevelSet_iff]
    simpa [EReal.coe_toReal hx0g_top hx0g_bot] using hy_level n
  have hy_bounded : Bornology.IsBounded (Set.range y) := by
    -- The source lower level set bound places the whole tail inside a bounded slice of `g`.
    exact
      ((coercive_iff_bounded_lowerLevelSet g.asEReal).1 hg_coe ((g.asEReal x0).toReal)).subset
        (fun z hz ↦ by
          rcases hz with ⟨n, rfl⟩
          exact hy_mem_level n)
  obtain ⟨R, hR⟩ := hy_bounded.subset_closedBall (0 : H)
  let r : ℝ := max R ‖x0‖
  have hR_nonneg : 0 ≤ R := by
    have hy0 : y 0 ∈ Metric.closedBall (0 : H) R := hR (Set.mem_range_self 0)
    have hy0_le : dist (0 : H) (y 0) ≤ R := by
      simpa [Metric.mem_closedBall] using hy0
    exact le_trans dist_nonneg hy0_le
  have hr_nonneg : 0 ≤ r := by
    exact le_trans hR_nonneg (le_max_left R ‖x0‖)
  let C : Set H := Metric.closedBall (0 : H) r ∩ effectiveDomain g
  have hy_dom_g : ∀ n, y n ∈ effectiveDomain g := by
    intro n
    let epsPos : PosReal := ⟨εtail n, (hεtail_mem n).1⟩
    have hy_dom_sum : y n ∈ effectiveDomain (f + epsPos • g) := by
      simpa [effectiveDomain, dom] using
        mem_dom_of_mem_argmin_of_isProper
          (isProper_of_mem_gammaZero
            (add_posReal_smul_mem_gammaZero_of_argmin_inter_effectiveDomain_nonempty
              hf hg hfeas epsPos))
          (hy_argmin n)
    have hy_dom_epsg : y n ∈ effectiveDomain (epsPos • g) :=
      ((mem_effectiveDomain_pointwiseAdd_iff f (epsPos • g) (y n)).1 hy_dom_sum).2
    exact (mem_effectiveDomain_posReal_smul_iff epsPos (y n)).1 hy_dom_epsg
  have hx0C : x0 ∈ C := by
    refine ⟨?_, hx0_dom_g⟩
    simpa [C, r, Metric.mem_closedBall, dist_eq_norm] using le_max_right R ‖x0‖
  have hyC : ∀ n, y n ∈ C := by
    intro n
    refine ⟨?_, hy_dom_g n⟩
    have hyR : y n ∈ Metric.closedBall (0 : H) R := hR (Set.mem_range_self n)
    exact
      (Metric.closedBall_subset_closedBall (show R ≤ r by exact le_max_left R ‖x0‖)) hyR
  obtain ⟨φ, huniform⟩ := hball_uniform (c := 0) (r := r) hr_nonneg ⟨x0, hx0C⟩
  have hy_strong : Tendsto y atTop (𝓝 x0) := by
    by_contra hnot
    have hnot_diff : ¬ Tendsto (fun n ↦ y n - x0) atTop (𝓝 (0 : H)) := by
      intro hdiff
      have hconst : Tendsto (fun _ : ℕ ↦ x0) atTop (𝓝 x0) := tendsto_const_nhds
      have hy' : Tendsto y atTop (𝓝 x0) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff.add hconst
      exact hnot hy'
    rcases exists_strictMono_subseq_norm_ge_of_not_tendsto_zero (fun n ↦ y n - x0) hnot_diff with
      ⟨c, hcpos, k, hk, hkdist⟩
    let cNN : NNReal := ⟨c, hcpos.le⟩
    let d : EReal := (((1 / 4 : ℝ) : EReal)) * φ cNN
    have hphi_c_nonneg : (0 : EReal) ≤ φ cNN := by
      rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
      exact huniform.monotone bot_le
    have hphi_c_ne_zero : φ cNN ≠ 0 := by
      intro hzero
      have hcNN_ne_zero : cNN ≠ 0 := by
        intro hcNN_zero
        have hc_zero : c = 0 := by
          exact congrArg (fun t : NNReal ↦ (t : ℝ)) hcNN_zero
        exact hcpos.ne' hc_zero
      exact hcNN_ne_zero ((huniform.modulus_eq_zero_iff cNN).1 hzero)
    have hphi_c_pos : (0 : EReal) < φ cNN :=
      lt_of_le_of_ne hphi_c_nonneg (Ne.symm hphi_c_ne_zero)
    have hd_nonneg : (0 : EReal) ≤ d := by
      dsimp [d]
      exact mul_nonneg (by norm_num) hphi_c_nonneg
    have hd_pos : (0 : EReal) < d := by
      -- The source contradiction uses a fixed positive midpoint gap on a subsequence bounded away
      -- from `x₀`.
      dsimp [d]
      have hquarter_pos : (0 : EReal) < (((1 / 4 : ℝ) : EReal)) := by
        exact_mod_cast (show (0 : ℝ) < 1 / 4 by norm_num)
      exact EReal.mul_pos hquarter_pos hphi_c_pos
    let mid : ℕ → EReal := fun n ↦ g.asEReal (midpoint ℝ (y (k n)) x0)
    let rhs : ℕ → EReal :=
      fun n ↦
        (((1 / 2 : ℝ) : EReal)) * g.asEReal (y (k n)) +
          (((1 / 2 : ℝ) : EReal)) * g.asEReal x0
    have hmid_plus_le_rhs : ∀ n, mid n + d ≤ rhs n := by
      intro n
      have hc_le : cNN ≤ ‖y (k n) - x0‖₊ := by
        exact_mod_cast hkdist n
      have hgap_le :
          d ≤ (((1 / 4 : ℝ) : EReal)) * φ ‖y (k n) - x0‖₊ := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left (huniform.monotone hc_le) (by norm_num : (0 : EReal) ≤ (1 / 4 : ℝ))
      -- Specialize the local uniform-convexity estimate at the midpoint and then freeze the gap at
      -- the positive distance lower bound `c`.
      calc
        mid n + d
            ≤ mid n + ((((1 / 4 : ℝ) : EReal)) * φ ‖y (k n) - x0‖₊) := by
              simpa [add_comm] using add_le_add_left hgap_le (mid n)
        _ ≤ rhs n := by
              simpa [mid, rhs] using
                midpoint_gap_le_of_uniformlyConvexOn huniform (hyC (k n)) hx0C
    have hmid_le_rhs : ∀ n, mid n ≤ rhs n := by
      intro n
      exact le_trans (le_add_of_nonneg_right hd_nonneg) (hmid_plus_le_rhs n)
    have hy_weak_k :
        Tendsto (fun n ↦ toWeakSpace ℝ H (y (k n))) atTop (𝓝 (toWeakSpace ℝ H x0)) :=
      hy_weak.comp hk.tendsto_atTop
    have hmid_weak :
        Tendsto (fun n ↦ toWeakSpace ℝ H (midpoint ℝ (y (k n)) x0)) atTop
          (𝓝 (toWeakSpace ℝ H x0)) := by
      have hscaled :
          Tendsto
            (fun n ↦ (1 / 2 : ℝ) • toWeakSpace ℝ H (y (k n)))
            atTop
            (𝓝 ((1 / 2 : ℝ) • toWeakSpace ℝ H x0)) :=
        hy_weak_k.const_smul (1 / 2 : ℝ)
      have hconst :
          Tendsto
            (fun _ : ℕ ↦ (1 / 2 : ℝ) • toWeakSpace ℝ H x0)
            atTop
            (𝓝 ((1 / 2 : ℝ) • toWeakSpace ℝ H x0)) :=
        tendsto_const_nhds
      have hmid_weak' :
          Tendsto
            (fun n ↦ toWeakSpace ℝ H (midpoint ℝ (y (k n)) x0))
            atTop
            (𝓝
              (((1 / 2 : ℝ) • toWeakSpace ℝ H x0) +
                ((1 / 2 : ℝ) • toWeakSpace ℝ H x0))) := by
        -- The midpoint map is affine, so weak convergence is preserved under it.
        simpa [toWeakSpace, midpoint_eq_smul_add] using hscaled.add hconst
      have hmid_limit :
          (((1 / 2 : ℝ) • toWeakSpace ℝ H x0) +
              ((1 / 2 : ℝ) • toWeakSpace ℝ H x0)) =
            toWeakSpace ℝ H x0 := by
        rw [← add_smul]
        norm_num
      rw [hmid_limit] at hmid_weak'
      exact hmid_weak'
    have hmid_liminf :
        g.asEReal x0 ≤ Filter.liminf mid atTop := by
      simpa [mid] using weak_seq_tendsto_le_liminf_of_mem_gammaZero (φ := g) hg hmid_weak
    have hy_val_k :
        Tendsto (fun n ↦ g.asEReal (y (k n))) atTop (𝓝 (g.asEReal x0)) :=
      hy_val.comp hk.tendsto_atTop
    have hhalf_top : ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      exact ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl (by norm_num : (0 : EReal) ≤ (1 / 2 : ℝ)),
        Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hx0g_top⟩
    have hhalf_bot : ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0) ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      exact ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inr hx0g_bot,
        Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
        Or.inl (by norm_num : (0 : EReal) ≤ (1 / 2 : ℝ))⟩
    have hrhs_tendsto :
        Tendsto rhs atTop (𝓝 (g.asEReal x0)) := by
      have hcont_mul :
          ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2)
            ((((1 / 2 : ℝ) : EReal)), g.asEReal x0) := by
        refine EReal.continuousAt_mul ?_ ?_ ?_ ?_
        · exact Or.inl (by norm_num : (((1 / 2 : ℝ) : EReal)) ≠ 0)
        · exact Or.inl (by norm_num : (((1 / 2 : ℝ) : EReal)) ≠ 0)
        · exact Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ))
        · exact Or.inl (EReal.coe_ne_top (1 / 2 : ℝ))
      have hhalf_tendsto :
          Tendsto
            (fun n ↦ (((1 / 2 : ℝ) : EReal)) * g.asEReal (y (k n)))
            atTop
            (𝓝 ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0)) := by
        exact hcont_mul.tendsto.comp
          ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ ↦ (((1 / 2 : ℝ) : EReal))) atTop
              (𝓝 ((((1 / 2 : ℝ) : EReal))))).prodMk_nhds hy_val_k)
      have hsum_tendsto :
          Tendsto
            (fun n ↦
              (((1 / 2 : ℝ) : EReal)) * g.asEReal (y (k n)) +
                (((1 / 2 : ℝ) : EReal)) * g.asEReal x0)
            atTop
            (𝓝
              (((((1 / 2 : ℝ) : EReal)) * g.asEReal x0) +
                ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0))) := by
        have hcont_add :
            ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
              (((((1 / 2 : ℝ) : EReal)) * g.asEReal x0),
                ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0)) := by
          exact EReal.continuousAt_add (Or.inl hhalf_top) (Or.inl hhalf_bot)
        exact hcont_add.tendsto.comp
          (hhalf_tendsto.prodMk_nhds
            (tendsto_const_nhds :
              Tendsto
                (fun _ : ℕ ↦ ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0))
                atTop
                (𝓝 ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0))))
      have hhalf_sum :
          (((((1 / 2 : ℝ) : EReal)) * g.asEReal x0) +
              ((((1 / 2 : ℝ) : EReal)) * g.asEReal x0)) =
            g.asEReal x0 := by
        rw [← EReal.coe_toReal hx0g_top hx0g_bot]
        change
          (((1 / 2 : ℝ) * (g.asEReal x0).toReal : ℝ) : EReal) +
              (((1 / 2 : ℝ) * (g.asEReal x0).toReal : ℝ) : EReal) =
            (((g.asEReal x0).toReal : ℝ) : EReal)
        rw [← EReal.coe_add]
        have hreal :
            (1 / 2 : ℝ) * (g.asEReal x0).toReal + (1 / 2 : ℝ) * (g.asEReal x0).toReal =
              (g.asEReal x0).toReal := by
          ring
        simpa using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal
      rw [hhalf_sum] at hsum_tendsto
      simpa [rhs] using hsum_tendsto
    have hplus_liminf :
        g.asEReal x0 + d ≤ Filter.liminf (fun n ↦ mid n + d) atTop := by
      calc
        g.asEReal x0 + d
            ≤ Filter.liminf mid atTop + Filter.liminf (fun _ : ℕ ↦ d) atTop := by
              simpa [add_comm] using add_le_add_left hmid_liminf d
        _ ≤ Filter.liminf (fun n ↦ mid n + d) atTop := by
              simpa [Function.comp] using
                (EReal.le_liminf_add (u := mid) (v := fun _ : ℕ ↦ d) (f := atTop))
    have hplus_limsup :
        Filter.limsup (fun n ↦ mid n + d) atTop ≤ g.asEReal x0 := by
      calc
        Filter.limsup (fun n ↦ mid n + d) atTop ≤ Filter.limsup rhs atTop :=
          Filter.limsup_le_limsup (Filter.Eventually.of_forall hmid_plus_le_rhs)
        _ = g.asEReal x0 := hrhs_tendsto.limsup_eq
    have hcontr :
        g.asEReal x0 + d ≤ g.asEReal x0 := by
      exact le_trans hplus_liminf <|
        le_trans (Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))
          hplus_limsup
    have hsum_lt :
        g.asEReal x0 < g.asEReal x0 + d := by
      simpa [add_comm] using
        EReal.add_lt_add_of_lt_of_le hd_pos le_rfl hx0g_bot hx0g_top
    exact (not_le_of_gt hsum_lt) hcontr
  have htail :
      Tendsto (fun n ↦ xε (εseq (n + N))) atTop (𝓝 x0) := by
    simpa [y, εtail, Nat.add_comm] using hy_strong
  exact (Filter.tendsto_add_atTop_iff_nat N).1 htail

end Regularization

end ERealFunction
