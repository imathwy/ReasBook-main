import Mathlib
import BauschkeLean.Chap01.Lemma_1_24
import BauschkeLean.Chap01.Lemma_1_32
import BauschkeLean.Chap01.Text_1_0_28
import BauschkeLean.Chap01.Text_1_0_31
import BauschkeLean.Chap03.Theorem_3_50
import BauschkeLean.Chap09.Corollary_9_10
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Proposition_13_11
import BauschkeLean.Chap13.Proposition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 19 13: view `K × ℝ` with the `ℓ²` product metric used in epigraph
separation arguments. -/
local instance parametricDuality_prod_pseudoMetricSpace_l2 : PseudoMetricSpace (K × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) K ℝ

/-- Helper for Proposition 19 13: equip `K × ℝ` with the `ℓ²` product norm coming from
`WithLp 2 (K × ℝ)`. -/
local instance parametricDuality_prod_normedAddCommGroup_l2 : NormedAddCommGroup (K × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) K ℝ

/-- Helper for Proposition 19 13: the `ℓ²` product norm on `K × ℝ` is compatible with scalar
multiplication. -/
local instance parametricDuality_prod_normedSpace_l2 : NormedSpace ℝ (K × ℝ) := by
  letI : NormedAddCommGroup (K × ℝ) := parametricDuality_prod_normedAddCommGroup_l2 (K := K)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) K ℝ

/-- Helper for Proposition 19 13: the product Hilbert structure on `K × ℝ` is the textbook one
`⟪(x, ξ), (u, μ)⟫ = ⟪x, u⟫ + ξμ`. -/
local instance parametricDuality_prod_innerProductSpace_l2 : InnerProductSpace ℝ (K × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

/-- Helper for Proposition 19 13: the Chapter 19 dual objective is the slice
`v ↦ sup_p (⟪p.2,v⟫ - F p)`. -/
private def perturbationDualObjective_local
    (F : H × K → Set.Ioi (⊥ : EReal)) : K → EReal :=
  fun v ↦ ⨆ p : H × K, ((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal)

local notation "perturbationDualObjective" => perturbationDualObjective_local

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: evaluating the local Chapter 19 dual objective expands its
defining supremum. -/
@[simp] private theorem perturbationDualObjective_apply
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    perturbationDualObjective F v =
      ⨆ p : H × K, ((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal) := rfl

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Proposition 19 13: evaluating the infimal postcomposition along `Prod.snd`
rewrites it as the fiberwise infimum over the first variable. -/
@[simp] private theorem infimalPostcomposition_snd_apply
    (F : H × K → Set.Ioi (⊥ : EReal)) (y : K) :
    (Prod.snd ▷ F) y = ⨅ x : H, (F (x, y) : EReal) := by
  change
    sInf ((fun p : H × K ↦ (F p : EReal)) '' (Prod.snd ⁻¹' ({y} : Set K))) =
      ⨅ x : H, (F (x, y) : EReal)
  rw [show
      (fun p : H × K ↦ (F p : EReal)) '' (Prod.snd ⁻¹' ({y} : Set K)) =
        Set.range (fun x : H ↦ (F (x, y) : EReal)) by
      ext z
      constructor
      · rintro ⟨⟨x, y'⟩, hy', rfl⟩
        refine ⟨x, ?_⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy'
        simp [hy']
      · rintro ⟨x, rfl⟩
        exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: each first-variable slice is bounded above by subtracting the
fiber infimum from the fixed pairing value. -/
private theorem iSup_first_slice_le_pairing_sub_fiberInf
    (G : H × K → EReal) (v y : K) :
    (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) ≤
      (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) := by
  let a : EReal := ((⟪y, v⟫_ℝ : ℝ) : EReal)
  have h_antitone : Antitone (fun t : EReal ↦ a - t) := by
    intro s t hst
    exact EReal.sub_le_sub le_rfl hst
  simpa [a] using (Antitone.le_map_iInf h_antitone (s := fun x : H ↦ G (x, y)))

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: subtracting the fiber infimum is bounded above by the supremum
of the corresponding first-variable slices. -/
private theorem pairing_sub_fiberInf_le_iSup_first_slice
    (G : H × K → EReal) (v y : K) :
    (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) ≤
      (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) := by
  let a : EReal := ((⟪y, v⟫_ℝ : ℝ) : EReal)
  let s : Set EReal := Set.range (fun x : H ↦ G (x, y))
  have hs : (⨅ x : H, G (x, y)) = sInf s := by
    simpa [s] using (sInf_range (f := fun x : H ↦ G (x, y))).symm
  rw [hs]
  refine le_of_forall_lt fun c hc ↦ ?_
  have hsInf_ne_top : sInf s ≠ ⊤ := by
    intro hsInf_top
    have : ¬ c < (⊥ : EReal) := by simp
    simp [hsInf_top] at hc
  have hc_ne_top : c ≠ ⊤ := hc.ne_top
  have hc_add : c + sInf s < a := by
    exact
      (EReal.lt_sub_iff_add_lt (b := sInf s) (c := c) (Or.inr hc_ne_top)
        (Or.inl hsInf_ne_top)).1 hc
  have hs_lt : sInf s < a - c := by
    exact
      (EReal.lt_sub_iff_add_lt (b := c) (c := sInf s) (Or.inr hsInf_ne_top)
        (Or.inl hc_ne_top)).2
        (by simpa [add_comm] using hc_add)
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hs_lt
  rcases hzmem with ⟨x, rfl⟩
  have hlt : c < a - G (x, y) := by
    have hz_add : G (x, y) + c < a := by
      exact EReal.add_lt_of_lt_sub hzlt
    exact
      (EReal.lt_sub_iff_add_lt (b := G (x, y)) (c := c) (Or.inr hc_ne_top)
        (Or.inl hzlt.ne_top)).2
        (by simpa [add_comm] using hz_add)
  exact lt_of_lt_of_le hlt (le_iSup (fun x : H ↦ a - G (x, y)) x)

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: fiberwise, subtracting the first-variable infimum is the same
as taking the supremum of the first-variable slices. -/
private theorem pairing_sub_fiberInf_eq_iSup_first_slice
    (G : H × K → EReal) (v y : K) :
    (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) =
      (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) := by
  refine le_antisymm
    (pairing_sub_fiberInf_le_iSup_first_slice G v y)
    (iSup_first_slice_le_pairing_sub_fiberInf G v y)

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: the conjugate of the value function is the Chapter 19 dual
objective. -/
private theorem conjugate_valueFunction_eq_dualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗ = perturbationDualObjective F := by
  ext v
  rw [conjugate_apply, perturbationDualObjective_apply]
  simp_rw [infimalPostcomposition_snd_apply]
  calc
    (⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, (F (x, y) : EReal))) =
        (⨆ y : K, ⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          refine iSup_congr fun y ↦ ?_
          exact
            pairing_sub_fiberInf_eq_iSup_first_slice
              (G := fun p : H × K ↦ (F p : EReal)) v y
    _ = (⨆ x : H, ⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          rw [iSup_comm]
    _ = ⨆ p : H × K, (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal)) := by
          rw [iSup_prod']

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: evaluating the conjugate at the origin gives the negative
infimum of the underlying function. -/
private theorem conjugate_zero_eq_neg_iInf_local
    (φ : K → EReal) :
    φ∗ 0 = -(⨅ x : K, φ x) := by
  calc
    φ∗ 0 = ⨆ x : K, -φ x := by
      simp [conjugate_apply]
    _ = sSup (Set.range fun x : K ↦ -φ x) := by
      rw [sSup_range]
    _ = -sInf ((-·) '' Set.range (fun x : K ↦ -φ x)) := by
      rw [EReal.sSup_eq_neg_sInf_image_neg]
    _ = -sInf (Set.range φ) := by
      congr 2
      ext z
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, by simp⟩
      · rintro ⟨x, rfl⟩
        refine ⟨-φ x, ?_, by simp⟩
        exact ⟨x, rfl⟩
    _ = -(⨅ x : K, φ x) := by
      rw [sInf_range]

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: the negative infimum of the local dual objective is the
biconjugate value of the value function at the origin. -/
private theorem neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    -sInf (Set.range (perturbationDualObjective F)) =
      (Prod.snd ▷ F)∗∗ 0 := by
  rw [← conjugate_valueFunction_eq_dualObjective]
  simpa [sInf_range] using (conjugate_zero_eq_neg_iInf_local ((Prod.snd ▷ F)∗)).symm

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: every affine defect in the definition of a Fenchel conjugate is
bounded above by the conjugate value. -/
private theorem affine_defect_le_conjugate
    (φ : K → EReal) (x u : K) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - φ x) ≤ φ∗ u := by
  rw [conjugate_apply]
  exact le_iSup (fun y : K ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - φ y)) x

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: the Fenchel biconjugate is pointwise bounded above by the
original function. -/
private theorem biconjugate_le_local
    (φ : K → EReal) :
    φ∗∗ ≤ φ := by
  intro x
  by_cases htop : φ x = ⊤
  · simp [htop]
  by_cases hbot : φ x = ⊥
  · have hconj_top : ∀ u : K, φ∗ u = ⊤ := by
      intro u
      have htop_le : (⊤ : EReal) ≤ φ∗ u := by
        simpa [hbot] using affine_defect_le_conjugate (φ := φ) x u
      exact top_le_iff.mp htop_le
    have hxle : φ∗∗ x ≤ ⊥ := by
      rw [conjugate_apply]
      refine iSup_le fun u ↦ ?_
      rw [hconj_top u]
      simp
    simpa [hbot] using hxle
  · rw [conjugate_apply]
    refine iSup_le fun u ↦ ?_
    have hdefect :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) - φ x) ≤ φ∗ u := by
      simpa [real_inner_comm] using affine_defect_le_conjugate (φ := φ) x u
    have hsum :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) ≤ φ∗ u + φ x) :=
      (EReal.sub_le_iff_le_add (Or.inl hbot) (Or.inl htop)).1 hdefect
    exact
      (EReal.sub_le_iff_le_add (Or.inr htop) (Or.inr hbot)).2
        (by simpa [add_comm] using hsum)

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: the biconjugate of the value function at the origin is bounded
above by the value function there. -/
private theorem biconjugate_valueFunction_zero_le_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗∗ 0 ≤ (Prod.snd ▷ F) 0 := by
  simpa using (biconjugate_le_local (Prod.snd ▷ F)) 0

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex
    {f : K → EReal} (hconv : IsConvex f) :
    Convex ℝ (epigraph f) := by
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy a ha0 ha1
  exact hconv ha0.le ha1.le

/-- Helper for Proposition 19 13: at the origin, lower semicontinuity of a convex function is
equivalent to agreement with its lower semicontinuous convex envelope. -/
private theorem lscAt_iff_lowerSemicontinuousConvexEnvelope_eq_self_of_convex
    {f : K → EReal} (hconv : IsConvex f) :
    LowerSemicontinuousAt f 0 ↔ lowerSemicontinuousConvexEnvelope f 0 = f 0 := by
  have henv_eq_hull :
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
      f (convex_epigraph_of_isConvex hconv)
  constructor
  · intro hlsc
    simpa [henv_eq_hull] using
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f 0).mp hlsc
  · intro hEq
    exact
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f 0).2
        (by simpa [henv_eq_hull] using hEq)

omit [CompleteSpace K] in
/-- Helper for Proposition 19 13: points of a set lie below the support-value supremum. -/
private theorem inner_le_innerSupremumOn_of_mem
    {C : Set K} {u x : K} (hx : x ∈ C) :
    (⟪x, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
  rw [innerSupremumOn_eq_sSup_image]
  exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩

/-- Helper for Proposition 19 13: every strict real lower bound at the origin of a convex
function that is lower semicontinuous and finite there lies below its Fenchel biconjugate value at
the origin. -/
private theorem real_lt_value_zero_le_biconjugate_zero
    {φ : K → EReal} (hconv : IsConvex φ) (hlsc : LowerSemicontinuousAt φ 0)
    (hzero : 0 ∈ effectiveDom φ) {c : ℝ} (hc : (c : EReal) < φ 0) :
    (c : EReal) ≤ φ∗∗ 0 := by
  let g : K → EReal := lowerSemicontinuousConvexEnvelope φ
  have hg_zero : g 0 = φ 0 := by
    exact (lscAt_iff_lowerSemicontinuousConvexEnvelope_eq_self_of_convex hconv).mp hlsc
  have hg_lsc : LowerSemicontinuous g := by
    simpa [g] using lowerSemicontinuous_lowerSemicontinuousConvexEnvelope φ
  have hg_closed : IsClosed (epigraph g) := by
    exact (lowerSemicontinuous_iff_isClosed_epigraph g).1 hg_lsc
  have hg_convex : Convex ℝ (epigraph g) := by
    simpa [g] using convex_epigraph_lowerSemicontinuousConvexEnvelope φ
  have hφ_zero_top : φ 0 ≠ ⊤ := (mem_effectiveDom_iff φ 0).mp hzero |>.1
  have hφ_zero_bot : φ 0 ≠ ⊥ := (mem_effectiveDom_iff φ 0).mp hzero |>.2
  have hg_zero_top : g 0 ≠ ⊤ := by
    simpa [hg_zero] using hφ_zero_top
  have hg_zero_bot : g 0 ≠ ⊥ := by
    simpa [hg_zero] using hφ_zero_bot
  let r : ℝ := (g 0).toReal
  have hr : g 0 = (r : EReal) := by
    simpa [r] using (EReal.coe_toReal hg_zero_top hg_zero_bot).symm
  have hC_nonempty : (epigraph g).Nonempty := by
    refine ⟨((0 : K), r), ?_⟩
    rw [mem_epigraph_iff]
    simp [hr]
  have hc_zero : (c : EReal) < g 0 := by
    simpa [hg_zero] using hc
  have hpoint_not_mem : ((0 : K), c) ∉ epigraph g := by
    intro hmem
    have hle : g 0 ≤ (c : EReal) := (mem_epigraph_iff g 0 c).mp hmem
    exact (not_le_of_gt hc_zero) hle
  have hg_dom0 : (0 : K) ∈ dom g := (mem_dom_iff_ne_top g 0).2 hg_zero_top
  have hg_dom : (dom g).Nonempty := ⟨0, hg_dom0⟩
  obtain ⟨u, hu_ne, hu_sep⟩ :=
    exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
      hC_nonempty hg_closed hg_convex hpoint_not_mem
  let v : K := u.1
  let μ : ℝ := u.2
  have hsep : σ[epigraph g] (v, μ) < ((c * μ : ℝ) : EReal) := by
    have hsep_u : σ[epigraph g] u < (((⟪((0 : K), c), u⟫_ℝ : ℝ) : EReal)) := hu_sep
    have hright : (((⟪((0 : K), c), u⟫_ℝ : ℝ) : EReal)) = ((c * u.2 : ℝ) : EReal) := by
      change (((⟪(0 : K), u.1⟫_ℝ + c * u.2 : ℝ) : EReal)) = ((c * u.2 : ℝ) : EReal)
      simp
    have hsep_u' : σ[epigraph g] u < ((c * u.2 : ℝ) : EReal) := by
      rwa [hright] at hsep_u
    simpa [v, μ] using hsep_u'
  have hμ_not_pos : ¬ 0 < μ := by
    intro hμ_pos
    have htop : σ[epigraph g] (v, μ) = ⊤ := by
      have hμ_neg : -μ < 0 := by linarith
      simpa [μ] using supportFunction_epigraph_eq_top_of_neg (f := g) hg_dom v hμ_neg
    have htop_lt := hsep
    rw [htop] at htop_lt
    simp at htop_lt
  have hμ_ne : μ ≠ 0 := by
    intro hμ_zero
    have hσ_dom : σ[epigraph g] (v, μ) = σ[dom g] v := by
      simpa [hμ_zero, μ] using supportFunction_epigraph_eq_supportFunction_dom_zero (f := g) v
    have hσ_nonneg : (0 : EReal) ≤ σ[dom g] v := by
      simpa using inner_le_innerSupremumOn_of_mem (C := dom g) (u := v) (x := 0) hg_dom0
    have hlt0 : σ[dom g] v < 0 := by
      rw [← hσ_dom]
      simpa [hμ_zero] using hsep
    exact (not_lt_of_ge hσ_nonneg) hlt0
  have hμ_neg : μ < 0 := by
    exact lt_of_le_of_ne (le_of_not_gt hμ_not_pos) hμ_ne
  let a : ℝ := -μ
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  let w : K := a⁻¹ • v
  have hσ_mul : σ[epigraph g] (v, μ) = ((a : ℝ) : EReal) * g∗ w := by
    simpa [a, w, μ] using supportFunction_epigraph_eq_mul_conjugate_of_pos (f := g) v ha_pos
  have hsep' : ((a : ℝ) : EReal) * g∗ w < ((a : ℝ) : EReal) * (-c : EReal) := by
    calc
      ((a : ℝ) : EReal) * g∗ w = σ[epigraph g] (v, μ) := hσ_mul.symm
      _ < ((c * μ : ℝ) : EReal) := hsep
      _ = ((a : ℝ) : EReal) * (-c : EReal) := by
        simp [a, EReal.coe_mul, mul_comm]
  have hw_conj : φ∗ w < (-c : EReal) := by
    have hgw_conj : g∗ w < (-c : EReal) := by
      by_cases hbot : g∗ w = ⊥
      · rw [hbot]
        exact bot_lt_iff_ne_bot.mpr (by simp)
      · have htop : g∗ w ≠ ⊤ := by
          intro htop
          rw [htop] at hsep'
          rw [EReal.coe_mul_top_of_pos ha_pos] at hsep'
          exact (not_top_lt hsep').elim
        let s : ℝ := (g∗ w).toReal
        have hs : g∗ w = (s : EReal) := by
          simpa [s] using (EReal.coe_toReal htop hbot).symm
        have hs_lt : s < -c := by
          have hreal : a * s < a * (-c) := by
            have hE : (((a : ℝ) : EReal) * (s : EReal)) < ((a : ℝ) : EReal) * (-c : EReal) := by
              have hE' := hsep'
              rw [hs] at hE'
              exact hE'
            exact_mod_cast hE
          exact (mul_lt_mul_iff_of_pos_left ha_pos).1 hreal
        rw [hs]
        exact_mod_cast hs_lt
    have hconj_le : φ∗ w ≤ g∗ w := by
      rw [conjugate_apply, conjugate_apply]
      refine iSup_mono fun y ↦ ?_
      exact EReal.sub_le_sub le_rfl (lowerSemicontinuousConvexEnvelope_le φ y)
    exact lt_of_le_of_lt hconj_le hgw_conj
  have hw_biconj : (-φ∗ w) ≤ φ∗∗ 0 := by
    simpa [conjugate_apply] using le_iSup (fun u : K ↦ -φ∗ u) w
  calc
    (c : EReal) = -(-c : EReal) := by simp
    _ ≤ -(φ∗ w) := by
      exact (EReal.neg_le_neg_iff.mpr hw_conj.le)
    _ ≤ φ∗∗ 0 := hw_biconj

/-- Helper for Proposition 19 13: a strict subepigraph real level at the origin of the value
function lies below its biconjugate value there. -/
private theorem real_lt_valueFunction_zero_le_biconjugate_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) (0 : K))
    (hzero : (0 : K) ∈ effectiveDom (Prod.snd ▷ F)) {c : ℝ}
    (hc : (c : EReal) < (Prod.snd ▷ F) 0) :
    (c : EReal) ≤ (Prod.snd ▷ F)∗∗ 0 :=
  real_lt_value_zero_le_biconjugate_zero hconv hlsc hzero hc

-- Proof sketch: Proposition 19.12 rewrites `-sInf (range (perturbationDualObjective F))` as the
-- biconjugate value `(Prod.snd ▷ F)∗∗ 0`. The upper bound `ϑ∗∗ 0 ≤ ϑ 0` is Proposition 19.12 (3).
-- For the reverse inequality, every strict real lower bound of `ϑ 0` lies below `ϑ∗∗ 0` by
-- separating the point `((0 : K), c)` from the epigraph of the lower semicontinuous convex
-- envelope of `ϑ`.
/-- Proposition 19 13: if the canonical value function `Prod.snd ▷ F` is convex, lower
semicontinuous at the origin, and finite there in the canonical sense
`0 ∈ effectiveDom (Prod.snd ▷ F)`, then the primal infimum `inf_x F(x, 0)` equals the negative
dual infimum `- inf_v F^*(0, v)`.
-/
theorem valueFunction_zero_eq_neg_sInf_perturbationDualObjective_of_lscAt_and_finite
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) (0 : K))
    (hzero : (0 : K) ∈ effectiveDom (Prod.snd ▷ F)) :
    (Prod.snd ▷ F) 0 = -sInf (Set.range (perturbationDualObjective F)) := by
  have hbiconj_le : (Prod.snd ▷ F)∗∗ 0 ≤ (Prod.snd ▷ F) 0 :=
    biconjugate_valueFunction_zero_le_valueFunction_zero F
  have hvalue_le_biconj : (Prod.snd ▷ F) 0 ≤ (Prod.snd ▷ F)∗∗ 0 := by
    by_contra hlt
    obtain ⟨d, hd_left, hd_right⟩ := exists_between (lt_of_not_ge hlt)
    have hd_top : d ≠ ⊤ := hd_right.ne_top
    have hd_bot : d ≠ ⊥ := hd_left.ne_bot
    let c : ℝ := d.toReal
    have hc_left : (c : EReal) < (Prod.snd ▷ F) 0 := by
      simpa [c, EReal.coe_toReal hd_top hd_bot] using hd_right
    have hc_le : (c : EReal) ≤ (Prod.snd ▷ F)∗∗ 0 :=
      real_lt_valueFunction_zero_le_biconjugate_zero F hconv hlsc hzero hc_left
    have hc_right : (Prod.snd ▷ F)∗∗ 0 < (c : EReal) := by
      simpa [c, EReal.coe_toReal hd_top hd_bot] using hd_left
    exact (not_lt_of_ge hc_le) hc_right
  have hbiconj_zero : (Prod.snd ▷ F)∗∗ 0 = (Prod.snd ▷ F) 0 :=
    le_antisymm hbiconj_le hvalue_le_biconj
  have hdual :
      -sInf (Set.range (perturbationDualObjective F)) = (Prod.snd ▷ F)∗∗ 0 :=
    neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero F
  calc
    (Prod.snd ▷ F) 0 = (Prod.snd ▷ F)∗∗ 0 := hbiconj_zero.symm
    _ = -sInf (Set.range (perturbationDualObjective F)) := hdual.symm

end ParametricDuality

end

end ERealFunction
