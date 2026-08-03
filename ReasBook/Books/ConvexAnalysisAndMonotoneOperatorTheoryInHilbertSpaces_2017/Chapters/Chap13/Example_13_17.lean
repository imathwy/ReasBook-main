import Mathlib
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_7
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_6
import BauschkeLean.Chap12.Definition_12_5
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction InnerProductSpace

namespace ERealFunction

noncomputable section

/-- Helper for Example 13 17: the real inner product agrees with ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  -- Reduce the one-dimensional inner product to the standard scalar formula on `ℝ`.
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Example 13 17: a nonnegative slope cannot define an affine minorant of
`x ↦ -|x|`. -/
private theorem negAbs_minorant_contradiction_of_nonneg_slope
    {u η : ℝ}
    (hu : 0 ≤ u)
    (hminor : ∀ x : ℝ, (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ (-|x| : EReal))) :
    False := by
  let x : ℝ := |η| + 1
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hineqE := hminor x
  -- Evaluate the minorant at a large positive point to expose the slope contribution.
  have hineq' : (((x * u + η : ℝ) : EReal) ≤ ((-x : ℝ) : EReal)) := by
    simpa [real_inner_eq_mul, abs_of_nonneg hx_nonneg] using hineqE
  have hineq : x * u + η ≤ -( |η| + 1 ) := by
    simpa [x] using EReal.coe_le_coe_iff.mp hineq'
  have hxu_nonneg : 0 ≤ x * u := mul_nonneg hx_nonneg hu
  -- Since the slope term is nonnegative, the intercept would have to lie below `-(|η|+1)`.
  linarith [hineq, hxu_nonneg, neg_abs_le η]

/-- Helper for Example 13 17: a negative slope cannot define an affine minorant of
`x ↦ -|x|`. -/
private theorem negAbs_minorant_contradiction_of_neg_slope
    {u η : ℝ}
    (hu : u < 0)
    (hminor : ∀ x : ℝ, (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ (-|x| : EReal))) :
    False := by
  let x : ℝ := -(|η| + 1)
  have hx_nonpos : x ≤ 0 := by
    dsimp [x]
    linarith [abs_nonneg η]
  have hx_abs : |x| = |η| + 1 := by
    have hη : 0 ≤ |η| + 1 := by positivity
    simpa [x, abs_of_nonneg hη] using abs_neg (|η| + 1)
  have hineqE := hminor x
  -- Evaluate the minorant at a large negative point so the negative slope also contributes
  -- a nonnegative term.
  have hineq' : (((x * u + η : ℝ) : EReal) ≤ ((-|x| : ℝ) : EReal)) := by
    simpa [real_inner_eq_mul] using hineqE
  have hineq : x * u + η ≤ -( |η| + 1 ) := by
    simpa [hx_abs] using EReal.coe_le_coe_iff.mp hineq'
  have hxu_nonneg : 0 ≤ x * u := mul_nonneg_of_nonpos_of_nonpos hx_nonpos hu.le
  -- The same intercept contradiction appears once the slope term is known to be nonnegative.
  linarith [hineq, hxu_nonneg, neg_abs_le η]

/-- The concave scalar function `x ↦ -|x|` admits no continuous affine minorant. -/
theorem noContinuousAffineMinorant_negAbs :
    ¬ ∃ u : ℝ, HasContinuousAffineMinorantWithSlope (fun x : ℝ ↦ (-|x| : EReal)) u := by
  rintro ⟨u, η, hminor⟩
  -- Split on the sign of the slope and use the matching test point from the source proof.
  by_cases hu : 0 ≤ u
  · exact negAbs_minorant_contradiction_of_nonneg_slope hu hminor
  · exact negAbs_minorant_contradiction_of_neg_slope (lt_of_not_ge hu) hminor

/-- Helper for Example 13 17: every lower semicontinuous convex minorant of `x ↦ -|x|` belongs
to `Γ(ℝ)`. -/
private theorem negAbs_minorant_mem_gamma
    (g : {g : ℝ → EReal // g ∈ lowerSemicontinuousConvexMinorants (fun x : ℝ ↦ (-|x| : EReal))}) :
    g.1 ∈ gamma ℝ := by
  rcases (mem_lowerSemicontinuousConvexMinorants_iff _ _).1 g.2 with ⟨hg_lsc, hg_epi, hg_le⟩
  have hg_dom : ∀ x : ℝ, x ∈ dom g.1 := by
    intro x
    rw [mem_dom_iff_ne_top]
    intro hx
    have htop : (⊤ : EReal) ≤ ((-|x| : ℝ) : EReal) := by
      simpa [hx] using hg_le x
    simp at htop
  have hg_conv : IsConvex g.1 := by
    intro x y a ha0 ha1
    by_cases h0 : a = 0
    · subst h0
      simp
    by_cases h1 : a = 1
    · subst h1
      have hcoeff : (1 - (1 : EReal)) = 0 := by
        simpa using EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      have hzero : (1 - (1 : EReal)) * g.1 y = 0 := by
        rw [hcoeff, zero_mul]
      simp [hzero]
    have ha_pos : 0 < a := lt_of_le_of_ne ha0 (fun h ↦ h0 h.symm)
    have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 h1
    exact (convex_epigraph_iff_jensen_on_dom g.1).1 hg_epi
      (hg_dom x) (hg_dom y) ha_pos ha_lt_one
  rw [mem_gamma_iff]
  exact ⟨hg_conv, hg_lsc⟩

/-- Helper for Example 13 17: the lower semicontinuous convex envelope of `x ↦ -|x|` still lies
in `Γ(ℝ)`. -/
private theorem lowerSemicontinuousConvexEnvelope_negAbs_mem_gamma :
    lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (-|x| : EReal)) ∈ gamma ℝ := by
  let f : ℝ → EReal := fun x ↦ (-|x| : EReal)
  let F : {g : ℝ → EReal // g ∈ lowerSemicontinuousConvexMinorants f} → ℝ → EReal :=
    fun g ↦ g.1
  have hF : ∀ g, F g ∈ gamma ℝ := by
    intro g
    simpa [f, F] using negAbs_minorant_mem_gamma g
  have hsup : (fun x ↦ ⨆ g, F g x) ∈ gamma ℝ :=
    iSup_mem_gamma F hF
  have hEnvelope :
      lowerSemicontinuousConvexEnvelope f =
        fun x ↦ ⨆ g : {g : ℝ → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
    funext x
    rw [lowerSemicontinuousConvexEnvelope_apply]
    apply le_antisymm
    · refine sSup_le fun y hy ↦ ?_
      rcases hy with ⟨g, hg, rfl⟩
      exact le_iSup_of_le ⟨g, hg⟩ le_rfl
    · refine iSup_le fun g ↦ ?_
      exact le_sSup ⟨g.1, g.2, rfl⟩
  simpa [f, F, hEnvelope] using hsup

/-- Helper for Example 13 17: the lower semicontinuous convex envelope remains below `x ↦ -|x|`.
-/
private theorem lowerSemicontinuousConvexEnvelope_negAbs_le :
    lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (-|x| : EReal)) ≤
      fun x : ℝ ↦ (-|x| : EReal) := by
  intro x
  rw [lowerSemicontinuousConvexEnvelope_apply]
  refine sSup_le fun y hy ↦ ?_
  rcases hy with ⟨g, hg, rfl⟩
  exact ((mem_lowerSemicontinuousConvexMinorants_iff _ _).1 hg).2.2 x

/-- Helper for Example 13 17: the lower semicontinuous convex envelope of `x ↦ -|x|` still admits
no continuous affine minorant. -/
private theorem lowerSemicontinuousConvexEnvelope_negAbs_no_affine_minorant :
    ¬ ∃ u : ℝ,
      HasContinuousAffineMinorantWithSlope
        (lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (-|x| : EReal))) u := by
  rintro ⟨u, η, hη⟩
  -- Any affine minorant of the envelope composes with `env f ≤ f` to give one for `f` itself.
  exact noContinuousAffineMinorant_negAbs
    ⟨u, η, fun x ↦ (hη x).trans (lowerSemicontinuousConvexEnvelope_negAbs_le x)⟩

-- Proof sketch: the lower semicontinuous convex envelope of `x ↦ -|x|` is the greatest lower
-- semicontinuous convex minorant of this concave function, so it collapses to the constant
-- `-∞` function.
/-- Example 13 17: for `f(x) = -|x|`, the lower semicontinuous convex envelope `\tilde f` is
identically `-∞`. -/
theorem lowerSemicontinuousConvexEnvelope_negAbs_eq_bot :
    lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (-|x| : EReal)) =
      fun _ : ℝ ↦ (⊥ : EReal) := by
  let f : ℝ → EReal := fun x ↦ (-|x| : EReal)
  let g : ℝ → EReal := lowerSemicontinuousConvexEnvelope f
  have hg_gamma : g ∈ gamma ℝ := by
    simpa [f, g] using lowerSemicontinuousConvexEnvelope_negAbs_mem_gamma
  have hg_conv : IsConvex g := (mem_gamma_iff g).1 hg_gamma |>.1
  have hg_le : g ≤ f := by
    simpa [f, g] using lowerSemicontinuousConvexEnvelope_negAbs_le
  have hg_zero : g 0 = ⊥ := by
    by_contra hbot
    have htop : g 0 ≠ ⊤ := by
      intro htop
      have hle : (⊤ : EReal) ≤ f 0 := by
        simpa [htop] using hg_le 0
      simp [f] at hle
    let t : ℝ := |(g 0).toReal| + 1
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      positivity
    have hg_not_top : ∀ x : ℝ, g x ≠ ⊤ := by
      intro x hx
      have hle : (⊤ : EReal) ≤ f x := by
        simpa [hx] using hg_le x
      simp [f] at hle
    have hg_epi : Convex ℝ (epigraph g) := by
      refine (convex_epigraph_iff_jensen_on_dom g).2 ?_
      intro x _ y _ a ha ha_lt
      exact hg_conv ha.le ha_lt.le
    have hneg_t : g (-t) ≤ ((-t : ℝ) : EReal) := by
      simpa [f, abs_neg, abs_of_nonneg ht_nonneg] using hg_le (-t)
    have ht_bound : g 0 ≤ ((-t : ℝ) : EReal) := by
      have hmid0 : (t, (-t : ℝ)) ∈ epigraph g := by
        rw [mem_epigraph_iff]
        have hx : g t ≤ ((-t : ℝ) : EReal) := by
          simpa [f, abs_of_nonneg ht_nonneg] using hg_le t
        exact hx
      have hmid1 : (-t, (-t : ℝ)) ∈ epigraph g := by
        rw [mem_epigraph_iff]
        exact hneg_t
      have hmid : midpoint ℝ (t, (-t : ℝ)) (-t, (-t : ℝ)) ∈ epigraph g :=
        hg_epi.midpoint_mem hmid0 hmid1
      have hpair :
          midpoint ℝ (t, (-t : ℝ)) (-t, (-t : ℝ)) = (0, (-t : ℝ)) := by
        ext <;> simp [midpoint, AffineMap.lineMap_apply_module]
        · linarith
        · linarith
      rw [hpair] at hmid
      exact (mem_epigraph_iff _ _ _).1 hmid
    have hreal :
        (((g 0).toReal : ℝ) : EReal) ≤ ((-|((g 0).toReal)| - 1 : ℝ) : EReal) := by
      simpa [t, EReal.coe_toReal htop hbot, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using ht_bound
    have hreal' : (g 0).toReal ≤ -|(g 0).toReal| - 1 :=
      EReal.coe_le_coe_iff.mp hreal
    linarith [neg_abs_le (g 0).toReal]
  ext x
  simpa [g] using eq_bot_of_mem_gamma_of_eq_bot hg_gamma hg_zero

/-- Helper for Example 13 17: a finite bound on the affine defect is equivalent to the
corresponding affine minorant inequality for `x ↦ -|x|`. -/
private theorem affine_defect_negAbs_le_real_iff
    (x u μ : ℝ) :
    ((((⟪x, u⟫_ℝ : ℝ) : EReal) - (-|x| : EReal)) ≤ (μ : EReal)) ↔
      (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ (-|x| : EReal)) := by
  constructor
  · intro h
    -- Move the finite scalar bound to the right, then subtract it back off there.
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (-|x| : EReal) + (μ : EReal)) := by
      simpa [add_comm] using
        (EReal.sub_le_iff_le_add
          (.inr (EReal.coe_ne_top μ))
          (.inr (EReal.coe_ne_bot μ))).1 h
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ (-|x| : EReal)) :=
      EReal.sub_le_of_le_add h'
    simpa [EReal.coe_sub] using h''
  · intro h
    -- Reversing the same rearrangement restores the affine-defect bound.
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ (-|x| : EReal)) := by
      simpa [EReal.coe_sub] using h
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (-|x| : EReal) + (μ : EReal)) := by
      simpa [add_comm] using
        (EReal.sub_le_iff_le_add
          (.inl (EReal.coe_ne_bot μ))
          (.inl (EReal.coe_ne_top μ))).1 h'
    exact EReal.sub_le_of_le_add' h''

/-- Helper for Example 13 17: any finite conjugate value of `x ↦ -|x|` yields a continuous affine
minorant with the same slope. -/
private theorem hasContinuousAffineMinorantWithSlope_negAbs_of_conjugate_ne_top
    {u : ℝ}
    (hu : ((fun x : ℝ ↦ (-|x| : EReal))∗ u) ≠ ⊤) :
    HasContinuousAffineMinorantWithSlope (fun x : ℝ ↦ (-|x| : EReal)) u := by
  have hnot : ¬ ∀ μ : ℝ, (μ : EReal) < ((fun x : ℝ ↦ (-|x| : EReal))∗ u) := by
    intro hμ
    exact hu <| (EReal.eq_top_iff_forall_lt _).2 hμ
  rcases not_forall.mp hnot with ⟨μ, hμ⟩
  refine ⟨-μ, ?_⟩
  intro x
  have hupper : ((fun x : ℝ ↦ (-|x| : EReal))∗ u) ≤ (μ : EReal) :=
    le_of_not_gt hμ
  have hx :
      ((((⟪x, u⟫_ℝ : ℝ) : EReal) - (-|x| : EReal)) ≤ (μ : EReal)) := by
    exact le_trans
      (le_iSup (fun y : ℝ ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - (-|y| : EReal))) x)
      (by simpa [conjugate_apply] using hupper)
  have hminor : (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ (-|x| : EReal)) :=
    (affine_defect_negAbs_le_real_iff x u μ).1 hx
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hminor

-- Proof sketch: choose the sign of `x` so that `ux + |x|` tends to `+∞` as `|x| → ∞`.
/-- Example 13 17: for `f(x) = -|x|`, the Fenchel conjugate `f^*` is identically `+∞`. -/
theorem conjugate_negAbs_eq_top :
    (fun x : ℝ ↦ (-|x| : EReal))∗ = fun _ : ℝ ↦ (⊤ : EReal) := by
  -- Proposition 13.12 turns the direct minorant obstruction into the global conjugate formula.
  exact (conjugate_eq_top_iff_no_continuousAffineMinorant (fun x : ℝ ↦ (-|x| : EReal))).2
    noContinuousAffineMinorant_negAbs

end

end ERealFunction
