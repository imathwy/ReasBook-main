import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap13.Proposition_13_22
import BauschkeLean.Chap14.Proposition_14_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 45: the Fenchel conjugate of the constant `-∞` function is the
constant `+∞` function. -/
private theorem conjugate_bot_eq_top :
    ((fun _ : H ↦ (⊥ : EReal))∗) = (fun _ : H ↦ (⊤ : EReal)) := by
  -- The constant `⊥` function cannot dominate any real affine minorant.
  refine
    (conjugate_eq_top_iff_no_continuousAffineMinorant (fun _ : H ↦ (⊥ : EReal))).2 ?_
  rintro ⟨u, η, hη⟩
  have hzero : ((η : EReal) ≤ (⊥ : EReal)) := by
    simpa using hη 0
  simp at hzero

/-- Helper for Proposition 13 45: the lower semicontinuous convex envelope of the constant `+∞`
function is itself. -/
private theorem lowerSemicontinuousConvexEnvelope_top :
    lowerSemicontinuousConvexEnvelope (fun _ : H ↦ (⊤ : EReal)) = (fun _ : H ↦ (⊤ : EReal)) := by
  apply le_antisymm
  · -- Proposition 9.8 always places the envelope below the original function.
    exact lowerSemicontinuousConvexEnvelope_le (fun _ : H ↦ (⊤ : EReal))
  · -- The constant `⊤` function is itself a lower semicontinuous convex minorant.
    have h_lsc : LowerSemicontinuous (fun _ : H ↦ (⊤ : EReal)) := by
      simpa using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (⊤ : EReal)))
    have h_conv : Convex ℝ (epigraph (fun _ : H ↦ (⊤ : EReal))) := by
      simpa [epigraph] using (convex_empty : Convex ℝ (∅ : Set (H × ℝ)))
    exact
      le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
        h_lsc h_conv le_rfl

/-- Helper for Proposition 13 45: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex_ereal
    {g : H → EReal} (hg_conv : IsConvex g) :
    Convex ℝ (epigraph g) := by
  -- Rewrite epigraph convexity directly from the Jensen inequality stored in `IsConvex`.
  refine (convex_epigraph_iff_jensen_on_dom g).2 ?_
  intro x y hx hy a ha ha_lt_one
  exact hg_conv ha.le ha_lt_one.le

/-- Helper for Proposition 13 45: a proper function with convex epigraph is convex. -/
private theorem isConvex_of_convex_epigraph_of_isProper
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hproper : IsProper g) :
    IsConvex g := by
  intro x y a ha₀ ha₁
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  by_cases ha_zero : a = 0
  · -- Endpoint `a = 0` is a definitional simplification.
    subst ha_zero
    simp
  by_cases ha_one : a = 1
  · -- Endpoint `a = 1` is the symmetric definitional simplification.
    subst ha_one
    rw [hcoef_eq]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha₀ (Ne.symm ha_zero)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha₁ ha_one
  by_cases hx : x ∈ dom g
  · by_cases hy : y ∈ dom g
    · -- On the domain, convexity of the epigraph gives the Jensen inequality.
      simpa only [hcoef_eq] using
        (convex_epigraph_iff_jensen_on_dom g).1 hconv hx hy ha_pos ha_lt_one
    · -- Outside the domain the function value is `⊤`, so the right-hand side is `⊤`.
      have hy_top : g y = ⊤ := by
        simpa [mem_dom_iff_ne_top] using hy
      have hx_term_ne_bot : (a : EReal) * g x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), ?_, Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha₀)⟩
        exact Or.inr (hproper.1 x)
      rw [hcoef_eq, hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
      rw [EReal.add_top_of_ne_bot hx_term_ne_bot]
      exact le_top
  · -- If `x` is outside the domain, the symmetric `⊤` computation finishes the proof.
    have hx_top : g x = ⊤ := by
      simpa [mem_dom_iff_ne_top] using hx
    have hy_term_ne_bot : (((1 - a : ℝ) : EReal) * g y) ≠ ⊥ := by
      by_cases hy : y ∈ dom g
      · rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - a)), ?_, Or.inl (EReal.coe_ne_top (1 - a)),
          Or.inl (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha₁))⟩
        exact Or.inr (hproper.1 y)
      · have hy_top : g y = ⊤ := by
          simpa [mem_dom_iff_ne_top] using hy
        rw [hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
        simp
    have hrhs_top :
        (a : EReal) * g x + (1 - (a : EReal)) * g y = ⊤ := by
      rw [hx_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
      exact EReal.top_add_of_ne_bot hy_term_ne_bot
    simp [hrhs_top]

/-- Helper for Proposition 13 45: affine real functionals, viewed in `EReal`, belong to `Γ(ℝ)`.
-/
private theorem real_affine_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The real affine formula is exactly Jensen linearity.
    intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact_mod_cast hreal
  · -- Continuity of the underlying real affine map upgrades to lower semicontinuity.
    simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

/-- Helper for Proposition 13 45: every continuous affine functional on `H`, viewed in `EReal`,
belongs to `Γ(H)`. -/
private theorem affine_function_mem_gamma (u : H) (η : ℝ) :
    (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) ∈ gamma H := by
  -- Compose the one-dimensional affine model with the continuous linear inner-product map.
  have hcomp :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - (-η) : ℝ) : EReal))
      (innerSL ℝ u)
      (real_affine_mem_gamma (-η))
  simpa [Function.comp, innerSL_apply_apply, real_inner_comm, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using hcomp

/-- Helper for Proposition 13 45: every continuous affine minorant lies below the lower
semicontinuous convex envelope. -/
private theorem continuousAffineMinorant_le_lowerSemicontinuousConvexEnvelope
    (f : H → EReal) {u : H} {η : ℝ}
    (hη : ∀ x : H, (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ f x)) :
    (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) ≤ lowerSemicontinuousConvexEnvelope f := by
  have hgamma :
      (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) ∈ gamma H :=
    affine_function_mem_gamma u η
  have hdata : IsConvex (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) ∧
      LowerSemicontinuous (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) :=
    (mem_gamma_iff _).1 hgamma
  -- Proposition 9.8 makes the envelope the maximal lower semicontinuous convex minorant.
  exact
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hdata.2
      (convex_epigraph_of_isConvex_ereal hdata.1)
      hη

section CompleteSpace

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 13 45: if `dom f∗` is nonempty and `f` is not identically `⊤`, then
its lower semicontinuous convex envelope is proper. -/
private theorem lowerSemicontinuousConvexEnvelope_isProper_of_dom_conjugate_nonempty_of_ne_top
    (f : H → EReal) (hdom : (dom f∗).Nonempty) (hf_ne_top : f ≠ ⊤) :
    IsProper (lowerSemicontinuousConvexEnvelope f) := by
  rcases hdom with ⟨u, hu⟩
  rcases (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).1 hu with ⟨η, hη⟩
  have hminor :
      (fun x : H ↦ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) ≤
        lowerSemicontinuousConvexEnvelope f :=
    continuousAffineMinorant_le_lowerSemicontinuousConvexEnvelope f hη
  have hx_exists : ∃ x : H, f x ≠ ⊤ := by
    by_contra hx_exists
    apply hf_ne_top
    funext x
    by_contra hx
    exact hx_exists ⟨x, hx⟩
  rcases hx_exists with ⟨x₀, hx₀⟩
  have hx₀_dom : x₀ ∈ dom (lowerSemicontinuousConvexEnvelope f) := by
    rw [mem_dom_iff_ne_top]
    intro hx₀_env
    have htop : (⊤ : EReal) ≤ f x₀ := by
      simpa [hx₀_env] using (lowerSemicontinuousConvexEnvelope_le f x₀)
    exact hx₀ (top_le_iff.mp htop)
  refine ⟨?_, ⟨x₀, hx₀_dom⟩⟩
  intro y
  have hy_minor :
      (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ lowerSemicontinuousConvexEnvelope f y) :=
    hminor y
  intro hy_bot
  have hbot : (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ (⊥ : EReal)) := by
    simp [hy_bot] at hy_minor
  simp at hbot

-- Proof sketch: if `(dom f∗).Nonempty`, then Proposition 13.12 supplies a continuous affine
-- minorant of `f`, which makes `lowerSemicontinuousConvexEnvelope f` proper because it lies
-- between that affine minorant and `f`. Proposition 13.16(iv) gives
-- `conjugate (lowerSemicontinuousConvexEnvelope f) = conjugate f`, so taking conjugates again and
-- applying Theorem 13.37 to the proper function `lowerSemicontinuousConvexEnvelope f` yields
-- `f∗∗ = lowerSemicontinuousConvexEnvelope f`.
/-- If the domain of `f*` is nonempty, equivalently if `f` admits a continuous affine minorant,
then the Fenchel biconjugate of `f` is its lower semicontinuous convex envelope `\breve f`. -/
theorem biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
    (f : H → EReal)
    (hdom : (dom f∗).Nonempty) :
    f∗∗ = lowerSemicontinuousConvexEnvelope f := by
  by_cases hf_top : f = ⊤
  · -- The degenerate `f = ⊤` branch is handled directly.
    have hconj_bot : f∗ = ⊥ := (conjugate_eq_bot_iff_eq_top (f := f)).2 hf_top
    calc
      f∗∗ = (⊥ : H → EReal)∗ := by
        simpa using congrArg conjugate hconj_bot
      _ = (fun _ : H ↦ (⊤ : EReal)) := by
        simpa using (conjugate_bot_eq_top (H := H))
      _ = lowerSemicontinuousConvexEnvelope f := by
        have henv_top :
            lowerSemicontinuousConvexEnvelope f = (fun _ : H ↦ (⊤ : EReal)) := by
          simpa [hf_top] using lowerSemicontinuousConvexEnvelope_top (H := H)
        exact henv_top.symm
  · -- In the nondegenerate branch, the envelope is proper and belongs to `Γ(H)`.
    let g : H → EReal := lowerSemicontinuousConvexEnvelope f
    have hg_proper : IsProper g :=
      lowerSemicontinuousConvexEnvelope_isProper_of_dom_conjugate_nonempty_of_ne_top
        f hdom hf_top
    have hg_lsc : LowerSemicontinuous g := by
      simpa [g] using lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f
    have hg_conv_epi : Convex ℝ (epigraph g) := by
      simpa [g] using convex_epigraph_lowerSemicontinuousConvexEnvelope f
    have hg_gamma : g ∈ Γ(H) := by
      rw [mem_gamma_iff]
      exact ⟨isConvex_of_convex_epigraph_of_isProper hg_conv_epi hg_proper, hg_lsc⟩
    have hg_gammaZero : properIoi g hg_proper ∈ Γ₀(H) :=
      properIoi_mem_gammaZero_of_mem_gamma hg_proper hg_gamma
    have hg_eq_biconj : g∗∗ = g :=
      by
        simpa [Function.asEReal] using biconjugate_eq_of_mem_gammaZero hg_gammaZero
    have hconj : g∗ = f∗ := by
      simpa [g] using conjugate_lowerSemicontinuousConvexEnvelope_eq f
    have hbiconj : g∗∗ = f∗∗ := congrArg conjugate hconj
    calc
      f∗∗ = g∗∗ := hbiconj.symm
      _ = g := hg_eq_biconj
      _ = lowerSemicontinuousConvexEnvelope f := rfl

end CompleteSpace

-- Proof sketch: by Proposition 13.12's pointwise bridge together with Proposition 13.12(ii),
-- `dom f∗ = ∅` means
-- `conjugate f = ⊤`. Therefore
-- `f∗∗ = conjugate (conjugate f)` is the conjugate of the
-- constant `⊤` function, which is identically `⊥` by Proposition 13.10(ii).
/-- If the domain of `f*` is empty, then the Fenchel biconjugate of `f` is identically `-∞`. -/
theorem biconjugate_eq_bot_of_dom_conjugate_eq_empty
    (f : H → EReal)
    (hdom : dom f∗ = ∅) :
    f∗∗ = ⊥ := by
  have hno_minorant : ¬ ∃ u : H, HasContinuousAffineMinorantWithSlope f u := by
    rintro ⟨u, hu⟩
    have hu_dom : u ∈ dom f∗ :=
      (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).2 hu
    rw [hdom] at hu_dom
    exact hu_dom
  have hconj_top : f∗ = (fun _ : H ↦ (⊤ : EReal)) :=
    (conjugate_eq_top_iff_no_continuousAffineMinorant f).2 hno_minorant
  -- Once `f*` is the constant `⊤` function, Proposition 13.10 identifies its conjugate with
  -- the constant `⊥` function.
  exact (conjugate_eq_bot_iff_eq_top (f := f∗)).2 hconj_top

section CompleteSpace

variable [CompleteSpace H]

attribute [local instance] Classical.propDecidable

-- Proof sketch: combine the previous two branch theorems by splitting on whether `(dom f∗)` is
-- nonempty; the affine-minorant reformulation comes directly from Proposition 13.12.
/-- Proposition 13 45: if the domain of the Fenchel conjugate `f*` is nonempty, equivalently if
`f` admits a continuous affine minorant, then `f** = \breve f`; otherwise `f**` is identically
`-∞`. -/
theorem biconjugate_eq_lowerSemicontinuousConvexEnvelope_or_bot
    (f : H → EReal) :
    f∗∗ =
      if (dom f∗).Nonempty then
        lowerSemicontinuousConvexEnvelope f
      else
        ⊥ := by
  by_cases hdom : (dom f∗).Nonempty
  · -- The nonempty-domain branch is exactly the first theorem.
    simp [hdom,
      biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty (f := f) hdom]
  · -- The empty-domain branch is exactly the second theorem.
    have hdom_empty : dom f∗ = ∅ := Set.not_nonempty_iff_eq_empty.mp hdom
    simp [hdom, biconjugate_eq_bot_of_dom_conjugate_eq_empty (f := f) hdom_empty]

end CompleteSpace

end Conjugation

end ERealFunction
