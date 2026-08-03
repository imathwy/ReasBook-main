import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap03.Corollary_3_24
import BauschkeLean.Chap16.Proposition_16_42
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Proposition_16_61
import BauschkeLean.Chap13.Proposition_13_45
import BauschkeLean.Chap16.Remark_16_28
import BauschkeLean.Chap07.Exercise_7_2
import BauschkeLean.Chap02.Example_2_32_2
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap03.Example_3_41
import BauschkeLean.Chap13.Example_13_5
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Example_13_43
import BauschkeLean.Chap16.Proposition_16_33
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap15.Proposition_15_22
import BauschkeLean.Chap01.Lemma_1_32
import BauschkeLean.Chap09.Corollary_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic search note: `lean_leansearch` only returned basic logic lemmas about negated
-- universal implications, so the statement surface below was checked against local Chapter 16
-- precedent for the convex-analytic API.

omit [CompleteSpace H] in
/-- Helper for Remark 16.46: a subgradient point of a `Γ₀(H)` function lies in the domain of its
Fenchel conjugate. -/
theorem mem_dom_conjugate_of_mem_subdifferential
    {F : H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H)) {x u : H}
    (hu : u ∈ (∂ F) x) :
    u ∈ dom (F.asEReal∗) := by
  -- A Fenchel--Young contact at `(x,u)` rules out the value `+∞` for `F* u`.
  rw [mem_dom_iff]
  exact lt_top_iff_ne_top.mpr
    (conjugate_value_ne_top_of_mem_subdifferential F hF.2.nonempty hu)

omit [CompleteSpace H] in
/-- Helper for Remark 16.46: a subgradient of a `Γ₀(H)` owner can only occur at a finite base
point of that owner. -/
theorem mem_effectiveDomain_of_mem_subdifferential_local
    {F : H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H)) {x u : H}
    (hu : u ∈ (∂ F) x) :
    x ∈ effectiveDomain F := by
  rcases hF.2.nonempty with ⟨y, hy⟩
  -- Test the subgradient inequality at one finite point to rule out `F x = ⊤`.
  by_contra hx
  have hx_top : (F x : EReal) = ⊤ := by
    apply le_antisymm le_top
    exact not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx)
  have hy_top : (F y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hxy : (⊤ : EReal) ≤ (F y : EReal) := by
    have hxy' : (⟪y - x, u⟫_ℝ : EReal) + (F x : EReal) ≤ (F y : EReal) :=
      (mem_subdifferential_iff (f := F) (x := x) (u := u)).1 hu y
    rw [hx_top] at hxy'
    simpa using hxy'
  exact hy_top (le_antisymm le_top hxy)

/-- Helper for Remark 16.46: Corollary 16.30 rewrites subgradients of a `Γ₀(H)` conjugate back to
subgradients of the original function. -/
theorem mem_subdifferential_gammaZeroConjugate_iff
    {F : H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H)) {x u : H} :
    x ∈ (∂ (F∗[hF])) u ↔ u ∈ (∂ F) x := by
  -- The conjugate subdifferential is exactly the inverse graph of `∂ F`.
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate F hF]
  exact SetValuedOperator.mem_inverse_iff (∂ F) u x

/-- Helper for Remark 16.46: the conjugate of `f + g` is the biconjugate of the dual infimal
convolution `f^* □ g^*`. -/
theorem conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates_local
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (f + g).asEReal∗ = (((f∗[hf]) □ (g∗[hg])) : H → EReal)∗∗ := by
  have hconj_f : (f∗[hf]).asEReal = f.asEReal∗ := by
    funext u
    simp [Function.asEReal]
  have hconj_g : (g∗[hg]).asEReal = g.asEReal∗ := by
    funext u
    simp [Function.asEReal]
  have hconj :
      ((((f∗[hf]) □ (g∗[hg])) : H → EReal)∗) = (f + g).asEReal := by
    calc
      ((((f∗[hf]) □ (g∗[hg])) : H → EReal)∗)
          = (f∗[hf]).asEReal∗ + (g∗[hg]).asEReal∗ := by
              exact conjugate_infimalConvolution_eq (f∗[hf]) (g∗[hg])
      _ = f.asEReal∗∗ + g.asEReal∗∗ := by rw [hconj_f, hconj_g]
      _ = f.asEReal + g.asEReal := by
            rw [biconjugate_eq_of_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hg]
      _ = (f + g).asEReal := by
            funext x
            simp [Function.asEReal_apply]
  -- Conjugating the dual identity once more gives the advertised biconjugate formula.
  simpa using congrArg conjugate hconj.symm

/-- Helper for Remark 16.46: Proposition 15.1 rewrites the conjugate of `f + g` as the lower
semicontinuous convex envelope of `f^* □ g^*`. -/
theorem conjugate_pointwiseAdd_eq_lscConvexEnvelope_infimalConvolution_conjugates_local
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (f + g).asEReal∗ =
      lowerSemicontinuousConvexEnvelope (((f∗[hf]) □ (g∗[hg])) : H → EReal) := by
  let F : H → EReal := (((f∗[hf]) □ (g∗[hg])) : H → EReal)
  have hconj : F∗ = (f + g).asEReal := by
    calc
      F∗ = (f∗[hf]).asEReal∗ + (g∗[hg]).asEReal∗ := by
            simpa [F] using conjugate_infimalConvolution_eq (f∗[hf]) (g∗[hg])
      _ = f.asEReal∗∗ + g.asEReal∗∗ := by
            simp
      _ = f.asEReal + g.asEReal := by
            rw [biconjugate_eq_of_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hg]
      _ = (f + g).asEReal := by
            funext x
            simp [Function.asEReal_apply]
  have hdom_conj : (dom F∗).Nonempty := by
    -- A finite primal point of `f + g` gives a point in the conjugate domain of `F`.
    have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
    rcases hfg.2.nonempty with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hconj]
    simpa [effectiveDomain, dom] using hu
  -- Rewrite through the local biconjugate identity, then use the general Chapter 13 envelope API.
  calc
    (f + g).asEReal∗ = F∗∗ := by
      simpa [F] using
        conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates_local f g hf hg
    _ = lowerSemicontinuousConvexEnvelope F := by
          simpa [F] using
            biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
              F hdom_conj
    _ = lowerSemicontinuousConvexEnvelope (((f∗[hf]) □ (g∗[hg])) : H → EReal) := by
          rfl

omit [CompleteSpace H] in
/-- Helper for Remark 16.46: once the active dual equality is written with an exact split
`f^* y + g^* (u - y)`, the two component Fenchel--Young equalities separate and recover the
subgradients of `f` and `g` at the same primal point `x`. -/
theorem component_subgradients_of_exact_dual_split
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x u y : H}
    (hsplit :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ y + g.asEReal∗ (u - y)) =
        ((inner ℝ x u : ℝ) : EReal)) :
    y ∈ (∂ f) x ∧ u - y ∈ (∂ g) x := by
  -- The conjugate terms are never `-∞` because `Γ₀(H)` functions have nonempty effective domains.
  have hc_bot : f.asEReal∗ y ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty y
  have hd_bot : g.asEReal∗ (u - y) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty (u - y)
  have hab_bot : (f x : EReal) + (g x : EReal) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hcd_bot : f.asEReal∗ y + g.asEReal∗ (u - y) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2
      ⟨bot_lt_iff_ne_bot.mpr hc_bot, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hsum_top :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ y + g.asEReal∗ (u - y)) ≠ ⊤ := by
    intro htop
    exact EReal.coe_ne_top (inner ℝ x u : ℝ) (hsplit.symm.trans htop)
  have hsum_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hab_bot hcd_bot).1 hsum_top
  have hab_top : (f x : EReal) + (g x : EReal) ≠ ⊤ := hsum_top_parts.1
  have hcd_top : f.asEReal∗ y + g.asEReal∗ (u - y) ≠ ⊤ := hsum_top_parts.2
  have hab_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) (ne_of_gt (g x).2)).1 hab_top
  have hcd_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hc_bot hd_bot).1 hcd_top
  have ha_top : (f x : EReal) ≠ ⊤ := hab_top_parts.1
  have hb_top : (g x : EReal) ≠ ⊤ := hab_top_parts.2
  have hc_top : f.asEReal∗ y ≠ ⊤ := hcd_top_parts.1
  have hd_top : g.asEReal∗ (u - y) ≠ ⊤ := hcd_top_parts.2
  have hac_top : (f x : EReal) + f.asEReal∗ y ≠ ⊤ :=
    EReal.add_ne_top ha_top hc_top
  have hbd_top : (g x : EReal) + g.asEReal∗ (u - y) ≠ ⊤ :=
    EReal.add_ne_top hb_top hd_top
  have hac_bot : (f x : EReal) + f.asEReal∗ y ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, bot_lt_iff_ne_bot.mpr hc_bot⟩
  have hbd_bot : (g x : EReal) + g.asEReal∗ (u - y) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(g x).2, bot_lt_iff_ne_bot.mpr hd_bot⟩
  -- Fenchel--Young gives the component lower bounds.
  have hfy_f :
      ((inner ℝ x y : ℝ) : EReal) ≤
        (f x : EReal) + f.asEReal∗ y :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hf) x y
  have hfy_g :
      ((inner ℝ x (u - y) : ℝ) : EReal) ≤
        (g x : EReal) + g.asEReal∗ (u - y) :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hg) x (u - y)
  have hfy_f_toReal :
      inner ℝ x y ≤
        (f x : EReal).toReal + (f.asEReal∗ y).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_f (EReal.coe_ne_bot _) hac_top
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot] at htmp
    exact htmp
  have hfy_g_toReal :
      inner ℝ x (u - y) ≤
        (g x : EReal).toReal + (g.asEReal∗ (u - y)).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_g (EReal.coe_ne_bot _) hbd_top
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot] at htmp
    exact htmp
  -- Convert the displayed equality to `ℝ` so linear arithmetic can isolate each equality case.
  have hsplit_toReal :
      ((f x : EReal).toReal + (g x : EReal).toReal) +
          ((f.asEReal∗ y).toReal + (g.asEReal∗ (u - y)).toReal) =
        inner ℝ x u := by
    have htmp := congrArg EReal.toReal hsplit
    rw [EReal.toReal_add hab_top hab_bot hcd_top hcd_bot,
      EReal.toReal_add ha_top (ne_of_gt (f x).2) hb_top (ne_of_gt (g x).2),
      EReal.toReal_add hc_top hc_bot hd_top hd_bot] at htmp
    exact htmp
  have hpair_real :
      inner ℝ x y + inner ℝ x (u - y) = inner ℝ x u := by
    calc
      inner ℝ x y + inner ℝ x (u - y)
          = inner ℝ x (y + (u - y)) := by
              rw [← inner_add_right]
      _ = inner ℝ x u := by
            congr 1
            abel
  have hcomp_f_toReal :
      (f x : EReal).toReal + (f.asEReal∗ y).toReal = inner ℝ x y := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hcomp_g_toReal :
      (g x : EReal).toReal + (g.asEReal∗ (u - y)).toReal =
        inner ℝ x (u - y) := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hfy_f_eq :
      (f x : EReal) + f.asEReal∗ y =
        ((inner ℝ x y : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hac_top hac_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot]
    exact hcomp_f_toReal
  have hfy_g_eq :
      (g x : EReal) + g.asEReal∗ (u - y) =
        ((inner ℝ x (u - y) : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hbd_top hbd_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot]
    exact hcomp_g_toReal
  -- Read the two exact Fenchel--Young equalities back as subgradient memberships.
  constructor
  · exact
      (mem_subdifferential_iff_fenchel_young_eq f hf.2.nonempty x y).2 hfy_f_eq
  · exact
      (mem_subdifferential_iff_fenchel_young_eq g hg.2.nonempty x (u - y)).2 hfy_g_eq

omit [CompleteSpace H] in
/-- Helper for Remark 16.46: a pointwise attained split of `(f + g)^* u` already suffices to
split the active subgradient `u ∈ ∂ (f + g) x`; no global formula `(f + g)^* = f^* □ g^*` is
needed at this step. -/
theorem subgradientSplit_of_memSubdifferential_pointwiseAdd_of_pointwiseExactValue
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    {x u y : H} (hu : u ∈ (∂ (f + g)) x)
    (hval :
      (f + g).asEReal∗ u =
        f.asEReal∗ y + g.asEReal∗ (u - y)) :
    u ∈ ((∂ f) + (∂ g)) x := by
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hsplit :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ y + g.asEReal∗ (u - y)) =
        ((inner ℝ x u : ℝ) : EReal) := by
    -- Corollary 16.30 gives the active Fenchel--Young equality for `u ∈ ∂ (f + g) x`, and the
    -- pointwise attained split rewrites only the conjugate term at `u`.
    have hfy :
        ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u =
          ((inner ℝ x u : ℝ) : EReal) := by
      simpa [pointwiseAdd_apply] using
        (mem_subdifferential_iff_fenchel_young_eq
          (f + g) hfg.2.nonempty x u).1 hu
    calc
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ y + g.asEReal∗ (u - y))
          = ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u := by
              rw [hval]
      _ = ((inner ℝ x u : ℝ) : EReal) := hfy
  -- The attained four-term contact splits into the two component subgradients at `x`.
  rcases component_subgradients_of_exact_dual_split hf hg hsplit with ⟨hy_f, hy_g⟩
  exact Set.mem_add.2 ⟨y, hy_f, u - y, hy_g, by abel⟩

/-- Helper for Remark 16.46: once the dual equality `(f + g)^* = f^* □ g^*` is available, an
active exact witness for `f^* □ g^*` at `u` turns the Fenchel--Young equality for
`u ∈ ∂ (f + g) x` into the four-term contact needed to split the subgradient. -/
theorem activeFenchelYoungContact_of_mem_subdifferential_and_exactWitness
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    {x u y : H} (hu : u ∈ (∂ (f + g)) x)
    (heq :
      (f + g).asEReal∗ =
        ((((f∗[hf]) □ (g∗[hg])) : H → EReal)))
    (hy :
      ((((f∗[hf]) □ (g∗[hg])) : H → EReal) u) =
        f.asEReal∗ y + g.asEReal∗ (u - y)) :
    ((f x : EReal) + (g x : EReal)) +
        (f.asEReal∗ y + g.asEReal∗ (u - y)) =
      ((inner ℝ x u : ℝ) : EReal) := by
  -- Package `f + g` into `Γ₀(H)` so Fenchel--Young applies at the active subgradient point.
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hfy :
      ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u =
        ((inner ℝ x u : ℝ) : EReal) := by
    simpa [pointwiseAdd_apply] using
      (mem_subdifferential_iff_fenchel_young_eq
        (f + g) hfg.2.nonempty x u).1 hu
  -- Rewrite the conjugate term through the dual formula and the exact witness.
  calc
    ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ y + g.asEReal∗ (u - y))
        = ((f x : EReal) + (g x : EReal)) +
            ((((f∗[hf]) □ (g∗[hg])) : H → EReal) u) := by
              rw [hy]
    _ = ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u := by
          rw [← heq]
    _ = ((inner ℝ x u : ℝ) : EReal) := hfy

/-- Helper for Remark 16.46: the dual equality `(f + g)^* = f^* □ g^*` together with an active
exact split of `f^* □ g^*` at `u` yields the decomposition `u ∈ (∂ f) x + (∂ g) x`. -/
theorem subgradient_split_of_mem_subdifferential_pointwiseAdd_of_exact
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    {x u : H} (hu : u ∈ (∂ (f + g)) x)
    (heq :
      (f + g).asEReal∗ =
        ((((f∗[hf]) □ (g∗[hg])) : H → EReal)))
    (hu_exact : infimalConvolution.ExactAt (f∗[hf]) (g∗[hg]) u) :
    u ∈ ((∂ f) + (∂ g)) x := by
  rcases hu_exact with ⟨y, hy⟩
  -- Rewrite the active Fenchel--Young equality using the exact split produced at `u`.
  have hsplit :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ y + g.asEReal∗ (u - y)) =
        ((inner ℝ x u : ℝ) : EReal) :=
    activeFenchelYoungContact_of_mem_subdifferential_and_exactWitness
      hf hg hdom hu heq hy
  -- The four-term contact splits into the two component subgradient memberships.
  rcases component_subgradients_of_exact_dual_split hf hg hsplit with ⟨hy_f, hy_g⟩
  have hu_split : y + (u - y) = u := by
    abel
  exact Set.mem_add.2 ⟨y, hy_f, u - y, hy_g, hu_split⟩

/-- Remark 16.46 (1): if `f, g ∈ Γ₀(H)` with intersecting effective domains and the exact dual
conjugate formula `(f + g)^* = f^* \boxdot g^*` holds, then `∂ (f + g) = ∂ f + ∂ g`.
This is the implication displayed as `(16.39)`; the source then paraphrases it by saying that
`f∗[hf] □ g∗[hg]` is exact on `dom (f + g)^*`. -/
theorem subdifferential_add_eq_add_of_infimalConvolution_exactOn_dom_conjugate
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hformula : ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ H)) :
    (∂ (f + g) : SetValuedOperator H H) = ∂ f + ∂ g := by
  have hdom_id :
      ((ContinuousLinearMap.id ℝ H) '' effectiveDomain f ∩ effectiveDomain g).Nonempty := by
    simpa using hdom
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g = ∂ g := by
    ext x u
    simp [ContinuousLinearMap.adjointImageSubdifferential, ContinuousLinearMap.adjointImage]
  simpa [Function.comp, hid] using
    (subdifferential_add_comp_eq_add_adjoint_image_of_conjugate_formula
      hf hg (ContinuousLinearMap.id ℝ H) hdom_id hformula)

/-- Remark 16.46 (2): if `f, g ∈ Γ₀(H)` with intersecting effective domains and
`∂ (f + g) = ∂ f + ∂ g`, then `f∗[hf] □ g∗[hg]` is exact at every point of
`dom ∂ (f + g)^*`. This is the almost converse displayed as `(16.40)`. -/
theorem infimalConvolution_exactAt_on_subdifferentialDom_conjugate_of_subdifferential_add_eq_add
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hsub : (∂ (f + g) : SetValuedOperator H H) = ∂ f + ∂ g) :
    ∀ ⦃u : H⦄,
      u ∈ SetValuedOperator.dom (∂ ((f + g).asEReal∗)) →
        infimalConvolution.ExactAt (f∗[hf]) (g∗[hg]) u := by
  -- Package `f + g` back into `Γ₀(H)` so Corollary 16.30 can move between primal and dual
  -- subgradients.
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  intro u hu
  rw [SetValuedOperator.mem_dom_iff] at hu
  rcases hu with ⟨x, hx⟩
  have hx_gamma : x ∈ (∂ ((f + g)∗[hfg])) u := by
    simpa [gammaZeroConjugate_apply] using hx
  have hu_primal : u ∈ (∂ (f + g)) x := by
    exact (mem_subdifferential_gammaZeroConjugate_iff hfg).mp hx_gamma
  -- Rewrite the assumed sum rule at the active primal point and unpack the additive witness.
  have hu_split : u ∈ ((∂ f) + (∂ g)) x := by
    simpa [hsub] using hu_primal
  rcases Set.mem_add.mp hu_split with ⟨y, hy, z, hz, huz⟩
  have hz_eq : z = u - y := by
    calc
      z = (y + z) - y := by abel
      _ = u - y := by rw [huz]
  -- Transport both component subgradients across conjugation so that `x` becomes a common
  -- subgradient of the two conjugate summands at the exact split `u = y + (u - y)`.
  have hx_f : x ∈ (∂ (f∗[hf])) y := by
    exact (mem_subdifferential_gammaZeroConjugate_iff hf).2 hy
  have hx_g_raw : x ∈ (∂ (g∗[hg])) z := by
    exact (mem_subdifferential_gammaZeroConjugate_iff hg).2 hz
  have hx_g : x ∈ (∂ (g∗[hg])) (u - y) := by
    simpa [hz_eq] using hx_g_raw
  have hinter :
      ((∂ (f∗[hf])) y ∩ (∂ (g∗[hg])) (u - y)).Nonempty := by
    exact ⟨x, ⟨hx_f, hx_g⟩⟩
  -- Proposition 16.61 now reads the common dual subgradient as exactness of `f* □ g*` at `u`.
  exact
    infimalConvolution_exactAt_of_subdifferential_inter_nonempty
      (f∗[hf]) (g∗[hg]) u y
      (gammaZeroConjugate_mem_gammaZero hf)
      (gammaZeroConjugate_mem_gammaZero hg)
      hinter

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Helper for Remark 16.46: infimal postcomposition along the identity map does not change the
underlying `EReal`-valued function. -/
theorem infimalPostcomposition_id_eq
    (f : H → Set.Ioi (⊥ : EReal)) :
    ((ContinuousLinearMap.id ℝ H) ▷ f) = (f : H → EReal) := by
  -- The identity fiber over `x` is the singleton `{x}`, so the defining infimum is just `f x`.
  funext x
  simp [ERealFunction.infimalPostcomposition]

/-- Helper for Remark 16.46: infimal postcomposition along the identity map also leaves a raw
`EReal`-valued owner unchanged. -/
theorem infimalPostcomposition_id_eq_ereal
    (φ : H → EReal) :
    ((ContinuousLinearMap.id ℝ H) ▷ φ) = φ := by
  -- The identity fiber over `x` is the singleton `{x}` even before packaging in `Γ₀(H)`.
  funext x
  simp [ERealFunction.infimalPostcomposition]

/-- Helper for Remark 16.46: every finite point is an exact identity-fiber witness for infimal
postcomposition. -/
theorem infimalPostcomposition_exactAt_id
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∈ effectiveDomain f) :
    infimalPostcomposition.ExactAt (ContinuousLinearMap.id ℝ H) f x := by
  -- Reuse the same point `x`; for the identity map the fiber equation and value equality are
  -- immediate.
  refine ⟨x, hx, rfl, ?_⟩
  rw [infimalPostcomposition_id_eq]

/-- Helper for Remark 16.46: the pointwise self-sum `f + f` is the positive-real scalar multiple
`2 • f`. -/
theorem pointwiseAdd_self_eq_twoPosReal_smul
    (f : H → Set.Ioi (⊥ : EReal)) :
    f + f = ((⟨(2 : ℝ), by norm_num⟩ : PosReal) • f) := by
  -- Compare both owners pointwise and rewrite the positive-real action on `]-∞,+∞]`.
  funext x
  apply Subtype.ext
  change (pointwiseAdd f f x : EReal) = (((⟨(2 : ℝ), by norm_num⟩ : PosReal) • f) x : EReal)
  rw [pointwiseAdd_apply, posReal_smul_apply]
  by_cases htop : (f x : EReal) = ⊤
  · simpa [htop] using
      (EReal.coe_mul_top_of_pos (by norm_num : 0 < (2 : ℝ)) :
        ((2 : ℝ) : EReal) * ⊤ = ⊤).symm
  · have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hcoe :
        (f x : EReal) = ((EReal.toReal (f x : EReal) : ℝ) : EReal) :=
      (EReal.coe_toReal htop hbot).symm
    rw [hcoe, hcoe, hcoe]
    exact_mod_cast (two_mul (EReal.toReal (f x : EReal))).symm

/-- Helper for Remark 16.46: the subdifferential of a self-sum is the sum of the two identical
subdifferentials. -/
theorem subdifferential_pointwiseAdd_self_eq_add_self
    (f : H → Set.Ioi (⊥ : EReal)) :
    (∂ (f + f) : SetValuedOperator H H) = ∂ f + ∂ f := by
  -- First rewrite `f + f` as the positive-real scaling `2 • f`.
  calc
    (∂ (f + f) : SetValuedOperator H H)
        = ∂ (((⟨(2 : ℝ), by norm_num⟩ : PosReal) • f) : H → Set.Ioi (⊥ : EReal)) := by
            rw [pointwiseAdd_self_eq_twoPosReal_smul]
    _ = (2 : ℝ) • (∂ f : SetValuedOperator H H) := by
          simpa using
            subdifferential_posReal_smul_eq_smul
              f (⟨(2 : ℝ), by norm_num⟩ : PosReal)
    _ = ∂ f + ∂ f := by
          -- Pointwise, convexity of each fiber turns `2 • (∂ f x)` into `(∂ f x) + (∂ f x)`.
          ext x u
          change u ∈ (2 : ℝ) • ((∂ f) x) ↔ u ∈ ((∂ f) x + (∂ f) x)
          constructor
          · intro hu
            rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
            exact Set.mem_add.2 ⟨v, hv, v, hv, by simp [two_smul]⟩
          · intro hu
            rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
            have hconv : Convex ℝ ((∂ f) x) := convex_subdifferential f x
            have hmid :
                (1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂ ∈ (∂ f) x :=
              hconv hu₁ hu₂ (by norm_num) (by norm_num) (by norm_num)
            refine Set.mem_smul_set.mpr ?_
            refine ⟨(1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂, hmid, ?_⟩
            calc
              (2 : ℝ) • ((1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂)
                  = ((2 : ℝ) * (1 / 2 : ℝ)) • u₁ +
                      ((2 : ℝ) * (1 - 1 / 2 : ℝ)) • u₂ := by
                        simp [smul_add, smul_smul]
              _ = (1 : ℝ) • u₁ + (1 : ℝ) • u₂ := by norm_num
              _ = u₁ + u₂ := by simp

/-- Helper for Remark 16.46: Corollary 16.30 identifies the range of `∂ (f∗[hf])` with the
domain of the primal subdifferential `∂ f`. -/
theorem range_subdifferential_gammaZeroConjugate_eq_dom_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    (∂ (f∗[hf]) : SetValuedOperator H H).range = SetValuedOperator.dom (∂ f) := by
  -- Rewrite `∂ (f∗[hf])` as the inverse graph of `∂ f`, then use the owner range/domain API.
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf]
  simpa using SetValuedOperator.range_inverse (∂ f : SetValuedOperator H H)

/-- Helper for Remark 16.46: if `0` is not in the range of `∂ f`, then it is not in the range of
`∂ f + ∂ f` either, because every subdifferential fiber is convex. -/
theorem zero_not_mem_range_add_self_of_zero_not_mem_range_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)}
    (hzero : (0 : H) ∉ (∂ f : SetValuedOperator H H).range) :
    (0 : H) ∉ ((∂ f : SetValuedOperator H H) + ∂ f).range := by
  intro hzero_add
  rcases (SetValuedOperator.mem_range_iff
    ((∂ f : SetValuedOperator H H) + ∂ f) (0 : H)).1 hzero_add with ⟨x, hx⟩
  rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
  have hconv : Convex ℝ ((∂ f) x) := by
    -- Subdifferential fibers are convex, so they contain the midpoint of any two elements.
    simpa using convex_subdifferential f x
  have hmid_raw :
      (1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v ∈ (∂ f) x := by
    -- Average the two fiber elements whose sum is zero.
    exact hconv hu hv (by norm_num) (by norm_num) (by norm_num)
  have hmid : (0 : H) ∈ (∂ f) x := by
    -- The midpoint is zero because `u + v = 0`.
    have hcomb : (1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v = (0 : H) := by
      calc
        (1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v
            = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v := by norm_num
        _ = (1 / 2 : ℝ) • (u + v) := by rw [smul_add]
        _ = 0 := by simp [huv]
    rw [← hcomb]
    exact hmid_raw
  have hzero_range : (0 : H) ∈ (∂ f : SetValuedOperator H H).range := by
    exact (SetValuedOperator.mem_range_iff (∂ f : SetValuedOperator H H) (0 : H)).2 ⟨x, hmid⟩
  exact hzero hzero_range

/-- Helper for Remark 16.46: the Remark 16.28 counterexample has `0` outside the range of the
subdifferential of its conjugate. -/
theorem zero_not_mem_range_remark1628ConjugateSubdifferential :
    (0 : ℝ²) ∉
      (∂ (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) :
        SetValuedOperator ℝ² ℝ²).range := by
  -- Route correction: transport the Remark 16.28 domain obstruction through Corollary 16.30.
  rw [range_subdifferential_gammaZeroConjugate_eq_dom_subdifferential
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero]
  rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
  simp

/-- Helper for Remark 16.46: the two boundary points from Remark 16.28 lie in the range of the
subdifferential of the conjugate counterexample. -/
theorem boundaryEndpoints_mem_range_remark1628ConjugateSubdifferential :
    (!₂[(0 : ℝ), (-1 : ℝ)] :
        ℝ²) ∈
        (∂ (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) :
          SetValuedOperator ℝ² ℝ²).range ∧
      (!₂[(0 : ℝ), (1 : ℝ)] :
        ℝ²) ∈
        (∂ (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) :
          SetValuedOperator ℝ² ℝ²).range := by
  -- The same Corollary 16.30 rewrite turns the two geometric boundary points into domain points.
  constructor
  · rw [range_subdifferential_gammaZeroConjugate_eq_dom_subdifferential
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero]
    rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
    simp
  · rw [range_subdifferential_gammaZeroConjugate_eq_dom_subdifferential
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero]
    rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
    simp

/-- Helper for Remark 16.46: the self-sum of the Remark 16.28 counterexample has `0` in the
range of its subdifferential. -/
theorem zero_mem_range_subdifferential_pointwiseAdd_self_remark1628 :
    (0 : ℝ²) ∈
      (∂ (oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample) :
        SetValuedOperator ℝ² ℝ²).range := by
  let xMin : ℝ² := !₂[(1 : ℝ), (0 : ℝ)]
  have hx_zero : (oneSubSqrtAbsMaxCounterexample xMin : EReal) = 0 := by
    -- The point `!₂[1,0]` is a zero-value point of the counterexample.
    rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue,
      oneSubSqrtIciExtension]
    simp [xMin]
  have hnonneg :
      ∀ y : ℝ², (0 : EReal) ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := by
    intro y
    -- The absolute-value branch keeps the maximum nonnegative at every point.
    have habs :
        (0 : EReal) ≤ (((|y 1| : ℝ) : EReal)) := by
      positivity
    calc
      (0 : EReal) ≤ (((|y 1| : ℝ) : EReal)) := habs
      _ ≤ oneSubSqrtAbsMaxValue y := by
        simp [oneSubSqrtAbsMaxValue]
      _ = (oneSubSqrtAbsMaxCounterexample y : EReal) := by
        rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply]
  have hzero_sub :
      (0 : ℝ²) ∈ (∂ oneSubSqrtAbsMaxCounterexample) xMin := by
    -- The zero vector is a subgradient at a global minimizer.
    rw [mem_subdifferential_iff]
    intro y
    have hinner_zero : ((inner ℝ (y - xMin) (0 : ℝ²) : ℝ) : EReal) = 0 := by
      simp
    have hx_le :
        (oneSubSqrtAbsMaxCounterexample xMin : EReal) ≤
          (oneSubSqrtAbsMaxCounterexample y : EReal) := by
      calc
        (oneSubSqrtAbsMaxCounterexample xMin : EReal) = 0 := hx_zero
        _ ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := hnonneg y
    simpa [hinner_zero] using hx_le
  have hzero_sum :
      (0 : ℝ²) ∈
        ((∂ oneSubSqrtAbsMaxCounterexample) + ∂ oneSubSqrtAbsMaxCounterexample) xMin := by
    -- Reuse the same zero subgradient in both summands.
    exact Set.mem_add.2 ⟨0, hzero_sub, 0, hzero_sub, by simp⟩
  have hsum_sub :
      (0 : ℝ²) ∈
        (∂ (oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample)) xMin := by
    -- Rewrite the self-sum subdifferential by the canonical scaling identity already proved above.
    simpa [subdifferential_pointwiseAdd_self_eq_add_self oneSubSqrtAbsMaxCounterexample] using
      hzero_sum
  exact
    (SetValuedOperator.mem_range_iff
      (∂ (oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample) :
        SetValuedOperator ℝ² ℝ²) 0).2 ⟨xMin, hsum_sub⟩

/-- Helper for Remark 16.46: the zero vector is a subgradient of the Remark 16.28
counterexample at the minimizer `!₂[1,0]`. -/
theorem zero_mem_subdifferential_oneSubSqrtAbsMaxCounterexample_atMinimizer :
    (0 : ℝ²) ∈ (∂ oneSubSqrtAbsMaxCounterexample) !₂[(1 : ℝ), (0 : ℝ)] := by
  have hx_zero : (oneSubSqrtAbsMaxCounterexample !₂[(1 : ℝ), (0 : ℝ)] : EReal) = 0 := by
    -- The concrete base point is a zero-value minimizer of the counterexample.
    rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue,
      oneSubSqrtIciExtension]
    simp
  have hnonneg :
      ∀ y : ℝ², (0 : EReal) ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := by
    intro y
    -- The absolute-value branch keeps the defining maximum nonnegative.
    have habs :
        (0 : EReal) ≤ (((|y 1| : ℝ) : EReal)) := by
      positivity
    calc
      (0 : EReal) ≤ (((|y 1| : ℝ) : EReal)) := habs
      _ ≤ oneSubSqrtAbsMaxValue y := by
            simp [oneSubSqrtAbsMaxValue]
      _ = (oneSubSqrtAbsMaxCounterexample y : EReal) := by
            rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply]
  -- At a global minimizer, the zero affine form satisfies every subgradient inequality.
  rw [mem_subdifferential_iff]
  intro y
  have hinner_zero : ((inner ℝ (y - !₂[(1 : ℝ), (0 : ℝ)]) (0 : ℝ²) : ℝ) : EReal) = 0 := by
    simp
  have hx_le :
      (oneSubSqrtAbsMaxCounterexample !₂[(1 : ℝ), (0 : ℝ)] : EReal) ≤
        (oneSubSqrtAbsMaxCounterexample y : EReal) := by
    calc
      (oneSubSqrtAbsMaxCounterexample !₂[(1 : ℝ), (0 : ℝ)] : EReal) = 0 := hx_zero
      _ ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := hnonneg y
  simpa [hinner_zero] using hx_le

/-- Helper for Remark 16.46: the conjugate of the Remark 16.28 counterexample is finite at
the origin. -/
theorem zero_mem_dom_remark1628Conjugate :
    (0 : ℝ²) ∈ dom
      (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero] : ℝ² →
        EReal) := by
  -- The minimizer subgradient at `!₂[1,0]` yields a finite conjugate value at `0`.
  have hdom :
      (0 : ℝ²) ∈ dom (oneSubSqrtAbsMaxCounterexample.asEReal∗) :=
    mem_dom_conjugate_of_mem_subdifferential
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero
      zero_mem_subdifferential_oneSubSqrtAbsMaxCounterexample_atMinimizer
  simpa [gammaZeroConjugate_apply] using hdom

/-- Helper for Remark 16.46: the conjugate of the self-sum from Remark 16.28 has a subgradient
at `0`. -/
theorem zero_mem_subdifferentialDom_pointwiseAdd_self_conjugate_remark1628 :
    (0 : ℝ²) ∈
      SetValuedOperator.dom
        (∂ (((oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample).asEReal∗) :
          ℝ² → EReal)) := by
  have hGG :
      oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample ∈ Γ₀(ℝ²) := by
    -- The self-sum stays in `Γ₀(ℝ²)` because the original counterexample has nonempty domain.
    simpa [Set.inter_self] using
      pointwiseAdd_mem_gammaZero oneSubSqrtAbsMaxCounterexample oneSubSqrtAbsMaxCounterexample
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero
        (by simpa [Set.inter_self] using
          oneSubSqrtAbsMaxCounterexample_mem_gammaZero.2.nonempty)
  rcases (SetValuedOperator.mem_range_iff
    (∂ (oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample) :
      SetValuedOperator ℝ² ℝ²) (0 : ℝ²)).1
      zero_mem_range_subdifferential_pointwiseAdd_self_remark1628 with ⟨x, hx⟩
  -- Transport the active primal subgradient through Corollary 16.30.
  rw [SetValuedOperator.mem_dom_iff]
  refine ⟨x, ?_⟩
  -- Compare the raw conjugate owner with the packaged `Γ₀` conjugate before applying Corollary
  -- 16.30.
  change x ∈
    (∂ ((oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample)∗[hGG]))
      (0 : ℝ²)
  exact (mem_subdifferential_gammaZeroConjugate_iff hGG).2 hx

/-- Helper for Remark 16.46: specializing the exact dual formula to the identity map rewrites the
packaged owner `(f + g)^*` to the raw infimal convolution `f^* □ g^*`. -/
theorem exactDualInfimalConvolutionFormula_id_eq_rawConjugateInfimalConvolution
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hformula : ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ H)) :
    (f + g).asEReal∗ = ((((f∗[hf]) □ (g∗[hg])) : H → EReal)) := by
  -- Route correction: normalize the private identity-map owner once, then reuse the raw equality.
  ext u
  have hu := congrFun hformula.eq u
  have hpost :
      ((((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗) : H → EReal)) = g.asEReal∗ := by
    simpa [ContinuousLinearMap.adjoint_id] using
      infimalPostcomposition_id_eq_ereal (φ := g.asEReal∗)
  -- Expose the private identity-map dual owner before simplifying it to the raw infimal
  -- convolution.
  change ((compositePrimalObjective f g (ContinuousLinearMap.id ℝ H))∗ u) =
      ((((f.asEReal∗) □ (((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗))) : H → EReal) u)
    at hu
  rw [hpost] at hu
  simpa [compositePrimalObjective, primalObjective, Function.comp,
    ContinuousLinearMap.adjoint_id,
    gammaZeroConjugate_apply] using hu

/-- Helper for Remark 16.46: a single pointwise gap between `(f + g)^*` and `f^* □ g^*`
already rules out the identity-map exact dual formula. -/
theorem notExactDualInfimalConvolutionFormulaId_of_conjugateGapAt
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) {u : H}
    (hgap :
      (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : H → EReal) u)) :
    ¬ ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ H) := by
  intro hformula
  have heq :=
    exactDualInfimalConvolutionFormula_id_eq_rawConjugateInfimalConvolution hf hg hformula
  -- Evaluate the identity-map equality at the bad dual point `u` and contradict the gap.
  exact hgap (congrFun heq u)

/-- Helper for Remark 16.46: the Remark 16.28 self-infimal-convolution is finite at `0`. -/
theorem zero_mem_dom_infimalConvolution_remark1628ConjugateSelf :
    (0 : ℝ²) ∈ dom
      ((((oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) □
        (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero])) :
          ℝ² → EReal)) := by
  let Gc :
      ℝ² → Set.Ioi (⊥ : EReal) :=
    oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]
  have hzero_dom : ((Gc (0 : ℝ²) : EReal)) < ⊤ := by
    -- The origin is already finite for the conjugate itself.
    simpa [Gc] using zero_mem_dom_remark1628Conjugate
  have hupper :
      ((((Gc □ Gc) : ℝ² → EReal) (0 : ℝ²))) ≤
        (Gc (0 : ℝ²) : EReal) + (Gc (0 : ℝ²) : EReal) := by
    -- Evaluate the infimal convolution at the split `y = 0`.
    rw [infimalConvolution_apply]
    simpa using
      (iInf_le (fun y : ℝ² ↦ (Gc y : EReal) + (Gc ((0 : ℝ²) - y) : EReal)) (0 : ℝ²))
  -- The candidate split has finite value, so the infimal convolution is finite as well.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hupper
    (lt_top_iff_ne_top.mpr (EReal.add_ne_top (ne_of_lt hzero_dom) (ne_of_lt hzero_dom)))

/-- Helper for Remark 16.46: under the assumed exact dual formula, the Remark 16.28
self-infimal-convolution has a subgradient at `0`. -/
theorem zero_mem_subdifferentialDom_infimalConvolution_remark1628ConjugateSelf_of_formula
    (hformula : ExactDualInfimalConvolutionFormula
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero
      (ContinuousLinearMap.id ℝ ℝ²)) :
    (0 : ℝ²) ∈
      SetValuedOperator.dom
        (∂ ((((oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) □
          (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero])) :
            ℝ² → EReal))) := by
  -- Rewrite the already proved point of `dom ∂((G + G)^*)` through the normalized raw identity.
  have heq :=
    exactDualInfimalConvolutionFormula_id_eq_rawConjugateInfimalConvolution
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero hformula
  simpa [heq] using zero_mem_subdifferentialDom_pointwiseAdd_self_conjugate_remark1628

omit [CompleteSpace H] in
/-- Helper for Remark 16.46: if the same subgradient of a `Γ₀(H)` function is active at `x` and
`-x`, then it is also active at the midpoint `0`. -/
theorem mem_subdifferential_zero_of_mem_subdifferential_neg
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : u ∈ (∂ f) x) (hneg : u ∈ (∂ f) (-x)) :
    u ∈ (∂ f) (0 : H) := by
  have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
    exact ⟨u, hx⟩
  have hneg_dom : -x ∈ SetValuedOperator.dom (∂ f) := by
    exact ⟨u, hneg⟩
  have hx_eff : x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hx_dom
  have hneg_eff : -x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hneg_dom
  have hconj_eq_x :=
    (mem_subdifferential_iff_fenchel_young_eq f hf.2.nonempty x u).1 hx
  have hconj_eq_neg :=
    (mem_subdifferential_iff_fenchel_young_eq f hf.2.nonempty (-x) u).1 hneg
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_eff)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfneg_top : (f (-x) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hneg_eff)
  have hfneg_bot : (f (-x) : EReal) ≠ ⊥ := ne_of_gt (f (-x)).2
  have hconj_top : f.asEReal∗ u ≠ ⊤ :=
    conjugate_value_ne_top_of_mem_subdifferential f hf.2.nonempty hx
  have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty u
  have hconj_eq_x_real :
      (f x : EReal).toReal + (f.asEReal∗ u).toReal = inner ℝ x u := by
    -- Convert the Fenchel--Young equality at `x` to `ℝ`.
    have htmp := congrArg EReal.toReal hconj_eq_x
    rw [EReal.toReal_add hfx_top hfx_bot hconj_top hconj_bot] at htmp
    exact htmp
  have hconj_eq_neg_real :
      (f (-x) : EReal).toReal + (f.asEReal∗ u).toReal = inner ℝ (-x) u := by
    -- Convert the symmetric Fenchel--Young equality at `-x` to `ℝ`.
    have htmp := congrArg EReal.toReal hconj_eq_neg
    rw [EReal.toReal_add hfneg_top hfneg_bot hconj_top hconj_bot] at htmp
    exact htmp
  have hconv_zero :
      (f (0 : H) : EReal) ≤
        ((1 / 2 : ℝ) : EReal) * (f x : EReal) +
          (1 - (1 / 2 : ℝ) : EReal) * (f (-x) : EReal) := by
    -- Jensen convexity at the symmetric pair `(x,-x)` evaluates the midpoint at `0`.
    have harg :
        ((2⁻¹ : ℝ) • x + -((1 - (2⁻¹ : ℝ)) • x)) = (0 : H) := by
      norm_num
    have htmp :=
      hf.2.ineq (x := x) hx_eff (y := -x) hneg_eff (α := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)
    simpa [smul_neg, harg] using htmp
  have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
  have hhalf_x_top : ((1 / 2 : ℝ) : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl ?_, Or.inl (EReal.coe_ne_top _), Or.inr hfx_top⟩
    positivity
  have hhalf_neg_top :
      (1 - (1 / 2 : ℝ) : EReal) * (f (-x) : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl ?_, Or.inl (EReal.coe_ne_top _), Or.inr hfneg_top⟩
    exact_mod_cast (show 0 ≤ 1 - (1 / 2 : ℝ) by norm_num)
  have hweighted_top :
      ((1 / 2 : ℝ) : EReal) * (f x : EReal) +
          (1 - (1 / 2 : ℝ) : EReal) * (f (-x) : EReal) ≠ ⊤ :=
    EReal.add_ne_top hhalf_x_top hhalf_neg_top
  have hfzero_top : (f (0 : H) : EReal) ≠ ⊤ := by
    -- The convex upper bound keeps the midpoint finite.
    exact ne_of_lt (lt_of_le_of_lt hconv_zero (lt_of_le_of_ne le_top hweighted_top))
  have hfzero_bot : (f (0 : H) : EReal) ≠ ⊥ := ne_of_gt (f (0 : H)).2
  have hconv_zero_real :
      (f (0 : H) : EReal).toReal ≤
        ((f x : EReal).toReal + (f (-x) : EReal).toReal) / 2 := by
    -- Rewrite the convex midpoint bound to a scalar inequality.
    have hhalf_sub : (1 - (1 / 2 : ℝ) : EReal) = ((1 / 2 : ℝ) : EReal) := by
      exact_mod_cast (show (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num)
    have htmp :=
      EReal.toReal_le_toReal hconv_zero hfzero_bot hweighted_top
    rw [hhalf_sub, ← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfneg_top hfneg_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at htmp
    have htmp' :
        (f (0 : H) : EReal).toReal ≤
          (1 / 2 : ℝ) * (f x : EReal).toReal +
            (1 / 2 : ℝ) * (f (-x) : EReal).toReal := by
      exact_mod_cast htmp
    nlinarith
  have hfy_zero :
      ((0 : ℝ) : EReal) ≤ (f (0 : H) : EReal) + f.asEReal∗ u := by
    -- Fenchel--Young supplies the reverse inequality at the midpoint.
    simpa using fenchel_young_inequality (isProper_of_mem_gammaZero hf) (0 : H) u
  have hsum_zero_top : (f (0 : H) : EReal) + f.asEReal∗ u ≠ ⊤ :=
    EReal.add_ne_top hfzero_top hconj_top
  have hsum_zero_bot : (f (0 : H) : EReal) + f.asEReal∗ u ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f (0 : H)).2, bot_lt_iff_ne_bot.mpr hconj_bot⟩
  have hfy_zero_real :
      0 ≤ (f (0 : H) : EReal).toReal + (f.asEReal∗ u).toReal := by
    -- Convert the Fenchel--Young lower bound at `0` to `ℝ`.
    have htmp := EReal.toReal_le_toReal hfy_zero (EReal.coe_ne_bot 0) hsum_zero_top
    rw [EReal.toReal_add hfzero_top hfzero_bot hconj_top hconj_bot] at htmp
    simpa using htmp
  have hsum_zero_real_le :
      (f (0 : H) : EReal).toReal + (f.asEReal∗ u).toReal ≤ 0 := by
    -- The two symmetric contact equalities force the midpoint contact inequality in the reverse
    -- direction.
    have hconj_eq_neg_real' :
        (f (-x) : EReal).toReal + (f.asEReal∗ u).toReal = -inner ℝ x u := by
      simpa using hconj_eq_neg_real
    linarith [hconv_zero_real, hconj_eq_x_real, hconj_eq_neg_real']
  have hconj_eq_zero :
      (f (0 : H) : EReal) + f.asEReal∗ u = ((0 : ℝ) : EReal) := by
    -- The lower and upper bounds match, so Fenchel--Young is exact at `0`.
    have hsum_zero_real_eq :
        (f (0 : H) : EReal).toReal + (f.asEReal∗ u).toReal = 0 :=
      le_antisymm hsum_zero_real_le hfy_zero_real
    apply
      (EReal.toReal_eq_toReal hsum_zero_top hsum_zero_bot (EReal.coe_ne_top 0)
        (EReal.coe_ne_bot 0)).mp
    rw [EReal.toReal_add hfzero_top hfzero_bot hconj_top hconj_bot]
    simpa using hsum_zero_real_eq
  exact
    (mem_subdifferential_iff_fenchel_young_eq f hf.2.nonempty (0 : H) u).2
      (by simpa using hconj_eq_zero)

/-- Helper for Remark 16.46: at the origin, the subdifferential of the support function of a
nonempty closed convex set is the set itself. -/
theorem subdifferential_supportFunction_eq_self_at_zero_of_nonempty_isClosed_convex_local
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (∂ σ[C]) 0 = C := by
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hargmin : Argmin ((ι[C]).asEReal) = C := by
    -- The indicator attains its minimum value exactly on the underlying set.
    ext x
    constructor
    · intro hx
      rw [mem_argmin_iff, isMinOn_univ_iff] at hx
      by_contra hxC
      rcases hC_nonempty with ⟨y, hy⟩
      simpa [indicator_apply, hxC, hy] using hx y
    · intro hx
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro y
      by_cases hy : y ∈ C <;> simp [indicator_apply, hx, hy]
  -- Rewrite the support function as the conjugate of the indicator, then invoke Proposition 16.33
  -- on the zero dual point.
  calc
    (∂ σ[C]) 0 = (∂ (((ι[C]).asEReal)∗)) 0 := by
      rw [← conjugate_indicator_eq_supportFunction (C := C)]
    _ = Argmin ((ι[C]).asEReal) := by
      simpa [gammaZeroConjugate_apply] using
        (argmin_eq_subdifferential_gammaZeroConjugate_zero (ι[C]) hC_gamma).symm
    _ = C := hargmin

/-- Helper for Remark 16.46: the concrete minimizer `!₂[1,0]` is a subgradient of the conjugate
of the Remark 16.28 self-sum at the dual point `0`. -/
theorem remark1628Minimizer_mem_subdifferential_pointwiseAdd_self_conjugate_at_zero :
    (!₂[(1 : ℝ), (0 : ℝ)] : ℝ²) ∈
      (∂ (((oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample).asEReal∗) :
        ℝ² → EReal)) (0 : ℝ²) := by
  let xMin : ℝ² := !₂[(1 : ℝ), (0 : ℝ)]
  have hGG :
      oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample ∈ Γ₀(ℝ²) := by
    -- The self-sum stays in `Γ₀(ℝ²)` because the original counterexample already does.
    simpa [Set.inter_self] using
      pointwiseAdd_mem_gammaZero oneSubSqrtAbsMaxCounterexample oneSubSqrtAbsMaxCounterexample
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero
        (by simpa [Set.inter_self] using
          oneSubSqrtAbsMaxCounterexample_mem_gammaZero.2.nonempty)
  have hzero_sub :
      (0 : ℝ²) ∈
        (∂ (oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample)) xMin := by
    -- The zero subgradient at the primal minimizer survives the self-sum rewrite.
    have hzero_base :
        (0 : ℝ²) ∈ (∂ oneSubSqrtAbsMaxCounterexample) xMin := by
      simpa [xMin] using zero_mem_subdifferential_oneSubSqrtAbsMaxCounterexample_atMinimizer
    have hzero_add :
        (0 : ℝ²) ∈
          ((∂ oneSubSqrtAbsMaxCounterexample) + ∂ oneSubSqrtAbsMaxCounterexample) xMin := by
      exact Set.mem_add.2 ⟨0, hzero_base, 0, hzero_base, by simp⟩
    simpa [subdifferential_pointwiseAdd_self_eq_add_self oneSubSqrtAbsMaxCounterexample] using
      hzero_add
  -- Corollary 16.30 transports the explicit primal subgradient to the conjugate owner at `0`.
  change xMin ∈
    (∂ ((oneSubSqrtAbsMaxCounterexample + oneSubSqrtAbsMaxCounterexample)∗[hGG]))
      (0 : ℝ²)
  exact (mem_subdifferential_gammaZeroConjugate_iff hGG).2 hzero_sub

/-- Helper for Remark 16.46: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem attouchBrezis_euclideanSpace_fin2_eq (x : ℝ²) :
    x = !₂[x 0, x 1] := by
  -- Coordinatewise extensionality reduces equality in `EuclideanSpace ℝ (Fin 2)` to two cases.
  ext i
  fin_cases i <;> simp

/-- Helper for Remark 16.46: the Remark 15.4 quadrant used in the Attouch--Brezis candidate. -/
private abbrev attouchBrezisQuadrant : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ 0 ≤ x 1}

/-- Helper for Remark 16.46: the vertical axis used in the Attouch--Brezis candidate. -/
private abbrev attouchBrezisVerticalAxis : Set ℝ² := {x : ℝ² | x 0 = 0}

/-- Helper for Remark 16.46: the positive vertical ray used in the Attouch--Brezis candidate. -/
private abbrev attouchBrezisVerticalRay : Set ℝ² := {x : ℝ² | x 0 = 0 ∧ 0 ≤ x 1}

/-- Helper for Remark 16.46: the explicit quadrant square-root branch from Remark 15.4(1). -/
private noncomputable def attouchBrezisQuadrantValue : ℝ² → EReal :=
  fun x : ℝ² ↦
    if x ∈ attouchBrezisQuadrant then
      (((-Real.sqrt (x 0 * x 1) : ℝ) : EReal))
    else
      ⊤

/-- Helper for Remark 16.46: the explicit quadrant square-root branch is proper as an
`EReal`-valued owner. -/
private theorem attouchBrezisQuadrantValue_isProper :
    IsProper attouchBrezisQuadrantValue := by
  -- The branch never hits `-∞`, and it is finite at the origin.
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro x
    by_cases hxQ : x ∈ attouchBrezisQuadrant
    · simp [attouchBrezisQuadrantValue, hxQ]
    · simp [attouchBrezisQuadrantValue, hxQ]
  · change attouchBrezisQuadrantValue 0 < ⊤
    simp [attouchBrezisQuadrantValue, attouchBrezisQuadrant]

/-- Helper for Remark 16.46: the packaged Remark 15.4 quadrant owner. -/
private noncomputable def attouchBrezisQuadrantOwner : ℝ² → Set.Ioi (⊥ : EReal) :=
  properIoi attouchBrezisQuadrantValue attouchBrezisQuadrantValue_isProper

/-- Helper for Remark 16.46: on the Remark 15.4 candidate, the explicit sum is the indicator of
the positive vertical ray. -/
private theorem attouchBrezis_pointwiseAdd_eq_indicator_verticalRay :
    attouchBrezisQuadrantOwner + ι[attouchBrezisVerticalAxis] = ι[attouchBrezisVerticalRay] := by
  funext x
  apply Subtype.ext
  by_cases hxC : x ∈ attouchBrezisVerticalRay
  · have hxL : x ∈ attouchBrezisVerticalAxis := hxC.1
    have hxQ : x ∈ attouchBrezisQuadrant := by
      -- On the ray, the first coordinate is `0` and the second is nonnegative.
      refine ⟨?_, hxC.2⟩
      simpa [hxC.1]
    -- On `C`, both summands vanish, so the sum equals the indicator value `0`.
    simp [attouchBrezisQuadrantOwner, attouchBrezisQuadrantValue, indicator_apply, hxC, hxL, hxQ,
      hxC.1]
  · by_cases hxL : x ∈ attouchBrezisVerticalAxis
    · have hxQ : x ∉ attouchBrezisQuadrant := by
        -- Route correction: off `C` but on the axis, the only failure is the negative
        -- second coordinate, so the quadrant branch is already `⊤`.
        intro hxQ
        exact hxC ⟨hxL, hxQ.2⟩
      simp [attouchBrezisQuadrantOwner, attouchBrezisQuadrantValue, indicator_apply, hxC, hxL, hxQ]
    · by_cases hxQ : x ∈ attouchBrezisQuadrant
      · have hf_ne_bot : (attouchBrezisQuadrantOwner x : EReal) ≠ ⊥ := by
          -- The quadrant branch is a real value, hence never `⊥`.
          simp [attouchBrezisQuadrantOwner, attouchBrezisQuadrantValue, hxQ]
        have hg_top : ((ι[attouchBrezisVerticalAxis] x : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
          -- Off the axis, the indicator contributes `⊤`.
          simp [indicator_apply, hxL]
        -- The non-bottom quadrant value absorbs the `⊤`, matching the indicator target.
        change
          (attouchBrezisQuadrantOwner x : EReal) +
              ((ι[attouchBrezisVerticalAxis] x : Set.Ioi (⊥ : EReal)) : EReal) =
            ((ι[attouchBrezisVerticalRay] x : Set.Ioi (⊥ : EReal)) : EReal)
        rw [hg_top, EReal.add_top_of_ne_bot hf_ne_bot]
        simp [indicator_apply, hxC]
      · simp [attouchBrezisQuadrantOwner, attouchBrezisQuadrantValue, indicator_apply, hxC, hxL, hxQ]

/-- Helper for Remark 16.46: the conjugate of the vertical-axis indicator is the indicator of the
horizontal axis. -/
private theorem attouchBrezis_verticalAxisConjugate_eq_indicator_horizontalAxis :
    ((ι[attouchBrezisVerticalAxis]).asEReal∗) = (ι[{u : ℝ² | u 1 = 0}]).asEReal := by
  let V : Submodule ℝ ℝ² :=
    { carrier := attouchBrezisVerticalAxis
      zero_mem' := by simp [attouchBrezisVerticalAxis]
      add_mem' := by
        intro x y hx hy
        have hx0 : x 0 = 0 := hx
        have hy0 : y 0 = 0 := hy
        calc
          (x + y) 0 = x 0 + y 0 := by simp
          _ = 0 := by simp [hx0, hy0]
      smul_mem' := by
        intro a x hx
        have hx0 : x 0 = 0 := hx
        calc
          (a • x) 0 = a * x 0 := by simp
          _ = 0 := by simp [hx0] }
  have horth : (Vᗮ : Set ℝ²) = {u : ℝ² | u 1 = 0} := by
    ext u
    constructor
    · intro hu
      have hu_test : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ = 0 := by
        -- Testing orthogonality on the unit vertical vector isolates the second coordinate.
        exact (V.mem_orthogonal u).mp hu !₂[(0 : ℝ), 1] (by simp [V, attouchBrezisVerticalAxis])
      have hcoord : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ = u 1 := by
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp
        have hinner : ⟪(1 : ℝ), u 1⟫_ℝ = u 1 * 1 := by
          exact RCLike.inner_apply (1 : ℝ) (u 1)
        rw [hinner]
        ring
      simpa [hcoord] using hu_test
    · intro hu
      exact (V.mem_orthogonal u).2 <| by
        intro x hx
        have hx0 : x 0 = 0 := hx
        -- On the vertical axis, only the second-coordinate inner product survives.
        rw [PiLp.inner_apply, Fin.sum_univ_two, hx0, hu]
        simp
  calc
    ((ι[attouchBrezisVerticalAxis]).asEReal∗) = (((ι[(V : Set ℝ²)]).asEReal)∗) := by
      rfl
    _ = (ι[(Vᗮ : Set ℝ²)]).asEReal :=
      conjugate_indicator_submodule_eq_indicator_orthogonal (V := V)
    _ = (ι[{u : ℝ² | u 1 = 0}]).asEReal := by
      exact congrArg (fun S : Set ℝ² ↦ (ι[S]).asEReal) horth

/-- Helper for Remark 16.46: when the second dual coordinate is nonnegative, the conjugate of the
Attouch--Brezis quadrant branch is `⊤`. -/
private theorem attouchBrezis_quadrantConjugate_eq_top_of_nonnegativeSecond
    (a b : ℝ) (hb : 0 ≤ b) :
    attouchBrezisQuadrantValue∗ !₂[a, b] = ⊤ := by
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  let t : ℝ := |M| + |a| + 1
  let x : ℝ² := !₂[1, t ^ 2]
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hxQ : x ∈ attouchBrezisQuadrant := by
    -- The witness `x = (1,t²)` stays in the quadrant for every real `t`.
    dsimp [x, attouchBrezisQuadrant]
    constructor <;> positivity
  have hsqrt : Real.sqrt (x 0 * x 1) = t := by
    -- On this witness, the square root simplifies to `sqrt (t²) = t` because `t > 0`.
    dsimp [x]
    rw [show (1 : ℝ) * t ^ 2 = t ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hinner_real : ⟪x, !₂[a, b]⟫_ℝ = a + b * t ^ 2 := by
    -- Expanding the two-coordinate inner product gives the affine term `a + b t²`.
    dsimp [x]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    norm_num
    have h1 : ⟪(1 : ℝ), a⟫_ℝ = a * 1 := by
      exact RCLike.inner_apply (1 : ℝ) a
    have h2 : ⟪t ^ 2, b⟫_ℝ = b * t ^ 2 := by
      exact RCLike.inner_apply (t ^ 2) b
    rw [h1, h2]
    ring
  have hinner :
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) = ((a + b * t ^ 2 : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  have hxval : attouchBrezisQuadrantValue x = ((-t : ℝ) : EReal) := by
    -- On the quadrant branch, the value is exactly `-sqrt (x₀ x₁) = -t`.
    simp [attouchBrezisQuadrantValue, hxQ, hsqrt]
  have hterm :
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - attouchBrezisQuadrantValue x =
        ((a + b * t ^ 2 + t : ℝ) : EReal) := by
    calc
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - attouchBrezisQuadrantValue x
          = ((a + b * t ^ 2 : ℝ) : EReal) - ((-t : ℝ) : EReal) := by
              rw [hinner, hxval]
      _ = ((a + b * t ^ 2 + t : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        ring
  have hM_lt_linear : M < a + t := by
    -- The choice `t = |M| + |a| + 1` makes the linear part already exceed `M`.
    dsimp [t]
    nlinarith [le_abs_self M, neg_abs_le a]
  have hM_lt_term : M < a + b * t ^ 2 + t := by
    have hquad_nonneg : 0 ≤ b * t ^ 2 := mul_nonneg hb (sq_nonneg t)
    linarith
  have hvalue :
      ((M : ℝ) : EReal) <
        (((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - attouchBrezisQuadrantValue x) := by
    -- The chosen witness beats the arbitrary finite lower bound `M`.
    have hvalue' : ((M : ℝ) : EReal) < ((a + b * t ^ 2 + t : ℝ) : EReal) := by
      exact_mod_cast hM_lt_term
    simpa [hterm] using hvalue'
  exact lt_of_lt_of_le hvalue
    (le_iSup
      (fun y : ℝ² ↦ ((⟪y, !₂[a, b]⟫_ℝ : ℝ) : EReal) - attouchBrezisQuadrantValue y) x)

local notation "L2Nat" => ℓ²(ℕ, ℝ)

/-- Helper for Remark 16.46: the standard `ℓ²(ℕ,ℝ)` coordinate vectors form an orthonormal
sequence. -/
private theorem l2NatSingle_orthonormal :
    Orthonormal ℝ (fun n : ℕ ↦ (lp.single 2 n (1 : ℝ) : L2Nat)) := by
  -- Compare the coordinate-vector inner products directly against the Kronecker delta.
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [lp.inner_single_left]
  · simp [lp.inner_single_left, hij]

/-- Helper for Remark 16.46: the concrete Hilbert space `ℓ²(ℕ,ℝ)` is not finite-dimensional. -/
private theorem l2Nat_not_finiteDimensional :
    ¬ FiniteDimensional ℝ L2Nat := by
  intro hfd
  let e : ℕ → L2Nat := fun n ↦ lp.single 2 n (1 : ℝ)
  have he : Orthonormal ℝ e := by
    simpa [e] using l2NatSingle_orthonormal
  letI : FiniteDimensional ℝ L2Nat := hfd
  have hfinite : Finite ℕ := LinearIndependent.finite he.linearIndependent
  exact hfinite.not_infinite inferInstance

/-- Helper for Remark 16.46: the odd-coordinate subsequence of an orthonormal family stays
orthonormal after reindexing. -/
private theorem oddIndex_orthonormal_local {e : ℕ → L2Nat}
    (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n + 1)) := by
  -- Reindex the original orthonormal family along the injective odd map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n + 1) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hmn))

/-- Helper for Remark 16.46: the even-coordinate subsequence of an orthonormal family stays
orthonormal after reindexing. -/
private theorem evenIndex_orthonormal_local {e : ℕ → L2Nat}
    (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n)) := by
  -- Reindex the original orthonormal family along the injective even map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) hmn)

/-- Helper for Remark 16.46: each rotated generator belongs to its closed rotated span. -/
private theorem rotatedEvenOddVector_mem_closedSpan_local
    (e : ℕ → L2Nat) (θ : ℕ → ℝ) (n : ℕ) :
    rotated_even_odd_vector e θ n ∈ rotated_even_odd_closed_span e θ := by
  -- The rotated vector is already one of the generators of the defining span.
  exact (Submodule.span ℝ (Set.range (rotated_even_odd_vector e θ))).le_topologicalClosure
    (Submodule.subset_span (by exact ⟨n, rfl⟩))

/-- Helper for Remark 16.46: rotated generators are orthonormal whenever the original sequence is
orthonormal. -/
private theorem rotatedEvenOddInner_kronecker_local
    (e : ℕ → L2Nat) (θ : ℕ → ℝ) (he : Orthonormal ℝ e) (m n : ℕ) :
    ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ n⟫_ℝ =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    -- On the diagonal, the two summands are orthogonal, so the norm square splits.
    have hcross :
        ⟪Real.cos (θ m) • e (2 * m), Real.sin (θ m) • e (2 * m + 1)⟫_ℝ = 0 := by
      have hneq : 2 * m ≠ 2 * m + 1 := by
        omega
      simp [real_inner_smul_left, real_inner_smul_right, he.2 hneq]
    calc
      ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ m⟫_ℝ
          = ‖rotated_even_odd_vector e θ m‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
      _ = ‖Real.cos (θ m) • e (2 * m)‖ ^ 2 + ‖Real.sin (θ m) • e (2 * m + 1)‖ ^ 2 := by
            simpa [pow_two, rotated_even_odd_vector] using
              norm_add_sq_eq_norm_sq_add_norm_sq_real hcross
      _ = Real.cos (θ m) ^ 2 + Real.sin (θ m) ^ 2 := by
            simp [norm_smul, he.1]
      _ = 1 := by
            have htrig := Real.sin_sq_add_cos_sq (θ m)
            linarith
    simp
  · -- Off the diagonal, every inner-product term vanishes by parity and orthonormality.
    have h_even : 2 * m ≠ 2 * n := by
      omega
    have h_even_odd : 2 * m ≠ 2 * n + 1 := by
      omega
    have h_odd_even : 2 * m + 1 ≠ 2 * n := by
      omega
    have h_odd : 2 * m + 1 ≠ 2 * n + 1 := by
      omega
    rw [rotated_even_odd_vector, rotated_even_odd_vector]
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp [hmn, real_inner_smul_left, real_inner_smul_right, he.2 h_even, he.2 h_even_odd,
      he.2 h_odd_even, he.2 h_odd]

/-- Helper for Remark 16.46: the even and odd coordinate functionals agree with the rotated
coordinate functional on each rotated generator. -/
private theorem rotatedCoordinateFunctional_eq_on_generators_local
    (e : ℕ → L2Nat) (θ : ℕ → ℝ) (he : Orthonormal ℝ e) (n m : ℕ) :
    (⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.cos (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) ∧
      (⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.sin (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) := by
  by_cases hnm : n = m
  · subst m
    -- On the diagonal, both coordinates are read directly from the rotated generator.
    have hneq : 2 * n ≠ 2 * n + 1 := by
      omega
    have hself : ‖rotated_even_odd_vector e θ n‖ ^ 2 = 1 := by
      have hinner :
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ = 1 := by
        simpa using rotatedEvenOddInner_kronecker_local e θ he n n
      simpa [real_inner_self_eq_norm_sq] using hinner
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ n⟫_ℝ = Real.cos (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq, he.1 (2 * n)]
        _ = Real.cos (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
              rw [hself]
              ring
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
    · have hneq' : 2 * n + 1 ≠ 2 * n := by
        omega
      calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ n⟫_ℝ = Real.sin (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq', he.1 (2 * n + 1)]
        _ = Real.sin (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
              rw [hself]
              ring
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
  · -- Off the diagonal, both coordinates vanish together with the rotated Kronecker term.
    have h_even : 2 * n ≠ 2 * m := by
      omega
    have h_even_odd : 2 * n ≠ 2 * m + 1 := by
      omega
    have h_odd_even : 2 * n + 1 ≠ 2 * m := by
      omega
    have h_odd : 2 * n + 1 ≠ 2 * m + 1 := by
      omega
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_even, he.2 h_even_odd]
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotatedEvenOddInner_kronecker_local e θ he n m
              rw [hrot]
              ring
    · calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_odd_even, he.2 h_odd]
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotatedEvenOddInner_kronecker_local e θ he n m
              rw [hrot]
              ring

/-- Helper for Remark 16.46: square-summability of `sin (θ n)` forces `cos (θ n)^2` to stay
nonsummable, because the trigonometric identity makes the cosine square eventually bounded below
away from zero. -/
private theorem notSummableCosSq_of_summableSinSq_local
    (θ : ℕ → ℝ)
    (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2)) :
    ¬ Summable (fun n : ℕ ↦ Real.cos (θ n) ^ 2) := by
  intro hcos
  -- Summability forces the sine-square sequence to converge to zero.
  have hsin_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.sin (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hθ_square_summable.tendsto_atTop_zero
  have hsin_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, Real.sin (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hsin_tendsto.eventually_lt_const (by norm_num)
  -- Then the cosine squares are eventually bounded below by `1 / 2`.
  have hcos_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) < Real.cos (θ n) ^ 2 := by
    filter_upwards [hsin_eventually] with n hsin
    have htrig := Real.sin_sq_add_cos_sq (θ n)
    linarith
  -- But a summable real sequence must also converge to zero.
  have hcos_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.cos (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hcos.tendsto_atTop_zero
  have hcos_small :
      ∀ᶠ n : ℕ in Filter.atTop, Real.cos (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hcos_tendsto.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hcos_eventually hcos_small
  rcases hcos_eventually with ⟨N₁, hN₁⟩
  rcases hcos_small with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hgt : (1 / 2 : ℝ) < Real.cos (θ N) ^ 2 := hN₁ N (le_max_left _ _)
  have hlt : Real.cos (θ N) ^ 2 < (1 / 2 : ℝ) := hN₂ N (le_max_right _ _)
  linarith

/-- Helper for Remark 16.46: Example 3.41 yields closed subspaces of `ℓ²(ℕ, ℝ)` with a closure
point outside their algebraic sum. -/
private theorem nonclosedSupWitnessExplicitBadPointData :
    ∃ U V : Submodule ℝ L2Nat,
      IsClosed (U : Set L2Nat) ∧
      IsClosed (V : Set L2Nat) ∧
      ∃ uBad : L2Nat,
        uBad ∈ closure (((U ⊔ V : Submodule ℝ L2Nat) : Set L2Nat)) ∧
        uBad ∉ (U ⊔ V : Submodule ℝ L2Nat) := by
  let e : ℕ → L2Nat := fun n ↦ (lp.single 2 n (1 : ℝ) : L2Nat)
  let θ : ℕ → ℝ := fun n ↦ ((1 : ℝ) / 2) ^ (n + 1)
  have he : Orthonormal ℝ e := by
    simpa [e] using l2NatSingle_orthonormal
  have hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    intro n
    constructor
    · dsimp [θ]
      positivity
    · have hθ_le_one : θ n ≤ 1 := by
        dsimp [θ]
        exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
      linarith [Real.pi_gt_three, hθ_le_one]
  have hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2) := by
    have hθ_summable : Summable θ := by
      have hgeom :
          Summable (fun n : ℕ ↦ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n)) :=
        Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      convert hgeom using 1
      ext n
      simp [θ, pow_succ, mul_comm]
    refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) ?_ hθ_summable
    intro n
    have hθ_nonneg : 0 ≤ θ n := (hθ n).1.le
    have hθ_le_one : θ n ≤ 1 := by
      dsimp [θ]
      exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
    calc
      Real.sin (θ n) ^ 2 ≤ θ n ^ 2 := Real.sin_sq_le_sq
      _ ≤ θ n := by nlinarith
  let U : Submodule ℝ L2Nat := even_indexed_closed_span e
  let V : Submodule ℝ L2Nat := rotated_even_odd_closed_span e θ
  have hU_closed : IsClosed (U : Set L2Nat) := by
    simpa [U] using isClosed_even_indexed_closed_span e
  have hV_closed : IsClosed (V : Set L2Nat) := by
    simpa [V] using isClosed_rotated_even_odd_closed_span e θ
  have hUV_not_closed :
      ¬ IsClosed (((U ⊔ V : Submodule ℝ L2Nat) : Set L2Nat)) := by
    simpa [U, V] using
      not_isClosed_sup_even_indexed_closed_span_rotated_even_odd_closed_span
        e θ he hθ hθ_square_summable
  let S : Set L2Nat := ((U ⊔ V : Submodule ℝ L2Nat) : Set L2Nat)
  have hbad :
      ∃ uBad : L2Nat, uBad ∈ closure S ∧ uBad ∉ S := by
    by_contra hno
    have hsubset : closure S ⊆ S := by
      intro x hx
      by_contra hxS
      exact hno ⟨x, hx, hxS⟩
    have hclosedS : IsClosed S := by
      rw [← closure_eq_iff_isClosed]
      exact Set.Subset.antisymm hsubset subset_closure
    exact hUV_not_closed hclosedS
  rcases hbad with ⟨uBad, huBad_closure, huBad_not_mem⟩
  exact ⟨U, V, hU_closed, hV_closed, uBad, huBad_closure, huBad_not_mem⟩

/-- Helper for Remark 16.46: `ℓ²(ℕ,ℝ)` contains closed subspaces with nonclosed algebraic sum,
and we package one explicit point in the closure outside that sum. -/
private theorem existsNonclosedSupPair_l2 :
    ∃ U V : Submodule ℝ L2Nat,
      IsClosed (U : Set L2Nat) ∧
      IsClosed (V : Set L2Nat) ∧
      ∃ uBad : L2Nat,
        uBad ∈ closure (((U ⊔ V : Submodule ℝ L2Nat) : Set L2Nat)) ∧
        uBad ∉ (U ⊔ V : Submodule ℝ L2Nat) := by
  simpa using nonclosedSupWitnessExplicitBadPointData

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Remark 16.46: the quadratic owner `halfSquaredNorm` belongs to `Γ₀(H)`. -/
private theorem halfSquaredNorm_mem_gammaZero_local [NormedSpace ℝ H] :
    (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  let q : H → ℝ := fun x : H ↦ ‖x‖ ^ 2 / 2
  have hq_eq :
      q.toEReal = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    funext x
    simp [q, halfSquaredNorm, moreauQuadraticKernel, div_eq_mul_inv, mul_comm]
  rw [← hq_eq]
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha0 ha1
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖ ^ 2) :=
      (convexOn_univ_norm :
          _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖)).pow
        (fun z _ ↦ norm_nonneg z) 2
    have hquad :
        ‖a • x + (1 - a) • y‖ ^ 2 / 2 ≤
          a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) := by
      have hquad' :
          ‖a • x + (1 - a) • y‖ ^ 2 ≤
            a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using
          hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
      nlinarith
    -- The real quadratic Jensen bound transports directly to the `EReal` owner.
    change (((‖a • x + (1 - a) • y‖ ^ 2) / 2 : ℝ) : EReal) ≤
      ((a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) : ℝ) : EReal)
    exact_mod_cast hquad
  · have hcont : Continuous q := by
      simpa [q, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
    -- Lower semicontinuity follows from continuity of the real quadratic owner.
    simpa [q] using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Remark 16.46: adding the quadratic regularization preserves `Γ₀(H)`. -/
private theorem pointwiseAdd_halfSquaredNorm_mem_gammaZero_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    f + halfSquaredNorm ∈ Γ₀(H) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  have hhalf_dom : x ∈ effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  -- The point `x` stays finite after adding the quadratic regularization.
  exact pointwiseAdd_mem_gammaZero
    f halfSquaredNorm hf halfSquaredNorm_mem_gammaZero_local ⟨x, hx, hhalf_dom⟩

/-- Helper for Remark 16.46: the first regularized witness owner is the conjugate of a closed
subspace indicator. -/
private abbrev nonclosedSupWitnessF
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  (ι[(U : Set H)])∗[hU]

/-- Helper for Remark 16.46: the second regularized witness owner is the conjugate of the
indicator-plus-quadratic subspace owner. -/
private abbrev nonclosedSupWitnessG
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (V : Submodule ℝ H)
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  ((ι[(V : Set H)] + halfSquaredNorm)∗[hVq])

/-- Helper for Remark 16.46: if the second effective domain is all of `H`, then the Attouch--Brézis
regularity condition `0 ∈ sri (effectiveDomain f - effectiveDomain g)` holds automatically. -/
private theorem zero_mem_sri_sub_effectiveDomain_of_dom_univ_local
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H)) :
    (0 : H) ∈ Set.strongRelativeInterior (effectiveDomain f - effectiveDomain g) := by
  -- Rewrite the domain difference against `univ`, then identify its strong relative interior.
  rw [hdom]
  obtain ⟨x, hx⟩ : (effectiveDomain f).Nonempty := ConvexOn.nonempty hf.2
  have hsub : effectiveDomain f - (Set.univ : Set H) = (Set.univ : Set H) := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      exact Set.mem_sub.mpr ⟨x, hx, x - y, by simp, by abel⟩
  rw [hsub]
  rw [Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

/-- Helper for Remark 16.46: an active subgradient of `f + g` with `effectiveDomain g = univ`
produces an attained split of `f^* □ g^*` at the same dual point. -/
private theorem
    exists_exact_infimalConvolution_witness_of_mem_subdifferential_pointwiseAdd_of_dom_univ
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H))
    {x u : H} (hu : u ∈ (∂ (f + g)) x) :
    ∃ w : H, (f.asEReal∗ □ g.asEReal∗) u = f.asEReal∗ (u - w) + g.asEReal∗ w := by
  have hsri :
      (0 : H) ∈ Set.strongRelativeInterior (effectiveDomain f - effectiveDomain g) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf hdom
  have hfg_dom : (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
    rcases hf.2.nonempty with ⟨x0, hx0⟩
    refine ⟨x0, hx0, ?_⟩
    simpa [hdom]
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hfg_dom
  have hu_dom_sum : u ∈ dom ((f + g).asEReal∗) :=
    mem_dom_conjugate_of_mem_subdifferential hfg hu
  have hu_dom_raw : u ∈ dom (f.asEReal∗ □ g.asEReal∗) := by
    -- Proposition 15.7 identifies the dual owner of `f + g` with the raw infimal convolution.
    rw [← ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri]
    exact hu_dom_sum
  rcases
      ERealFunction.InfimalConvolutionRegularity.infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
          f g hf hg hsri hu_dom_raw with
    ⟨y, hy⟩
  have hy_raw :
      (f.asEReal∗ □ g.asEReal∗) u = f.asEReal∗ y + g.asEReal∗ (u - y) := by
    simpa [gammaZeroConjugate_apply] using hy
  refine ⟨u - y, ?_⟩
  -- Repackage the outer-exact split in the `w`-coordinate used by the local Chapter 16 helpers.
  calc
    (f.asEReal∗ □ g.asEReal∗) u = f.asEReal∗ y + g.asEReal∗ (u - y) := hy_raw
    _ = f.asEReal∗ (u - (u - y)) + g.asEReal∗ (u - y) := by
          congr 1
          abel

/-- Helper for Remark 16.46: under `effectiveDomain g = univ`, every active subgradient of
`f + g` splits into one subgradient of `f` and one of `g`. -/
private theorem dual_split_of_mem_subdifferential_pointwiseAdd_of_dom_univ
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H))
    {x u : H} (hu : u ∈ (∂ (f + g)) x) :
    ∃ v : H, v ∈ (∂ f) x ∧ u - v ∈ (∂ g) x := by
  have hsri :
      (0 : H) ∈ Set.strongRelativeInterior (effectiveDomain f - effectiveDomain g) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf hdom
  have heq :
      (f + g).asEReal∗ = ((((f∗[hf]) □ (g∗[hg])) : H → EReal)) :=
    ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri
  have hdom_inter : (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
    rcases hf.2.nonempty with ⟨x0, hx0⟩
    refine ⟨x0, hx0, ?_⟩
    simpa [hdom]
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom_inter
  have hu_dom_sum : u ∈ dom ((f + g).asEReal∗) :=
    mem_dom_conjugate_of_mem_subdifferential hfg hu
  have hu_dom_raw : u ∈ dom ((((f∗[hf]) □ (g∗[hg])) : H → EReal)) := by
    rw [← heq]
    exact hu_dom_sum
  have hu_exact : infimalConvolution.ExactAt (f∗[hf]) (g∗[hg]) u :=
    ERealFunction.InfimalConvolutionRegularity.infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri hu_dom_raw
  have hu_split :
      u ∈ ((∂ f) + (∂ g)) x :=
    subgradient_split_of_mem_subdifferential_pointwiseAdd_of_exact
      hf hg hdom_inter hu heq hu_exact
  rcases Set.mem_add.mp hu_split with ⟨v, hvf, w, hwg, hsum⟩
  refine ⟨v, hvf, ?_⟩
  have hw_eq : w = u - v := by
    calc
      w = (v + w) - v := by abel
      _ = u - v := by rw [hsum]
  simpa [hw_eq] using hwg

/-- Helper for Remark 16.46: the quadratic regularized witness has full effective domain. -/
private theorem effectiveDomain_nonclosedSupWitnessG_eq_univ
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (V : Submodule ℝ H)
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    effectiveDomain (nonclosedSupWitnessG V hVq) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rw [mem_effectiveDomain_iff]
    -- Example 13.5 rewrites the conjugate to an everywhere-finite real-valued distance formula.
    rw [nonclosedSupWitnessG, gammaZeroConjugate_apply]
    rw [congrFun
      (fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
        (V : Set H) ⟨0, V.zero_mem⟩) x]
    exact EReal.coe_lt_top _

/-- Helper for Remark 16.46: the `dom g = univ` branch of the Chapter 16 sum rule can be used
directly without reopening the later regularity disjunction. -/
private theorem subdifferential_add_eq_add_of_dom_univ_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = Set.univ) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + ∂ g := by
  ext x u
  constructor
  · intro hu
    -- Split the active subgradient using the exact Attouch--Brézis dual witness.
    obtain ⟨v, hvf, hvg⟩ :=
      dual_split_of_mem_subdifferential_pointwiseAdd_of_dom_univ hf hg hdom hu
    exact Set.mem_add.2 ⟨v, hvf, u - v, hvg, by abel⟩
  · intro hu
    -- Proposition 16.6 supplies the easy inclusion after specializing the linear map to the
    -- identity.
    have hu_id :
        u ∈ (∂ f) x +
          ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g x := by
      simpa [ContinuousLinearMap.adjointImageSubdifferential] using hu
    simpa [Function.comp] using
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) x hu_id)

/-- Helper for Remark 16.46: if the first summand has full effective domain, commute the sum and
reuse the existing `dom = univ` branch on the second slot. -/
private theorem subdifferential_add_eq_add_of_dom_univ_left_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain f = Set.univ) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + ∂ g := by
  have hswap :
      (∂ (g + f) : SetValuedOperator H H) = (∂ g) + ∂ f :=
    subdifferential_add_eq_add_of_dom_univ_local hg hf hdom
  have hadd : f + g = g + f := by
    -- Pointwise addition of the two owners is commutative.
    ext x
    simp [pointwiseAdd_apply, add_comm]
  calc
    (∂ (f + g) : SetValuedOperator H H) = ∂ (g + f) := by
      simp [hadd]
    _ = (∂ g) + ∂ f := hswap
    _ = (∂ f) + ∂ g := by
      -- Swap the two additive witnesses in the pointwise Minkowski sum.
      ext x u
      constructor
      · intro hu
        rcases Set.mem_add.mp hu with ⟨a, ha, b, hb, hab⟩
        exact Set.mem_add.2 ⟨b, hb, a, ha, by simpa [add_comm] using hab⟩
      · intro hu
        rcases Set.mem_add.mp hu with ⟨a, ha, b, hb, hab⟩
        exact Set.mem_add.2 ⟨b, hb, a, ha, by simpa [add_comm] using hab⟩

/-- Helper for Remark 16.46: the regularized witness pair satisfies the Chapter 16 sum rule
because the second owner has full effective domain. -/
private theorem subdifferential_add_eq_add_nonclosedSupWitness
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    (∂ (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) : SetValuedOperator H H) =
      ∂ (nonclosedSupWitnessF U hU) + ∂ (nonclosedSupWitnessG V hVq) := by
  -- Route correction: use the `dom = univ` regularity branch instead of reopening any local
  -- finite-dimensional witness search.
  have hf : nonclosedSupWitnessF U hU ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hU
  have hg : nonclosedSupWitnessG V hVq ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hVq
  have hdom_univ :
      effectiveDomain (nonclosedSupWitnessG V hVq) = Set.univ :=
    effectiveDomain_nonclosedSupWitnessG_eq_univ V hVq
  exact subdifferential_add_eq_add_of_dom_univ_local hf hg hdom_univ

/-- Helper for Remark 16.46: the Attouch--Brézis strong-relative-interior hypothesis already
packages the full identity-map exact dual formula. -/
private theorem exactDualInfimalConvolutionFormula_id_of_zero_mem_sri_sub_effectiveDomain
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ Set.strongRelativeInterior (effectiveDomain f - effectiveDomain g)) :
    ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ H) := by
  refine
    { eq := ?_
      outerExact := ?_
      innerExact := ?_ }
  · -- Proposition 15.7 gives the raw identity-map conjugate formula under the same `sri`
    -- hypothesis; normalize both sides to the Chapter 16 structure field.
    ext u
    have hpost :
        ((((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗) : H → EReal)) = g.asEReal∗ := by
      simpa [ContinuousLinearMap.adjoint_id] using
        infimalPostcomposition_id_eq_ereal (φ := g.asEReal∗)
    change ((compositePrimalObjective f g (ContinuousLinearMap.id ℝ H))∗ u) =
        ((((f.asEReal∗) □ (((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗))) : H → EReal) u)
    rw [hpost]
    simpa [compositePrimalObjective, primalObjective, Function.comp] using
      congrFun
        (ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
            f g hf hg hsri)
        u
  · intro u hu
    have hu_sum : u ∈ dom ((f + g).asEReal∗) := by
      -- Re-express the composite objective at the identity map as the pointwise sum.
      simpa [compositePrimalObjective, primalObjective, Function.comp] using hu
    have hu_raw : u ∈ dom (f.asEReal∗ □ g.asEReal∗) := by
      rw [← ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
          f g hf hg hsri]
      exact hu_sum
    rcases
        ERealFunction.InfimalConvolutionRegularity.infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
            f g hf hg hsri hu_raw with
      ⟨y, hy⟩
    have hpost :
        ((((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗) : H → EReal)) = g.asEReal∗ := by
      simpa [ContinuousLinearMap.adjoint_id] using
        infimalPostcomposition_id_eq_ereal (φ := g.asEReal∗)
    refine ⟨y, ?_⟩
    -- Rewrite the raw exact split to the Chapter 16 identity-map outer exactness spelling.
    change
      (((f.asEReal∗) □ (((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗))) u) =
        f.asEReal∗ y + (((ContinuousLinearMap.id ℝ H).adjoint ▷ g.asEReal∗) (u - y))
    rw [hpost]
    simpa [gammaZeroConjugate_apply] using hy
  · intro y hy
    have hpost :
        (((ContinuousLinearMap.id ℝ H).adjoint ▷ (g∗[hg])) : H → EReal) =
          (g∗[hg] : H → EReal) := by
      simpa [ContinuousLinearMap.adjoint_id] using
        infimalPostcomposition_id_eq (f := g∗[hg])
    have hy_dom : y ∈ dom ((g∗[hg] : H → EReal)) := by
      -- On the identity fiber, the infimal postcomposition owner is literally `g*`.
      rw [hpost] at hy
      exact hy
    have hy_eff : y ∈ effectiveDomain (g∗[hg]) := by
      simpa [effectiveDomain, dom] using hy_dom
    simpa [ContinuousLinearMap.adjoint_id] using
      infimalPostcomposition_exactAt_id (f := g∗[hg]) hy_eff

/-- Helper for Remark 16.46: the current Example 3.41 regularized witness family cannot serve as
the desired counterexample, because the second owner has full effective domain and therefore the
identity-map exact dual formula already holds. -/
private theorem exactDualInfimalConvolutionFormula_nonclosedSupWitness
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    ExactDualInfimalConvolutionFormula
      (gammaZeroConjugate_mem_gammaZero hU)
      (gammaZeroConjugate_mem_gammaZero hVq)
      (ContinuousLinearMap.id ℝ H) := by
  have hf : nonclosedSupWitnessF U hU ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hU
  have hg : nonclosedSupWitnessG V hVq ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hVq
  have hsri :
      (0 : H) ∈
        Set.strongRelativeInterior
          (effectiveDomain (nonclosedSupWitnessF U hU) - effectiveDomain (nonclosedSupWitnessG V hVq)) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf
      (effectiveDomain_nonclosedSupWitnessG_eq_univ V hVq)
  -- Route correction: this closes the old Example 3.41 branch by proving exactness directly,
  -- rather than continuing the failed search for a nonexact witness inside that family.
  exact
    exactDualInfimalConvolutionFormula_id_of_zero_mem_sri_sub_effectiveDomain hf hg hsri

/-- Helper for Remark 16.46: every current Example 3.41 regularized witness already has
intersecting effective domains, satisfies the Chapter 16 sum rule, and also satisfies the
identity-map exact dual formula. Hence this family cannot realize the desired counterexample. -/
private theorem nonclosedSupWitness_hasSumRule_andExactFormula
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    (effectiveDomain (nonclosedSupWitnessF U hU) ∩
        effectiveDomain (nonclosedSupWitnessG V hVq)).Nonempty ∧
      ((∂ (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) :
          SetValuedOperator H H) =
        ∂ (nonclosedSupWitnessF U hU) + ∂ (nonclosedSupWitnessG V hVq)) ∧
      ExactDualInfimalConvolutionFormula
        (gammaZeroConjugate_mem_gammaZero hU)
        (gammaZeroConjugate_mem_gammaZero hVq)
        (ContinuousLinearMap.id ℝ H) := by
  have hf : nonclosedSupWitnessF U hU ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hU
  have hg_dom :
      effectiveDomain (nonclosedSupWitnessG V hVq) = Set.univ :=
    effectiveDomain_nonclosedSupWitnessG_eq_univ V hVq
  rcases hf.2.nonempty with ⟨x, hx⟩
  refine ⟨?_, ?_, ?_⟩
  · -- A finite point of the first owner automatically belongs to the second domain because `dom g`
    -- is all of `H`.
    refine ⟨x, hx, ?_⟩
    simpa [hg_dom]
  · -- The regularized witness sum rule is already proved by the `dom = univ` branch.
    exact subdifferential_add_eq_add_nonclosedSupWitness U V hU hVq
  · -- Route correction: this packages the verified obstruction that the old witness family is
    -- exact under the identity map, so any remaining proof must switch to a different family.
    exact exactDualInfimalConvolutionFormula_nonclosedSupWitness U V hU hVq

/-- Helper for Remark 16.46: the first regularized witness owner is exactly the indicator of the
orthogonal complement `Uᗮ`. -/
private theorem nonclosedSupWitnessF_apply_eq_indicator_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) (x : H) :
    (nonclosedSupWitnessF U hU x : EReal) = (ι[(Uᗮ : Set H)] x : EReal) := by
  -- Rewrite the packaged conjugate back through Example 13.3 at the evaluation point `x`.
  simpa [nonclosedSupWitnessF, gammaZeroConjugate_apply] using
    congrFun (conjugate_indicator_submodule_eq_indicator_orthogonal (V := U)) x

/-- Helper for Remark 16.46: outside `Uᗮ`, the regularized witness sum is automatically `⊤`
because its first summand is the indicator of `Uᗮ`. -/
private theorem pointwiseAdd_nonclosedSupWitness_eq_top_of_not_mem_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    {x : H} (hx : x ∉ (Uᗮ : Set H)) :
    ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : EReal) = ⊤ := by
  have hF_top : (nonclosedSupWitnessF U hU x : EReal) = ⊤ := by
    rw [nonclosedSupWitnessF_apply_eq_indicator_orthogonal]
    simp [indicator_apply, hx]
  have hG_ne_bot : (nonclosedSupWitnessG V hVq x : EReal) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hVq.2.nonempty x
  calc
    ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : EReal)
        = (nonclosedSupWitnessF U hU x : EReal) + (nonclosedSupWitnessG V hVq x : EReal) := by
            rfl
    _ = ⊤ + (nonclosedSupWitnessG V hVq x : EReal) := by rw [hF_top]
    _ = ⊤ := by
          simpa using EReal.top_add_of_ne_bot hG_ne_bot

/-- Helper for Remark 16.46: the effective domain of the regularized witness sum is contained in
`Uᗮ`. -/
private theorem dom_pointwiseAdd_nonclosedSupWitness_subset_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    dom ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal) ⊆ (Uᗮ : Set H) := by
  intro x hx
  by_contra hx_orth
  have htop :
      ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : EReal) = ⊤ :=
    pointwiseAdd_nonclosedSupWitness_eq_top_of_not_mem_orthogonal U V hU hVq hx_orth
  rw [mem_dom_iff] at hx
  exact (lt_top_iff_ne_top.mp hx) htop

/-- Helper for Remark 16.46: the conjugate of the regularized witness sum only depends on the
`Uᗮ`-component of the dual variable. -/
private theorem conjugate_pointwiseAdd_nonclosedSupWitness_eq_on_starProjection
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (u : H) :
    ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal∗) u =
      ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal∗)
        ((⟨Uᗮ, U.isClosed_orthogonal⟩ : ClosedSubmodule ℝ H).starProjection u) := by
  let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
  -- Proposition 13.23 applies because the primal domain is already confined to `Uᗮ`.
  simpa [Uc, Function.comp] using
    congrFun
      (conjugate_eq_conjugate_comp_starProjection_of_dom_subset
        ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal)
        Uc
        (dom_pointwiseAdd_nonclosedSupWitness_subset_orthogonal U V hU hVq))
      u

/-- Helper for Remark 16.46: on the orthogonal complement `Uᗮ`, the first witness owner
vanishes, so the regularized sum reduces to the second witness owner. -/
private theorem pointwiseAdd_nonclosedSupWitness_eq_nonclosedSupWitnessG_of_mem_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    {x : H} (hx : x ∈ (Uᗮ : Set H)) :
    ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : EReal) =
      (nonclosedSupWitnessG V hVq x : EReal) := by
  have hF_zero : (nonclosedSupWitnessF U hU x : EReal) = 0 := by
    -- On `Uᗮ`, the first witness owner is the vanishing indicator value.
    rw [nonclosedSupWitnessF_apply_eq_indicator_orthogonal]
    simp [indicator_apply, hx]
  calc
    ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : EReal)
        = (nonclosedSupWitnessF U hU x : EReal) + (nonclosedSupWitnessG V hVq x : EReal) := by
            rfl
    _ = 0 + (nonclosedSupWitnessG V hVq x : EReal) := by rw [hF_zero]
    _ = (nonclosedSupWitnessG V hVq x : EReal) := by simp

/-- Helper for Remark 16.46: for a closed subspace `W`, the ambient quadratic
`x ↦ (1 / 2) ‖P_W x‖^2` is the Fenchel conjugate of `ι[W] + (1 / 2) ‖·‖^2`. -/
private theorem halfSquaredNorm_comp_orthogonalProjection_eq_conjugate_indicator_add_halfSquaredNorm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : ClosedSubmodule ℝ H) :
    (fun x : H ↦ ((halfSquaredNorm (W.orthogonalProjection x) : Set.Ioi (⊥ : EReal)) : EReal)) =
      ((ι[(W : Set H)] + halfSquaredNorm).asEReal)∗ := by
  funext x
  rw [congrFun
    (fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
      (W : Set H) ⟨0, W.zero_mem⟩) x]
  have hsplit :
      Metric.infDist x (W : Set H) ^ 2 + ‖W.orthogonalProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [infDist_eq_norm_orthogonalProjection_orthogonal (V := W) (x := x)]
    simpa [add_comm] using
      (norm_sq_eq_add_norm_sq_orthogonalProjection (V := W) (x := x)).symm
  have hproj :
      (‖x‖ ^ 2 - Metric.infDist x (W : Set H) ^ 2) / 2 =
        ‖W.orthogonalProjection x‖ ^ 2 / 2 := by
    nlinarith
  -- The Pythagorean identity turns the squared-distance formula into the projected quadratic.
  rw [halfSquaredNorm_apply]
  exact congrArg (fun r : ℝ ↦ (r : EReal)) hproj.symm

/-- Helper for Remark 16.46: for a closed subspace `W`, the conjugate of
`x ↦ (1 / 2) ‖P_W x‖^2` is `ι[W] + (1 / 2) ‖·‖^2`. -/
private theorem conjugate_halfSquaredNorm_comp_orthogonalProjection_eq_indicator_add_halfSquaredNorm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : ClosedSubmodule ℝ H) :
    (fun x : H ↦ ((halfSquaredNorm (W.orthogonalProjection x) : Set.Ioi (⊥ : EReal)) : EReal))∗ =
      (ι[(W : Set H)] + halfSquaredNorm).asEReal := by
  have hW_gamma :
      (ι[(W : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      ⟨0, W.zero_mem⟩ W.isClosed W.convex
  have hsum_gamma :
      (ι[(W : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero_local (ι[(W : Set H)]) hW_gamma
  -- Conjugate the normalized projector quadratic once more and close by Fenchel--Moreau.
  rw [halfSquaredNorm_comp_orthogonalProjection_eq_conjugate_indicator_add_halfSquaredNorm]
  simpa using biconjugate_eq_of_mem_gammaZero hsum_gamma

/-- Helper for Remark 16.46: projecting `U ⊔ V` to `Uᗮ` forgets the `U`-component and leaves only
the projected `V`-part. -/
private theorem orthogonalProjection_image_sup_eq_image
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) :
    let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
    Uc.orthogonalProjection '' (((U ⊔ V : Submodule ℝ H) : Set H)) =
      Uc.orthogonalProjection '' (V : Set H) := by
  dsimp
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Submodule.mem_sup.mp hz with ⟨u, hu, v, hv, rfl⟩
    -- The orthogonal projector onto `Uᗮ` kills vectors from `U`, so only the `V`-part remains.
    refine ⟨v, hv, ?_⟩
    have hu_proj :
        Uᗮ.orthogonalProjection u = 0 := by
      exact
        Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
          (Submodule.le_orthogonal_orthogonal U hu)
    simp [map_add, hu_proj]
  · rintro ⟨v, hv, rfl⟩
    -- Every `V`-vector already belongs to `U ⊔ V`.
    refine ⟨v, Submodule.mem_sup.2 ?_, rfl⟩
    exact ⟨0, U.zero_mem, v, hv, by simp⟩

/-- Helper for Remark 16.46: if `u` lies in `closure (U ⊔ V)`, then its orthogonal projection to
`Uᗮ` lies in the closure of the projected `V`-image. -/
private theorem orthogonalProjection_mem_projectedClosure_of_mem_closure_sup
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) {u : H}
    (hu : u ∈ closure (((U ⊔ V : Submodule ℝ H) : Set H))) :
    let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
    Uc.orthogonalProjection u ∈ closure (Uc.orthogonalProjection '' (V : Set H)) := by
  let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
  -- Push the closure point through the continuous orthogonal projection first.
  have hu_image :
      Uc.orthogonalProjection u ∈
        Uc.orthogonalProjection '' closure (((U ⊔ V : Submodule ℝ H) : Set H)) :=
    ⟨u, hu, rfl⟩
  have hu_closure :
      Uc.orthogonalProjection u ∈
        closure (Uc.orthogonalProjection '' (((U ⊔ V : Submodule ℝ H) : Set H))) :=
    (image_closure_subset_closure_image Uc.orthogonalProjection.continuous) hu_image
  -- Then collapse the projected image of `U ⊔ V` to the projected image of `V`.
  simpa [Uc, orthogonalProjection_image_sup_eq_image U V] using hu_closure

/-- Helper for Remark 16.46: a closure point in `U ⊔ V` that already lies in `Uᗮ` becomes a
point of the projected closure after packaging it in the orthogonal subtype `Uᗮ`. -/
private theorem mem_projectedClosureSubtype_of_mem_closure_sup
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) {u : H}
    (hu_orth : u ∈ (Uᗮ : Set H))
    (hu_closure : u ∈ closure (((U ⊔ V : Submodule ℝ H) : Set H))) :
    let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
    (⟨u, hu_orth⟩ : Uc) ∈ closure (Uc.orthogonalProjection '' (V : Set H)) := by
  let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
  have hproj_mem :
      Uc.orthogonalProjection u ∈ closure (Uc.orthogonalProjection '' (V : Set H)) :=
    orthogonalProjection_mem_projectedClosure_of_mem_closure_sup U V hu_closure
  have hproj_eq : Uc.orthogonalProjection u = ⟨u, hu_orth⟩ := by
    -- On `Uᗮ`, the orthogonal projection is the identity after packaging the point in the subtype.
    simpa [Uc] using
      (Submodule.orthogonalProjection_mem_subspace_eq_self
        (⟨u, hu_orth⟩ : (Uc : Submodule ℝ H)))
  simpa [hproj_eq] using hproj_mem

/-- Helper for Remark 16.46: if the projected bad point came from an actual projected `V`-vector,
then the original ambient point would already lie in `U ⊔ V`. -/
private theorem orthogonalProjection_not_mem_projectedImage_of_not_mem_sup
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) (hU_closed : IsClosed (U : Set H)) {u : H}
    (hu : u ∉ (((U ⊔ V : Submodule ℝ H) : Set H))) :
    ((⟨Uᗮ, U.isClosed_orthogonal⟩ : ClosedSubmodule ℝ H).orthogonalProjection u) ∉
      ((⟨Uᗮ, U.isClosed_orthogonal⟩ : ClosedSubmodule ℝ H).orthogonalProjection '' (V : Set H)) := by
  let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
  intro hproj
  rcases hproj with ⟨v, hv, hvproj⟩
  let Uclosed : ClosedSubmodule ℝ H := ⟨U, hU_closed⟩
  let K : Submodule ℝ H := Uc
  have hu_diff_mem :
      u - Uc.starProjection u ∈ (U : Set H) := by
    -- The orthogonal complement of `Uᗮ` is `U` because `U` is closed.
    have horth : u - K.starProjection u ∈ (Kᗮ : Set H) :=
      Submodule.sub_starProjection_mem_orthogonal (K := K) u
    simpa [Uc, Uclosed, K] using horth
  have hv_diff_mem :
      v - Uc.starProjection v ∈ (U : Set H) := by
    -- The same orthogonal decomposition applies to every `V`-vector.
    have horth : v - K.starProjection v ∈ (Kᗮ : Set H) :=
      Submodule.sub_starProjection_mem_orthogonal (K := K) v
    simpa [Uc, Uclosed, K] using horth
  have hu_mem_sup :
      u ∈ (((U ⊔ V : Submodule ℝ H) : Set H)) := by
    have hproj_eq : ((Uc.orthogonalProjection v : Uc) : H) = (Uc.orthogonalProjection u : H) := by
      exact congrArg (fun z : Uc ↦ (z : H)) hvproj
    have hU_part_mem :
        (u - (Uc.orthogonalProjection u : H)) - (v - (Uc.orthogonalProjection v : H)) ∈
          (U : Set H) :=
      Submodule.sub_mem U hu_diff_mem hv_diff_mem
    have hu_decomp :
        ((u - (Uc.orthogonalProjection u : H)) - (v - (Uc.orthogonalProjection v : H))) + v =
          u := by
      calc
        ((u - (Uc.orthogonalProjection u : H)) - (v - (Uc.orthogonalProjection v : H))) + v
            = u - (Uc.orthogonalProjection u : H) + (Uc.orthogonalProjection v : H) := by
                abel
        _ = u := by
              rw [hproj_eq]
              abel
    -- Replace the projected piece by the original `V`-vector `v`.
    exact Submodule.mem_sup.2 ⟨_, hU_part_mem, v, hv, hu_decomp⟩
  exact hu hu_mem_sup

/-- Helper for Remark 16.46: Example 3.41 already yields a concrete projected bad point in
`Uᗮ`, namely a point in the closure of the projected `V`-image but outside the image itself. -/
private theorem existsProjectedBadPointOutsideProjectedImage_l2 :
    ∃ U V : Submodule ℝ L2Nat,
      IsClosed (U : Set L2Nat) ∧
      IsClosed (V : Set L2Nat) ∧
      let Uc : ClosedSubmodule ℝ L2Nat := ⟨Uᗮ, U.isClosed_orthogonal⟩
      ∃ u0 : Uc,
        u0 ∈ closure (Uc.orthogonalProjection '' (V : Set L2Nat)) ∧
        u0 ∉ Uc.orthogonalProjection '' (V : Set L2Nat) := by
  rcases existsNonclosedSupPair_l2 with ⟨U, V, hU_closed, hV_closed, uBad, huBad_closure,
    huBad_not_mem⟩
  refine ⟨U, V, hU_closed, hV_closed, ?_⟩
  let Uc : ClosedSubmodule ℝ L2Nat := ⟨Uᗮ, U.isClosed_orthogonal⟩
  refine ⟨Uc.orthogonalProjection uBad, ?_, ?_⟩
  · -- Push the ambient closure point through the orthogonal projection.
    exact orthogonalProjection_mem_projectedClosure_of_mem_closure_sup U V huBad_closure
  · -- If the projected point came from `V`, the ambient bad point would lie in `U ⊔ V`.
    exact
      orthogonalProjection_not_mem_projectedImage_of_not_mem_sup
        U V hU_closed huBad_not_mem

/-- Helper for Remark 16.46: the orthogonal complement `Uᗮ`, packaged as a closed submodule. -/
private abbrev orthogonalClosedSubmodule
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : Submodule ℝ H) : ClosedSubmodule ℝ H :=
  ⟨Uᗮ, U.isClosed_orthogonal⟩

/-- Helper for Remark 16.46: the packaged orthogonal complement `orthogonalClosedSubmodule U` is
complete. -/
private instance orthogonalClosedSubmoduleCompleteSpace
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : Submodule ℝ H) :
    CompleteSpace (orthogonalClosedSubmodule U) := by
  simpa [orthogonalClosedSubmodule] using U.isClosed_orthogonal.completeSpace_coe

/-- Helper for Remark 16.46: the image of `V` under the orthogonal projection onto `Uᗮ`. -/
private abbrev projectedImageSubmodule
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) : Submodule ℝ (orthogonalClosedSubmodule U) :=
  Submodule.map (orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap V

/-- Helper for Remark 16.46: package the projected bad point entirely in the restricted spelling
world `K := Uᗮ`, together with the projected image `A` and the closure witness `u0 ∈ closure A`.
-/
private theorem projectedImageBadPointData_l2 :
    ∃ U V : Submodule ℝ L2Nat,
      IsClosed (U : Set L2Nat) ∧
      IsClosed (V : Set L2Nat) ∧
      ∃ u0 : orthogonalClosedSubmodule U,
        u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
        u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
  rcases existsProjectedBadPointOutsideProjectedImage_l2 with
    ⟨U, V, hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  refine ⟨U, V, hU_closed, hV_closed, ?_⟩
  let Uc : ClosedSubmodule ℝ L2Nat := orthogonalClosedSubmodule U
  let A : Submodule ℝ Uc := projectedImageSubmodule U V
  have hA_eq :
      (A : Set Uc) = Uc.orthogonalProjection '' (V : Set L2Nat) := by
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  refine ⟨u0, ?_, ?_⟩
  · -- Rewrite the closure witness through the carrier of the projected submodule `A`.
    simpa [hA_eq] using hu0_closure
  · -- The same carrier rewrite turns nonmembership in the projected image into `u0 ∉ A`.
    simpa [hA_eq] using hu0_not_mem

/-- Helper for Remark 16.46: freeze the projected-image geometry in the exact restricted-space
spelling needed for the replacement asymmetric witness route. -/
private theorem asymmetricProjectedEpigraphWitnessData_l2 :
    ∃ U V : Submodule ℝ L2Nat,
      IsClosed (U : Set L2Nat) ∧
      IsClosed (V : Set L2Nat) ∧
      ∃ u0 : orthogonalClosedSubmodule U,
        ¬ IsClosed (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
        (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)).Nonempty ∧
        u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
        u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  have hA_not_closed :
      ¬ IsClosed (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
    -- A closure point outside `A` certifies that the projected image is not closed.
    intro hA_closed
    have hu0_mem :
        u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
      rw [← hA_closed.closure_eq]
      exact hu0_closure
    exact hu0_not_mem hu0_mem
  have hA_nonempty :
      (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)).Nonempty := by
    -- The projected image is a submodule, so it contains the zero vector.
    refine ⟨0, ?_⟩
    change 0 ∈
      Submodule.map (orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap V
    exact Submodule.zero_mem _
  -- Package the restricted geometry once so the remaining witness construction can focus on the
  -- function pair rather than on more ambient/projected transport.
  refine ⟨U, V, hU_closed, hV_closed, u0, hA_not_closed, hA_nonempty, hu0_closure, hu0_not_mem⟩

/-- Helper for Remark 16.46: the projected bad point already separates the indicator of the
closure of the projected image from the raw indicator of the projected image itself. -/
private theorem projectedImageIndicatorClosureGap_l2 :
    ∃ U V : Submodule ℝ L2Nat,
      ∃ u0 : orthogonalClosedSubmodule U,
        let A : Submodule ℝ (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
        u0 ∈ closure (A : Set (orthogonalClosedSubmodule U)) ∧
          u0 ∉ (A : Set (orthogonalClosedSubmodule U)) ∧
          (ι[closure (A : Set (orthogonalClosedSubmodule U))] u0 : EReal) = 0 ∧
          (ι[(A : Set (orthogonalClosedSubmodule U))] u0 : EReal) = ⊤ := by
  rcases asymmetricProjectedEpigraphWitnessData_l2 with
    ⟨U, V, _hU_closed, _hV_closed, u0, _hA_not_closed, _hA_nonempty, hu0_closure, hu0_not_mem⟩
  refine ⟨U, V, u0, ?_⟩
  let A : Submodule ℝ (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
  have hu0_closure_image :
      u0 ∈ closure
        (((orthogonalClosedSubmodule U).orthogonalProjection : L2Nat → orthogonalClosedSubmodule U) ''
          (V : Set L2Nat)) := by
    -- Unfold the projected-image carrier once so the closure witness is available in the image
    -- spelling used by the indicator owner.
    simpa [A, projectedImageSubmodule] using hu0_closure
  have hu0_not_mem_image :
      u0 ∉
        (((orthogonalClosedSubmodule U).orthogonalProjection : L2Nat → orthogonalClosedSubmodule U) ''
          (V : Set L2Nat)) := by
    -- The same carrier normalization keeps the bad point outside the raw projected image.
    simpa [A, projectedImageSubmodule] using hu0_not_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The packaged point already lies in the closure-side owner.
    change u0 ∈
      closure
        (((orthogonalClosedSubmodule U).orthogonalProjection : L2Nat →
            orthogonalClosedSubmodule U) '' (V : Set L2Nat))
    exact hu0_closure_image
  · -- By construction the same point still stays outside the raw projected image.
    change u0 ∉
      (((orthogonalClosedSubmodule U).orthogonalProjection : L2Nat →
          orthogonalClosedSubmodule U) '' (V : Set L2Nat))
    exact hu0_not_mem_image
  · -- The closure indicator vanishes at a point of `closure A`.
    simpa [projectedImageSubmodule, indicator_apply, hu0_closure_image]
  · -- The raw indicator is `⊤` at a point outside `A`.
    change
      (ι[(((orthogonalClosedSubmodule U).orthogonalProjection : L2Nat →
          orthogonalClosedSubmodule U) '' (V : Set L2Nat))] u0 : EReal) = ⊤
    simpa [indicator_apply, hu0_not_mem_image]

/-- Helper for Remark 16.46: the raw restricted owner on `Uᗮ` is the projected-image indicator
regularized by `halfSquaredNorm`. -/
private abbrev projectedImageRawOwner
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) :
    orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal) :=
  (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] + halfSquaredNorm)

/-- Helper for Remark 16.46: the closed comparison owner replaces the projected image by its
closure while keeping the same quadratic regularization. -/
private abbrev projectedImageClosureOwner
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) :
    orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal) :=
  (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] +
    halfSquaredNorm)

/-- Helper for Remark 16.46: replacing the projected image by its closure only decreases the
indicator term, so the closed comparison owner is a pointwise minorant of the raw owner. -/
private theorem projectedImageClosureOwner_le_rawOwner
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) :
    (projectedImageClosureOwner U V).asEReal ≤ (projectedImageRawOwner U V).asEReal := by
  intro x
  have hA_eq :
      (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) =
        (((orthogonalClosedSubmodule U).orthogonalProjection : H → orthogonalClosedSubmodule U) ''
          (V : Set H)) := by
    ext z
    constructor
    · intro hz
      exact Submodule.mem_map.mp hz
    · rintro ⟨v, hv, rfl⟩
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  by_cases hxA : x ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))
  · -- On the projected image, both indicator terms vanish and the owners coincide.
    have hxClosure :
        x ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) :=
      subset_closure hxA
    have hxA_image :
        x ∈
          (((orthogonalClosedSubmodule U).orthogonalProjection : H → orthogonalClosedSubmodule U) ''
            (V : Set H)) := by
      simpa [hA_eq] using hxA
    have hxClosure_image :
        x ∈
          closure
            (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H)) := by
      simpa [hA_eq] using hxClosure
    change
      (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) +
          (halfSquaredNorm x : EReal) ≤
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) +
          (halfSquaredNorm x : EReal)
    rw [show
        (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x :
          EReal) = 0 by
      change
        (ι[closure
            (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = 0
      simp [indicator_apply, hxClosure_image]]
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) = 0 by
      change
        (ι[(((orthogonalClosedSubmodule U).orthogonalProjection : H →
              orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = 0
      simp [indicator_apply, hxA_image]]
  · by_cases hxClosure :
      x ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))
    · -- Outside the raw projected image, the raw owner is already `⊤`.
      have hxA_image :
          x ∉
            (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H)) := by
        simpa [hA_eq] using hxA
      have hxClosure_image :
          x ∈
            closure
              (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                  orthogonalClosedSubmodule U) '' (V : Set H)) := by
        simpa [hA_eq] using hxClosure
      change
        (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x :
            EReal) +
            (halfSquaredNorm x : EReal) ≤
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) +
            (halfSquaredNorm x : EReal)
      have hhalf_ne_bot : (halfSquaredNorm x : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x).2
      rw [show
          (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x :
            EReal) = 0 by
        change
          (ι[closure
              (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                  orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = 0
        simp [indicator_apply, hxClosure_image]]
      rw [show
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) = ⊤ by
        change
          (ι[(((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = ⊤
        simp [indicator_apply, hxA_image]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp
    · -- Outside the closure, both indicators are `⊤`, so the comparison is immediate.
      have hxA_image :
          x ∉
            (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H)) := by
        simpa [hA_eq] using hxA
      have hxClosure_image :
          x ∉
            closure
              (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                  orthogonalClosedSubmodule U) '' (V : Set H)) := by
        simpa [hA_eq] using hxClosure
      change
        (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x :
            EReal) +
            (halfSquaredNorm x : EReal) ≤
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) +
            (halfSquaredNorm x : EReal)
      have hhalf_ne_bot : (halfSquaredNorm x : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x).2
      rw [show
          (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x :
            EReal) = ⊤ by
        change
          (ι[closure
              (((orthogonalClosedSubmodule U).orthogonalProjection : H →
                  orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = ⊤
        simp [indicator_apply, hxClosure_image]]
      rw [show
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] x : EReal) = ⊤ by
        change
          (ι[(((orthogonalClosedSubmodule U).orthogonalProjection : H →
                orthogonalClosedSubmodule U) '' (V : Set H))] x : EReal) = ⊤
        simp [indicator_apply, hxA_image]]

/-- Helper for Remark 16.46: replacing the projected image by its closure preserves the `Γ₀`
structure, because the closure indicator is closed convex and the quadratic tail is unchanged. -/
private theorem projectedImageClosureOwner_mem_gammaZero_l2
    (U V : Submodule ℝ L2Nat) :
    (projectedImageClosureOwner U V) ∈ Γ₀(orthogonalClosedSubmodule U) := by
  let K : Submodule ℝ L2Nat := Uᗮ
  let E := ↥K
  let A : Submodule ℝ E := by
    simpa [E, K, orthogonalClosedSubmodule, projectedImageSubmodule] using
      projectedImageSubmodule U V
  letI : Module ℝ E := by
    change Module ℝ ↥K
    infer_instance
  let hE_complete : CompleteSpace E := U.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace E := hE_complete
  have hclosure_indicator :
      (ι[closure (A : Set E)] : E → Set.Ioi (⊥ : EReal)) ∈ Γ₀(E) := by
    -- The closure of a submodule is a closed convex set containing the origin.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ isClosed_closure ?_
    · exact ⟨0, subset_closure (show (0 : E) ∈ A by simp [A])⟩
    · simpa [Submodule.topologicalClosure_coe] using
        (A.topologicalClosure.convex : Convex ℝ (A.topologicalClosure : Set E))
  -- Add the unchanged quadratic tail through the local `Γ₀` stability helper.
  simpa [projectedImageClosureOwner, E, K, orthogonalClosedSubmodule] using
    @pointwiseAdd_halfSquaredNorm_mem_gammaZero_local E _ _ hE_complete
      (ι[closure (A : Set E)]) hclosure_indicator

/-- Helper for Remark 16.46: the closed comparison owner is a lower semicontinuous convex
minorant of the raw projected-image owner, so it lies below the latter's lsc convex envelope. -/
private theorem projectedImageClosureOwner_le_lowerSemicontinuousConvexEnvelope_l2
    (U V : Submodule ℝ L2Nat) :
    (projectedImageClosureOwner U V).asEReal ≤
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) := by
  let K : Submodule ℝ L2Nat := Uᗮ
  let E := ↥K
  let hE_complete : CompleteSpace E := U.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace E := hE_complete
  have hclosure_gamma :
      projectedImageClosureOwner U V ∈ Γ₀(E) := by
    simpa [E, K, orthogonalClosedSubmodule] using
      projectedImageClosureOwner_mem_gammaZero_l2 U V
  have hclosure_lsc :
      LowerSemicontinuous (projectedImageClosureOwner U V).asEReal :=
    -- The `Γ₀` package already records lower semicontinuity of the `EReal` owner.
    hclosure_gamma.1
  have hclosure_conv :
      Convex ℝ (epigraph (projectedImageClosureOwner U V).asEReal) :=
    -- Likewise, the closure owner has convex epigraph because it belongs to `Γ₀`.
    convex_epigraph_asEReal_of_mem_gammaZero hclosure_gamma
  -- Apply the maximality property of the lsc convex envelope to the closed comparison owner.
  exact
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      (H := E)
      hclosure_lsc hclosure_conv (by
        simpa [E, K, orthogonalClosedSubmodule] using projectedImageClosureOwner_le_rawOwner U V)

/-- Helper for Remark 16.46: the raw projected-image owner has convex epigraph, because its
effective domain is the projected submodule and on that submodule it agrees with
`halfSquaredNorm`. -/
private theorem convex_epigraph_projectedImageRawOwner
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H) :
    Convex ℝ (epigraph ((projectedImageRawOwner U V).asEReal)) := by
  let K := orthogonalClosedSubmodule U
  let A : Submodule ℝ K := projectedImageSubmodule U V
  have hraw_def :
      projectedImageRawOwner U V = ((ι[(A : Set K)]) + halfSquaredNorm) := by
    rfl
  have hhalf_conv :
      ConvexOn (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))
        (effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) :=
    (mem_gammaZero_iff.mp (halfSquaredNorm_mem_gammaZero_local (H := K))).2
  refine (convex_epigraph_iff_jensen_on_dom ((projectedImageRawOwner U V).asEReal)).2 ?_
  intro x y hx hy a ha0 ha1
  have hxA : x ∈ (A : Set K) := by
    rw [mem_dom_iff] at hx
    by_contra hxA
    have htop : ((projectedImageRawOwner U V x : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
      rw [hraw_def]
      change (ι[(A : Set K)] x : EReal) + (halfSquaredNorm x : EReal) = ⊤
      have hhalf_ne_bot : (halfSquaredNorm x : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x).2
      rw [show (ι[(A : Set K)] x : EReal) = ⊤ by simp [indicator_apply, hxA]]
      simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
    exact (lt_top_iff_ne_top.mp hx) htop
  have hyA : y ∈ (A : Set K) := by
    rw [mem_dom_iff] at hy
    by_contra hyA
    have htop : ((projectedImageRawOwner U V y : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
      rw [hraw_def]
      change (ι[(A : Set K)] y : EReal) + (halfSquaredNorm y : EReal) = ⊤
      have hhalf_ne_bot : (halfSquaredNorm y : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm y).2
      rw [show (ι[(A : Set K)] y : EReal) = ⊤ by simp [indicator_apply, hyA]]
      simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
    exact (lt_top_iff_ne_top.mp hy) htop
  have hxyA : a • x + (1 - a) • y ∈ (A : Set K) := by
    -- The projected image is a submodule, so it is convex.
    refine A.convex hxA hyA ha0.le (sub_nonneg.mpr ha1.le) ?_
    ring
  have hx_half : x ∈ effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  have hy_half : y ∈ effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  -- On the projected submodule the indicator vanishes, so Jensen reduces to the quadratic term.
  rw [hraw_def]
  change
    (ι[(A : Set K)] (a • x + (1 - a) • y) : EReal) + (halfSquaredNorm (a • x + (1 - a) • y) : EReal) ≤
      a * ((ι[(A : Set K)] x : EReal) + (halfSquaredNorm x : EReal)) +
        (1 - a) * ((ι[(A : Set K)] y : EReal) + (halfSquaredNorm y : EReal))
  rw [show (ι[(A : Set K)] (a • x + (1 - a) • y) : EReal) = 0 by simp [indicator_apply, hxyA]]
  rw [show (ι[(A : Set K)] x : EReal) = 0 by simp [indicator_apply, hxA]]
  rw [show (ι[(A : Set K)] y : EReal) = 0 by simp [indicator_apply, hyA]]
  simpa using hhalf_conv.ineq hx_half hy_half ha0 ha1

/-- Helper for Remark 16.46: package the Example 3.41 projected bad point together with the raw
owner `ι[A] + ‖·‖²/2`, the closed comparison owner `ι[closure A] + ‖·‖²/2`, and the pointwise
gap facts needed for the later lsc-envelope comparison. -/
private theorem projectedImageRawDualModelAtBadPoint_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (u0 : orthogonalClosedSubmodule U),
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
      ((projectedImageClosureOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) < ⊤ ∧
      (projectedImageClosureOwner U V).asEReal ≤ (projectedImageRawOwner U V).asEReal := by
  rcases projectedImageIndicatorClosureGap_l2 with
    ⟨U, V, u0, hu0_closure, hu0_not_mem, hu0_indicator_closure, hu0_indicator_raw⟩
  refine ⟨U, V, u0, hu0_closure, hu0_not_mem, ?_, ?_, projectedImageClosureOwner_le_rawOwner U V⟩
  · -- At the bad point, the raw projected-image indicator contributes `⊤`.
    change
      (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u0 : EReal) +
          (halfSquaredNorm u0 : EReal) = ⊤
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    rw [hu0_indicator_raw]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  · -- The closed comparison owner stays finite because the closure indicator vanishes there.
    have hhalf :
        (halfSquaredNorm u0 : EReal) < ⊤ := by
      rw [halfSquaredNorm_apply]
      exact EReal.coe_lt_top ((‖u0‖ ^ 2) / 2 : ℝ)
    change
      (ι[closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u0 : EReal) +
          (halfSquaredNorm u0 : EReal) < ⊤
    rw [hu0_indicator_closure]
    simpa using hhalf

/-- Helper for Remark 16.46: the lower semicontinuous convex envelope of the raw projected-image
owner is already finite at the packaged bad point, because the bad point lies in the closure of
the projected image while the quadratic term varies continuously there. -/
private theorem projectedImageRawOwnerEnvelopeFiniteAtBadPoint_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (u0 : orthogonalClosedSubmodule U),
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ :=
    by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, _hV_closed, u0, hu0_closure, hu0_not_mem⟩
  let K : Submodule ℝ L2Nat := Uᗮ
  let E := ↥K
  let A : Submodule ℝ E := by
    simpa [E, K, orthogonalClosedSubmodule, projectedImageSubmodule] using
      projectedImageSubmodule U V
  letI : Module ℝ E := by
    change Module ℝ ↥K
    infer_instance
  let hE_complete : CompleteSpace E := U.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace E := hE_complete
  have hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    -- Outside the projected image, the indicator branch makes the raw owner equal `⊤`.
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    have hu0_not_mem_A : u0 ∉ (A : Set E) := by
      intro hu0_mem_A
      have hu0_mem_projected :
          u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
        change u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) at hu0_mem_A
        exact hu0_mem_A
      exact hu0_not_mem hu0_mem_projected
    change
      (ι[(A : Set E)] u0 : EReal) + (halfSquaredNorm u0 : EReal) = ⊤
    rw [show (ι[(A : Set E)] u0 : EReal) = ⊤ by
      simpa [indicator_apply] using hu0_not_mem_A]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  have hu0_env_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
    let q : E → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
    have hcont_q : Continuous q := by
      have hnorm_sq : Continuous fun x : E ↦ ‖x‖ ^ 2 := by
        simpa using (continuous_norm.pow 2 : Continuous fun x : E ↦ ‖x‖ ^ 2)
      -- The quadratic graph is continuous, so closure points of the projected image stay closure
      -- points after adding the real height `‖x‖² / 2`.
      simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_const.mul hnorm_sq :
          Continuous fun x : ↥K ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
    have hgraph_closure :
        (u0, q u0) ∈ closure ((fun x : E ↦ (x, q x)) '' (A : Set E)) := by
      have hu0_image : (u0, q u0) ∈ (fun x : E ↦ (x, q x)) '' closure (A : Set E) := by
        exact ⟨u0, hu0_closure, rfl⟩
      -- Push the projected-image closure point through the quadratic graph map.
      exact image_closure_subset_closure_image (continuous_id.prodMk hcont_q) hu0_image
    have hgraph_subset :
        (fun x : E ↦ (x, q x)) '' (A : Set E) ⊆
          epigraph ((projectedImageRawOwner U V).asEReal) := by
      rintro _ ⟨x, hxA, rfl⟩
      rw [mem_epigraph_iff]
      -- On the projected image, the raw owner collapses to the quadratic tail.
      rw [projectedImageRawOwner]
      change
        (ι[(A : Set E)] x : EReal) + (halfSquaredNorm x : EReal) ≤ ((q x : ℝ) : EReal)
      rw [show (ι[(A : Set E)] x : EReal) = 0 by simp [indicator_apply, hxA]]
      rw [halfSquaredNorm_apply]
      simpa [q]
    have hraw_epi :
        (u0, q u0) ∈ closure (epigraph ((projectedImageRawOwner U V).asEReal)) :=
      closure_mono hgraph_subset hgraph_closure
    have henv_epi :
        (u0, q u0) ∈
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) := by
      have hepi_eq :
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) =
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) := by
        exact
          @epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
            E _ _ hE_complete ((projectedImageRawOwner U V).asEReal)
      have hclosure_convexHull :
          (u0, q u0) ∈
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) :=
        closure_mono (subset_convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal)))
          hraw_epi
      rw [hepi_eq]
      exact hclosure_convexHull
    have henv_le :
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 ≤
          ((q u0 : ℝ) : EReal) := by
      exact (mem_epigraph_iff _ _ _).mp henv_epi
    -- The real graph height bounds the envelope by a finite value at the bad point.
    exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
  exact ⟨U, V, u0, hu0_closure, hu0_not_mem, hu0_raw_top, hu0_env_finite⟩

/-- Helper for Remark 16.46: a projected bad point outside `P_{Uᗮ}(V)` already forces the raw
projected-image owner to be `⊤`, while the lower-semicontinuous convex envelope stays finite at
that same point. -/
private theorem projectedImageRawOwnerGapData_of_badPoint_l2
    (U V : Submodule ℝ L2Nat)
    (u0 : orthogonalClosedSubmodule U)
    (hu0_closure :
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)))
    (hu0_not_mem :
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
  let K : Submodule ℝ L2Nat := Uᗮ
  let E := ↥K
  let A : Submodule ℝ E := by
    simpa [E, K, orthogonalClosedSubmodule, projectedImageSubmodule] using
      projectedImageSubmodule U V
  letI : Module ℝ E := by
    change Module ℝ ↥K
    infer_instance
  let hE_complete : CompleteSpace E := U.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace E := hE_complete
  have hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    -- Outside the projected image, the indicator branch makes the raw owner equal `⊤`.
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    have hu0_not_mem_A : u0 ∉ (A : Set E) := by
      intro hu0_mem_A
      have hu0_mem_projected :
          u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
        change u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) at hu0_mem_A
        exact hu0_mem_A
      exact hu0_not_mem hu0_mem_projected
    change
      (ι[(A : Set E)] u0 : EReal) + (halfSquaredNorm u0 : EReal) = ⊤
    rw [show (ι[(A : Set E)] u0 : EReal) = ⊤ by
      simpa [indicator_apply] using hu0_not_mem_A]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  have hu0_env_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
    let q : E → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
    have hcont_q : Continuous q := by
      have hnorm_sq : Continuous fun x : E ↦ ‖x‖ ^ 2 := by
        simpa using (continuous_norm.pow 2 : Continuous fun x : E ↦ ‖x‖ ^ 2)
      -- The quadratic graph is continuous, so closure points of the projected image stay closure
      -- points after adding the real height `‖x‖² / 2`.
      simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_const.mul hnorm_sq :
          Continuous fun x : ↥K ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
    have hgraph_closure :
        (u0, q u0) ∈ closure ((fun x : E ↦ (x, q x)) '' (A : Set E)) := by
      have hu0_image : (u0, q u0) ∈ (fun x : E ↦ (x, q x)) '' closure (A : Set E) := by
        exact ⟨u0, hu0_closure, rfl⟩
      -- Push the projected-image closure point through the quadratic graph map.
      exact image_closure_subset_closure_image (continuous_id.prodMk hcont_q) hu0_image
    have hgraph_subset :
        (fun x : E ↦ (x, q x)) '' (A : Set E) ⊆
          epigraph ((projectedImageRawOwner U V).asEReal) := by
      rintro _ ⟨x, hxA, rfl⟩
      rw [mem_epigraph_iff]
      -- On the projected image, the raw owner collapses to the quadratic tail.
      rw [projectedImageRawOwner]
      change
        (ι[(A : Set E)] x : EReal) + (halfSquaredNorm x : EReal) ≤ ((q x : ℝ) : EReal)
      rw [show (ι[(A : Set E)] x : EReal) = 0 by simp [indicator_apply, hxA]]
      rw [halfSquaredNorm_apply]
      simpa [q]
    have hraw_epi :
        (u0, q u0) ∈ closure (epigraph ((projectedImageRawOwner U V).asEReal)) :=
      closure_mono hgraph_subset hgraph_closure
    have henv_epi :
        (u0, q u0) ∈
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) := by
      have hepi_eq :
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) =
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) := by
        exact
          @epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
            E _ _ hE_complete ((projectedImageRawOwner U V).asEReal)
      have hclosure_convexHull :
          (u0, q u0) ∈
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) :=
        closure_mono (subset_convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal)))
          hraw_epi
      rw [hepi_eq]
      exact hclosure_convexHull
    have henv_le :
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 ≤
          ((q u0 : ℝ) : EReal) := by
      exact (mem_epigraph_iff _ _ _).mp henv_epi
    -- The real graph height bounds the envelope by a finite value at the bad point.
    exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
  exact ⟨hu0_raw_top, hu0_env_finite⟩

/-- Helper for Remark 16.46: the same projected bad point also yields the geometric epigraph gap
needed by the replacement witness route, namely a point outside the raw epigraph but inside the
closure of its convex hull. -/
private theorem projectedImageRawEpigraphClosureGap_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (u0 : orthogonalClosedSubmodule U),
      let K := orthogonalClosedSubmodule U
      let q : K → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
      (u0, q u0) ∉ epigraph ((projectedImageRawOwner U V).asEReal) ∧
        (u0, q u0) ∈
          closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) :=
    by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, _hV_closed, u0, hu0_closure, hu0_not_mem⟩
  refine ⟨U, V, u0, ?_⟩
  let K : Submodule ℝ L2Nat := Uᗮ
  let E := ↥K
  let A : Submodule ℝ E := by
    simpa [E, K, orthogonalClosedSubmodule, projectedImageSubmodule] using
      projectedImageSubmodule U V
  let hE_complete : CompleteSpace E := U.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace E := hE_complete
  let q : E → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
  dsimp [K, q]
  have hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    -- The bad point lies outside the projected image, so the raw indicator branch is `⊤`.
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    have hu0_not_mem_A : u0 ∉ (A : Set E) := by
      intro hu0_mem_A
      have hu0_mem_projected :
          u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
        change u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) at hu0_mem_A
        exact hu0_mem_A
      exact hu0_not_mem hu0_mem_projected
    change
      (ι[(A : Set E)] u0 : EReal) +
          (halfSquaredNorm u0 : EReal) = ⊤
    rw [show
        (ι[(A : Set E)] u0 : EReal) = ⊤ by
      simpa [indicator_apply] using hu0_not_mem_A]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  have hcont_q : Continuous q := by
    have hnorm_sq : Continuous fun x : E ↦ ‖x‖ ^ 2 := by
      simpa using (continuous_norm.pow 2 : Continuous fun x : E ↦ ‖x‖ ^ 2)
    -- The same quadratic graph map transports closure points into the epigraph closure.
    simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (continuous_const.mul hnorm_sq :
        Continuous fun x : ↥K ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
  have hgraph_closure :
      (u0, q u0) ∈ closure ((fun x : E ↦ (x, q x)) '' (A : Set E)) := by
    have hu0_image : (u0, q u0) ∈ (fun x : E ↦ (x, q x)) '' closure (A : Set E) := by
      exact ⟨u0, hu0_closure, rfl⟩
    -- Push the bad-point closure witness through the quadratic graph embedding.
    exact image_closure_subset_closure_image (continuous_id.prodMk hcont_q) hu0_image
  have hgraph_subset :
      (fun x : E ↦ (x, q x)) '' (A : Set E) ⊆
        epigraph ((projectedImageRawOwner U V).asEReal) := by
    rintro _ ⟨x, hxA, rfl⟩
    rw [mem_epigraph_iff]
    -- On the projected image, the raw owner is exactly the quadratic height.
    rw [projectedImageRawOwner]
    change
      (ι[(A : Set E)] x : EReal) + (halfSquaredNorm x : EReal) ≤ ((q x : ℝ) : EReal)
    rw [show (ι[(A : Set E)] x : EReal) = 0 by simp [indicator_apply, hxA]]
    rw [halfSquaredNorm_apply]
    simpa [q]
  have hraw_epi :
      (u0, q u0) ∈ closure (epigraph ((projectedImageRawOwner U V).asEReal)) :=
    closure_mono hgraph_subset hgraph_closure
  have hclosure_convexHull :
      (u0, q u0) ∈ closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) :=
    closure_mono (subset_convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) hraw_epi
  refine ⟨?_, hclosure_convexHull⟩
  intro hu0_epi
  have hu0_le :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) ≤ ((q u0 : ℝ) : EReal) := by
    exact (mem_epigraph_iff _ _ _).mp hu0_epi
  -- The finite quadratic height cannot dominate the raw top value at the bad point.
  rw [hu0_raw_top] at hu0_le
  exact (not_le_of_gt (EReal.coe_lt_top _)) hu0_le

/-- Helper for Remark 16.46: the raw-epigraph indicator gap route on the plain product space is
retired and no longer participates in the active proof graph. -/
private theorem projectedImageRawEpigraphIndicatorGap_l2 :
    True := by
  trivial

/-- Helper for Remark 16.46: restricting the regularized witness sum to the orthogonal subtype
`Uᗮ` removes the indicator branch and leaves only the second witness owner. -/
private theorem pointwiseAdd_nonclosedSupWitness_eq_nonclosedSupWitnessG_on_orthogonalSubtype
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    let Uc : ClosedSubmodule ℝ H := ⟨Uᗮ, U.isClosed_orthogonal⟩
    (fun x : Uc ↦
      (((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x : Set.Ioi (⊥ : EReal)) :
        EReal)) =
      fun x : Uc ↦ (nonclosedSupWitnessG V hVq x : EReal) := by
  funext x
  -- Evaluate the ambient orthogonal-slice simplification on the subtype point `x`.
  simpa using
    pointwiseAdd_nonclosedSupWitness_eq_nonclosedSupWitnessG_of_mem_orthogonal
      U V hU hVq x.2

/-- Helper for Remark 16.46: once the restricted conjugate on `Uᗮ` is finite at an orthogonal
point `u`, Proposition 13.23 transports that finiteness back to the ambient conjugate of the
regularized witness sum. -/
private theorem mem_dom_conjugate_pointwiseAdd_nonclosedSupWitness_of_mem_restrictedDom
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    {u : H} (hu_orth : u ∈ (Uᗮ : Set H))
    (hu :
      (⟨u, hu_orth⟩ : orthogonalClosedSubmodule U) ∈
        dom
          ((fun x : orthogonalClosedSubmodule U ↦
            (((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x :
                Set.Ioi (⊥ : EReal)) : EReal))∗)) :
    u ∈ dom ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal∗) := by
  let Uc : ClosedSubmodule ℝ H := orthogonalClosedSubmodule U
  let F : H → EReal := (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal
  let Frest : Uc → EReal := fun x : Uc ↦ F x
  have hconj :
      Frest∗ ∘ Uc.orthogonalProjection = F∗ :=
    conjugate_restrict_comp_orthogonalProjection_of_dom_subset
      F Uc (dom_pointwiseAdd_nonclosedSupWitness_subset_orthogonal U V hU hVq)
  have hproj_eq : Uc.orthogonalProjection u = ⟨u, hu_orth⟩ := by
    -- On `Uᗮ`, the orthogonal projection is the identity after packaging the point in the subtype.
    simpa [Uc] using
      (Submodule.orthogonalProjection_mem_subspace_eq_self
        (⟨u, hu_orth⟩ : (Uc : Submodule ℝ H)))
  -- Rewrite the ambient conjugate value at `u` to the restricted conjugate value at `⟨u, hu_orth⟩`.
  rw [mem_dom_iff] at hu ⊢
  have hvalue :
      Frest∗ (⟨u, hu_orth⟩ : Uc) = F∗ u := by
    simpa [Function.comp, hproj_eq] using congrFun hconj u
  rw [← hvalue]
  exact hu

/-- Helper for Remark 16.46: outside `U ⊔ V`, the raw dual infimal convolution attached to the
regularized witness pair is forced to be `⊤`. -/
private theorem rawInfimalConvolution_nonclosedSupWitness_eq_top_of_not_mem_sup
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    {u : H} (hu : u ∉ (((U ⊔ V : Submodule ℝ H) : Set H))) :
    ((((nonclosedSupWitnessF U hU)∗[gammaZeroConjugate_mem_gammaZero hU]) □
        ((nonclosedSupWitnessG V hVq)∗[gammaZeroConjugate_mem_gammaZero hVq]) :
      H → EReal) u) = ⊤ := by
  have hFraw :
      ((nonclosedSupWitnessF U hU)∗[gammaZeroConjugate_mem_gammaZero hU]).asEReal =
        (ι[(U : Set H)] : H → EReal) := by
    simpa [nonclosedSupWitnessF, gammaZeroConjugate_apply] using
      biconjugate_eq_of_mem_gammaZero hU
  have hGraw :
      ((nonclosedSupWitnessG V hVq)∗[gammaZeroConjugate_mem_gammaZero hVq]).asEReal =
        ((ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) : H → EReal) := by
    simpa [nonclosedSupWitnessG, gammaZeroConjugate_apply] using
      biconjugate_eq_of_mem_gammaZero hVq
  let G : H → Set.Ioi (⊥ : EReal) := ι[(V : Set H)] + halfSquaredNorm
  change
    infimalConvolution
        (((nonclosedSupWitnessF U hU)∗[gammaZeroConjugate_mem_gammaZero hU]).asEReal)
        (((nonclosedSupWitnessG V hVq)∗[gammaZeroConjugate_mem_gammaZero hVq]).asEReal)
        u = ⊤
  rw [hFraw, hGraw]
  change
    (⨅ y : H,
      (ι[(U : Set H)] y : EReal) +
        ((G (u - y) : Set.Ioi (⊥ : EReal)) : EReal)) = ⊤
  refine iInf_eq_top.2 ?_
  intro y
  by_cases hyU : y ∈ (U : Set H)
  · have hu_sub_not_mem : u - y ∉ (V : Set H) := by
      intro hyV
      exact hu (Submodule.mem_sup.2 ⟨y, hyU, u - y, hyV, by abel⟩)
    have hFy_ne_bot : (ι[(U : Set H)] y : EReal) ≠ ⊥ := by
      simp [indicator_apply, hyU]
    have hhalf_ne_bot : (halfSquaredNorm (u - y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (halfSquaredNorm (u - y)).2
    have hGy_top : ((G (u - y) : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
      change (ι[(V : Set H)] (u - y) : EReal) + (halfSquaredNorm (u - y) : EReal) = ⊤
      rw [show (ι[(V : Set H)] (u - y) : EReal) = ⊤ by
        simp [indicator_apply, hu_sub_not_mem]]
      simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
    rw [hGy_top]
    simpa using EReal.add_top_of_ne_bot hFy_ne_bot
  · have hGy_ne_bot :
        ((G (u - y) : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ := by
      exact ne_of_gt (G (u - y)).2
    have hFy_top : (ι[(U : Set H)] y : EReal) = ⊤ := by
      simp [indicator_apply, hyU]
    rw [hFy_top]
    simpa using EReal.top_add_of_ne_bot hGy_ne_bot

/-- Helper for Remark 16.46: for the current Example 3.41 regularized family, a projected bad
point `u ∈ Uᗮ \ A` cannot lie in the restricted conjugate domain, because Proposition 13.23 would
transport that finiteness back to the ambient witness and contradict the already-proved identity-map
exactness of the ambient family. -/
private theorem not_mem_restrictedDom_conjugate_pointwiseAdd_nonclosedSupWitness_of_not_mem_projectedImage
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU : (ι[(U : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
    {u : H} (hu_orth : u ∈ (Uᗮ : Set H))
    (huA :
      (⟨u, hu_orth⟩ : orthogonalClosedSubmodule U) ∉
        (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    (⟨u, hu_orth⟩ : orthogonalClosedSubmodule U) ∉
      dom
        ((fun x : orthogonalClosedSubmodule U ↦
          (((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x :
              Set.Ioi (⊥ : EReal)) : EReal))∗) := by
  let Uc : ClosedSubmodule ℝ H := orthogonalClosedSubmodule U
  let A : Submodule ℝ Uc := projectedImageSubmodule U V
  intro hu_dom
  have hu_dom_ambient :
      u ∈ dom ((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal∗) :=
    mem_dom_conjugate_pointwiseAdd_nonclosedSupWitness_of_mem_restrictedDom
      U V hU hVq hu_orth hu_dom
  have hA_eq :
      (A : Set Uc) = Uc.orthogonalProjection '' (V : Set H) := by
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hproj_eq : Uc.orthogonalProjection u = ⟨u, hu_orth⟩ := by
    -- The packaged orthogonal point is fixed by the projection onto `Uᗮ`.
    simpa [Uc] using
      (Submodule.orthogonalProjection_mem_subspace_eq_self
        (⟨u, hu_orth⟩ : (Uc : Submodule ℝ H)))
  have hu_not_mem_sup : u ∉ (((U ⊔ V : Submodule ℝ H) : Set H)) := by
    intro hu_sup
    have hproj_sup :
        Uc.orthogonalProjection u ∈ Uc.orthogonalProjection '' (((U ⊔ V : Submodule ℝ H) : Set H)) :=
      ⟨u, hu_sup, rfl⟩
    have hproj_image :
        Uc.orthogonalProjection u ∈ Uc.orthogonalProjection '' (V : Set H) := by
      simpa [Uc, orthogonalProjection_image_sup_eq_image U V] using hproj_sup
    have huA_mem : (⟨u, hu_orth⟩ : Uc) ∈ (A : Set Uc) := by
      simpa [hA_eq, hproj_eq] using hproj_image
    exact huA huA_mem
  have hraw_top :
      ((((nonclosedSupWitnessF U hU)∗[gammaZeroConjugate_mem_gammaZero hU]) □
          ((nonclosedSupWitnessG V hVq)∗[gammaZeroConjugate_mem_gammaZero hVq]) :
        H → EReal) u) = ⊤ :=
    rawInfimalConvolution_nonclosedSupWitness_eq_top_of_not_mem_sup U V hU hVq hu_not_mem_sup
  have hgap :
      (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq).asEReal∗ u ≠
        ((((nonclosedSupWitnessF U hU)∗[gammaZeroConjugate_mem_gammaZero hU]) □
          ((nonclosedSupWitnessG V hVq)∗[gammaZeroConjugate_mem_gammaZero hVq]) :
          H → EReal) u) := by
    rw [mem_dom_iff] at hu_dom_ambient
    intro hEq
    exact (lt_top_iff_ne_top.mp hu_dom_ambient) (hEq.trans hraw_top)
  have hnot_exact :
      ¬ ExactDualInfimalConvolutionFormula
        (gammaZeroConjugate_mem_gammaZero hU)
        (gammaZeroConjugate_mem_gammaZero hVq)
        (ContinuousLinearMap.id ℝ H) :=
    notExactDualInfimalConvolutionFormulaId_of_conjugateGapAt
      (gammaZeroConjugate_mem_gammaZero hU)
      (gammaZeroConjugate_mem_gammaZero hVq) hgap
  -- The already-proved exactness of the ambient family rules out this restricted-domain witness.
  exact hnot_exact (exactDualInfimalConvolutionFormula_nonclosedSupWitness U V hU hVq)

/-- Helper for Remark 16.46: the Example 3.41 projected-image route is now reduced to one
packaged frontier datum. It provides the concrete closed subspaces, the associated regularized
`Γ₀` owners, the Chapter 16 sum rule for that ambient family, and the verified obstruction that
the projected bad point still lies outside the restricted conjugate domain. -/
private theorem existsProjectedImageRegularizedWitnessFrontier_l2 :
    ∃ (U V : Submodule ℝ L2Nat)
      (hU : (ι[(U : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat))
      (hVq : (ι[(V : Set L2Nat)] + halfSquaredNorm : L2Nat → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat))
      (u0 : orthogonalClosedSubmodule U),
      ¬ IsClosed (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)).Nonempty ∧
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      (effectiveDomain (nonclosedSupWitnessF U hU) ∩
          effectiveDomain (nonclosedSupWitnessG V hVq)).Nonempty ∧
      ((∂ (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) :
          SetValuedOperator L2Nat L2Nat) =
        ∂ (nonclosedSupWitnessF U hU) + ∂ (nonclosedSupWitnessG V hVq)) ∧
      u0 ∉
        dom
          ((fun x : orthogonalClosedSubmodule U ↦
            (((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x :
                Set.Ioi (⊥ : EReal)) : EReal))∗) := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  have hU :
      (ι[(U : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      ⟨0, U.zero_mem⟩ hU_closed U.convex
  have hV :
      (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      ⟨0, V.zero_mem⟩ hV_closed V.convex
  have hVq :
      (ι[(V : Set L2Nat)] + halfSquaredNorm : L2Nat → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero_local (ι[(V : Set L2Nat)]) hV
  have hA_not_closed :
      ¬ IsClosed (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
    intro hA_closed
    have hu0_mem :
        u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
      rw [← hA_closed.closure_eq]
      exact hu0_closure
    exact hu0_not_mem hu0_mem
  have hA_nonempty :
      (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)).Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈
      Submodule.map (orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap V
    exact Submodule.zero_mem _
  have hcurrent :
      (effectiveDomain (nonclosedSupWitnessF U hU) ∩
          effectiveDomain (nonclosedSupWitnessG V hVq)).Nonempty ∧
        ((∂ (nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) :
            SetValuedOperator L2Nat L2Nat) =
          ∂ (nonclosedSupWitnessF U hU) + ∂ (nonclosedSupWitnessG V hVq)) ∧
        ExactDualInfimalConvolutionFormula
          (gammaZeroConjugate_mem_gammaZero hU)
          (gammaZeroConjugate_mem_gammaZero hVq)
          (ContinuousLinearMap.id ℝ L2Nat) :=
    nonclosedSupWitness_hasSumRule_andExactFormula U V hU hVq
  have hu0_not_restrictedDom :
      u0 ∉
        dom
          ((fun x : orthogonalClosedSubmodule U ↦
            (((nonclosedSupWitnessF U hU + nonclosedSupWitnessG V hVq) x :
                Set.Ioi (⊥ : EReal)) : EReal))∗) := by
    -- The projected bad point stays outside the restricted conjugate domain for the ambient
    -- regularized family, so the remaining work must change the owner construction itself.
    exact
      not_mem_restrictedDom_conjugate_pointwiseAdd_nonclosedSupWitness_of_not_mem_projectedImage
        U V hU hVq u0.2 (by simpa using hu0_not_mem)
  -- Package the fully verified projected-image frontier for the final theorem.
  refine ⟨U, V, hU, hVq, u0, hA_not_closed, hA_nonempty, hu0_closure, hu0_not_mem, ?_⟩
  exact ⟨hcurrent.1, hcurrent.2.1, hu0_not_restrictedDom⟩

/-- Helper for Remark 16.46: restricting the second regularized witness owner to the orthogonal
subtype `Uᗮ` preserves the `Γ₀` structure needed for the composite-witness packaging route. -/
private theorem restrict_nonclosedSupWitnessG_mem_gammaZero
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    (fun x : orthogonalClosedSubmodule U ↦ nonclosedSupWitnessG V hVq x) ∈
      Γ₀(orthogonalClosedSubmodule U) := by
  have hG : nonclosedSupWitnessG V hVq ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hVq
  rw [mem_gammaZero_iff] at hG ⊢
  constructor
  · -- Lower semicontinuity survives restriction to the closed orthogonal subtype.
    simpa [orthogonalClosedSubmodule] using hG.1.comp continuous_subtype_val
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The restricted owner is finite at the origin because the ambient owner has full domain.
      refine ⟨0, ?_⟩
      have hzero :
          (0 : H) ∈ effectiveDomain (nonclosedSupWitnessG V hVq) := by
        simpa [effectiveDomain_nonclosedSupWitnessG_eq_univ V hVq]
      simpa [mem_effectiveDomain_iff] using hzero
    · intro x hx y hy a ha0 ha1
      have hx' : (x : H) ∈ effectiveDomain (nonclosedSupWitnessG V hVq) := by
        simpa [mem_effectiveDomain_iff] using hx
      have hy' : (y : H) ∈ effectiveDomain (nonclosedSupWitnessG V hVq) := by
        simpa [mem_effectiveDomain_iff] using hy
      -- Convexity is inherited pointwise from the ambient `Γ₀` owner.
      simpa using hG.2.ineq hx' hy' ha0 ha1

/-- Helper for Remark 16.46: the restricted second witness owner on `Uᗮ` still has full effective
domain, so any remaining obstruction is no longer about properness of the restricted owner. -/
private theorem effectiveDomain_restrict_nonclosedSupWitnessG_eq_univ
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hVq : (ι[(V : Set H)] + halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H)) :
    effectiveDomain (fun x : orthogonalClosedSubmodule U ↦ nonclosedSupWitnessG V hVq x) =
      Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rw [mem_effectiveDomain_iff]
    have hx_mem : (x : H) ∈ effectiveDomain (nonclosedSupWitnessG V hVq) := by
      simpa [effectiveDomain_nonclosedSupWitnessG_eq_univ V hVq]
    simpa [mem_effectiveDomain_iff] using hx_mem

/-- Helper for Remark 16.46: freeze the linear graph of a continuous linear map as a plain set on
the product space, so the dead product-graph branch still has a canonical statement surface. -/
private def linearGraphSet
    {A : Type*} {B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (LAB : A →L[ℝ] B) : Set (A × B) :=
  (LAB.toLinearMap.graph : Set (A × B))

/-- Helper for Remark 16.46: the horizontal slice in `L2Nat × Uᗮ` is the graph of the zero map,
so its points are exactly the pairs with vanishing `Uᗮ` coordinate. -/
private abbrev horizontalOrthogonalSliceSet
    (U : Submodule ℝ L2Nat) :
    Set (L2Nat × orthogonalClosedSubmodule U) :=
  linearGraphSet (0 : L2Nat →L[ℝ] orthogonalClosedSubmodule U)

/-- Helper for Remark 16.46: the projected-image graph remembers exactly those pairs
`(v, P_{Uᗮ} v)` with `v ∈ V`. This is the product-space carrier used by the vertical-slice route.
-/
private def projectedImageGraphSet
    (U V : Submodule ℝ L2Nat) :
    Set (L2Nat × orthogonalClosedSubmodule U) :=
  {p | p.1 ∈ (V : Set L2Nat) ∧
      p.2 = (orthogonalClosedSubmodule U).orthogonalProjection p.1}

/-- Helper for Remark 16.46: on the vertical slice `(0,u)`, membership in the sum of the
horizontal graph and the projected-image graph is equivalent to `u ∈ P_{Uᗮ}(V)`. This is the
sign/order check for the product-space normalization. -/
private theorem verticalGraphSlice_mem_sum_iff_projectedImage
    (U V : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    ((0, u) : L2Nat × orthogonalClosedSubmodule U) ∈
        horizontalOrthogonalSliceSet U + projectedImageGraphSet U V ↔
      u ∈ projectedImageSubmodule U V := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have ha_zero : a.2 = 0 := by
      simpa [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff] using ha
    rcases hb with ⟨hbV, hbproj⟩
    have hb_second : b.2 = u := by
      have hab_snd := congrArg Prod.snd hab
      calc
        b.2 = (0 : orthogonalClosedSubmodule U) + b.2 := by
          exact (zero_add b.2).symm
        _ = a.2 + b.2 := by rw [ha_zero]
        _ = u := hab_snd
    exact Submodule.mem_map.mpr ⟨b.1, hbV, hbproj.symm.trans hb_second⟩
  · intro hu
    rcases Submodule.mem_map.mp hu with ⟨v, hvV, hvproj⟩
    refine ⟨(-v, 0), ?_, (v, u), ?_, ?_⟩
    · -- The first summand stays on the horizontal zero graph.
      change (0 : orthogonalClosedSubmodule U) = 0
      rfl
    · -- The second summand records the projected-image witness `u = P_{Uᗮ} v`.
      exact ⟨hvV, hvproj.symm⟩
    · -- Adding the horizontal correction `(-v, 0)` recovers the vertical slice point `(0,u)`.
      apply Prod.ext
      · simp
      · exact (zero_add u)

/- Route correction for Remark 16.46: the auxiliary epigraph branch is retired and no longer
participates in the active proof graph.

/-- Helper for Remark 16.46: the auxiliary epigraph witness space adds one real height coordinate
to the product witness space `L2Nat × Uᗮ`. -/
private abbrev productGraphEpigraphSpace
    (U : Submodule ℝ L2Nat) :=
  (L2Nat × orthogonalClosedSubmodule U) × ℝ

/-- Helper for Remark 16.46: the zero-height horizontal slice is the epigraph lift of the retired
horizontal graph witness. -/
private abbrev horizontalSliceEpigraphSet
    (U : Submodule ℝ L2Nat) :
    Set (productGraphEpigraphSpace U) :=
  {z | z.1 ∈ horizontalOrthogonalSliceSet U ∧ z.2 = 0}

/-- Helper for Remark 16.46: the graph-side epigraph lift remembers a projected-image graph point
and any height above its quadratic tail. -/
private def projectedImageGraphEpigraphSet
    (U V : Submodule ℝ L2Nat) :
    Set (productGraphEpigraphSpace U) :=
  {z | z.1 ∈ projectedImageGraphSet U V ∧ (halfSquaredNorm z.1.2 : EReal) ≤ z.2}

/-- Helper for Remark 16.46: the surviving raw epigraph obstruction only depends on the second
product coordinate and the added height variable. -/
private abbrev pullbackProjectedImageRawEpigraphSet
    (U V : Submodule ℝ L2Nat) :
    Set (productGraphEpigraphSpace U) :=
  {z | (z.1.2, z.2) ∈ epigraph ((projectedImageRawOwner U V).asEReal)}

/-- Helper for Remark 16.46: the zero-height horizontal slice is a closed convex epigraph set, so
its indicator is a `Γ₀` owner on the auxiliary epigraph space. -/
private theorem horizontalSliceEpigraphIndicator_mem_gammaZero_l2
    (U : Submodule ℝ L2Nat) :
    let Eepi := productGraphEpigraphSpace U
    (ι[horizontalSliceEpigraphSet U] : Eepi → Set.Ioi (⊥ : EReal)) ∈ Γ₀(Eepi) := by
  let Eepi := productGraphEpigraphSpace U
  have hclosed_zeroSecond :
      IsClosed {z : Eepi | z.1.2 = (0 : orthogonalClosedSubmodule U)} := by
    -- The dormant `Uᗮ` coordinate is the zero set of the continuous second projection.
    exact isClosed_eq (continuous_snd.comp continuous_fst) continuous_const
  have hclosed_zeroHeight :
      IsClosed {z : Eepi | z.2 = 0} := by
    -- The added height coordinate is also pinned to zero by a closed equation.
    exact isClosed_eq continuous_snd continuous_const
  have hclosed :
      IsClosed (horizontalSliceEpigraphSet U : Set Eepi) := by
    -- Unfold the slice once so closedness is just the intersection of the two zero sets above.
    simpa [Eepi, horizontalSliceEpigraphSet, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff] using hclosed_zeroSecond.inter hclosed_zeroHeight
  refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ hclosed ?_
  · -- The origin belongs to the horizontal slice at height zero.
    exact ⟨(((0 : L2Nat), 0), 0), by
      simp [horizontalSliceEpigraphSet, horizontalOrthogonalSliceSet, linearGraphSet,
        LinearMap.mem_graph_iff]⟩
  · intro x hx y hy a ha0 ha1
    rcases hx with ⟨hx_slice, hx_height⟩
    rcases hy with ⟨hy_slice, hy_height⟩
    constructor
    · -- Convex combinations keep the dormant `Uᗮ` coordinate equal to `0`.
      simpa [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, hx_slice,
        hy_slice]
    · -- The height coordinate also stays at `0` under convex combinations.
      nlinarith [hx_height, hy_height]

/-- Helper for Remark 16.46: the graph-side quadratic epigraph set is closed and convex, so its
indicator is a `Γ₀` owner on the auxiliary epigraph space. -/
private theorem projectedImageGraphEpigraphIndicator_mem_gammaZero_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    let Eepi := productGraphEpigraphSpace U
    (ι[projectedImageGraphEpigraphSet U V] : Eepi → Set.Ioi (⊥ : EReal)) ∈ Γ₀(Eepi) := by
  let Eepi := productGraphEpigraphSpace U
  let K := orthogonalClosedSubmodule U
  have hclosed_memV :
      IsClosed {z : Eepi | z.1.1 ∈ (V : Set L2Nat)} := by
    -- Closedness of `V` pulls back along the first product projection.
    exact hV_closed.preimage (continuous_fst.comp continuous_fst)
  have hclosed_graph :
      IsClosed {z : Eepi | z.1.2 = (orthogonalClosedSubmodule U).orthogonalProjection z.1.1} := by
    -- The graph equation is the equality of two continuous coordinate maps.
    exact isClosed_eq
      (continuous_snd.comp continuous_fst)
      ((orthogonalClosedSubmodule U).orthogonalProjection.continuous.comp
        (continuous_fst.comp continuous_fst))
  have hclosed_halfSquaredEpi :
      IsClosed (epigraph (fun x : K ↦ (halfSquaredNorm x : EReal))) := by
    -- The quadratic epigraph is closed because `halfSquaredNorm` is lower semicontinuous.
    exact
      (lowerSemicontinuous_iff_isClosed_epigraph
        (fun x : K ↦ (halfSquaredNorm x : EReal))).1
        (halfSquaredNorm_mem_gammaZero_local (H := K)).1
  have hclosed_height :
      IsClosed {z : Eepi | (halfSquaredNorm z.1.2 : EReal) ≤ z.2} := by
    have hcoord : Continuous fun z : Eepi ↦ (z.1.2, z.2) := by
      -- The height condition is the pullback of the quadratic epigraph along the coordinate map.
      exact (continuous_snd.comp continuous_fst).prodMk continuous_snd
    simpa [epigraph] using hclosed_halfSquaredEpi.preimage hcoord
  have hclosed :
      IsClosed (projectedImageGraphEpigraphSet U V : Set Eepi) := by
    -- The epigraph set is the intersection of the `V`-constraint, the graph equation, and the
    -- quadratic height inequality.
    simpa [Eepi, projectedImageGraphEpigraphSet] using
      hclosed_memV.inter (hclosed_graph.inter hclosed_height)
  refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ hclosed ?_
  · -- The origin satisfies the graph constraint and the quadratic height inequality.
    exact ⟨(((0 : L2Nat), 0), 0), by
      simp [projectedImageGraphEpigraphSet, projectedImageGraphSet, halfSquaredNorm_apply]⟩
  · intro x hx y hy a ha0 ha1
    rcases hx with ⟨hx_graph, hx_height⟩
    rcases hy with ⟨hy_graph, hy_height⟩
    rcases hx_graph with ⟨hxV, hxproj⟩
    rcases hy_graph with ⟨hyV, hyproj⟩
    have hhalf_conv :
        ConvexOn (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))
          (effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) :=
      (mem_gammaZero_iff.mp (halfSquaredNorm_mem_gammaZero_local (H := K))).2
    have hx_half : x.1.2 ∈ effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
      rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
    have hy_half : y.1.2 ∈ effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
      rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
    constructor
    · constructor
      · -- Convex combinations preserve `V`-membership.
        simpa using V.convex hxV hyV ha0 ha1
      · -- The graph equation is linear in the ambient coordinate.
        apply Subtype.ext
        change a • ((x.1.2 : K) : L2Nat) + (1 - a) • ((y.1.2 : K) : L2Nat) =
          (((orthogonalClosedSubmodule U).orthogonalProjection
            (a • x.1.1 + (1 - a) • y.1.1) : K) : L2Nat)
        rw [(orthogonalClosedSubmodule U).orthogonalProjection.map_add,
          (orthogonalClosedSubmodule U).orthogonalProjection.map_smul,
          (orthogonalClosedSubmodule U).orthogonalProjection.map_smul, hxproj, hyproj]
        rfl
    · -- Jensen convexity of `halfSquaredNorm` keeps the epigraph height inequality valid.
      have ha0E : (0 : EReal) ≤ a := by
        exact_mod_cast ha0
      have ha1E : (0 : EReal) ≤ 1 - a := by
        exact_mod_cast sub_nonneg.mpr ha1
      calc
        (halfSquaredNorm (a • x.1.2 + (1 - a) • y.1.2) : EReal)
            ≤ a * (halfSquaredNorm x.1.2 : EReal) + (1 - a) * (halfSquaredNorm y.1.2 : EReal) := by
                simpa using hhalf_conv.ineq hx_half hy_half ha0 ha1
        _ ≤ a * x.2 + (1 - a) * y.2 := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hx_height ha0E)
                (mul_le_mul_of_nonneg_left hy_height ha1E)

/-- Helper for Remark 16.46: the auxiliary epigraph pullback is exactly the Minkowski sum of the
zero-height horizontal slice and the graph-side quadratic epigraph set. -/
private theorem horizontalSliceEpigraphSet_add_projectedImageGraphEpigraphSet_eq_pullbackRawEpigraph_l2
    (U V : Submodule ℝ L2Nat) :
    horizontalSliceEpigraphSet U + projectedImageGraphEpigraphSet U V =
      pullbackProjectedImageRawEpigraphSet U V := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with ⟨ha_slice, ha_height⟩
    rcases hb with ⟨hb_graph, hb_height⟩
    rcases hb_graph with ⟨hbV, hbproj⟩
    have ha_second : a.1.2 = 0 := by
      simpa [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff] using ha_slice
    have hz_second : (a.1 + b.1).2 = b.1.2 := by
      simpa [ha_second]
    have hz_mem :
        (a.1 + b.1).2 ∈ projectedImageSubmodule U V := by
      refine Submodule.mem_map.mpr ⟨b.1.1, hbV, ?_⟩
      exact hbproj.symm.trans hz_second.symm
    have hz_height : (halfSquaredNorm ((a.1 + b.1).2) : EReal) ≤ b.2 := by
      simpa [hz_second] using hb_height
    -- On the lifted sum, the second coordinate is a genuine projected-image point and the height
    -- constraint comes entirely from the graph-side epigraph summand.
    change (((a.1 + b.1).2, a.2 + b.2) : orthogonalClosedSubmodule U × ℝ) ∈
      epigraph ((projectedImageRawOwner U V).asEReal)
    rw [mem_epigraph_iff, projectedImageRawOwner]
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] ((a.1 + b.1).2) :
          EReal) = 0 by
      simp [indicator_apply, hz_mem]]
    simpa [ha_height] using hz_height
  · intro hz
    change ((z.1.2, z.2) : orthogonalClosedSubmodule U × ℝ) ∈
      epigraph ((projectedImageRawOwner U V).asEReal) at hz
    rw [mem_epigraph_iff, projectedImageRawOwner] at hz
    have hz_mem :
        z.1.2 ∈ projectedImageSubmodule U V := by
      by_contra hz_mem
      have hhalf_ne_bot : (halfSquaredNorm z.1.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm z.1.2).2
      have htop : (⊤ : EReal) ≤ z.2 := by
        rw [show
            (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] z.1.2 :
              EReal) = ⊤ by
          simp [indicator_apply, hz_mem]] at hz
        simpa [EReal.top_add_of_ne_bot hhalf_ne_bot] using hz
      exact (not_le_of_gt (EReal.coe_lt_top z.2)) htop
    have hz_height : (halfSquaredNorm z.1.2 : EReal) ≤ z.2 := by
      rw [show
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] z.1.2 :
            EReal) = 0 by
        simp [indicator_apply, hz_mem]] at hz
      simpa using hz
    rcases Submodule.mem_map.mp hz_mem with ⟨v, hvV, hvproj⟩
    refine
      ⟨(((z.1.1 - v), 0), 0), ?_, ((v, z.1.2), z.2), ?_, ?_⟩
    · -- The first summand only corrects the dormant `L2Nat` coordinate and stays at height `0`.
      constructor
      · simpa [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff]
      · rfl
    · -- The second summand records the actual projected-image witness and the epigraph height.
      exact ⟨⟨hvV, hvproj.symm⟩, hz_height⟩
    · -- Adding the horizontal correction recovers the original lifted point `z`.
      ext <;> simp

/-- Helper for Remark 16.46: the closure-convex-hull obstruction on the raw projected-image
epigraph lifts verbatim to the auxiliary pullback epigraph set by inserting a dormant first
coordinate `0`. -/
private theorem pullbackProjectedImageRawEpigraphClosureGap_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (u0 : orthogonalClosedSubmodule U),
      let Eepi := productGraphEpigraphSpace U
      let q : orthogonalClosedSubmodule U → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
      let z0 : Eepi := (((0 : L2Nat), u0), q u0)
      z0 ∉ pullbackProjectedImageRawEpigraphSet U V ∧
        z0 ∈ closure (convexHull ℝ (pullbackProjectedImageRawEpigraphSet U V)) := by
  rcases projectedImageRawEpigraphClosureGap_l2 with ⟨U, V, u0, hgap⟩
  refine ⟨U, V, u0, ?_⟩
  let K := orthogonalClosedSubmodule U
  let Eepi := productGraphEpigraphSpace U
  let q : K → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
  let p0 : K × ℝ := (u0, q u0)
  let z0 : Eepi := (((0 : L2Nat), u0), q u0)
  let J : (K × ℝ) →L[ℝ] Eepi :=
    { toLinearMap :=
        { toFun := fun p ↦ (((0 : L2Nat), p.1), p.2)
          map_add' := by
            intro p q
            ext <;> simp
          map_smul' := by
            intro a p
            ext <;> simp }
      cont := by
        simpa using
          ((ContinuousLinearMap.inr ℝ L2Nat K).prodMap
            (ContinuousLinearMap.id ℝ ℝ)).continuous }
  rcases hgap with ⟨hp0_not_mem, hp0_closure⟩
  have hJ_image_convex :
      J '' convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal)) =
        convexHull ℝ (J '' epigraph ((projectedImageRawOwner U V).asEReal)) := by
    simpa [J] using
      J.toLinearMap.image_convexHull (epigraph ((projectedImageRawOwner U V).asEReal))
  have hJ_subset :
      J '' epigraph ((projectedImageRawOwner U V).asEReal) ⊆
        pullbackProjectedImageRawEpigraphSet U V := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [J, pullbackProjectedImageRawEpigraphSet] using hp
  have hz0_not_mem : z0 ∉ pullbackProjectedImageRawEpigraphSet U V := by
    intro hz0_mem
    exact hp0_not_mem (by simpa [z0, pullbackProjectedImageRawEpigraphSet] using hz0_mem)
  have hJ_closure :
      z0 ∈ closure (J '' convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) := by
    have hp0_image : z0 ∈ J '' closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) := by
      exact ⟨p0, hp0_closure, by simp [J, z0, p0]⟩
    exact image_closure_subset_closure_image J.continuous hp0_image
  have hz0_closure :
      z0 ∈ closure (convexHull ℝ (pullbackProjectedImageRawEpigraphSet U V)) := by
    rw [hJ_image_convex] at hJ_closure
    exact closure_mono (subset_convexHull ℝ _ ∘ hJ_subset) hJ_closure
  exact ⟨hz0_not_mem, hz0_closure⟩

/-- Helper for Remark 16.46: the lifted pullback epigraph-indicator route is retired and no longer
used by the active proof graph. -/
private theorem pullbackProjectedImageRawEpigraphIndicatorGap_l2 :
    True := by
  trivial

-/

/- Route correction for Remark 16.46: the retired product-graph branch has been collapsed out of
the active file. It carried only obsolete normalization attempts and dormant proof holes, while the
live proof now proceeds through the projected-image same-space witness route below. -/

/-- Helper for Remark 16.46: the same-space projector quadratic
`x ↦ (1 / 2) ‖P_W x‖²` is a `Γ₀(H)` owner because it is the conjugate of
`ι[W] + (1 / 2) ‖·‖²`. -/
private theorem projectorQuadratic_mem_gammaZero
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : ClosedSubmodule ℝ H) :
    (fun x : H ↦ (halfSquaredNorm (W.orthogonalProjection x) : Set.Ioi (⊥ : EReal))) ∈ Γ₀(H) := by
  let g : H → Set.Ioi (⊥ : EReal) := ι[(W : Set H)] + halfSquaredNorm
  have hW_gamma :
      (ι[(W : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      ⟨0, W.zero_mem⟩ W.isClosed W.convex
  have hg : g ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero_local (ι[(W : Set H)]) hW_gamma
  have hproj_eq :
      (fun x : H ↦ (halfSquaredNorm (W.orthogonalProjection x) : Set.Ioi (⊥ : EReal))) =
        g∗[hg] := by
    funext x
    apply Subtype.ext
    -- Rewrite both subtype values through the same ambient conjugate formula.
    rw [gammaZeroConjugate_apply]
    simpa [g] using
      congrFun
        (halfSquaredNorm_comp_orthogonalProjection_eq_conjugate_indicator_add_halfSquaredNorm W)
        x
  -- Replace the projector quadratic by the already-packaged `Γ₀(H)` conjugate owner.
  rw [hproj_eq]
  exact gammaZeroConjugate_mem_gammaZero hg

/-- Helper for Remark 16.46: the projector quadratic is finite everywhere, so its effective
domain is all of `H`. -/
private theorem effectiveDomain_projectorQuadratic_eq_univ
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : ClosedSubmodule ℝ H) :
    effectiveDomain
        (fun x : H ↦ (halfSquaredNorm (W.orthogonalProjection x) : Set.Ioi (⊥ : EReal))) =
      Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _

/-- Helper for Remark 16.46: the same-space projector-quadratic branch is mathematically dead for
the final counterexample, because both owners have full effective domain and therefore satisfy the
identity-map exact dual formula. -/
private theorem exactDualInfimalConvolutionFormula_projectorQuadratic_id
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : ClosedSubmodule ℝ H) :
    ExactDualInfimalConvolutionFormula
      (projectorQuadratic_mem_gammaZero U)
      (projectorQuadratic_mem_gammaZero V)
      (ContinuousLinearMap.id ℝ H) := by
  have hsri :
      (0 : H) ∈ Set.strongRelativeInterior
        (effectiveDomain
            (fun x : H ↦ (halfSquaredNorm (U.orthogonalProjection x) : Set.Ioi (⊥ : EReal))) -
          effectiveDomain
            (fun x : H ↦ (halfSquaredNorm (V.orthogonalProjection x) : Set.Ioi (⊥ : EReal)))) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local
      (projectorQuadratic_mem_gammaZero U)
      (effectiveDomain_projectorQuadratic_eq_univ V)
  -- The local `dom = univ` exactness theorem rules out projector quadratics as a counterexample.
  exact
    exactDualInfimalConvolutionFormula_id_of_zero_mem_sri_sub_effectiveDomain
      (projectorQuadratic_mem_gammaZero U)
      (projectorQuadratic_mem_gammaZero V)
      hsri

/-- Helper for Remark 16.46: any same-space witness whose second owner is `halfSquaredNorm`
already satisfies the identity-map exact dual formula, because that second owner has full
effective domain. -/
private theorem exactDualInfimalConvolutionFormula_id_with_halfSquaredNorm_secondOwner
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ExactDualInfimalConvolutionFormula
      hf
      (halfSquaredNorm_mem_gammaZero_local : (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
      (ContinuousLinearMap.id ℝ H) := by
  have hdom_univ :
      effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) = Set.univ := by
    ext x
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    constructor
    · intro _
      simp
    · intro _
      exact EReal.coe_lt_top _
  -- The `dom = univ` Attouch--Brézis hypothesis is automatic for the quadratic second owner.
  have hsri :
      (0 : H) ∈ Set.strongRelativeInterior
        (effectiveDomain f -
          effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf hdom_univ
  exact
    exactDualInfimalConvolutionFormula_id_of_zero_mem_sri_sub_effectiveDomain
      hf
      (halfSquaredNorm_mem_gammaZero_local :
        (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H))
      hsri

/-- Helper for Remark 16.46: once a same-space `Γ₀` pair on `Uᗮ` realizes
`projectedImageRawOwner U V` as its raw dual infimal convolution, the already packaged
bad-point data force the desired dual gap at that same point. -/
private theorem existsRemark1646WitnessWithConjugateGap_fromProjectedImagePair
    {U V : Submodule ℝ L2Nat}
    {u0 : orthogonalClosedSubmodule U}
    {f g : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hsub :
      (∂ (f + g) :
          SetValuedOperator (orthogonalClosedSubmodule U) (orthogonalClosedSubmodule U)) =
        ∂ f + ∂ g)
    (hraw :
      ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal)) =
        (projectedImageRawOwner U V).asEReal)
    (hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤)
    (hu0_env_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
      ((∂ (f + g) :
          SetValuedOperator (orthogonalClosedSubmodule U) (orthogonalClosedSubmodule U)) =
        ∂ f + ∂ g) ∧
      u0 ∈ dom ((f + g).asEReal∗) ∧
      (f + g).asEReal∗ u0 ≠
        ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal) u0) := by
  let K := orthogonalClosedSubmodule U
  letI : CompleteSpace K := by
    simpa [orthogonalClosedSubmodule] using U.isClosed_orthogonal.completeSpace_coe
  -- Rewrite `(f + g)^*` through Proposition 15.1 and the raw-owner identity before comparing
  -- the finite envelope value with the raw top value at `u0`.
  have hconj :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal)) :=
    conjugate_pointwiseAdd_eq_lscConvexEnvelope_infimalConvolution_conjugates_local
      (H := K) f g hf hg hdom
  have hu0_sum_finite : (f + g).asEReal∗ u0 < ⊤ := by
    -- The finite envelope bound transports across the raw-owner identification.
    rw [hconj, hraw]
    exact hu0_env_finite
  have hu0_raw_top' :
      ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal) u0) = ⊤ := by
    rw [hraw]
    exact hu0_raw_top
  have hu0_dom :
      u0 ∈ dom ((f + g).asEReal∗) := by
    -- Finite conjugate value is exactly domain membership.
    rw [mem_dom_iff]
    exact hu0_sum_finite
  have hu0_gap :
      (f + g).asEReal∗ u0 ≠
        ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal) u0) := by
    -- The left-hand side is finite, while the raw owner remains `⊤` at the bad point.
    intro hEq
    exact (ne_of_lt hu0_sum_finite) (hEq.trans hu0_raw_top')
  exact ⟨hdom, hsub, hu0_dom, hu0_gap⟩

/-- Helper for Remark 16.46: package only the two pointwise obstruction facts needed at the bad
projected-image witness, namely the raw top value and the finite lower-semicontinuous convex
envelope value at the same point. -/
private theorem existsProjectedImageRawOwnerObstructionData_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (u0 : orthogonalClosedSubmodule U),
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
  rcases projectedImageRawOwnerEnvelopeFiniteAtBadPoint_l2 with
    ⟨U, V, u0, _hu0_closure, _hu0_not_mem, hu0_raw_top, hu0_env_finite⟩
  -- Keep only the pointwise raw/envelope gap data needed by the next witness construction.
  exact ⟨U, V, u0, hu0_raw_top, hu0_env_finite⟩

/-- Helper for Remark 16.46: once a same-space `Γ₀` pair on `Uᗮ` realizes the projected-image raw
owner, the already packaged bad-point obstruction immediately gives the thinner pointwise gap
package needed at `u0`. -/
private theorem projectedImagePair_packagesPointwiseGapWitness_l2
    {U V : Submodule ℝ L2Nat}
    {u0 : orthogonalClosedSubmodule U}
    {f g : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hsub :
      (∂ (f + g) :
          SetValuedOperator (orthogonalClosedSubmodule U) (orthogonalClosedSubmodule U)) =
        ∂ f + ∂ g)
    (hraw :
      ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal)) =
        (projectedImageRawOwner U V).asEReal)
    (hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤)
    (hu0_env_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
      ((∂ (f + g) :
          SetValuedOperator (orthogonalClosedSubmodule U) (orthogonalClosedSubmodule U)) =
        ∂ f + ∂ g) ∧
      ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal) u0) = ⊤ ∧
      (f + g).asEReal∗ u0 < ⊤ := by
  let K := orthogonalClosedSubmodule U
  letI : CompleteSpace K := by
    simpa [orthogonalClosedSubmodule] using U.isClosed_orthogonal.completeSpace_coe
  have hconj :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal)) :=
    -- Proposition 15.1 rewrites the conjugate to the envelope of the raw infimal convolution.
    conjugate_pointwiseAdd_eq_lscConvexEnvelope_infimalConvolution_conjugates_local
      (H := K) f g hf hg hdom
  have hu0_pointwise_raw_top :
      ((((f∗[hf]) □ (g∗[hg])) : orthogonalClosedSubmodule U → EReal) u0) = ⊤ := by
    -- Evaluate the raw-owner realization at the bad point `u0`.
    rw [hraw]
    exact hu0_raw_top
  have hu0_pointwise_conj_finite :
      (f + g).asEReal∗ u0 < ⊤ := by
    -- The same realization turns the envelope-side finite bound into conjugate finiteness.
    rw [hconj, hraw]
    exact hu0_env_finite
  exact ⟨hdom, hsub, hu0_pointwise_raw_top, hu0_pointwise_conj_finite⟩

/-- Helper for Remark 16.46: the horizontal slice indicator is a `Γ₀` owner on the product-space
vertical model. -/
private theorem horizontalOrthogonalSliceIndicator_mem_gammaZero_l2
    (U : Submodule ℝ L2Nat) :
    (ι[horizontalOrthogonalSliceSet U] :
      (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)) ∈
      Γ₀(L2Nat × orthogonalClosedSubmodule U) := by
  let K := orthogonalClosedSubmodule U
  let M : L2Nat →L[ℝ] K := 0
  have hnonempty : (horizontalOrthogonalSliceSet U : Set (L2Nat × K)).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, M]
  have hclosed : IsClosed (horizontalOrthogonalSliceSet U : Set (L2Nat × K)) := by
    simpa [horizontalOrthogonalSliceSet] using linearGraphSet_isClosed M
  have hconvex : Convex ℝ (horizontalOrthogonalSliceSet U : Set (L2Nat × K)) := by
    simpa [horizontalOrthogonalSliceSet] using linearGraphSet_convex M
  -- The zero graph is a closed convex set with the origin as a point, so its indicator is `Γ₀`.
  simpa [K] using
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hnonempty hclosed hconvex

/-- Helper for Remark 16.46: if `V` is closed, then the projected-image graph is a closed convex
constraint set in the product witness space. -/
private theorem projectedImageGraphIndicator_mem_gammaZero_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    (ι[projectedImageGraphSet U V] :
      (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)) ∈
      Γ₀(L2Nat × orthogonalClosedSubmodule U) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let K := orthogonalClosedSubmodule U
  have hnonempty : (projectedImageGraphSet U V : Set E).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [projectedImageGraphSet]
  have hclosed_memV : IsClosed {p : E | p.1 ∈ (V : Set L2Nat)} := by
    simpa using hV_closed.preimage (continuous_fst : Continuous fun p : E ↦ p.1)
  have hclosed_graph :
      IsClosed {p : E | p.2 = (orthogonalClosedSubmodule U).orthogonalProjection p.1} := by
    exact
      isClosed_eq
        (continuous_snd : Continuous fun p : E ↦ p.2)
        ((orthogonalClosedSubmodule U).orthogonalProjection.continuous.comp continuous_fst)
  have hclosed : IsClosed (projectedImageGraphSet U V : Set E) := by
    simpa [projectedImageGraphSet] using hclosed_memV.inter hclosed_graph
  have hconvex : Convex ℝ (projectedImageGraphSet U V : Set E) := by
    intro p hp q hq a ha0 ha1
    rcases hp with ⟨hpV, hpProj⟩
    rcases hq with ⟨hqV, hqProj⟩
    constructor
    · exact V.convex hpV hqV ha0 ha1
    · calc
        a • p.2 + (1 - a) • q.2
            = a • (orthogonalClosedSubmodule U).orthogonalProjection p.1 +
                (1 - a) • (orthogonalClosedSubmodule U).orthogonalProjection q.1 := by
                  rw [hpProj, hqProj]
        _ = (orthogonalClosedSubmodule U).orthogonalProjection
              (a • p.1 + (1 - a) • q.1) := by
                simp [ContinuousLinearMap.map_add, map_smul]
  -- The projected-image graph is a closed convex constraint set, so its indicator is `Γ₀`.
  exact indicator_mem_gammaZero_of_nonempty_isClosed_convex hnonempty hclosed hconvex

/-- Helper for Remark 16.46: the vertical regularization `p ↦ ‖p.2‖² / 2` is a `Γ₀` owner on the
product witness space. -/
private theorem secondCoordinateHalfSquaredNorm_mem_gammaZero_l2
    (U : Submodule ℝ L2Nat) :
    (fun p : L2Nat × orthogonalClosedSubmodule U ↦
      (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal))) ∈
      Γ₀(L2Nat × orthogonalClosedSubmodule U) := by
  letI : CompleteSpace (orthogonalClosedSubmodule U) := by
    simpa [orthogonalClosedSubmodule] using U.isClosed_orthogonal.completeSpace_coe
  have hq :
      (halfSquaredNorm : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal)) ∈
        Γ₀(orthogonalClosedSubmodule U) :=
    halfSquaredNorm_mem_gammaZero_local
  rw [mem_gammaZero_iff] at hq ⊢
  constructor
  · -- Lower semicontinuity survives composition with the continuous second projection.
    simpa using hq.1.comp continuous_snd
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The origin is a finite point of the pulled-back quadratic owner.
      refine ⟨(0, 0), ?_⟩
      rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
    · intro x _hx y _hy a ha0 ha1
      have hxq :
          x.2 ∈ effectiveDomain (halfSquaredNorm : orthogonalClosedSubmodule U →
            Set.Ioi (⊥ : EReal)) := by
        rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
        exact EReal.coe_lt_top _
      have hyq :
          y.2 ∈ effectiveDomain (halfSquaredNorm : orthogonalClosedSubmodule U →
            Set.Ioi (⊥ : EReal)) := by
        rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
        exact EReal.coe_lt_top _
      -- Jensen convexity is inherited from the ambient half-squared norm on the second factor.
      simpa using hq.2.ineq hxq hyq ha0 ha1

/-- Helper for Remark 16.46: the older product-graph normal-form comparison is retired and no
longer used by the active proof graph. -/
private theorem projectedImageGraphOwner_eq_separableSum_add_graphIndicator_l2
    (U V : Submodule ℝ L2Nat) :
    True := by
  let _ := U
  let _ := V
  trivial

/-- Helper for Remark 16.46: the origin belongs to the strong relative interior of the whole
ambient space. -/
private theorem zero_mem_sri_univ_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    (0 : E) ∈ Set.strongRelativeInterior (Set.univ : Set E) := by
  -- Reduce the strong-relative-interior claim to the cone computation for `univ`.
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      (E := E) Set.univ_nonempty convex_univ).2 ?_
  calc
    Set.cone (Set.univ : Set E) = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rw [Set.cone_def]
        exact ConvexCone.subset_hull (by simp)
    _ = closure (Submodule.span ℝ (Set.univ : Set E) : Set E) := by
      simp

/-- Helper for Remark 16.46: if the second owner is finite everywhere, then the shifted Chapter 15
regularity hypothesis `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)` is automatic. -/
private theorem zero_mem_sri_sub_image_effectiveDomain_of_dom_univ_local
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (L : H →L[ℝ] K)
    (hdom : effectiveDomain g = (Set.univ : Set K)) :
    (0 : K) ∈ Set.strongRelativeInterior (effectiveDomain g - L '' effectiveDomain f) := by
  -- Rewrite the domain difference against `univ`, then use the universal SRI helper.
  rw [hdom]
  rcases hf.2.nonempty with ⟨x, hx⟩
  have hsub :
      (Set.univ : Set K) - L '' effectiveDomain f = (Set.univ : Set K) := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      refine Set.mem_sub.mpr ?_
      refine ⟨y + L x, by simp, L x, ?_, by abel⟩
      exact ⟨x, hx, rfl⟩
  rw [hsub]
  exact zero_mem_sri_univ_local

/-- Helper for Remark 16.46: the linear tilt `x ↦ -⟪x, u⟫` is a `Γ₀` owner. -/
private theorem negativeInnerToEReal_mem_gammaZero_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E) :
    (fun x : E ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity comes from continuity of the linear functional.
    have hcont :
        Continuous (fun x : E ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) := by
      simpa using continuous_coe_real_ereal.comp ((continuous_id.inner continuous_const).neg)
    exact hcont.lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The tilt is finite everywhere, in particular at the origin.
      refine ⟨0, ?_⟩
      simp
    · -- Affinity of the linear functional gives Jensen convexity as an equality.
      intro x _hx y _hy a ha0 ha1
      have hreal :
          -⟪a • x + (1 - a) • y, u⟫_ℝ =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      simp only [Function.toEReal_apply, EReal.coe_neg, mul_neg, ge_iff_le]
      have hcast :
          (((-⟪a • x + (1 - a) • y, u⟫_ℝ : ℝ) : EReal)) =
            (((a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      simpa [EReal.coe_add, EReal.coe_mul] using le_of_eq hcast

/-- Helper for Remark 16.46: tilting a closed convex indicator by `x ↦ -⟪x, u⟫` preserves the
`Γ₀` property. -/
private theorem indicatorLinearTilt_mem_gammaZero_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (u : E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] + (fun x : E ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(E) := by
  have hGammaC : ι[C] ∈ Γ₀(E) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hGammaLinear :
      (fun x : E ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(E) :=
    negativeInnerToEReal_mem_gammaZero_local u
  rcases hC_nonempty with ⟨x, hx⟩
  -- The linear tilt is finite at every point, so one point of `C` is enough for the domain
  -- intersection needed by `pointwiseAdd_mem_gammaZero`.
  refine pointwiseAdd_mem_gammaZero
    (ι[C]) ((fun x : E ↦ -⟪x, u⟫_ℝ).toEReal) hGammaC hGammaLinear ?_
  refine ⟨x, ?_, ?_⟩
  · simpa [mem_effectiveDomain_iff, indicator_apply] using hx
  · simp

/-- Helper for Remark 16.46: tilting the `V`-indicator turns the Chapter 15 dual objective into
the shifted projected-image dual objective. -/
private theorem compositeDualObjective_indicatorLinearTilt_eq_shifted_local
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (C : Set H) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (u : H) :
    compositeDualObjective (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) g L =
      shiftedCompositeDualObjective (ι[C]) g L u := by
  funext v
  -- Rewrite the conjugate of the tilted indicator once, then the two dual objectives agree
  -- pointwise.
  rw [compositeDualObjective_apply, shiftedCompositeDualObjective_apply]
  have hconj :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := (ι[C]).asEReal) (y := (0 : H)) (v := -u) (β := 0))
      (-(L.adjoint v))
  have hconj' :
      ((Function.asEReal (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal))∗) (-(L.adjoint v)) =
        ((Function.asEReal ι[C])∗) (u - L.adjoint v) := by
    simpa [translate_apply, pointwiseAdd_apply, Function.toEReal_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
      using hconj
  rw [hconj']

/-- Helper for Remark 16.46: the local affine tilt makes the projected-image shifted dual
objective attain its minimum at the active point `ξ`. -/
private theorem exists_mem_argmin_shiftedProjectedImageCompositeDualObjective_local_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat))
    (ξ : orthogonalClosedSubmodule U)
    [CompleteSpace (orthogonalClosedSubmodule U)] :
    let K := orthogonalClosedSubmodule U
    let P : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
    let tilt : L2Nat → Set.Ioi (⊥ : EReal) :=
      ι[(V : Set L2Nat)] + (fun x : L2Nat ↦ -⟪x, (ξ : L2Nat)⟫_ℝ).toEReal
    ∃ w ∈ Argmin
        (shiftedCompositeDualObjective
          (ι[(V : Set L2Nat)])
          (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) P (ξ : L2Nat)),
      compositePrimalOptimalValue tilt (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) P =
        -(shiftedCompositeDualObjective
          (ι[(V : Set L2Nat)])
          (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) P (ξ : L2Nat) w) := by
  let K := orthogonalClosedSubmodule U
  let P : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
  let tilt : L2Nat → Set.Ioi (⊥ : EReal) :=
    ι[(V : Set L2Nat)] + (fun x : L2Nat ↦ -⟪x, (ξ : L2Nat)⟫_ℝ).toEReal
  have htilt : tilt ∈ Γ₀(L2Nat) := by
    -- Tilting the closed subspace indicator by a continuous linear functional preserves `Γ₀`.
    simpa [tilt] using
      indicatorLinearTilt_mem_gammaZero_local
        (C := (V : Set L2Nat)) (u := (ξ : L2Nat))
        ⟨0, V.zero_mem⟩ hV_closed V.convex
  have hhalf : (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
    simpa using (halfSquaredNorm_mem_gammaZero_local (H := K))
  have htilt_dom :
      effectiveDomain tilt = effectiveDomain (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) := by
    ext x
    by_cases hx : x ∈ (V : Set L2Nat)
    · -- On `V`, the indicator is finite and the linear tilt stays finite.
      simp [tilt, mem_effectiveDomain_iff, indicator_apply, hx]
    · -- Off `V`, both owners are excluded by the indicator term.
      simp [tilt, mem_effectiveDomain_iff, indicator_apply, hx]
  have hcore :
      (0 : K) ∈
        Set.core
          (effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) -
            P '' effectiveDomain tilt) := by
    -- The tilt does not change the effective domain, so the previous core lemma applies verbatim.
    rw [htilt_dom]
    simpa [K, P] using zero_mem_core_sub_image_effectiveDomain_projectedImage_l2 U V
  rcases
      exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain
        tilt htilt (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) hhalf P hcore
    with ⟨w, hwArg, hwValue⟩
  have hshift :
      compositeDualObjective tilt (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) P =
        shiftedCompositeDualObjective
          (ι[(V : Set L2Nat)])
          (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) P (ξ : L2Nat) := by
    -- The dual objective rewrite is the stable bridge from the tilted problem to the shifted one.
    simpa [K, P, tilt] using
      compositeDualObjective_indicatorLinearTilt_eq_shifted_local
        (C := (V : Set L2Nat))
        (g := (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)))
        (L := P) (u := (ξ : L2Nat))
  refine ⟨w, ?_, ?_⟩
  · simpa [hshift] using hwArg
  · simpa [hshift] using hwValue

/-- Helper for Remark 16.46: the Chapter 15 product-graph core hypothesis is automatic for the
projected-image model because the quadratic summand is finite everywhere and the projected image
contains the origin. -/
private theorem zero_mem_core_sub_image_effectiveDomain_projectedImage_l2
    (U V : Submodule ℝ L2Nat) :
    let K := orthogonalClosedSubmodule U
    let M : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
    (0 : K) ∈
      Set.core
        (effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) -
          M '' effectiveDomain (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) :=
  let K := orthogonalClosedSubmodule U
  let M : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
  have hzero_image :
      (0 : K) ∈ M '' effectiveDomain (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) := by
    refine ⟨0, ?_, by simp [M]⟩
    -- The ambient indicator is finite at the origin because every submodule contains `0`.
    simpa [mem_effectiveDomain_iff, indicator_apply]
  have hdiff_univ :
      effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) -
          M '' effectiveDomain (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal)) =
        (Set.univ : Set K) := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      refine Set.mem_sub.mpr ⟨y, ?_, 0, hzero_image, by simp⟩
      -- The quadratic term is finite everywhere on `K`.
      rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  rw [hdiff_univ, Set.mem_core_iff]
  constructor
  · simp
  · ext y
    constructor
    · intro _
      simp
    · intro _
      -- The translate `univ - {0}` is still all of `univ`, so its cone is `univ`.
      change y ∈ (Set.cone (Set.univ - ({(0 : K)} : Set K)) : Set K)
      simp [Set.cone_def]

/-- Helper for Remark 16.46: the Chapter 15 composite dual owner for the projected-image graph
data attains its minimum, so the remaining blocker is only the transport back to the horizontal
slice witness `s □ t`. -/
private theorem exists_mem_argmin_projectedImageCompositeDualObjective_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    let K := orthogonalClosedSubmodule U
    let F : L2Nat → Set.Ioi (⊥ : EReal) := ι[(V : Set L2Nat)]
    let G : K → Set.Ioi (⊥ : EReal) := halfSquaredNorm
    let M : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
    ∃ w ∈ Argmin (compositeDualObjective F G M),
      compositePrimalOptimalValue F G M = -(compositeDualObjective F G M w) :=
  let K := orthogonalClosedSubmodule U
  let F : L2Nat → Set.Ioi (⊥ : EReal) := ι[(V : Set L2Nat)]
  let G : K → Set.Ioi (⊥ : EReal) := halfSquaredNorm
  let M : L2Nat →L[ℝ] K := (orthogonalClosedSubmodule U).orthogonalProjection
  have hF : F ∈ Γ₀(L2Nat) := by
    -- Closed subspaces have `Γ₀` indicators.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ hV_closed V.convex
    exact ⟨0, V.zero_mem⟩
  have hG : G ∈ Γ₀(K) := by
    -- The quadratic summand is already packaged as a `Γ₀` owner.
    simpa [G] using (halfSquaredNorm_mem_gammaZero_local (H := K))
  have hcore :
      (0 : K) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F) := by
    -- The preceding lemma freezes exactly the Chapter 15 regularity hypothesis we need.
    simpa [K, F, G, M] using zero_mem_core_sub_image_effectiveDomain_projectedImage_l2 U V
  -- Apply Proposition 15.22 directly to the projected-image composite problem.
  simpa [K, F, G, M] using
    exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain
      F hF G hG M hcore

/-- Helper for Remark 16.46: the effective domain of a second-coordinate pullback is the product
of the free first factor with the effective domain of the pulled-back owner. -/
private theorem effectiveDomain_secondCoordinatePullback_eq_univ_prod_general
    {A K : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (φ : K → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (fun p : A × K ↦ φ p.2) = (Set.univ : Set A) ×ˢ effectiveDomain φ := by
  ext p
  constructor
  · intro hp
    -- Finiteness of the pullback is controlled entirely by the second coordinate.
    constructor
    · simp
    · simpa [mem_effectiveDomain_iff] using hp
  · rintro ⟨_, hp⟩
    -- Any finite second coordinate yields a finite product-space value.
    simpa [mem_effectiveDomain_iff] using hp

/-- Helper for Remark 16.46: the subdifferential of a second-coordinate pullback
`(a, b) ↦ φ b` is exactly `({0} : Set A) ×ˢ (∂ φ) b`. -/
private theorem subdifferential_secondCoordinatePullback_eq_zero_prod_general
    {A K : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup (A × K)] [InnerProductSpace ℝ (A × K)] [CompleteSpace (A × K)]
    (φ : K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(K)) (abar : A) (bbar : K) :
    (∂ (fun p : A × K ↦ φ p.2)) (abar, bbar) = ({0} : Set A) ×ˢ ((∂ φ) bbar) := by
  ext p
  rcases p with ⟨u, a⟩
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    have hbbar_dom : bbar ∈ effectiveDomain φ := by
      rcases hφ.2.nonempty with ⟨t0, ht0⟩
      have htest :
          (⟪(abar, t0) - (abar, bbar), (u, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤
            (φ t0 : EReal) := by
        simpa using hu (abar, t0)
      have ht0_top : (φ t0 : EReal) < ⊤ := mem_effectiveDomain_iff.mp ht0
      by_contra hbbar_dom
      have hbbar_top : (φ bbar : EReal) = ⊤ := by
        have hbbar_not_lt : ¬ ((φ bbar : EReal) < ⊤) := by
          simpa [mem_effectiveDomain_iff] using hbbar_dom
        exact top_unique <| le_of_not_gt hbbar_not_lt
      have htop : (⊤ : EReal) ≤ (φ t0 : EReal) := by
        simpa [hbbar_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] using htest
      exact ht0_top.not_ge htop
    have hbbar_top : (φ bbar : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hbbar_dom)
    have hbbar_bot : (φ bbar : EReal) ≠ ⊥ := ne_of_gt (φ bbar).2
    have hu_zero : u = 0 := by
      have htest :
          (⟪(abar + u, bbar) - (abar, bbar), (u, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤
            (φ bbar : EReal) := by
        simpa using hu (abar + u, bbar)
      have htest_pair :
          (⟪(u, (0 : K)), (u, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤ (φ bbar : EReal) := by
        simpa using htest
      have hinner_pair : ⟪(u, (0 : K)), (u, a)⟫_ℝ = ⟪u, u⟫_ℝ := by
        change ⟪u, u⟫_ℝ + ⟪(0 : K), a⟫_ℝ = ⟪u, u⟫_ℝ
        simp
      have htest0 : (⟪u, u⟫_ℝ : EReal) + (φ bbar : EReal) ≤ (φ bbar : EReal) := by
        simpa [hinner_pair] using htest_pair
      have htest' :
          (((‖u‖ ^ 2 + (φ bbar : EReal).toReal : ℝ) : EReal)) ≤ (φ bbar : EReal) := by
        rw [EReal.coe_add, EReal.coe_toReal hbbar_top hbbar_bot]
        simpa [real_inner_self_eq_norm_sq] using htest0
      have hsq : (‖u‖ ^ 2 : ℝ) ≤ 0 := by
        have hrealE :
            (((‖u‖ ^ 2 + (φ bbar : EReal).toReal : ℝ) : EReal)) ≤
              ((((φ bbar : EReal).toReal : ℝ)) : EReal) := by
          simpa [EReal.coe_toReal hbbar_top hbbar_bot] using htest'
        have hreal : ‖u‖ ^ 2 + (φ bbar : EReal).toReal ≤ (φ bbar : EReal).toReal := by
          exact_mod_cast hrealE
        linarith
      have hnorm : ‖u‖ = 0 := by
        nlinarith [sq_nonneg ‖u‖, hsq]
      exact norm_eq_zero.mp hnorm
    constructor
    · exact Set.mem_singleton_iff.mpr hu_zero
    · subst u
      -- Once the first coordinate vanishes, only vertical variations remain in the
      -- subgradient inequality.
      rw [mem_subdifferential_iff]
      intro t
      have htest :
          (⟪(abar, t) - (abar, bbar), (0, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤
            (φ t : EReal) := by
        simpa using hu (abar, t)
      have htest_pair :
          (⟪((0 : A), t - bbar), (0, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤ (φ t : EReal) := by
        simpa using htest
      have hinner_pair : ⟪((0 : A), t - bbar), (0, a)⟫_ℝ = ⟪t - bbar, a⟫_ℝ := by
        change ⟪(0 : A), (0 : A)⟫_ℝ + ⟪t - bbar, a⟫_ℝ = ⟪t - bbar, a⟫_ℝ
        simp
      simpa [hinner_pair] using htest_pair
  · rintro ⟨hu, ha⟩
    rcases Set.mem_singleton_iff.mp hu with rfl
    rw [mem_subdifferential_iff] at ha
    intro q
    rcases q with ⟨z, t⟩
    -- Conversely, the scalar subgradient inequality is read through the second-coordinate
    -- projection.
    have htest : (⟪t - bbar, a⟫_ℝ : EReal) + (φ bbar : EReal) ≤ (φ t : EReal) := ha t
    have hinner_pair : ⟪(z - abar, t - bbar), (0, a)⟫_ℝ = ⟪t - bbar, a⟫_ℝ := by
      change ⟪z - abar, (0 : A)⟫_ℝ + ⟪t - bbar, a⟫_ℝ = ⟪t - bbar, a⟫_ℝ
      simp
    have htest_pair :
        (⟪(z - abar, t - bbar), (0, a)⟫_ℝ : EReal) + (φ bbar : EReal) ≤ (φ t : EReal) := by
      simpa [hinner_pair] using htest
    simpa [hinner_pair] using htest_pair

/-- Helper for Remark 16.46: a nonnegative owner with value `0` at the origin has a conjugate
finite at the origin. -/
private theorem zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(E))
    (hnonneg : ∀ x : E, (0 : EReal) ≤ (φ x : EReal))
    (hzero : (φ 0 : EReal) = 0) :
    (0 : E) ∈ effectiveDomain (φ∗[hφ]) := by
  rw [mem_effectiveDomain_iff, gammaZeroConjugate_apply, conjugate_zero_eq_neg_iInf]
  have hiInf_eq_zero : (⨅ x : E, (φ x : EReal)) = 0 := by
    apply le_antisymm
    · simpa [hzero] using (iInf_le (fun x : E ↦ (φ x : EReal)) 0)
    · exact le_iInf hnonneg
  rw [hiInf_eq_zero]
  simp

/-- Helper for Remark 16.46: the projected-image raw owner is nonnegative because it is the sum
of an indicator and the half-squared norm. -/
private theorem projectedImageRawOwner_nonneg_l2
    (U V : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    (0 : EReal) ≤ ((projectedImageRawOwner U V u : Set.Ioi (⊥ : EReal)) : EReal) := by
  by_cases hu : u ∈ projectedImageSubmodule U V
  · -- On the projected image, the indicator vanishes and only the nonnegative quadratic tail remains.
    change
      (0 : EReal) ≤
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) +
          (halfSquaredNorm u : EReal)
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) = 0 by
      simp [indicator_apply, hu]]
    positivity
  · -- Off the projected image, the indicator contributes `⊤`, so the sum is automatically nonnegative.
    have hhalf_ne_bot : (halfSquaredNorm u : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u).2
    change
      (0 : EReal) ≤
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) +
          (halfSquaredNorm u : EReal)
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) = ⊤ by
      simp [indicator_apply, hu]]
    rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
    simp

/-- Helper for Remark 16.46: the projected-image raw owner vanishes at the origin because both the
indicator and the quadratic tail vanish there. -/
private theorem projectedImageRawOwner_zero_l2
    (U V : Submodule ℝ L2Nat) :
    ((projectedImageRawOwner U V 0 : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
  change
    (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] 0 : EReal) +
        (halfSquaredNorm 0 : EReal) = 0
  rw [show
      (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] 0 : EReal) = 0 by
    simp [indicator_apply]]
  -- Both the indicator and the quadratic tail vanish at the origin.
  simpa [halfSquaredNorm_apply]

/- Route correction for Remark 16.46: the following envelope/product-graph support branch is
retired. It is preserved only as historical context and is no longer on the active dependency
chain for the same-space witness construction below. 

/- Route correction for Remark 16.46: this older envelope-support block is superseded by the later
working versions of the same helpers and is kept out of the active elaboration path.

/-- Helper for Remark 16.46: package the lower-semicontinuous convex envelope of the
projected-image raw owner as a `Γ₀` owner on `Uᗮ`. -/
private theorem projectedImageEnvelopeGammaZero_l2
    (U V : Submodule ℝ L2Nat) :
    ∃ ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal),
      ψ ∈ Γ₀(orthogonalClosedSubmodule U) ∧
        ψ.asEReal =
          lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) :=
  -- TODO: repackage the envelope as a `Γ₀` owner after the subtype-topology obligations in this
  -- block are normalized.
  retired_placeholder

/-- Helper for Remark 16.46: the subdifferential of a second-coordinate pullback is exactly the
zero-first-coordinate slice of the original subdifferential. -/
private theorem mem_subdifferential_secondCoordinatePullback_iff_zero_fst_l2
    (U : Submodule ℝ L2Nat)
    (ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
    (hψ : ψ ∈ Γ₀(orthogonalClosedSubmodule U))
    {x u : L2Nat × orthogonalClosedSubmodule U} :
    x ∈ (∂ (fun p : L2Nat × orthogonalClosedSubmodule U ↦ (ψ p.2 : EReal))) u ↔
      x.1 = 0 ∧ x.2 ∈ (∂ ψ) u.2 := by
  -- The generic pullback formula specializes directly to `L2Nat × Uᗮ`.
  rw [subdifferential_secondCoordinatePullback_eq_zero_prod_general
    (A := L2Nat) (K := orthogonalClosedSubmodule U) ψ hψ u.1 u.2]
  simp

/-- Helper for Remark 16.46: at a point on the horizontal slice `{(a,0)}`, the subdifferential of
the slice indicator consists exactly of vectors with vanishing first coordinate. -/
private theorem mem_subdifferential_horizontalOrthogonalSliceIndicator_iff_zero_fst_l2
    (U : Submodule ℝ L2Nat) (a : L2Nat) (u : L2Nat × orthogonalClosedSubmodule U) :
    u ∈
        (∂ (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))) (a, 0) ↔
      u.1 = 0 :=
  -- TODO: restore this horizontal-slice normal-cone calculation after the product-space
  -- subdifferential rewrites are stabilized again.
  retired_placeholder

/-- Helper for Remark 16.46: once the raw dual infimal convolution has been normalized to the
second-coordinate projected-image owner, Proposition 15.1 rewrites `(f + g)^*` as the lower
semicontinuous convex envelope of that same pullback. -/
private theorem conjugatePointwiseAdd_eq_secondCoordinateEnvelopePullback_l2
    (U V : Submodule ℝ L2Nat)
    (f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hraw_snd :
      ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal)) =
        fun p : L2Nat × orthogonalClosedSubmodule U =>
          ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) :
    (f + g).asEReal∗ =
      lowerSemicontinuousConvexEnvelope
        (fun p : L2Nat × orthogonalClosedSubmodule U =>
          ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
  -- Reuse the generic Chapter 15 envelope formula and then rewrite the normalized raw owner.
  calc
    (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal)) := by
          exact
            conjugate_pointwiseAdd_eq_lscConvexEnvelope_infimalConvolution_conjugates_local
              f g hf hg hdom
    _ =
        lowerSemicontinuousConvexEnvelope
          (fun p : L2Nat × orthogonalClosedSubmodule U =>
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
          rw [hraw_snd]

/-- Helper for Remark 16.46: the conjugate of the packaged projected-image envelope `ψ`
coincides with the raw conjugate of `projectedImageRawOwner U V`. -/
private theorem projectedImageEnvelopeConjugate_eq_rawConjugate_l2
    (U V : Submodule ℝ L2Nat)
    (ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
    (hψ : ψ ∈ Γ₀(orthogonalClosedSubmodule U))
    (hψ_eq :
      ψ.asEReal =
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) :
    (ψ∗[hψ]).asEReal = ((projectedImageRawOwner U V).asEReal)∗ :=
  -- TODO: recover this conjugate normalization after the envelope package above is stable again.
  retired_placeholder

-/

/-- Helper for Remark 16.46: the raw projected-image owner and its closure-side comparison owner
have the same conjugate, because Example 13.5 only depends on the distance to the closure of the
projected image. -/
private theorem projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2
    (U V : Submodule ℝ L2Nat) :
    ((projectedImageRawOwner U V).asEReal)∗ =
      ((projectedImageClosureOwner U V).asEReal)∗ := by
  let K := orthogonalClosedSubmodule U
  let A : Set K := (projectedImageSubmodule U V : Set K)
  have hA_nonempty : A.Nonempty := ⟨0, by simp [A]⟩
  have hzero_mem_A : (0 : K) ∈ A := by simpa [A] using hA_nonempty.some_mem
  have hclosure_nonempty : (closure A).Nonempty := ⟨0, subset_closure hzero_mem_A⟩
  funext ξ
  -- Example 13.5 rewrites both conjugates through the same squared-distance formula.
  rw [projectedImageRawOwner, projectedImageClosureOwner]
  rw [fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
      A hA_nonempty]
  rw [fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
      (closure A) hclosure_nonempty]
  congr 1
  rw [Metric.infDist_closure]

/-- Helper for Remark 16.46: the subdifferential of a submodule indicator consists exactly of
orthogonal vectors at points inside the submodule. -/
private theorem mem_subdifferential_indicator_submodule_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : Submodule ℝ E) {x u : E} :
    u ∈ (∂ (ι[(W : Set E)] : E → Set.Ioi (⊥ : EReal))) x ↔ x ∈ W ∧ u ∈ Wᗮ := by
  have hdom :
      (effectiveDomain (ι[(W : Set E)] : E → Set.Ioi (⊥ : EReal))).Nonempty := by
    refine ⟨0, ?_⟩
    simp [mem_effectiveDomain_iff, indicator_apply]
  constructor
  · intro hu
    have hfy :=
      (mem_subdifferential_iff_fenchel_young_eq
        (f := (ι[(W : Set E)] : E → Set.Ioi (⊥ : EReal))) hdom x u).1 hu
    rw [conjugate_indicator_submodule_eq_indicator_orthogonal (V := W)] at hfy
    by_cases hx : x ∈ W
    · by_cases huW : u ∈ Wᗮ
      · exact ⟨hx, huW⟩
      · have : (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ⊤ := by
          simpa [indicator_apply, hx, huW] using hfy
        exact (EReal.coe_ne_top _ this).elim
    · have : (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ⊤ := by
        simpa [indicator_apply, hx] using hfy
      exact (EReal.coe_ne_top _ this).elim
  · rintro ⟨hx, huW⟩
    -- Rewrite the conjugate once to the orthogonal indicator and then discharge the exact
    -- Fenchel--Young equality on the submodule/orthogonal pair.
    refine
      (mem_subdifferential_iff_fenchel_young_eq
        (f := (ι[(W : Set E)] : E → Set.Ioi (⊥ : EReal))) hdom x u).2 ?_
    rw [conjugate_indicator_submodule_eq_indicator_orthogonal (V := W)]
    have hinner : ⟪x, u⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hx huW
    simp [indicator_apply, hx, huW, hinner]

/-- Helper for Remark 16.46: on the horizontal slice `{(a, 0)}`, the indicator subgradient is the
vertical normal cone, so only points with zero second coordinate contribute, and the resulting
subgradients have zero first coordinate. -/
private theorem mem_subdifferential_horizontalOrthogonalSliceIndicator_iff
    (U : Submodule ℝ L2Nat)
    {x u : L2Nat × orthogonalClosedSubmodule U} :
    x ∈
        (∂ (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))) u ↔
      u.2 = 0 ∧ x.1 = 0 := by
  let K := orthogonalClosedSubmodule U
  let M : L2Nat →L[ℝ] K := 0
  let W : Submodule ℝ (L2Nat × K) := M.toLinearMap.graph
  -- Rewrite the slice owner as the zero-graph indicator, then use the generic indicator formula.
  change
    x ∈
        (∂ (ι[(W : Set (L2Nat × K))] :
          (L2Nat × K) → Set.Ioi (⊥ : EReal))) u ↔
      u.2 = 0 ∧ x.1 = 0
  rw [mem_subdifferential_indicator_submodule_iff W]
  constructor
  · rintro ⟨huW, hxW⟩
    constructor
    · -- Belonging to the zero graph is exactly the zero-second-coordinate condition.
      simpa [W, M, linearGraphSet, LinearMap.mem_graph_iff] using huW
    · -- Orthogonality to the zero graph reduces to the vanishing first coordinate.
      have hx_zero : x.1 + M.adjoint x.2 = 0 :=
        (mem_orthogonal_graph_iff (M := M) (w := x)).1 hxW
      simpa [M] using hx_zero
  · rintro ⟨hu2, hx1⟩
    constructor
    · -- A point with zero second coordinate lies on the horizontal slice graph.
      simpa [W, M, linearGraphSet, LinearMap.mem_graph_iff, hu2]
    · -- The same zero-first-coordinate equation is the graph-orthogonality condition.
      have hx_zero : x.1 + M.adjoint x.2 = 0 := by
        simpa [M, hx1]
      exact (mem_orthogonal_graph_iff (M := M) (w := x)).2 hx_zero

/-- Helper for Remark 16.46: the quadratic subdifferential on a Hilbert space is the singleton
map `u ↦ {u}`. -/
private theorem subdifferential_halfSquaredNorm_apply_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) :
    (∂ (halfSquaredNorm : E → Set.Ioi (⊥ : EReal))) x = ({x} : Set E) := by
  ext u
  rw [Set.mem_singleton_iff]
  constructor
  · intro hu
    -- Fenchel--Young equality for `halfSquaredNorm` forces the quadratic gap
    -- `‖x - u‖²` to vanish.
    have hfy := (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x u).1 hu
    rw [fenchelConjugate_halfSquaredNorm] at hfy
    norm_num [halfSquaredNorm_apply] at hfy
    have hfy' :
        (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) = inner ℝ x u := by
      exact_mod_cast hfy
    have hnorm : ‖x - u‖ ^ (2 : ℕ) = 0 := by
      rw [norm_sub_sq_real]
      nlinarith [hfy', real_inner_comm x u]
    have hzero : ‖x - u‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · intro hu
    subst u
    -- Self-conjugacy of `halfSquaredNorm` makes Fenchel--Young exact on the diagonal.
    exact (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x x).2 <| by
      rw [fenchelConjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply,
        real_inner_self_eq_norm_sq]
      exact_mod_cast (by ring :
        ‖x‖ ^ (2 : ℕ) / 2 + ‖x‖ ^ (2 : ℕ) / 2 = ‖x‖ ^ (2 : ℕ))

/-- Helper for Remark 16.46: every closure point of `P_{Uᗮ}(V)` is a fixed-point subgradient of
the raw conjugate at the same point. -/
private theorem projectedImageClosurePoint_mem_subdifferentialRawConjugate_l2
    (U V : Submodule ℝ L2Nat)
    {u0 : orthogonalClosedSubmodule U}
    (hu0_closure :
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    u0 ∈ (∂ (((projectedImageRawOwner U V).asEReal)∗)) u0 := by
  let K := orthogonalClosedSubmodule U
  let A : Submodule ℝ K := projectedImageSubmodule U V
  let W : Submodule ℝ K := A.topologicalClosure
  have hclosure_gamma :
      projectedImageClosureOwner U V ∈ Γ₀(K) :=
    projectedImageClosureOwner_mem_gammaZero_l2 U V
  have hW_indicator :
      (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
    -- The closure of a submodule is a closed convex submodule containing `0`.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ⟨0, W.zero_mem⟩ ?_ W.convex
    simpa [W] using Submodule.isClosed_topologicalClosure A
  have hhalf_dom :
      effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) = Set.univ := by
    ext y
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    simp
  have hclosure_subdiff :
      (∂ (projectedImageClosureOwner U V) : SetValuedOperator K K) =
        (∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
          ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
    -- Rewrite the closure owner once to the indicator-plus-quadratic normal form.
    simpa [projectedImageClosureOwner, W, Submodule.topologicalClosure_coe] using
      (subdifferential_add_eq_add_of_dom_univ_local
        (f := (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)))
        (g := (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)))
        hW_indicator halfSquaredNorm_mem_gammaZero_local hhalf_dom)
  have hu0_indicator :
      (0 : K) ∈ (∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) u0 := by
    -- The zero vector is orthogonal to the closed projected-image submodule at every point of it.
    refine (mem_subdifferential_indicator_submodule_iff W).2 ?_
    refine ⟨?_, by simp⟩
    simpa [W, Submodule.topologicalClosure_coe] using hu0_closure
  have hu0_half :
      u0 ∈ (∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) u0 := by
    -- The quadratic owner is exact on the diagonal.
    simpa [subdifferential_halfSquaredNorm_apply_local]
  have hu0_closure_owner :
      u0 ∈ (∂ (projectedImageClosureOwner U V)) u0 := by
    have hu0_split :
        u0 ∈
          ((∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
            ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) u0 := by
      exact Set.mem_add.2 ⟨0, hu0_indicator, u0, hu0_half, by simp⟩
    simpa [hclosure_subdiff] using hu0_split
  have hu0_closure_conj :
      u0 ∈ (∂ (((projectedImageClosureOwner U V).asEReal)∗)) u0 := by
    have hu0_closure_gamma :
        u0 ∈ (∂ ((projectedImageClosureOwner U V)∗[hclosure_gamma])) u0 := by
      -- Corollary 16.30 turns the primal closure-owner subgradient into the dual one.
      exact (mem_subdifferential_gammaZeroConjugate_iff hclosure_gamma).2 hu0_closure_owner
    simpa [gammaZeroConjugate_apply] using hu0_closure_gamma
  -- The raw owner and its closure-side comparison owner have the same conjugate.
  simpa [projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V] using
    hu0_closure_conj

/-- Helper for Remark 16.46: a subgradient of the raw conjugate already determines the closure-side
support data, namely membership in `closure (P_{Uᗮ}(V))` and the orthogonality residual
`ξ - u ∈ (P_{Uᗮ}(V))ᗮ`. -/
private theorem projectedImageClosureSupportData_of_mem_subdifferentialRawConjugate_l2
    (U V : Submodule ℝ L2Nat)
    {ξ u : orthogonalClosedSubmodule U}
    (hx : u ∈ (∂ (((projectedImageRawOwner U V).asEReal)∗)) ξ) :
    u ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      ξ - u ∈
        (((projectedImageSubmodule U V)ᗮ :
          Submodule ℝ (orthogonalClosedSubmodule U)) :
            Set (orthogonalClosedSubmodule U)) := by
  let K := orthogonalClosedSubmodule U
  let A : Submodule ℝ K := projectedImageSubmodule U V
  let W : Submodule ℝ K := A.topologicalClosure
  have hclosure_gamma :
      projectedImageClosureOwner U V ∈ Γ₀(K) :=
    projectedImageClosureOwner_mem_gammaZero_l2 U V
  have hW_indicator :
      (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
    -- The closure of a submodule is a closed convex submodule containing `0`.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ⟨0, W.zero_mem⟩ ?_ W.convex
    simpa [W] using Submodule.isClosed_topologicalClosure A
  have hhalf_dom :
      effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) = Set.univ := by
    ext y
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    simp
  have hclosure_subdiff :
      (∂ (projectedImageClosureOwner U V) : SetValuedOperator K K) =
        (∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
          ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
    -- Rewrite the closure owner once to the indicator-plus-quadratic normal form.
    simpa [projectedImageClosureOwner, W, Submodule.topologicalClosure_coe] using
      (subdifferential_add_eq_add_of_dom_univ_local
        (f := (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)))
        (g := (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)))
        hW_indicator halfSquaredNorm_mem_gammaZero_local hhalf_dom)
  have hx_closure_conj :
      u ∈ (∂ (((projectedImageClosureOwner U V).asEReal)∗)) ξ := by
    simpa [projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V] using hx
  have hx_closure_gamma :
      u ∈ (∂ ((projectedImageClosureOwner U V)∗[hclosure_gamma])) ξ := by
    simpa [gammaZeroConjugate_apply] using hx_closure_conj
  have hx_closure_owner :
      ξ ∈ (∂ (projectedImageClosureOwner U V)) u :=
    (mem_subdifferential_gammaZeroConjugate_iff hclosure_gamma).1 hx_closure_gamma
  have hx_split :
      ξ ∈
        ((∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
          ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) u := by
    simpa [hclosure_subdiff] using hx_closure_owner
  rcases Set.mem_add.mp hx_split with ⟨v, hv_indicator, w, hw_half, hsum⟩
  have hw_eq : w = u := by
    simpa [subdifferential_halfSquaredNorm_apply_local] using hw_half
  have hv_mem :
      u ∈ W ∧ v ∈ Wᗮ :=
    (mem_subdifferential_indicator_submodule_iff W).1 hv_indicator
  refine ⟨?_, ?_⟩
  · -- The indicator part places `u` in the closure of the projected image.
    simpa [W, Submodule.topologicalClosure_coe] using hv_mem.1
  · have hv_eq : v = ξ - u := by
      calc
        v = v + w - w := by abel
        _ = ξ - u := by rw [hsum, hw_eq]
    have hv_orth :
        v ∈ (((projectedImageSubmodule U V)ᗮ :
          Submodule ℝ (orthogonalClosedSubmodule U)) :
            Set (orthogonalClosedSubmodule U)) := by
      simpa [A, W, Submodule.orthogonal_closure] using hv_mem.2
    simpa [hv_eq] using hv_orth

/-- Helper for Remark 16.46: an explicit projected-image witness immediately makes the projection
fiber exact at `-u`. -/
private theorem projectedImageProjectionExactAt_of_witness_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U} {a : L2Nat}
    (haV : a ∈ V)
    (hproj : (orthogonalClosedSubmodule U).orthogonalProjection a = -u) :
    infimalPostcomposition.ExactAt
      (orthogonalClosedSubmodule U).orthogonalProjection
      (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
      (-u) := by
  have hu_image : -u ∈ projectedImageSubmodule U V :=
    Submodule.mem_map.mpr ⟨a, haV, hproj⟩
  -- Convert the explicit fiber witness to the existing projected-image exactness lemma.
  simpa using projectionIndicator_exactAt_of_mem_projectedImage_l2 U V hu_image

/-- Helper for Remark 16.46: exactness of the projection fiber immediately recovers a concrete
ambient witness in `V` whose projection is `-u`. -/
private theorem projectedImageWitness_of_projectionExactAt_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hexact :
      infimalPostcomposition.ExactAt
        (orthogonalClosedSubmodule U).orthogonalProjection
        (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
        (-u)) :
    ∃ a : L2Nat, a ∈ V ∧ (orthogonalClosedSubmodule U).orthogonalProjection a = -u := by
  rcases
      (infimalPostcomposition.exactAt_iff_exists_eq
        (orthogonalClosedSubmodule U).orthogonalProjection
        (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
        (-u)).1 hexact with
    ⟨hu_dom, a, hproj, hEq⟩
  have haV : a ∈ V := by
    -- Exactness identifies the attained fiber value with a finite indicator value.
    by_contra haV
    have hfinite :
        (((ι[(V : Set L2Nat)] a : Set.Ioi (⊥ : EReal)) : EReal)) < ⊤ := by
      rw [mem_dom_iff] at hu_dom
      rw [hEq] at hu_dom
      exact hu_dom
    simp [indicator_apply, haV] at hfinite
  exact ⟨a, haV, hproj⟩

/-- Helper for Remark 16.46: once the projection-fiber indicator is exact at `-u`, the product
vertical slice `(0,u)` has the exact raw split and hence finite value. -/
private theorem projectedImageVerticalExactAtFinite_of_projectionExactAt_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hexact :
      infimalPostcomposition.ExactAt
        (orthogonalClosedSubmodule U).orthogonalProjection
        (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
        (-u)) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    infimalConvolution.ExactAt s t (0, u) ∧ (((s □ t) : E → EReal) (0, u)) < ⊤ := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  rcases projectedImageWitness_of_projectionExactAt_l2 U V hexact with ⟨a, haV, hproj⟩
  have hu_image : u ∈ projectedImageSubmodule U V := by
    refine Submodule.mem_map.mpr ?_
    refine ⟨-a, V.neg_mem haV, ?_⟩
    simpa using congrArg Neg.neg hproj
  have hraw_value :
      (((s □ t) : E → EReal) (0, u)) = (halfSquaredNorm u : EReal) := by
    -- Evaluate the normalized raw infimal convolution on the vertical slice `(0, u)`.
    rw [horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V (0, u)]
    rw [projectedImageRawOwner]
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) = 0 by
      simp [indicator_apply, hu_image]]
    simp
  have hexact_vertical : infimalConvolution.ExactAt s t (0, u) := by
    refine ⟨(a, 0), ?_⟩
    have hs_value : (s (a, 0) : EReal) = 0 := by
      simp [s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
    have hgraph :
        ((-a, u) : E) ∈ projectedImageGraphSet U V := by
      constructor
      · exact V.neg_mem haV
      · simpa using congrArg Neg.neg hproj
    have ht_value : (t (-a, u) : EReal) = (halfSquaredNorm u : EReal) := by
      rw [show
          (ι[projectedImageGraphSet U V] ((-a, u) : E) : EReal) = 0 by
        simp [indicator_apply, hgraph]]
      simp [t]
    -- The explicit graph witness attains the raw infimal-convolution value at `(0, u)`.
    calc
      (((s □ t) : E → EReal) (0, u)) = (halfSquaredNorm u : EReal) := hraw_value
      _ = (s (a, 0) : EReal) + (t ((0, u) - (a, 0)) : EReal) := by
            rw [hs_value, subtract_horizontalSliceWitness_l2 U (0, u) a, ht_value]
            simp
  refine ⟨hexact_vertical, ?_⟩
  -- The exact value is the finite quadratic height on the projected image.
  rw [hraw_value, halfSquaredNorm_apply]
  exact EReal.coe_lt_top _

/-- Helper for Remark 16.46: an actual projected-image point `u ∈ P_{Uᗮ}(V)` gives a concrete
ambient witness in `V` whose projection is `-u` after negating the source vector. -/
private theorem projectedImageWitness_of_mem_projectedImage_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hu_image : u ∈ projectedImageSubmodule U V) :
    ∃ a : L2Nat, a ∈ V ∧ (orthogonalClosedSubmodule U).orthogonalProjection a = -u := by
  rcases Submodule.mem_map.mp hu_image with ⟨a, haV, hproj⟩
  -- Negating a projected-image witness flips the projection to the target fiber `P a = -u`.
  refine ⟨-a, V.neg_mem haV, ?_⟩
  simpa using congrArg Neg.neg hproj

/-- Helper for Remark 16.46: once projected-image membership of `u` is known, the projection
fiber over `-u` is exact. -/
private theorem projectionExactAt_of_mem_projectedImage_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hu_image : u ∈ projectedImageSubmodule U V) :
    infimalPostcomposition.ExactAt
      (orthogonalClosedSubmodule U).orthogonalProjection
      (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
      (-u) := by
  rcases projectedImageWitness_of_mem_projectedImage_l2 U V hu_image with ⟨a, haV, hproj⟩
  -- The witness-to-exactness adapter isolates the projection-fiber API from the membership proof.
  exact projectedImageProjectionExactAt_of_witness_l2 U V haV hproj

/-- Helper for Remark 16.46: the graph-plus-quadratic owner is finite exactly on the projected
image graph, because the quadratic tail is finite everywhere and only the indicator can blow up. -/
private theorem mem_effectiveDomain_projectedImageGraphOwner_iff_l2
    (U V : Submodule ℝ L2Nat)
    {p : L2Nat × orthogonalClosedSubmodule U} :
    p ∈ effectiveDomain
        (fun q : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] q : Set.Ioi (⊥ : EReal)) + halfSquaredNorm q.2) ↔
      p ∈ projectedImageGraphSet U V := by
  by_cases hp : p ∈ projectedImageGraphSet U V
  · constructor
    · intro _
      exact hp
    · intro _
      rw [mem_effectiveDomain_iff]
      rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = 0 by
        simp [indicator_apply, hp]]
      rw [halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  · constructor
    · intro hp_dom
      rw [mem_effectiveDomain_iff] at hp_dom
      have hhalf_ne_bot : (halfSquaredNorm p.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm p.2).2
      rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ by
        simp [indicator_apply, hp]] at hp_dom
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot] at hp_dom
      exact (lt_irrefl (⊤ : EReal)) hp_dom
    · intro hp'
      exact (hp hp').elim

/-- Helper for Remark 16.46: subtracting the horizontal-slice candidate `(u.1 + a, 0)` from `u`
leaves exactly the graph-side witness `(-a, u.2)`. -/
private theorem subtract_horizontalSliceWitness_l2
    (U : Submodule ℝ L2Nat)
    (u : L2Nat × orthogonalClosedSubmodule U)
    (a : L2Nat) :
    u - (u.1 + a, 0) = (-a, u.2) := by
  -- This is the product-space identity needed to glue the horizontal and graph-side witnesses.
  ext i <;> simp <;> abel

/-- Helper for Remark 16.46: at a bad projected point `u0 ∉ P_{Uᗮ}(V)`, the explicit product-graph
witness pair cannot have `(0,u0)` in `∂ f + ∂ g` because any `∂ g` summand must lie on the
projected-image graph. -/
private theorem productGraphWitness_badPoint_not_mem_subdifferentialAdd_l2
    (U V : Submodule ℝ L2Nat)
    {u0 : orthogonalClosedSubmodule U}
    {f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hfs :
      (f∗[hf]) =
        (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)))
    (hgs :
      (g∗[hg]) =
        (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
    (hu0_not_mem :
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    ((0, u0) : L2Nat × orthogonalClosedSubmodule U) ∉
      ((∂ f) + ∂ g) ((0, u0) : L2Nat × orthogonalClosedSubmodule U) := by
  intro hu
  rcases Set.mem_add.mp hu with ⟨v, hvf, w, hwg, hsum⟩
  have hvf_zero : v.2 = 0 := by
    exact (mem_subdifferential_productGraphWitnessF_iff_l2 U hf hfs).1 hvf |>.2
  have hwg_gamma :
      ((0, u0) : L2Nat × orthogonalClosedSubmodule U) ∈
        (∂ (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2)) w := by
    -- Transport the `∂ g` summand across conjugation so the explicit graph-side owner can be read.
    rw [← mem_subdifferential_gammaZeroConjugate_iff hg]
    simpa [hgs] using hwg
  have hgraph_owner_gamma :
      (fun p : L2Nat × orthogonalClosedSubmodule U ↦
        (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2) ∈
        Γ₀(L2Nat × orthogonalClosedSubmodule U) := by
    -- The graph-side owner is exactly `g*`, hence still belongs to `Γ₀`.
    simpa [hgs] using gammaZeroConjugate_mem_gammaZero hg
  have hw_dom :
      w ∈ effectiveDomain
        (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2) :=
    mem_effectiveDomain_of_mem_subdifferential_local hgraph_owner_gamma hwg_gamma
  have hw_graph : w ∈ projectedImageGraphSet U V :=
    (mem_effectiveDomain_projectedImageGraphOwner_iff_l2 U V).1 hw_dom
  have hw2_eq : w.2 = u0 := by
    -- The horizontal-slice summand has zero second coordinate, so `w` carries the full `u0`.
    simpa [hvf_zero] using congrArg Prod.snd hsum
  have hu0_mem :
      u0 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
    have hw2_mem :
        w.2 ∈ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
      exact Submodule.mem_map.mpr ⟨w.1, hw_graph.1, hw_graph.2⟩
    simpa [hw2_eq] using hw2_mem
  exact hu0_not_mem hu0_mem

/-- Helper for Remark 16.46: if `u` lies in the projected image and `ξ - u` is orthogonal to that
projected image, then every graph point `(-a, u)` with `a ∈ V` and `P_{Uᗮ} a = -u` carries the
graph-side subgradient `(0, ξ)` for the regularized graph owner. -/
private theorem mem_subdifferential_projectedImageGraphOwner_of_mem_projectedImage_and_orthogonal
    (U V : Submodule ℝ L2Nat)
    {u ξ : orthogonalClosedSubmodule U} {a : L2Nat}
    (haV : a ∈ V)
    (hproj : (orthogonalClosedSubmodule U).orthogonalProjection a = -u)
    (horth :
      ξ - u ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U))) :
    (0, ξ) ∈
      (∂ (fun p : L2Nat × orthogonalClosedSubmodule U ↦
        (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
        (-a, u) := by
  have hy_graph : ((-a, u) : L2Nat × orthogonalClosedSubmodule U) ∈ projectedImageGraphSet U V := by
    -- The chosen point lies on the projected-image graph by construction.
    constructor
    · simpa using V.neg_mem haV
    · simpa using congrArg Neg.neg hproj
  -- The proof is the graph-indicator inequality plus the quadratic lower support at `u`.
  rw [mem_subdifferential_iff]
  intro z
  rcases z with ⟨b, w⟩
  by_cases hz : ((b, w) : L2Nat × orthogonalClosedSubmodule U) ∈ projectedImageGraphSet U V
  · rcases hz with ⟨hbV, hbproj⟩
    have hdiff_mem :
        w - u ∈ projectedImageSubmodule U V := by
      -- Subtracting two graph points stays in the projected image submodule.
      refine Submodule.mem_map.mpr ?_
      refine ⟨b + a, V.add_mem hbV haV, ?_⟩
      calc
        (orthogonalClosedSubmodule U).orthogonalProjection (b + a)
            = (orthogonalClosedSubmodule U).orthogonalProjection b +
                (orthogonalClosedSubmodule U).orthogonalProjection a := by
                  simp
        _ = w + (-u) := by rw [hbproj, hproj]
        _ = w - u := by simp [sub_eq_add_neg]
    have horth_zero : ⟪w - u, ξ - u⟫_ℝ = 0 := by
      -- Orthogonality against the projected image kills the residual linear term.
      have hmem_orth : w - u ∈ projectedImageSubmodule U V := hdiff_mem
      exact Submodule.inner_right_of_mem_orthogonal horth hmem_orth
    have hquad_real :
        ⟪w - u, ξ⟫_ℝ + ‖u‖ ^ 2 / 2 ≤ ‖w‖ ^ 2 / 2 := by
      calc
        ⟪w - u, ξ⟫_ℝ + ‖u‖ ^ 2 / 2
            = ⟪w - u, u⟫_ℝ + ‖u‖ ^ 2 / 2 := by
                rw [show ξ = u + (ξ - u) by abel]
                rw [inner_add_right, horth_zero]
                simp
        _ = ‖w‖ ^ 2 / 2 - ‖w - u‖ ^ 2 / 2 := by
              nlinarith [real_inner_self_eq_norm_sq (w - u), real_inner_self_eq_norm_sq u,
                real_inner_self_eq_norm_sq w, sq_norm_add_sq_norm_sub_eq_two_inner (u := w) (v := u)]
        _ ≤ ‖w‖ ^ 2 / 2 := by
              have hnonneg : 0 ≤ ‖w - u‖ ^ 2 / 2 := by positivity
              linarith
    have hgraph_value :
        (((ι[projectedImageGraphSet U V] ((-a, u) : L2Nat × orthogonalClosedSubmodule U) :
            Set.Ioi (⊥ : EReal)) : EReal)) = 0 := by
      simp [indicator_apply, hy_graph]
    have hz_value :
        (((ι[projectedImageGraphSet U V] ((b, w) : L2Nat × orthogonalClosedSubmodule U) :
            Set.Ioi (⊥ : EReal)) : EReal)) = 0 := by
      simp [indicator_apply, hz]
    -- After the indicator terms vanish, the claim is exactly the quadratic support inequality.
    have hinner_pair :
        ⟪((b, w) : L2Nat × orthogonalClosedSubmodule U) - (-a, u), (0, ξ)⟫_ℝ =
          ⟪w - u, ξ⟫_ℝ := by
      change ⟪b - (-a), (0 : L2Nat)⟫_ℝ + ⟪w - u, ξ⟫_ℝ = ⟪w - u, ξ⟫_ℝ
      simp
    have hquad_ereal :
        (⟪w - u, ξ⟫_ℝ : EReal) + (halfSquaredNorm u : EReal) ≤ (halfSquaredNorm w : EReal) := by
      simpa [halfSquaredNorm_apply] using (show
        (((⟪w - u, ξ⟫_ℝ + ‖u‖ ^ 2 / 2 : ℝ)) : EReal) ≤ (((‖w‖ ^ 2 / 2 : ℝ)) : EReal) from
          by exact_mod_cast hquad_real)
    simpa [pointwiseAdd_apply, hgraph_value, hz_value, hinner_pair] using hquad_ereal
  · have hhalf_ne_bot : (halfSquaredNorm w : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm w).2
    have hz_top :
        (((ι[projectedImageGraphSet U V] ((b, w) : L2Nat × orthogonalClosedSubmodule U) :
            Set.Ioi (⊥ : EReal)) : EReal)) = ⊤ := by
      simp [indicator_apply, hz]
    have hy_value :
        ((((ι[projectedImageGraphSet U V] ((-a, u) : L2Nat × orthogonalClosedSubmodule U) :
            Set.Ioi (⊥ : EReal)) : EReal) + (halfSquaredNorm u : EReal))) =
          (halfSquaredNorm u : EReal) := by
      rw [show
          (((ι[projectedImageGraphSet U V] ((-a, u) : L2Nat × orthogonalClosedSubmodule U) :
              Set.Ioi (⊥ : EReal)) : EReal)) = 0 by
        simp [indicator_apply, hy_graph]]
      simp
    -- Off the graph, the indicator contributes `⊤`, so the subgradient inequality is automatic.
    rw [pointwiseAdd_apply, hz_top]
    rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
    simpa [hy_value] using
      (le_top :
        (⟪((b, w) : L2Nat × orthogonalClosedSubmodule U) - (-a, u), (0, ξ)⟫_ℝ : EReal) +
            (((ι[projectedImageGraphSet U V] ((-a, u) : L2Nat × orthogonalClosedSubmodule U) :
                Set.Ioi (⊥ : EReal)) : EReal) + (halfSquaredNorm u : EReal)) ≤
          ⊤)

/-- Helper for Remark 16.46: the rejected active-point route is genuinely false. There are closed
projected-image data and a bad point `u0 ∉ P_{Uᗮ}(V)` that still has finite envelope value and
lies in the subdifferential of the raw conjugate at `ξ = u0`. -/
private theorem exists_activeRawConjugateBadPoint_withFiniteEnvelope_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat))
      (u0 : orthogonalClosedSubmodule U),
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ ∧
        u0 ∈ dom (((projectedImageRawOwner U V).asEReal)∗) ∧
        u0 ∈ (∂ (((projectedImageRawOwner U V).asEReal)∗)) u0 := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  let K := orthogonalClosedSubmodule U
  let A : Submodule ℝ K := projectedImageSubmodule U V
  let W : Submodule ℝ K := A.topologicalClosure
  have hu0_env_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
    let q : K → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
    have hcont_q : Continuous q := by
      have hnorm_sq : Continuous fun x : K ↦ ‖x‖ ^ 2 := by
        simpa using (continuous_norm.pow 2 : Continuous fun x : K ↦ ‖x‖ ^ 2)
      simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_const.mul hnorm_sq :
          Continuous fun x : K ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
    have hgraph_closure :
        (u0, q u0) ∈ closure ((fun x : K ↦ (x, q x)) '' (A : Set K)) := by
      -- Push the closure point through the continuous graph map `x ↦ (x, ‖x‖² / 2)`.
      have hu0_image : (u0, q u0) ∈ (fun x : K ↦ (x, q x)) '' closure (A : Set K) := by
        exact ⟨u0, hu0_closure, rfl⟩
      exact image_closure_subset_closure_image (continuous_id.prodMk hcont_q) hu0_image
    have hgraph_subset :
        (fun x : K ↦ (x, q x)) '' (A : Set K) ⊆
          epigraph ((projectedImageRawOwner U V).asEReal) := by
      rintro _ ⟨x, hxA, rfl⟩
      rw [mem_epigraph_iff]
      -- On the projected image, the raw owner is exactly the quadratic tail.
      rw [projectedImageRawOwner]
      change
        (ι[(A : Set K)] x : EReal) + (halfSquaredNorm x : EReal) ≤ ((q x : ℝ) : EReal)
      rw [show (ι[(A : Set K)] x : EReal) = 0 by simp [indicator_apply, hxA]]
      rw [halfSquaredNorm_apply]
      simpa [q]
    have hraw_epi :
        (u0, q u0) ∈ closure (epigraph ((projectedImageRawOwner U V).asEReal)) :=
      closure_mono hgraph_subset hgraph_closure
    have henv_epi :
        (u0, q u0) ∈
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) := by
      have hepi_eq :
          epigraph (lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) =
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) := by
        exact
          epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
            (H := K) ((projectedImageRawOwner U V).asEReal)
      have hclosure_convexHull :
          (u0, q u0) ∈
            closure (convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) :=
        closure_mono (subset_convexHull ℝ (epigraph ((projectedImageRawOwner U V).asEReal))) hraw_epi
      rw [hepi_eq]
      exact hclosure_convexHull
    have henv_le :
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 ≤
          ((q u0 : ℝ) : EReal) := by
      exact (mem_epigraph_iff _ _ _).mp henv_epi
    -- The real graph height bounds the envelope by a finite value at the bad point.
    exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
  have hclosure_gamma :
      projectedImageClosureOwner U V ∈ Γ₀(K) :=
    projectedImageClosureOwner_mem_gammaZero_l2 U V
  have hW_indicator :
      (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
    -- The closure of a submodule is a closed convex submodule containing `0`.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ⟨0, W.zero_mem⟩ ?_ W.convex
    simpa [W] using Submodule.isClosed_topologicalClosure A
  have hhalf_dom :
      effectiveDomain (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) = Set.univ := by
    ext y
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    simp
  have hclosure_subdiff :
      (∂ (projectedImageClosureOwner U V) : SetValuedOperator K K) =
        (∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
          ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)) := by
    -- Rewrite the closure owner once to the indicator-plus-quadratic normal form.
    simpa [projectedImageClosureOwner, W, Submodule.topologicalClosure_coe] using
      (subdifferential_add_eq_add_of_dom_univ_local
        (f := (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal)))
        (g := (halfSquaredNorm : K → Set.Ioi (⊥ : EReal)))
        hW_indicator halfSquaredNorm_mem_gammaZero_local hhalf_dom)
  have hu0_indicator :
      (0 : K) ∈ (∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) u0 := by
    -- The zero vector is always orthogonal to the closure submodule at a point of that submodule.
    refine (mem_subdifferential_indicator_submodule_iff W).2 ?_
    refine ⟨?_, by simp⟩
    simpa [W, Submodule.topologicalClosure_coe] using hu0_closure
  have hu0_half :
      u0 ∈ (∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) u0 := by
    -- The quadratic owner is exact on the diagonal.
    simpa [subdifferential_halfSquaredNorm_apply_local]
  have hu0_closure_owner :
      u0 ∈ (∂ (projectedImageClosureOwner U V)) u0 := by
    have hu0_split :
        u0 ∈
          ((∂ (ι[(W : Set K)] : K → Set.Ioi (⊥ : EReal))) +
            ∂ (halfSquaredNorm : K → Set.Ioi (⊥ : EReal))) u0 := by
      exact Set.mem_add.2 ⟨0, hu0_indicator, u0, hu0_half, by simp⟩
    simpa [hclosure_subdiff] using hu0_split
  have hu0_rawConj :
      u0 ∈ (∂ (((projectedImageRawOwner U V).asEReal)∗)) u0 := by
    have hu0_closure_conj :
        u0 ∈ (∂ (((projectedImageClosureOwner U V).asEReal)∗)) u0 := by
      have hu0_closure_gamma :
          u0 ∈ (∂ ((projectedImageClosureOwner U V)∗[hclosure_gamma])) u0 := by
        -- Corollary 16.30 turns the primal closure-owner subgradient into the dual one.
        exact (mem_subdifferential_gammaZeroConjugate_iff hclosure_gamma).2 hu0_closure_owner
      simpa [gammaZeroConjugate_apply] using hu0_closure_gamma
    simpa [projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V] using
      hu0_closure_conj
  have hu0_rawConj_dom :
      u0 ∈ dom (((projectedImageRawOwner U V).asEReal)∗) := by
    have hu0_closure_dom :
        u0 ∈ dom (((projectedImageClosureOwner U V).asEReal)∗) :=
      mem_dom_conjugate_of_mem_subdifferential hclosure_gamma hu0_closure_owner
    simpa [projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V] using
      hu0_closure_dom
  exact ⟨U, V, hV_closed, u0, hu0_not_mem, hu0_env_finite, hu0_rawConj_dom, hu0_rawConj⟩

/-- Helper for Remark 16.46: the old product-graph reverse-inclusion route is retired. The bad
active-point theorem shows that its witness-extraction premise is false, so the remaining work
must proceed through a same-space pair on `Uᗮ`. -/
private theorem retiredProductGraphReverseInclusionRoute_l2 : True := by
  -- Route correction: keep a proved placeholder here so the dead product branch no longer stays
  -- on the active dependency chain.
  trivial

/-- Helper for Remark 16.46: the active bad-point package for the product-graph route keeps the
closedness of `V`, the concrete failure `u0 ∉ P_{Uᗮ}(V)`, and the raw/envelope value gap at the
same point. -/
private theorem existsProjectedImageProductGraphGapData_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat))
      (u0 : orthogonalClosedSubmodule U),
      u0 ∉ (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
        ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
  rcases exists_activeRawConjugateBadPoint_withFiniteEnvelope_l2 with
    ⟨U, V, hV_closed, u0, hu0_not_mem, hu0_env_finite, _hu0_rawConj_dom, _hu0_rawConj⟩
  have hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    -- Outside the projected image, the indicator branch contributes `⊤` at the bad point.
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    rw [projectedImageRawOwner]
    rw [show
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u0 : EReal) = ⊤ by
      simp [indicator_apply, hu0_not_mem]]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  exact ⟨U, V, hV_closed, u0, hu0_not_mem, hu0_raw_top, hu0_env_finite⟩

/-- Helper for Remark 16.46: the concrete product-graph witness pair is obtained by conjugating
the horizontal-slice owner and the graph-plus-quadratic owner, and its raw dual infimal
convolution is exactly the second-coordinate projected-image owner. -/
private theorem productGraphConjugateWitnessOwners_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    ∃ (f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
      (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U)),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        (f∗[hf]) =
          (ι[horizontalOrthogonalSliceSet U] :
            (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)) ∧
        (g∗[hg]) =
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2) ∧
        ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal)) =
          fun p : L2Nat × orthogonalClosedSubmodule U =>
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  have hs : s ∈ Γ₀(E) := by
    -- The horizontal-slice owner is already a packaged `Γ₀` indicator.
    simpa [E, s] using horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U
  have ht_graph :
      (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∈ Γ₀(E) := by
    -- Closedness of `V` upgrades the graph indicator to a `Γ₀` owner.
    simpa [E] using projectedImageGraphIndicator_mem_gammaZero_l2 U V hV_closed
  have ht_half :
      (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal))) ∈ Γ₀(E) := by
    -- The quadratic tail is the pulled-back half-squared norm on the second coordinate.
    simpa [E] using secondCoordinateHalfSquaredNorm_mem_gammaZero_l2 U
  have ht_dom :
      (effectiveDomain (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∩
          effectiveDomain (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))).Nonempty := by
    -- The origin is a common finite point of the graph indicator and the quadratic tail.
    refine ⟨(0, 0), ?_, ?_⟩
    · simp [mem_effectiveDomain_iff, projectedImageGraphSet]
    · rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  have ht : t ∈ Γ₀(E) := by
    -- Adding the quadratic tail keeps the graph owner in `Γ₀(E)`.
    exact pointwiseAdd_mem_gammaZero
      (ι[projectedImageGraphSet U V]) (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))
      ht_graph ht_half ht_dom
  let f : E → Set.Ioi (⊥ : EReal) := s∗[hs]
  let g : E → Set.Ioi (⊥ : EReal) := t∗[ht]
  have hf : f ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hs
  have hg : g ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero ht
  have hs_nonneg : ∀ p : E, (0 : EReal) ≤ (s p : EReal) := by
    intro p
    by_cases hp : p ∈ horizontalOrthogonalSliceSet U
    · simp [s, indicator_apply, hp]
    · simp [s, indicator_apply, hp]
  have hs_zero : (s 0 : EReal) = 0 := by
    -- The horizontal slice contains the origin.
    simp [s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff]
  have ht_nonneg : ∀ p : E, (0 : EReal) ≤ (t p : EReal) := by
    intro p
    by_cases hp : p ∈ projectedImageGraphSet U V
    · -- On the graph, only the quadratic tail remains.
      rw [show (ι[projectedImageGraphSet U V] p : EReal) = 0 by simp [indicator_apply, hp]]
      positivity
    · -- Off the graph, the indicator contributes `⊤`, so the sum is still nonnegative.
      have hhalf_ne_bot : (halfSquaredNorm p.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm p.2).2
      rw [show (ι[projectedImageGraphSet U V] p : EReal) = ⊤ by simp [indicator_apply, hp]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp
  have ht_zero : (t 0 : EReal) = 0 := by
    -- The origin is also a graph point, and its quadratic value vanishes.
    simp [t, projectedImageGraphSet, halfSquaredNorm_apply]
  have hf_zero :
      (0 : E) ∈ effectiveDomain f := by
    -- Nonnegativity plus a zero value at the origin make the conjugate finite at `0`.
    exact zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero hs hs_nonneg hs_zero
  have hg_zero :
      (0 : E) ∈ effectiveDomain g := by
    -- The same zero-test works for the graph-plus-quadratic owner.
    exact zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero ht ht_nonneg ht_zero
  have hfs : (f∗[hf]) = s := by
    -- Conjugating the packaged witness owner again returns the original slice owner.
    funext p
    apply Subtype.ext
    simpa [f, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hs) p
  have hgs : (g∗[hg]) = t := by
    -- The same biconjugation rewrite recovers the graph-plus-quadratic owner.
    funext p
    apply Subtype.ext
    simpa [g, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero ht) p
  refine ⟨f, g, hf, hg, ?_, hfs, hgs, ?_⟩
  · -- Both conjugate witnesses are finite at the origin.
    exact ⟨0, hf_zero, hg_zero⟩
  · -- Route correction: freeze the raw dual infimal convolution on the stable product-graph model.
    funext p
    rw [hfs, hgs]
    simpa [E, s, t] using horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V p

/-- Helper for Remark 16.46: once the explicit product-graph conjugate witnesses are fixed, the
Chapter 15 conjugate formula rewrites `(f + g)^*` to the lower-semicontinuous convex envelope of
the second-coordinate projected-image owner. -/
private theorem productGraphConjugateWitnessEnvelopePullback_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    ∃ (f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
      (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U)),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        (f∗[hf]) =
          (ι[horizontalOrthogonalSliceSet U] :
            (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)) ∧
        (g∗[hg]) =
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2) ∧
        ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal)) =
          fun p : L2Nat × orthogonalClosedSubmodule U =>
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) ∧
        (f + g).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : L2Nat × orthogonalClosedSubmodule U =>
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
  rcases productGraphConjugateWitnessOwners_l2 U V hV_closed with
    ⟨f, g, hf, hg, hdom, hfs, hgs, hraw_snd⟩
  refine ⟨f, g, hf, hg, hdom, hfs, hgs, hraw_snd, ?_⟩
  -- The explicit raw normalization lets us reuse the existing second-coordinate pullback formula.
  exact
    conjugatePointwiseAdd_eq_secondCoordinateEnvelopePullback_l2 U V f g hf hg hdom hraw_snd

/-- Helper for Remark 16.46: package the concrete product-space witness already constructed from
the horizontal slice and projected-image graph owners, together with the bad point `(0, u0)` where
the raw dual infimal convolution is `⊤` but the conjugate stays finite. -/
private theorem existsProductGraphCounterexamplePackage_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat))
      (u0 : orthogonalClosedSubmodule U)
      (f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
      (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U)),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        (f∗[hf]) =
          (ι[horizontalOrthogonalSliceSet U] :
            (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)) ∧
        (g∗[hg]) =
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2) ∧
        ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal) =
          fun p : L2Nat × orthogonalClosedSubmodule U =>
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) ∧
        (f + g).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : L2Nat × orthogonalClosedSubmodule U =>
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) ∧
        ((((f∗[hf]) □ (g∗[hg])) : (L2Nat × orthogonalClosedSubmodule U) → EReal) (0, u0)) = ⊤ ∧
        (f + g).asEReal∗ (0, u0) < ⊤ := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  rcases productGraphConjugateWitnessEnvelopePullback_l2 U V hV_closed with
    ⟨f, g, hf, hg, hdom, hfs, hgs, hraw_snd, hconj_pullback⟩
  let K := orthogonalClosedSubmodule U
  let E := L2Nat × K
  have hu0_raw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    -- Outside the projected image, the indicator branch forces the raw owner to be `⊤`.
    have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
    rw [projectedImageRawOwner]
    rw [show
        (ι[(projectedImageSubmodule U V : Set K)] u0 : EReal) = ⊤ by
      simp [indicator_apply, hu0_not_mem]]
    simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
  have hraw_bad :
      ((((f∗[hf]) □ (g∗[hg])) : E → EReal) (0, u0)) = ⊤ := by
    -- Evaluate the frozen raw normalization at the concrete bad point `(0, u0)`.
    rw [hraw_snd]
    simpa using hu0_raw_top
  have hpullback_env_finite :
      lowerSemicontinuousConvexEnvelope
          (fun p : E =>
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
          (0, u0) < ⊤ := by
    let A : Set K := projectedImageSubmodule U V
    let q : K → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
    have hcont_q : Continuous q := by
      have hnorm_sq : Continuous fun x : K ↦ ‖x‖ ^ 2 := by
        simpa using (continuous_norm.pow 2 : Continuous fun x : K ↦ ‖x‖ ^ 2)
      simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_const.mul hnorm_sq :
          Continuous fun x : K ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
    have hgraph_closure :
        (((0 : L2Nat), u0), q u0) ∈
          closure ((fun x : K ↦ (((0 : L2Nat), x), q x)) '' A) := by
      -- Push the closure witness for `u0` through the graph map `x ↦ ((0, x), ‖x‖² / 2)`.
      have hu0_image :
          (((0 : L2Nat), u0), q u0) ∈
            (fun x : K ↦ (((0 : L2Nat), x), q x)) '' closure A := by
        exact ⟨u0, hu0_closure, rfl⟩
      have hcont_graph : Continuous fun x : K ↦ (((0 : L2Nat), x), q x) := by
        exact (continuous_const.prod_mk continuous_id).prodMk hcont_q
      exact image_closure_subset_closure_image hcont_graph hu0_image
    have hgraph_subset :
        (fun x : K ↦ (((0 : L2Nat), x), q x)) '' A ⊆
          epigraph
            (fun p : E =>
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
      rintro _ ⟨x, hxA, rfl⟩
      rw [mem_epigraph_iff]
      -- On the projected image, the pullback owner is exactly the quadratic tail.
      rw [projectedImageRawOwner]
      change
        (ι[(A : Set K)] x : EReal) + (halfSquaredNorm x : EReal) ≤ ((q x : ℝ) : EReal)
      rw [show (ι[(A : Set K)] x : EReal) = 0 by simp [indicator_apply, hxA]]
      rw [halfSquaredNorm_apply]
      simpa [q]
    have hraw_epi :
        (((0 : L2Nat), u0), q u0) ∈
          closure
            (epigraph
              (fun p : E =>
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
      closure_mono hgraph_subset hgraph_closure
    have henv_epi :
        (((0 : L2Nat), u0), q u0) ∈
          epigraph
            (lowerSemicontinuousConvexEnvelope
              (fun p : E =>
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
      have hepi_eq :
          epigraph
              (lowerSemicontinuousConvexEnvelope
                (fun p : E =>
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) =
            closure
              (convexHull ℝ
                (epigraph
                  (fun p : E =>
                    ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
        exact
          epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
            (H := E)
            (fun p : E =>
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
      have hclosure_convexHull :
          (((0 : L2Nat), u0), q u0) ∈
            closure
              (convexHull ℝ
                (epigraph
                  (fun p : E =>
                    ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
        closure_mono
          (subset_convexHull ℝ
            (epigraph
              (fun p : E =>
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
          hraw_epi
      rw [hepi_eq]
      exact hclosure_convexHull
    have henv_le :
        lowerSemicontinuousConvexEnvelope
            (fun p : E =>
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
            (0, u0) ≤
          ((q u0 : ℝ) : EReal) := by
      exact (mem_epigraph_iff _ _ _).mp henv_epi
    -- The real graph height gives a finite upper bound on the product-space envelope value.
    exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
  have hconj_finite :
      (f + g).asEReal∗ (0, u0) < ⊤ := by
    -- Rewrite the conjugate once to the packaged envelope pullback.
    simpa [hconj_pullback] using hpullback_env_finite
  exact ⟨U, V, hV_closed, u0, f, g, hf, hg, hdom, hfs, hgs, hraw_snd, hconj_pullback, hraw_bad,
    hconj_finite⟩

-/

/-- Helper for Remark 16.46: the lower semicontinuous convex envelope of the raw projected-image
owner agrees with the concrete closure-side comparison owner. -/
private theorem projectedImageClosureOwner_eq_lowerSemicontinuousConvexEnvelope_l2
    (U V : Submodule ℝ L2Nat) :
    (projectedImageClosureOwner U V).asEReal =
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) := by
  -- Route correction: the active product-graph support theorem needs the concrete closure owner,
  -- so the remaining bridge is exactly the envelope identification for this owner.
  have hclosure_gamma :
      projectedImageClosureOwner U V ∈ Γ₀(orthogonalClosedSubmodule U) :=
    projectedImageClosureOwner_mem_gammaZero_l2 U V
  have hdom_rawConj :
      (dom (((projectedImageRawOwner U V).asEReal)∗)).Nonempty := by
    -- The closure owner is `Γ₀`, so its conjugate is finite somewhere; the raw owner shares that
    -- conjugate by the distance-to-closure normalization.
    rcases (gammaZeroConjugate_mem_gammaZero hclosure_gamma).2.nonempty with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simpa [effectiveDomain, dom, gammaZeroConjugate_apply,
      projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V] using hu
  have hbiconj_eq :
      (((projectedImageRawOwner U V).asEReal)∗∗) =
        (((projectedImageClosureOwner U V).asEReal)∗∗) := by
    -- Conjugating the already proved raw/closure dual equality once more identifies the
    -- corresponding biconjugates.
    exact congrArg conjugate (projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V)
  -- Rewrite the closure owner to its biconjugate and then use the generic Chapter 13 envelope
  -- formula for the raw owner.
  calc
    (projectedImageClosureOwner U V).asEReal =
        (((projectedImageClosureOwner U V).asEReal)∗∗) := by
          symm
          exact biconjugate_eq_of_mem_gammaZero hclosure_gamma
    _ = (((projectedImageRawOwner U V).asEReal)∗∗) := by
          exact hbiconj_eq.symm
    _ = lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) := by
          simpa using
            biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
              ((projectedImageRawOwner U V).asEReal) hdom_rawConj

/-- Helper for Remark 16.46: package the lower-semicontinuous convex envelope of the
projected-image raw owner as the concrete `Γ₀` closure owner on `Uᗮ`. -/
private theorem projectedImageEnvelopeGammaZero_l2
    (U V : Submodule ℝ L2Nat) :
    ∃ ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal),
      ψ ∈ Γ₀(orthogonalClosedSubmodule U) ∧
        ψ.asEReal =
          lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) := by
  -- Use the already constructed closure owner once its envelope identity is fixed.
  refine ⟨projectedImageClosureOwner U V, projectedImageClosureOwner_mem_gammaZero_l2 U V, ?_⟩
  exact projectedImageClosureOwner_eq_lowerSemicontinuousConvexEnvelope_l2 U V

/-- Helper for Remark 16.46: the subdifferential of a second-coordinate pullback is exactly the
zero-first-coordinate slice of the original subdifferential. -/
private theorem mem_subdifferential_secondCoordinatePullback_iff_zero_fst_l2
    (U : Submodule ℝ L2Nat)
    (ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
    (hψ : ψ ∈ Γ₀(orthogonalClosedSubmodule U))
    {x u : L2Nat × orthogonalClosedSubmodule U} :
    x ∈ (∂ (fun p : L2Nat × orthogonalClosedSubmodule U ↦ (ψ p.2 : EReal))) u ↔
      x.1 = 0 ∧ x.2 ∈ (∂ ψ) u.2 := by
  -- The generic pullback formula specializes directly to `L2Nat × Uᗮ`.
  rw [subdifferential_secondCoordinatePullback_eq_zero_prod_general
    (A := L2Nat) (K := orthogonalClosedSubmodule U) ψ hψ u.1 u.2]
  simp

/-- Helper for Remark 16.46: the conjugate of the packaged projected-image envelope `ψ`
coincides with the raw conjugate of `projectedImageRawOwner U V`. -/
private theorem projectedImageEnvelopeConjugate_eq_rawConjugate_l2
    (U V : Submodule ℝ L2Nat)
    (ψ : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
    (hψ : ψ ∈ Γ₀(orthogonalClosedSubmodule U))
    (hψ_eq :
      ψ.asEReal =
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal)) :
    (ψ∗[hψ]).asEReal = ((projectedImageRawOwner U V).asEReal)∗ := by
  have hψ_closure :
      ψ.asEReal = (projectedImageClosureOwner U V).asEReal := by
    rw [hψ_eq]
    symm
    exact projectedImageClosureOwner_eq_lowerSemicontinuousConvexEnvelope_l2 U V
  -- Rewrite the abstract envelope package to the concrete closure owner, then use the already
  -- proved raw/closure conjugate normalization.
  calc
    (ψ∗[hψ]).asEReal = ψ.asEReal∗ := by
      rfl
    _ = ((projectedImageClosureOwner U V).asEReal)∗ := by
          rw [hψ_closure]
    _ = ((projectedImageRawOwner U V).asEReal)∗ := by
          rw [projectedImageRawConjugate_eq_projectedImageClosureConjugate_l2 U V]

/-- Helper for Remark 16.46: infimal postcomposition of the ambient `V`-indicator along the
orthogonal projection is exactly the indicator of the projected image `P_{Uᗮ}(V)`. -/
private theorem projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2
    (U V : Submodule ℝ L2Nat) :
    (((orthogonalClosedSubmodule U).orthogonalProjection ▷
        (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) :
        orthogonalClosedSubmodule U → EReal) =
      (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] :
        orthogonalClosedSubmodule U → EReal) := by
  funext u
  by_cases hu : u ∈ projectedImageSubmodule U V
  · -- On the projected image, a concrete fiber point in `V` attains the infimum with value `0`.
    rcases Submodule.mem_map.mp hu with ⟨a, haV, hproj⟩
    have hupper :
        (((orthogonalClosedSubmodule U).orthogonalProjection ▷
              (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) ≤
          (0 : EReal) := by
      rw [infimalPostcomposition_apply]
      refine sInf_le ?_
      exact ⟨a, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hproj, by
        simp [indicator_apply, haV]⟩
    have hlower :
        (0 : EReal) ≤
          (((orthogonalClosedSubmodule U).orthogonalProjection ▷
                (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) := by
      rw [infimalPostcomposition_apply]
      refine le_sInf ?_
      rintro _ ⟨x, _, rfl⟩
      by_cases hxV : x ∈ (V : Set L2Nat)
      · simp [indicator_apply, hxV]
      · simp [indicator_apply, hxV]
    have hvalue :
        (((orthogonalClosedSubmodule U).orthogonalProjection ▷
              (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) =
          (0 : EReal) :=
      le_antisymm hupper hlower
    -- Both sides are the zero indicator value at a projected-image point.
    simp [indicator_apply, hu, hvalue]
  · -- Outside the projected image, every point in the fiber misses `V`, so the infimum is `⊤`.
    have htop :
        (((orthogonalClosedSubmodule U).orthogonalProjection ▷
              (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) =
          (⊤ : EReal) := by
      apply le_antisymm le_top
      have htop_le :
          (⊤ : EReal) ≤
            sInf
              ((fun x : L2Nat ↦
                  ((ι[(V : Set L2Nat)] x : Set.Ioi (⊥ : EReal)) : EReal)) ''
                ((orthogonalClosedSubmodule U).orthogonalProjection ⁻¹' ({u} : Set _))) := by
        refine le_sInf ?_
        rintro _ ⟨x, hxfiber, rfl⟩
        have hxproj :
            (orthogonalClosedSubmodule U).orthogonalProjection x = u := by
          simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxfiber
        have hx_not_mem : x ∉ (V : Set L2Nat) := by
          intro hxV
          exact hu (Submodule.mem_map.mpr ⟨x, hxV, hxproj⟩)
        simp [indicator_apply, hx_not_mem]
      simpa [infimalPostcomposition_apply] using htop_le
    -- The projected-image indicator is `⊤` outside `P_{Uᗮ}(V)`.
    simp [indicator_apply, hu, htop]

/-- Helper for Remark 16.46: the raw projected-image owner is the projection-fiber infimal
postcomposition of `ι[V]`, followed by the unchanged quadratic tail on `Uᗮ`. -/
private theorem projectedImageRawOwner_asEReal_apply_l2
    (U V : Submodule ℝ L2Nat)
    (u : orthogonalClosedSubmodule U) :
    ((projectedImageRawOwner U V u : Set.Ioi (⊥ : EReal)) : EReal) =
      (((orthogonalClosedSubmodule U).orthogonalProjection ▷
          (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) +
        (halfSquaredNorm u : EReal) := by
  -- Rewrite only the indicator branch; the quadratic term is already in the desired normal form.
  rw [projectedImageRawOwner]
  have hproj :
      (((orthogonalClosedSubmodule U).orthogonalProjection ▷
            (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) =
        (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) := by
    simpa using
      congrFun (projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2 U V) u
  rw [hproj]
  rfl

/-- Helper for Remark 16.46: the whole-function `EReal` coercion of the raw projected-image owner
is the projection-fiber infimal postcomposition plus the quadratic tail. -/
private theorem projectedImageRawOwner_eq_projectionIndicatorInfimalPostcomposition_l2
    (U V : Submodule ℝ L2Nat) :
    (projectedImageRawOwner U V).asEReal =
      (fun u : orthogonalClosedSubmodule U ↦
        (((orthogonalClosedSubmodule U).orthogonalProjection ▷
            (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) +
          (halfSquaredNorm u : EReal)) := by
  funext u
  -- Repackage the pointwise normal form as the function-level rewrite still used nearby.
  exact projectedImageRawOwner_asEReal_apply_l2 U V u

/-- Helper for Remark 16.46: the effective domain of the raw projected-image owner is exactly the
projected image `P_{Uᗮ}(V)`. -/
private theorem mem_effectiveDomain_projectedImageRawOwner_iff_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U} :
    u ∈ effectiveDomain (projectedImageRawOwner U V) ↔
      u ∈ projectedImageSubmodule U V := by
  by_cases hu : u ∈ projectedImageSubmodule U V
  · constructor
    · intro _
      exact hu
    · intro _
      -- On the projected image, the indicator contributes `0`, so only the finite quadratic tail
      -- remains.
      rw [mem_effectiveDomain_iff]
      rw [projectedImageRawOwner_asEReal_apply_l2 U V u]
      rw [projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2 U V]
      simp [indicator_apply, hu, halfSquaredNorm_apply]
  · constructor
    · intro hu_dom
      -- Outside the projected image, the indicator branch becomes `⊤`, so the whole owner leaves
      -- its effective domain.
      rw [mem_effectiveDomain_iff] at hu_dom
      rw [projectedImageRawOwner_asEReal_apply_l2 U V u] at hu_dom
      rw [projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2 U V] at hu_dom
      have hhalf_ne_bot : (halfSquaredNorm u : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u).2
      rw [show
          (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u : EReal) = ⊤ by
        simp [indicator_apply, hu]] at hu_dom
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot] at hu_dom
      exact (lt_irrefl (⊤ : EReal) hu_dom).elim
    · intro hu'
      exact (hu hu').elim

/-- Helper for Remark 16.46: raw membership in `projectedImageSubmodule U V` gives an exact
projection-fiber witness for the ambient `V`-indicator. -/
private theorem projectionIndicator_exactAt_of_mem_projectedImage_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hu : u ∈ projectedImageSubmodule U V) :
    infimalPostcomposition.ExactAt
      (orthogonalClosedSubmodule U).orthogonalProjection
      (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
      u := by
  rcases Submodule.mem_map.mp hu with ⟨a, haV, hproj⟩
  have hvalue :
      (((orthogonalClosedSubmodule U).orthogonalProjection ▷
            (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) =
        (0 : EReal) := by
    -- Rewrite to the projected-image indicator and evaluate it at the active point `u`.
    rw [projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2 U V]
    simp [indicator_apply, hu]
  have hu_dom :
      u ∈
        dom
          (((orthogonalClosedSubmodule U).orthogonalProjection ▷
              (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) :
              orthogonalClosedSubmodule U → EReal) := by
    -- The attained value is `0`, hence finite.
    rw [mem_dom_iff, hvalue]
    exact EReal.coe_lt_top 0
  refine
    (infimalPostcomposition.exactAt_iff_exists_eq
      (orthogonalClosedSubmodule U).orthogonalProjection
      (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))
      u).2 ?_
  refine ⟨hu_dom, a, hproj, ?_⟩
  -- The chosen fiber point lies in `V`, so the ambient indicator contributes exactly `0`.
  simpa [indicator_apply, haV] using hvalue

/-- Helper for Remark 16.46: the first product witness is the conjugate of the horizontal-slice
indicator, so its subdifferential is exactly the vertical-slice normal cone
`u ∈ (∂ f) x ↔ x.1 = 0 ∧ u.2 = 0`. -/
private theorem mem_subdifferential_productGraphWitnessF_iff_l2
    (U : Submodule ℝ L2Nat)
    {f : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hfs :
      (f∗[hf]) =
        (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)))
    {x u : L2Nat × orthogonalClosedSubmodule U} :
    u ∈ (∂ f) x ↔ x.1 = 0 ∧ u.2 = 0 := by
  -- Transport the subgradient relation across conjugation and read the slice normal cone in
  -- coordinates.
  rw [← mem_subdifferential_gammaZeroConjugate_iff hf]
  rw [hfs]
  constructor
  · intro hx
    rcases (mem_subdifferential_horizontalOrthogonalSliceIndicator_iff U).1 hx with
      ⟨hu2, hx1⟩
    exact ⟨hx1, hu2⟩
  · rintro ⟨hx1, hu2⟩
    exact (mem_subdifferential_horizontalOrthogonalSliceIndicator_iff U).2 ⟨hu2, hx1⟩

/-- Helper for Remark 16.46: once a concrete ambient witness `a ∈ V` with
`P_{Uᗮ} a = -u.2` is available, the explicit graph-side owner already contributes the summand
`(-a, u.2) ∈ (∂ g) x`. -/
private theorem mem_subdifferential_productGraphWitnessG_of_projectedImageWitness
    (U V : Submodule ℝ L2Nat)
    {g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hgs :
      (g∗[hg]) =
        (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
    {x u : L2Nat × orthogonalClosedSubmodule U} {a : L2Nat}
    (hx1 : x.1 = 0)
    (haV : a ∈ V)
    (hproj : (orthogonalClosedSubmodule U).orthogonalProjection a = -u.2)
    (horth :
      x.2 - u.2 ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U))) :
    (-a, u.2) ∈ (∂ g) x := by
  -- Transport `∂ g` across conjugation so the explicit graph-side owner `g*` can be used.
  rw [← mem_subdifferential_gammaZeroConjugate_iff hg]
  rw [hgs]
  -- The graph-side owner already gives the desired subgradient once the projected-image witness is
  -- fixed.
  simpa [hx1] using
    (mem_subdifferential_projectedImageGraphOwner_of_mem_projectedImage_and_orthogonal
      U V haV hproj horth :
      (0, x.2) ∈
        (∂ (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
          (-a, u.2))

/-- Helper for Remark 16.46: any chosen point on a projection fiber gives the canonical upper
bound on the corresponding projection infimum. This is the fiberwise half of the local exactness
bridge needed for the shifted-dual witness extraction. -/
private theorem projectionFiberInfimalPostcomposition_le_of_map_eq_l2
    (U : Submodule ℝ L2Nat)
    (φ : L2Nat → Set.Ioi (⊥ : EReal))
    {a : L2Nat} {y : orthogonalClosedSubmodule U}
    (hay : (orthogonalClosedSubmodule U).orthogonalProjection a = y) :
    (((orthogonalClosedSubmodule U).orthogonalProjection ▷ φ) y) ≤ (φ a : EReal) := by
  -- Unfold the fiber infimum and use the chosen point `a` as an admissible witness.
  change
    sInf
        ((fun z ↦ (φ z : EReal)) ''
          ((fun z ↦ (orthogonalClosedSubmodule U).orthogonalProjection z) ⁻¹' {y})) ≤
      (φ a : EReal)
  refine sInf_le ?_
  exact ⟨a, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hay, rfl⟩

/-- Helper for Remark 16.46: if the adjoint of a dual point is a source-side subgradient at a
fiber point `a`, then that same `a` attains the projection infimum at `y = P_{Uᗮ} a`. This is
the local Proposition 16.60-style value identity used by the current product-space pivot. -/
private theorem projectionFiberValue_eq_of_adjoint_mem_subdifferential_l2
    (U : Submodule ℝ L2Nat)
    (φ : L2Nat → Set.Ioi (⊥ : EReal))
    {a : L2Nat} {y v : orthogonalClosedSubmodule U}
    (hay : (orthogonalClosedSubmodule U).orthogonalProjection a = y)
    (hv :
      (orthogonalClosedSubmodule U).orthogonalProjection.adjoint v ∈ (∂ φ) a) :
    (((orthogonalClosedSubmodule U).orthogonalProjection ▷ φ) y) = (φ a : EReal) := by
  let P : L2Nat →L[ℝ] orthogonalClosedSubmodule U := (orthogonalClosedSubmodule U).orthogonalProjection
  have hupper :
      (P ▷ φ) y ≤ (φ a : EReal) :=
    projectionFiberInfimalPostcomposition_le_of_map_eq_l2 U φ hay
  have hlower :
      ((⟪y - P a, v⟫_ℝ : ℝ) : EReal) + (φ a : EReal) ≤ (P ▷ φ) y := by
    rw [infimalPostcomposition_apply]
    -- The source-side subgradient inequality controls every point in the target fiber.
    refine le_sInf ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzy : P z = y := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
    have hvz :
        (⟪z - a, P.adjoint v⟫_ℝ : EReal) + (φ a : EReal) ≤ (φ z : EReal) :=
      (mem_subdifferential_iff (f := φ) (x := a) (u := P.adjoint v)).1 hv z
    have hinner : ⟪z - a, P.adjoint v⟫_ℝ = ⟪y - P a, v⟫_ℝ := by
      calc
        ⟪z - a, P.adjoint v⟫_ℝ = ⟪P (z - a), v⟫_ℝ := by
          simpa using (ContinuousLinearMap.adjoint_inner_right P (z - a) v)
        _ = ⟪P z - P a, v⟫_ℝ := by
          simp [P, ContinuousLinearMap.map_sub]
        _ = ⟪y - P a, v⟫_ℝ := by
          rw [hzy]
    simpa [hinner] using hvz
  have hlower' : (φ a : EReal) ≤ (P ▷ φ) y := by
    simpa [P, hay] using hlower
  exact le_antisymm hupper hlower'

/-- Helper for Remark 16.46: once an adjoint-side subgradient at a fiber point is available, the
projection infimum is exact there. This isolates the remaining local bridge needed to convert the
shifted dual minimizer into an actual ambient witness. -/
private theorem projectionFiberExactAt_of_mem_effectiveDomain_of_adjoint_mem_subdifferential_l2
    (U : Submodule ℝ L2Nat)
    (φ : L2Nat → Set.Ioi (⊥ : EReal))
    {a : L2Nat} {y v : orthogonalClosedSubmodule U}
    (ha : a ∈ effectiveDomain φ)
    (hay : (orthogonalClosedSubmodule U).orthogonalProjection a = y)
    (hv :
      (orthogonalClosedSubmodule U).orthogonalProjection.adjoint v ∈ (∂ φ) a) :
    infimalPostcomposition.ExactAt
      (orthogonalClosedSubmodule U).orthogonalProjection
      φ
      y := by
  -- Package the chosen fiber point together with the value identity from the previous lemma.
  refine ⟨a, ha, hay, ?_⟩
  exact projectionFiberValue_eq_of_adjoint_mem_subdifferential_l2 U φ hay hv

/-- Helper for Remark 16.46: an active ambient product-space subgradient only yields the closure
support data justified by the envelope pullback, namely vanishing first coordinate together with
closure membership and the orthogonality residual on the second coordinate. -/
private theorem productGraphWitnessClosureSupport_of_mem_subdifferential_l2
    (U V : Submodule ℝ L2Nat)
    (hV_closed : IsClosed (V : Set L2Nat))
    {f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hconj_pullback :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
    {x u : L2Nat × orthogonalClosedSubmodule U}
    (hu : u ∈ (∂ (f + g)) x) :
    x.1 = 0 ∧
      u.2 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) ∧
      x.2 - u.2 ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U)) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let K := orthogonalClosedSubmodule U
  have hfg : f + g ∈ Γ₀(E) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  rcases projectedImageEnvelopeGammaZero_l2 U V with ⟨ψ, hψ, hψ_eq⟩
  have hx_conj :
      x ∈ (∂ ((f + g)∗[hfg])) u := by
    -- Corollary 16.30 moves the active primal subgradient to the conjugate surface.
    exact (mem_subdifferential_gammaZeroConjugate_iff hfg).2 hu
  have hpullback :
      (fun p : E ↦ (ψ p.2 : EReal)) = (f + g).asEReal∗ := by
    -- Rewrite the envelope pullback to the packaged `Γ₀` owner on the second coordinate.
    funext p
    rw [hconj_pullback, ← hψ_eq]
  have hx_pullback :
      x ∈ (∂ (fun p : E ↦ (ψ p.2 : EReal))) u := by
    -- The product-space conjugate is exactly the second-coordinate pullback of `ψ`.
    simpa [gammaZeroConjugate_apply, hpullback] using hx_conj
  rcases
      (mem_subdifferential_secondCoordinatePullback_iff_zero_fst_l2 U ψ hψ).1 hx_pullback with
    ⟨hx1, hx2⟩
  have hu_rawConj :
      u.2 ∈ (∂ (((projectedImageRawOwner U V).asEReal)∗)) x.2 := by
    have hu_envConj :
        u.2 ∈ (∂ (ψ∗[hψ])) x.2 := by
      -- Move back through Corollary 16.30 on `ψ`.
      exact
        (mem_subdifferential_gammaZeroConjugate_iff hψ).2
          hx2
    -- The packaged envelope and the raw owner have the same conjugate.
    simpa [gammaZeroConjugate_apply,
      projectedImageEnvelopeConjugate_eq_rawConjugate_l2 U V ψ hψ hψ_eq] using hu_envConj
  rcases
      projectedImageClosureSupportData_of_mem_subdifferentialRawConjugate_l2 U V hu_rawConj with
    ⟨hu2_closure, horth⟩
  exact ⟨hx1, hu2_closure, horth⟩

/-- Helper for Remark 16.46: the old ambient witness-extraction split has been retired. The live
proof no longer depends on this product-space reverse-inclusion wrapper after the same-space
orthogonal-graph pivot. -/
private theorem productGraphWitnessSplitOfActiveSubgradient_l2
    (U V : Submodule ℝ L2Nat)
    (hV_closed : IsClosed (V : Set L2Nat))
    {f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hfs :
      (f∗[hf]) =
        (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)))
    (hgs :
      (g∗[hg]) =
        (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
    (hconj_pullback :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
    {x u : L2Nat × orthogonalClosedSubmodule U}
    (hu : u ∈ (∂ (f + g)) x) :
    True := by
  let _ := U
  let _ := V
  let _ := hV_closed
  let _ := hf
  let _ := hg
  let _ := hdom
  let _ := hfs
  let _ := hgs
  let _ := hconj_pullback
  let _ := hu
  -- Route correction: the requested ambient witness extraction was false; the active proof now
  -- closes the sum rule through the same-space orthogonal-graph package instead.
  trivial

/-- Helper for Remark 16.46: the ambient product-graph sum-rule wrapper is retired together with
the false witness-extraction route. -/
private theorem productGraphWitnessSubdifferentialAddEq_l2
    (U V : Submodule ℝ L2Nat)
    (hV_closed : IsClosed (V : Set L2Nat))
    {f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hfs :
      (f∗[hf]) =
        (ι[horizontalOrthogonalSliceSet U] :
          (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)))
    (hgs :
      (g∗[hg]) =
        (fun p : L2Nat × orthogonalClosedSubmodule U ↦
          (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2))
    (hconj_pullback :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :
    True := by
  let _ := U
  let _ := V
  let _ := hV_closed
  let _ := hf
  let _ := hg
  let _ := hdom
  let _ := hfs
  let _ := hgs
  let _ := hconj_pullback
  -- Route correction: this ambient equality is no longer the target interface after the pivot to
  -- the same-space `Uᗮ` witness package.
  trivial

/-- Helper for Remark 16.46: a nonempty fixed first-coordinate slice of a `Γ₀(A × K)` owner is
again a `Γ₀(K)` owner. -/
private theorem secondVariableSlice_mem_gammaZero_of_nonempty_effectiveDomain_local
    {A K : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (F : A × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(A × K)) (a : A)
    (ha : (effectiveDomain (fun y : K ↦ F (a, y))).Nonempty) :
    (fun y : K ↦ F (a, y)) ∈ Γ₀(K) := by
  -- Restrict lower semicontinuity and convexity of `F` to the vertical slice `y ↦ (a, y)`.
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · simpa [Function.comp] using hF.1.comp (Continuous.prodMk_right a)
  · refine ⟨ha, ?_, ?_⟩
    · intro y hy
      simpa [mem_effectiveDomain_iff] using hy
    · intro y₁ hy₁ y₂ hy₂ α hα0 hα1
      simpa [Prod.smul_mk, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using
        hF.2.ineq
          (x := (a, y₁))
          (hx := by simpa [mem_effectiveDomain_iff] using hy₁)
          (y := (a, y₂))
          (hy := by simpa [mem_effectiveDomain_iff] using hy₂)
          (α := α) hα0 hα1

/-- Helper for Remark 16.46: the first owner obtained by restricting the horizontal-slice product
witness to the vertical zero slice is identically zero. -/
private theorem productGraphVerticalZeroSliceFirstOwner_eq_zero_l2
    (U : Submodule ℝ L2Nat) :
    ∀ u : orthogonalClosedSubmodule U,
      (((((ι[horizontalOrthogonalSliceSet U] :
            (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal))∗
            [horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U]) (0, u)) :
          Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
  intro u
  let K := orthogonalClosedSubmodule U
  let M : L2Nat →L[ℝ] K := 0
  let W : Submodule ℝ (L2Nat × K) := M.toLinearMap.graph
  have hW_gamma :
      (ι[(W : Set (L2Nat × K))] : (L2Nat × K) → Set.Ioi (⊥ : EReal)) ∈ Γ₀(L2Nat × K) := by
    -- Rewrite the horizontal slice as the graph of the zero map before invoking the `Γ₀` API.
    simpa [W, M, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff] using
      horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U
  change
    ((((ι[(W : Set (L2Nat × K))] : (L2Nat × K) → Set.Ioi (⊥ : EReal))∗[hW_gamma])
        ((0 : L2Nat), u) : Set.Ioi (⊥ : EReal)) : EReal) = 0
  rw [gammaZeroConjugate_apply, conjugate_indicator_submodule_eq_indicator_orthogonal (V := W)]
  have hmem : (((0 : L2Nat), u) : L2Nat × K) ∈ Wᗮ := by
    -- A vertical vector is orthogonal to the horizontal graph because the first coordinate is `0`.
    exact (mem_orthogonal_graph_iff (M := M) (w := ((0 : L2Nat), u))).2 (by simp [M])
  -- The conjugate indicator vanishes on points of the orthogonal graph.
  simp [indicator_apply, hmem]

/-- Helper for Remark 16.46: the stable product-space witness already descends to a genuine
`Γ₀(Uᗮ)` pair on the vertical zero slice, with intersecting effective domains at the origin. -/
private theorem productGraphVerticalZeroSliceWitnessPair_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    ∃ (fK gK : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
      (hfK : fK ∈ Γ₀(orthogonalClosedSubmodule U))
      (hgK : gK ∈ Γ₀(orthogonalClosedSubmodule U)),
      (effectiveDomain fK ∩ effectiveDomain gK).Nonempty := by
  let E := L2Nat × orthogonalClosedSubmodule U
  rcases productGraphConjugateWitnessOwners_l2 U V hV_closed with
    ⟨f, g, hf, hg, _hdom, hfs, hgs, _hraw⟩
  let fK : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal) := fun u ↦ f (0, u)
  let gK : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal) := fun u ↦ g (0, u)
  have hfStar : (f∗[hf]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hf
  have hgStar : (g∗[hg]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hg
  have hfStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((f∗[hf]) p : EReal) := by
    intro p
    -- The horizontal-slice indicator is either `0` or `⊤`, hence always nonnegative.
    rw [hfs]
    by_cases hp : p ∈ horizontalOrthogonalSliceSet U
    · simp [indicator_apply, hp]
    · simp [indicator_apply, hp]
  have hfStar_zero : ((f∗[hf]) 0 : EReal) = 0 := by
    -- The origin lies on the horizontal slice.
    rw [hfs]
    simp [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have hgStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((g∗[hg]) p : EReal) := by
    intro p
    -- The graph-plus-quadratic owner is nonnegative on the graph and `⊤` off the graph.
    rw [hgs]
    by_cases hp : p ∈ projectedImageGraphSet U V
    · rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = 0 by
        simp [indicator_apply, hp]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm p.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm p.2).2
      rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ by
        simp [indicator_apply, hp]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp
  have hgStar_zero : ((g∗[hg]) 0 : EReal) = 0 := by
    -- The origin lies on the projected-image graph and has zero quadratic height.
    rw [hgs]
    simp [projectedImageGraphSet, halfSquaredNorm_apply]
  have hf_zero : (0 : E) ∈ effectiveDomain f := by
    -- Finite conjugate value at the origin of `f*` gives a finite primal value at the origin of
    -- `f`.
    have hzero :
        (0 : E) ∈ effectiveDomain ((f∗[hf])∗[hfStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hfStar) hfStar_nonneg hfStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hg_zero : (0 : E) ∈ effectiveDomain g := by
    -- The same origin test works for `g` because `g*` is the graph-plus-quadratic owner.
    have hzero :
        (0 : E) ∈ effectiveDomain ((g∗[hg])∗[hgStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hgStar) hgStar_nonneg hgStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hfK_zero : (0 : orthogonalClosedSubmodule U) ∈ effectiveDomain fK := by
    -- Restrict the product witness finiteness at `(0, 0)` to the vertical zero slice.
    simpa [fK, mem_effectiveDomain_iff] using hf_zero
  have hgK_zero : (0 : orthogonalClosedSubmodule U) ∈ effectiveDomain gK := by
    -- The graph-side witness is likewise finite at the vertical origin.
    simpa [gK, mem_effectiveDomain_iff] using hg_zero
  have hfK : fK ∈ Γ₀(orthogonalClosedSubmodule U) := by
    -- Restrict the first product witness to the vertical zero slice.
    exact
      secondVariableSlice_mem_gammaZero_of_nonempty_effectiveDomain_local
        f hf 0 ⟨0, hfK_zero⟩
  have hgK : gK ∈ Γ₀(orthogonalClosedSubmodule U) := by
    -- Restrict the second product witness to the same zero slice.
    exact
      secondVariableSlice_mem_gammaZero_of_nonempty_effectiveDomain_local
        g hg 0 ⟨0, hgK_zero⟩
  exact ⟨fK, gK, hfK, hgK, ⟨0, hfK_zero, hgK_zero⟩⟩

/-- Helper for Remark 16.46: the orthogonal complement of `graph(P_{Uᗮ})` is the canonical
closed carrier for the surviving product-graph witness route. -/
private theorem orthogonalGraph_isClosed_l2
    (U : Submodule ℝ L2Nat) :
    IsClosed
      ((((orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap.graph)ᗮ :
        Submodule ℝ (L2Nat × orthogonalClosedSubmodule U)) :
        Set (L2Nat × orthogonalClosedSubmodule U)) := by
  -- Closedness is the standard orthogonal-complement fact for submodules of a Hilbert space.
  exact ((orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap.graph).isClosed_orthogonal

/-- Helper for Remark 16.46: the orthogonal complement of `graph(P_{Uᗮ})` is the canonical
closed carrier for the surviving product-graph witness route. -/
private abbrev orthogonalGraphCarrier_l2
    (U : Submodule ℝ L2Nat) :
    ClosedSubmodule ℝ (L2Nat × orthogonalClosedSubmodule U) :=
  ⟨(((orthogonalClosedSubmodule U).orthogonalProjection.toLinearMap.graph)ᗮ),
    orthogonalGraph_isClosed_l2 U⟩

/-- Helper for Remark 16.46: the canonical orthogonal-graph point attached to `u` is
`(P_{Uᗮ}† u, -u)`. -/
private theorem pair_projectionAdjoint_neg_mem_orthogonalGraph_l2
    (U : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    ((((orthogonalClosedSubmodule U).orthogonalProjection.adjoint u), -u) :
      L2Nat × orthogonalClosedSubmodule U) ∈
      ((orthogonalGraphCarrier_l2 U : Submodule ℝ
        (L2Nat × orthogonalClosedSubmodule U)) : Set
        (L2Nat × orthogonalClosedSubmodule U)) := by
  -- Specialize the Chapter 15 orthogonal-graph membership lemma to `P_{Uᗮ}`.
  simpa [orthogonalGraphCarrier_l2] using
    pair_adjoint_neg_mem_orthogonal_graph
      (M := (orthogonalClosedSubmodule U).orthogonalProjection) u

/-- Helper for Remark 16.46: every point of the orthogonal graph has the canonical form
`(P_{Uᗮ}† u, -u)`. -/
private theorem orthogonalGraphPoint_eq_pair_projectionAdjoint_neg_l2
    (U : Submodule ℝ L2Nat)
    {z : L2Nat × orthogonalClosedSubmodule U}
    (hz :
      z ∈ ((orthogonalGraphCarrier_l2 U : Submodule ℝ
        (L2Nat × orthogonalClosedSubmodule U)) : Set
        (L2Nat × orthogonalClosedSubmodule U))) :
    ∃ u : orthogonalClosedSubmodule U,
      z = (((orthogonalClosedSubmodule U).orthogonalProjection.adjoint u), -u) := by
  -- Reuse the Chapter 15 parameterization of vectors orthogonal to `graph(M)`.
  simpa [orthogonalGraphCarrier_l2] using
    orthogonal_graph_point_eq_pair_adjoint_neg
      (M := (orthogonalClosedSubmodule U).orthogonalProjection) hz

/-- Helper for Remark 16.46: the orthogonal graph is linearly parameterized by the `Uᗮ`
coordinate `u`, with inverse `u ↦ (P_{Uᗮ}† (-u), u)`. -/
private noncomputable abbrev orthogonalGraphCarrierEquivOrthogonalComplement_l2
    (U : Submodule ℝ L2Nat) :
    orthogonalGraphCarrier_l2 U ≃ₗ[ℝ] orthogonalClosedSubmodule U :=
  { toFun := fun z ↦ z.1.2
    invFun := fun u ↦
      ⟨(((orthogonalClosedSubmodule U).orthogonalProjection.adjoint (-u)), u),
        pair_projectionAdjoint_neg_mem_orthogonalGraph_l2 U (-u)⟩
    left_inv := by
      intro z
      -- Rewrite an arbitrary orthogonal-graph point through the canonical `u`-parameterization.
      rcases orthogonalGraphPoint_eq_pair_projectionAdjoint_neg_l2 U z.2 with ⟨u, rfl⟩
      rfl
    right_inv := by
      intro u
      -- The second coordinate of the canonical orthogonal-graph point is exactly `u`.
      rfl
    map_add' := by
      intro z w
      rfl
    map_smul' := by
      intro a z
      rfl }

/-- Helper for Remark 16.46: the orthogonal-graph parameterization acts on points by taking the
second coordinate. -/
@[simp] private theorem orthogonalGraphCarrierEquivOrthogonalComplement_l2_apply
    (U : Submodule ℝ L2Nat) (z : orthogonalGraphCarrier_l2 U) :
    orthogonalGraphCarrierEquivOrthogonalComplement_l2 U z = z.1.2 :=
  rfl

/-- Helper for Remark 16.46: the inverse parameterization sends `u` to the canonical orthogonal
graph point `((P_{Uᗮ}† (-u)), u)`. -/
@[simp] private theorem orthogonalGraphCarrierEquivOrthogonalComplement_l2_symm_apply
    (U : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    (orthogonalGraphCarrierEquivOrthogonalComplement_l2 U).symm u =
      ⟨(((orthogonalClosedSubmodule U).orthogonalProjection.adjoint (-u)), u),
        pair_projectionAdjoint_neg_mem_orthogonalGraph_l2 U (-u)⟩ :=
  rfl

/-- Helper for Remark 16.46: the direct orthogonal-graph parameterization
`u ↦ (P_{Uᗮ}† (-u), u)` as a continuous linear map into `L2Nat × Uᗮ`. -/
private abbrev orthogonalGraphEmbedding_l2
    (U : Submodule ℝ L2Nat) :
    orthogonalClosedSubmodule U →L[ℝ] (L2Nat × orthogonalClosedSubmodule U) :=
  ((((orthogonalClosedSubmodule U).orthogonalProjection.adjoint).comp
      ((-1 : ℝ) • ContinuousLinearMap.id ℝ (orthogonalClosedSubmodule U))).prod
    (ContinuousLinearMap.id ℝ (orthogonalClosedSubmodule U)))

/-- Helper for Remark 16.46: evaluating the orthogonal-graph embedding gives the canonical point
`(P_{Uᗮ}† (-u), u)`. -/
@[simp] private theorem orthogonalGraphEmbedding_l2_apply
    (U : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    orthogonalGraphEmbedding_l2 U u =
      (((orthogonalClosedSubmodule U).orthogonalProjection.adjoint (-u)), u) :=
  rfl

/-- Helper for Remark 16.46: the adjoint of the orthogonal-graph embedding sends the horizontal
slice point `(-u, 0)` back to `u`. This is the explicit fiber witness behind the route check
below. -/
@[simp] private theorem orthogonalGraphEmbedding_l2_adjoint_horizontal_apply
    (U : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    (orthogonalGraphEmbedding_l2 U).adjoint ((-(u : L2Nat)), 0) = u := by
  ext v
  -- Expand the adjoint pairing once and use that `P_{Uᗮ}` fixes orthogonal vectors.
  simp [orthogonalGraphEmbedding_l2, ContinuousLinearMap.adjoint_inner_right]

/-- Helper for Remark 16.46: the adjoint of the orthogonal-graph embedding is the explicit affine
combination `-(P_{Uᗮ} x) + u` on ambient points `(x,u)`. -/
@[simp] private theorem orthogonalGraphEmbedding_l2_adjoint_apply
    (U : Submodule ℝ L2Nat) (p : L2Nat × orthogonalClosedSubmodule U) :
    (orthogonalGraphEmbedding_l2 U).adjoint p =
      -(orthogonalClosedSubmodule U).orthogonalProjection p.1 + p.2 := by
  -- Evaluate the adjoint against an arbitrary test vector and expand the defining inner products.
  ext u
  simp [orthogonalGraphEmbedding_l2, ContinuousLinearMap.adjoint_inner_right]

/-- Helper for Remark 16.46: composing the orthogonal-graph embedding with its adjoint scales the
identity on `Uᗮ` by `2`. This is the scalar transport used by the later same-space chain-rule
step. -/
@[simp] private theorem orthogonalGraphEmbedding_l2_adjoint_apply_embedding
    (U : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    (orthogonalGraphEmbedding_l2 U).adjoint (orthogonalGraphEmbedding_l2 U u) = (2 : ℝ) • u := by
  -- Rewrite the adjoint on the canonical orthogonal-graph point and simplify the projection term.
  simp [orthogonalGraphEmbedding_l2_adjoint_apply, orthogonalGraphEmbedding_l2, two_smul]

/-- Helper for Remark 16.46: along the direct orthogonal-graph embedding, the horizontal-slice
indicator collapses to the constant-zero infimal postcomposition owner. This rules out the naive
pullback route for the first dual summand. -/
private theorem orthogonalGraphEmbedding_horizontalSliceInfimalPostcomposition_eq_zero_l2
    (U : Submodule ℝ L2Nat) :
    let K := orthogonalClosedSubmodule U
    let E := L2Nat × K
    (((orthogonalGraphEmbedding_l2 U).adjoint ▷
        (ι[horizontalOrthogonalSliceSet U] : E → Set.Ioi (⊥ : EReal))) :
        K → EReal) =
      fun _ ↦ (0 : EReal) := by
  funext u
  apply le_antisymm
  · -- The horizontal slice already contains an explicit fiber point over every `u`.
    rw [infimalPostcomposition_apply]
    refine sInf_le ?_
    refine ⟨((-(u : L2Nat)), 0), ?_, ?_⟩
    · simpa using orthogonalGraphEmbedding_l2_adjoint_horizontal_apply U u
    · simp [horizontalOrthogonalSliceSet, linearGraphSet, indicator_apply]
  · -- The indicator only takes the values `0` and `⊤`, so the fiber infimum cannot be negative.
    rw [infimalPostcomposition_apply]
    refine le_sInf ?_
    rintro _ ⟨x, _, rfl⟩
    by_cases hx : x ∈ horizontalOrthogonalSliceSet U
    · simp [indicator_apply, hx]
    · simp [indicator_apply, hx]

/-- Helper for Remark 16.46: on the canonical orthogonal-graph point
`(P_{Uᗮ}† (-u), u)`, the raw horizontal-slice infimal convolution is exactly
`projectedImageRawOwner U V u`. -/
private theorem horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_on_orthogonalPoint_l2
    (U V : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let p : E := (((orthogonalClosedSubmodule U).orthogonalProjection.adjoint (-u)), u)
    ((((ι[horizontalOrthogonalSliceSet U] : E → Set.Ioi (⊥ : EReal)) □
        (fun q : E ↦
          (ι[projectedImageGraphSet U V] q : Set.Ioi (⊥ : EReal)) + halfSquaredNorm q.2)) :
        E → EReal) p) =
      (projectedImageRawOwner U V u : EReal) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let p : E := (((orthogonalClosedSubmodule U).orthogonalProjection.adjoint (-u)), u)
  -- The established product-graph raw normalization depends only on the second coordinate.
  simpa [E, p] using
    horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V p

/-- Helper for Remark 16.46: the raw horizontal-slice infimal convolution, evaluated at the
inverse image of `u` under the orthogonal-graph parameterization, is exactly
`projectedImageRawOwner U V u`. -/
private theorem
    horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_on_carrierInverse_l2
    (U V : Submodule ℝ L2Nat) (u : orthogonalClosedSubmodule U) :
    let E := L2Nat × orthogonalClosedSubmodule U
    ((((ι[horizontalOrthogonalSliceSet U] : E → Set.Ioi (⊥ : EReal)) □
        (fun q : E ↦
          (ι[projectedImageGraphSet U V] q : Set.Ioi (⊥ : EReal)) + halfSquaredNorm q.2)) :
        E → EReal)
      (((orthogonalGraphCarrierEquivOrthogonalComplement_l2 U).symm u :
          orthogonalGraphCarrier_l2 U) :
        E)) =
      (projectedImageRawOwner U V u : EReal) := by
  -- Rewrite the carrier inverse to the canonical orthogonal-graph point already normalized above.
  simpa [orthogonalGraphCarrierEquivOrthogonalComplement_l2, orthogonalGraphCarrier_l2] using
    horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_on_orthogonalPoint_l2 U V u

/-- Helper for Remark 16.46: if `u` lies in the projected image, then the carrier inverse of `u`
already carries an exact horizontal-slice / graph-plus-quadratic split. -/
private theorem orthogonalGraphCarrierInverseExactAt_l2
    (U V : Submodule ℝ L2Nat)
    {u : orthogonalClosedSubmodule U}
    (hu_image : u ∈ projectedImageSubmodule U V) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let p : E :=
      (((orthogonalGraphCarrierEquivOrthogonalComplement_l2 U).symm u :
          orthogonalGraphCarrier_l2 U) :
        E)
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun q : E ↦
      (ι[projectedImageGraphSet U V] q : Set.Ioi (⊥ : EReal)) +
        (halfSquaredNorm q.2 : Set.Ioi (⊥ : EReal))
    infimalConvolution.ExactAt s t p ∧ (((s □ t) : E → EReal) p) < ⊤ := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let p : E :=
    (((orthogonalGraphCarrierEquivOrthogonalComplement_l2 U).symm u :
        orthogonalGraphCarrier_l2 U) :
      E)
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun q : E ↦
    (ι[projectedImageGraphSet U V] q : Set.Ioi (⊥ : EReal)) +
      (halfSquaredNorm q.2 : Set.Ioi (⊥ : EReal))
  rcases projectedImageWitness_of_mem_projectedImage_l2 U V hu_image with ⟨a, haV, hproj⟩
  have hraw_projected :
      (((s □ t) : E → EReal) p) = (projectedImageRawOwner U V u : EReal) := by
    -- Route correction: rewrite the carrier inverse value directly to the projected-image owner
    -- before choosing the explicit splitting witness.
    simpa [E, p, s, t] using
      horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_on_carrierInverse_l2 U V u
  have hraw_value :
      (((s □ t) : E → EReal) p) = (halfSquaredNorm u : EReal) := by
    -- On the projected image, the raw owner is just the finite quadratic height.
    rw [hraw_projected, projectedImageRawOwner_asEReal_apply_l2]
    rw [show
        (((orthogonalClosedSubmodule U).orthogonalProjection ▷
              (ι[(V : Set L2Nat)] : L2Nat → Set.Ioi (⊥ : EReal))) u) = 0 by
      simpa using
        congrFun (projectionIndicator_infimalPostcomposition_eq_projectedImageIndicator_l2 U V) u]
    simp
  have hexact_p : infimalConvolution.ExactAt s t p := by
    refine ⟨(p.1 + a, 0), ?_⟩
    have hs_value : (s (p.1 + a, 0) : EReal) = 0 := by
      -- The chosen horizontal witness lies on the zero-second-coordinate slice by construction.
      simp [s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
    have hgraph :
        ((-a, u) : E) ∈ projectedImageGraphSet U V := by
      -- Negating the projected-image witness gives the graph-side point over `u`.
      constructor
      · exact V.neg_mem haV
      · simpa using congrArg Neg.neg hproj
    have ht_value : (t (-a, u) : EReal) = (halfSquaredNorm u : EReal) := by
      -- On the graph, the indicator vanishes and only the quadratic tail remains.
      rw [show
          (ι[projectedImageGraphSet U V] ((-a, u) : E) : EReal) = 0 by
        simp [indicator_apply, hgraph]]
      simp [t]
    -- The same explicit ambient witness that works on the vertical slice also works at the carrier
    -- inverse because only the second coordinate enters the graph-side residual.
    calc
      (((s □ t) : E → EReal) p) = (halfSquaredNorm u : EReal) := hraw_value
      _ = (s (p.1 + a, 0) : EReal) + (t (p - (p.1 + a, 0)) : EReal) := by
            rw [hs_value, show p - (p.1 + a, 0) = (-a, u) by
              simpa [p] using subtract_horizontalSliceWitness_l2 U p a, ht_value]
            simp
  refine ⟨hexact_p, ?_⟩
  -- The exact value is still the finite quadratic height.
  rw [hraw_value, halfSquaredNorm_apply]
  exact EReal.coe_lt_top _

/-- Helper for Remark 16.46: restricting the stable ambient product witnesses to the closed
orthogonal-graph carrier already gives a genuine noncollapsed `Γ₀` pair on that carrier, with a
common finite point at the origin. -/
private theorem orthogonalGraphRestrictedWitnessPair_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    ∃ (fW gW : orthogonalGraphCarrier_l2 U → Set.Ioi (⊥ : EReal))
      (hfW : fW ∈ Γ₀(orthogonalGraphCarrier_l2 U))
      (hgW : gW ∈ Γ₀(orthogonalGraphCarrier_l2 U)),
      (effectiveDomain fW ∩ effectiveDomain gW).Nonempty := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let W := orthogonalGraphCarrier_l2 U
  let i : W →L[ℝ] E := W.subtypeL
  rcases productGraphConjugateWitnessOwners_l2 U V hV_closed with
    ⟨f, g, hf, hg, _hdom, hfs, hgs, _hraw⟩
  let fW : W → Set.Ioi (⊥ : EReal) := f ∘ i
  let gW : W → Set.Ioi (⊥ : EReal) := g ∘ i
  have hfStar : (f∗[hf]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hf
  have hgStar : (g∗[hg]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hg
  have hfStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((f∗[hf]) p : EReal) := by
    intro p
    -- The horizontal-slice indicator is either `0` or `⊤`, so it stays nonnegative everywhere.
    rw [hfs]
    by_cases hp : p ∈ horizontalOrthogonalSliceSet U
    · simp [indicator_apply, hp]
    · simp [indicator_apply, hp]
  have hfStar_zero : ((f∗[hf]) 0 : EReal) = 0 := by
    -- The origin belongs to the horizontal slice.
    rw [hfs]
    simp [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have hgStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((g∗[hg]) p : EReal) := by
    intro p
    -- The graph-plus-quadratic owner is nonnegative on the graph and `⊤` off the graph.
    rw [hgs]
    by_cases hp : p ∈ projectedImageGraphSet U V
    · rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = 0 by
        simp [indicator_apply, hp]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm p.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm p.2).2
      rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ by
        simp [indicator_apply, hp]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp
  have hgStar_zero : ((g∗[hg]) 0 : EReal) = 0 := by
    -- The origin lies on the projected-image graph and has zero quadratic height.
    rw [hgs]
    simp [projectedImageGraphSet, halfSquaredNorm_apply]
  have hf_zero : (0 : E) ∈ effectiveDomain f := by
    -- Nonnegativity and the zero value at the origin force the primal witness to be finite there.
    have hzero :
        (0 : E) ∈ effectiveDomain ((f∗[hf])∗[hfStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hfStar) hfStar_nonneg hfStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hg_zero : (0 : E) ∈ effectiveDomain g := by
    -- The same origin test works for the graph-plus-quadratic witness.
    have hzero :
        (0 : E) ∈ effectiveDomain ((g∗[hg])∗[hgStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hgStar) hgStar_nonneg hgStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hi_dom_f : (Set.range i ∩ effectiveDomain f).Nonempty := by
    -- The carrier inclusion meets `effectiveDomain f` at the common origin.
    exact ⟨0, ⟨0, rfl⟩, hf_zero⟩
  have hi_dom_g : (Set.range i ∩ effectiveDomain g).Nonempty := by
    -- The same origin witness works for `g`.
    exact ⟨0, ⟨0, rfl⟩, hg_zero⟩
  have hfW : fW ∈ Γ₀(W) := by
    -- Restrict the first ambient witness along the closed-carrier inclusion.
    simpa [fW, i, Function.comp] using
      comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty f hf i hi_dom_f
  have hgW : gW ∈ Γ₀(W) := by
    -- Restrict the second ambient witness along the same inclusion.
    simpa [gW, i, Function.comp] using
      comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty g hg i hi_dom_g
  have hfW_zero : (0 : W) ∈ effectiveDomain fW := by
    -- The restricted first witness is finite at the carrier origin because the ambient one is.
    simpa [fW, i, mem_effectiveDomain_iff, Function.comp] using hf_zero
  have hgW_zero : (0 : W) ∈ effectiveDomain gW := by
    -- The restricted second witness is finite at the same carrier origin.
    simpa [gW, i, mem_effectiveDomain_iff, Function.comp] using hg_zero
  exact ⟨fW, gW, hfW, hgW, ⟨0, hfW_zero, hgW_zero⟩⟩

/-- Helper for Remark 16.46: keep the ambient product-graph witness formulas together with their
restrictions to the orthogonal-graph carrier, so later arguments can use the ambient
normalization equalities without rebuilding the restricted `Γ₀` pair. -/
private theorem orthogonalGraphRestrictedWitnessPackage_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let W := orthogonalGraphCarrier_l2 U
    let i : W →L[ℝ] E := W.subtypeL
    ∃ (f g : E → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(E))
      (hg : g ∈ Γ₀(E))
      (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
      (fW gW : W → Set.Ioi (⊥ : EReal))
      (hfW : fW ∈ Γ₀(W))
      (hgW : gW ∈ Γ₀(W)),
      (effectiveDomain fW ∩ effectiveDomain gW).Nonempty ∧
        fW = f ∘ i ∧
        gW = g ∘ i ∧
        (f∗[hf]) =
          (ι[horizontalOrthogonalSliceSet U] :
            E → Set.Ioi (⊥ : EReal)) ∧
        (g∗[hg]) =
          (fun p : E ↦
            (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) +
              halfSquaredNorm p.2) ∧
        ((((f∗[hf]) □ (g∗[hg])) : E → EReal)) =
          fun p : E ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) ∧
        (f + g).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let W := orthogonalGraphCarrier_l2 U
  let i : W →L[ℝ] E := W.subtypeL
  rcases productGraphConjugateWitnessEnvelopePullback_l2 U V hV_closed with
    ⟨f, g, hf, hg, hdom, hfs, hgs, hraw, hconj_pullback⟩
  let fW : W → Set.Ioi (⊥ : EReal) := f ∘ i
  let gW : W → Set.Ioi (⊥ : EReal) := g ∘ i
  have hfStar : (f∗[hf]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hf
  have hgStar : (g∗[hg]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hg
  have hfStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((f∗[hf]) p : EReal) := by
    intro p
    -- The horizontal-slice indicator only takes the values `0` and `⊤`.
    rw [hfs]
    by_cases hp : p ∈ horizontalOrthogonalSliceSet U
    · simp [indicator_apply, hp]
    · simp [indicator_apply, hp]
  have hfStar_zero : ((f∗[hf]) 0 : EReal) = 0 := by
    -- The ambient origin belongs to the horizontal slice.
    rw [hfs]
    simp [horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have hgStar_nonneg : ∀ p : E, (0 : EReal) ≤ ((g∗[hg]) p : EReal) := by
    intro p
    -- The graph-plus-quadratic owner is nonnegative on the graph and `⊤` off the graph.
    rw [hgs]
    by_cases hp : p ∈ projectedImageGraphSet U V
    · rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = 0 by
        simp [indicator_apply, hp]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm p.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm p.2).2
      rw [show
          ((ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ by
        simp [indicator_apply, hp]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp
  have hgStar_zero : ((g∗[hg]) 0 : EReal) = 0 := by
    -- The ambient origin lies on the projected-image graph and has zero quadratic height.
    rw [hgs]
    simp [projectedImageGraphSet, halfSquaredNorm_apply]
  have hf_zero : (0 : E) ∈ effectiveDomain f := by
    -- Finite conjugate value at the origin forces the primal witness to be finite there.
    have hzero :
        (0 : E) ∈ effectiveDomain ((f∗[hf])∗[hfStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hfStar) hfStar_nonneg hfStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hg_zero : (0 : E) ∈ effectiveDomain g := by
    -- The same origin test works for the graph-plus-quadratic witness.
    have hzero :
        (0 : E) ∈ effectiveDomain ((g∗[hg])∗[hgStar]) :=
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        (hφ := hgStar) hgStar_nonneg hgStar_zero
    simpa [gammaZeroConjugate_apply] using hzero
  have hi_dom_f : (Set.range i ∩ effectiveDomain f).Nonempty := by
    -- The carrier inclusion meets `effectiveDomain f` at the common origin.
    exact ⟨0, ⟨0, rfl⟩, hf_zero⟩
  have hi_dom_g : (Set.range i ∩ effectiveDomain g).Nonempty := by
    -- The same origin witness works for the second ambient owner.
    exact ⟨0, ⟨0, rfl⟩, hg_zero⟩
  have hfW : fW ∈ Γ₀(W) := by
    -- Restrict the first ambient witness along the closed orthogonal-graph inclusion.
    simpa [fW, i, Function.comp] using
      comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
        f hf i hi_dom_f
  have hgW : gW ∈ Γ₀(W) := by
    -- Restrict the second ambient witness along the same inclusion.
    simpa [gW, i, Function.comp] using
      comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
        g hg i hi_dom_g
  have hfW_zero : (0 : W) ∈ effectiveDomain fW := by
    -- The restricted first witness stays finite at the carrier origin.
    simpa [fW, i, mem_effectiveDomain_iff, Function.comp] using hf_zero
  have hgW_zero : (0 : W) ∈ effectiveDomain gW := by
    -- The restricted second witness is finite at the same carrier origin.
    simpa [gW, i, mem_effectiveDomain_iff, Function.comp] using hg_zero
  exact ⟨f, g, hf, hg, hdom, fW, gW, hfW, hgW, ⟨0, hfW_zero, hgW_zero⟩,
    rfl, rfl, hfs, hgs, hraw, hconj_pullback⟩

/-- Helper for Remark 16.46: the orthogonal-graph restriction of the ambient product witnesses
already has `0` as a common additive subgradient witness. This closes the origin half of the
carrier sum-rule argument; only the global active-point collapse remains. -/
private theorem orthogonalGraphRestrictedOriginSplit_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    let W := orthogonalGraphCarrier_l2 U
    ∃ (fW gW : W → Set.Ioi (⊥ : EReal))
      (hfW : fW ∈ Γ₀(W))
      (hgW : gW ∈ Γ₀(W)),
      (effectiveDomain fW ∩ effectiveDomain gW).Nonempty ∧
        (0 : W) ∈ (∂ fW) 0 ∧
        (0 : W) ∈ (∂ gW) 0 := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let W := orthogonalGraphCarrier_l2 U
  let i : W →L[ℝ] E := W.subtypeL
  rcases orthogonalGraphRestrictedWitnessPackage_l2 U V hV_closed with
    ⟨f, g, hf, hg, _hdom, fW, gW, hfW, hgW, hdomW, hfW_def, hgW_def, hfs, hgs, _hraw,
      _hconj_pullback⟩
  have hzero_fstar : (0 : E) ∈ (∂ (f∗[hf])) (0 : E) := by
    -- The horizontal-slice indicator has the zero normal vector at the ambient origin.
    rw [hfs]
    exact (mem_subdifferential_horizontalOrthogonalSliceIndicator_iff U).2 ⟨rfl, rfl⟩
  have hzero_f : (0 : E) ∈ (∂ f) (0 : E) := by
    -- Corollary 16.30 turns the zero subgradient of `f*` back into one for `f`.
    exact (mem_subdifferential_gammaZeroConjugate_iff hf).mp hzero_fstar
  have hzero_gstar : (0 : E) ∈ (∂ (g∗[hg])) (0 : E) := by
    -- The graph-plus-quadratic owner also has the ambient origin as a self-subgradient.
    rw [hgs]
    simpa using
      (mem_subdifferential_projectedImageGraphOwner_of_mem_projectedImage_and_orthogonal
        U V (a := 0) (u := 0) (ξ := 0) (by simpa) (by simp) (by simpa))
  have hzero_g : (0 : E) ∈ (∂ g) (0 : E) := by
    -- Apply the same conjugate-to-primal transport for the second ambient witness.
    exact (mem_subdifferential_gammaZeroConjugate_iff hg).mp hzero_gstar
  have hzero_fW : (0 : W) ∈ (∂ fW) (0 : W) := by
    -- Restrict the ambient zero subgradient to the orthogonal-graph carrier.
    simpa [hfW_def, i, Function.comp] using
      (mem_subdifferential_restrict_of_mem_subdifferential_ambient_local
        (B := W) (f := f) (x := (0 : W)) (u := (0 : W)) hzero_f)
  have hzero_gW : (0 : W) ∈ (∂ gW) (0 : W) := by
    -- The same restriction step gives the carrier-side zero subgradient for `gW`.
    simpa [hgW_def, i, Function.comp] using
      (mem_subdifferential_restrict_of_mem_subdifferential_ambient_local
        (B := W) (f := g) (x := (0 : W)) (u := (0 : W)) hzero_g)
  exact ⟨fW, gW, hfW, hgW, hdomW, hzero_fW, hzero_gW⟩

/-- Helper for Remark 16.46: precomposing the orthogonal-graph carrier witness pair with the
carrier parameterization gives a genuine same-space `Γ₀(Uᗮ)` pair with a common finite point. -/
private theorem orthogonalGraphSameSpaceWitnessPair_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    ∃ (fK gK : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
      (hfK : fK ∈ Γ₀(orthogonalClosedSubmodule U))
      (hgK : gK ∈ Γ₀(orthogonalClosedSubmodule U)),
      (effectiveDomain fK ∩ effectiveDomain gK).Nonempty := by
  let W := orthogonalGraphCarrier_l2 U
  let K := orthogonalClosedSubmodule U
  let e : W ≃L[ℝ] K := orthogonalGraphCarrierEquivOrthogonalComplement_l2 U
  rcases orthogonalGraphRestrictedWitnessPair_l2 U V hV_closed with
    ⟨fW, gW, hfW, hgW, hdomW⟩
  let fK : K → Set.Ioi (⊥ : EReal) := fW ∘ e.symm
  let gK : K → Set.Ioi (⊥ : EReal) := gW ∘ e.symm
  have hfK : fK ∈ Γ₀(K) := by
    -- Move the first carrier witness along the explicit linear equivalence `e`.
    simpa [fK, Function.comp] using
      mem_gammaZero_comp_continuousLinearEquiv hfW e.symm
  have hgK : gK ∈ Γ₀(K) := by
    -- The second carrier witness transports in the same way.
    simpa [gK, Function.comp] using
      mem_gammaZero_comp_continuousLinearEquiv hgW e.symm
  rcases hdomW with ⟨w, hwf, hwg⟩
  refine ⟨fK, gK, hfK, hgK, ⟨e w, ?_, ?_⟩⟩
  · -- The common finite carrier point stays finite after applying the equivalence.
    simpa [fK, Function.comp, mem_effectiveDomain_iff] using hwf
  · -- The same transported point stays finite for the second witness.
    simpa [gK, Function.comp, mem_effectiveDomain_iff] using hwg

/-- Helper for Remark 16.46: on the orthogonal graph, vanishing first coordinate already forces
the second coordinate to vanish. -/
private theorem orthogonalGraphCarrier_snd_eq_zero_of_fst_eq_zero_l2
    (U : Submodule ℝ L2Nat)
    {z : orthogonalGraphCarrier_l2 U}
    (hz1 : ((z : orthogonalGraphCarrier_l2 U) : L2Nat × orthogonalClosedSubmodule U).1 = 0) :
    ((z : orthogonalGraphCarrier_l2 U) : L2Nat × orthogonalClosedSubmodule U).2 = 0 := by
  rcases orthogonalGraphPoint_eq_pair_projectionAdjoint_neg_l2 U z.2 with ⟨u, rfl⟩
  have hu_zero : u = 0 := by
    apply Subtype.ext
    simpa using hz1
  simpa [hu_zero]

/-- Helper for Remark 16.46: a closure point of `P_{Uᗮ}(V)` that is also orthogonal to that
projected image must vanish. -/
private theorem projectedImageClosurePoint_eq_zero_of_mem_orthogonal_l2
    (U V : Submodule ℝ L2Nat)
    {η : orthogonalClosedSubmodule U}
    (hη_closure :
      η ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)))
    (hη_orth :
      η ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U))) :
    η = 0 := by
  let A : Submodule ℝ (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
  let W : Submodule ℝ (orthogonalClosedSubmodule U) := A.topologicalClosure
  have hη_mem_closure : η ∈ W := by
    -- Rewrite closure membership as membership in the closed projected-image submodule.
    simpa [W, Submodule.topologicalClosure_coe] using hη_closure
  have hη_mem_orth : η ∈ Wᗮ := by
    -- Orthogonality to `P_{Uᗮ}(V)` is unchanged after closing that submodule.
    simpa [A, W, Submodule.orthogonal_closure] using hη_orth
  have hinner_zero : ⟪η, η⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hη_mem_closure hη_mem_orth
  -- The only vector orthogonal to itself is the zero vector.
  simpa using inner_self_eq_zero.mp hinner_zero

/-- Helper for Remark 16.46: any ambient active point whose base point lies on the orthogonal
graph already collapses to the graph origin, and its second dual coordinate vanishes. -/
private theorem orthogonalGraphAmbientActivePoint_zero_l2
    (U V : Submodule ℝ L2Nat)
    (hV_closed : IsClosed (V : Set L2Nat))
    {f g : (L2Nat × orthogonalClosedSubmodule U) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hg : g ∈ Γ₀(L2Nat × orthogonalClosedSubmodule U))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hconj_pullback :
      (f + g).asEReal∗ =
        lowerSemicontinuousConvexEnvelope
          (fun p : L2Nat × orthogonalClosedSubmodule U ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
    {z : orthogonalGraphCarrier_l2 U}
    {ξ : L2Nat × orthogonalClosedSubmodule U}
    (hξ : ξ ∈ (∂ (f + g)) (z : L2Nat × orthogonalClosedSubmodule U)) :
    z = 0 ∧ ξ.2 = 0 := by
  have hsupport :=
    productGraphWitnessClosureSupport_of_mem_subdifferential_l2
      U V hV_closed hf hg hdom hconj_pullback hξ
  rcases hsupport with ⟨hz1, hξ2_closure, hz2_subξ2_orth⟩
  have hz2_zero :
      ((z : orthogonalGraphCarrier_l2 U) : L2Nat × orthogonalClosedSubmodule U).2 = 0 :=
    -- On the orthogonal graph, the first coordinate already determines the second one.
    orthogonalGraphCarrier_snd_eq_zero_of_fst_eq_zero_l2 U hz1
  have hz_zero : z = 0 := by
    -- Once both product coordinates vanish, the carrier point itself is the origin.
    apply Subtype.ext
    ext <;> simp [hz1, hz2_zero]
  have hnegξ2_orth :
      -ξ.2 ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U)) := by
    -- Setting the orthogonal-graph base point to `0` makes the residual exactly `-ξ.2`.
    simpa [hz2_zero] using hz2_subξ2_orth
  have hξ2_orth :
      ξ.2 ∈
        (((projectedImageSubmodule U V)ᗮ : Submodule ℝ (orthogonalClosedSubmodule U)) :
          Set (orthogonalClosedSubmodule U)) := by
    -- The orthogonal complement is a submodule, so it is closed under negation.
    simpa using
      (Submodule.neg_mem ((projectedImageSubmodule U V)ᗮ) hnegξ2_orth)
  have hξ2_zero :
      ξ.2 = 0 :=
    projectedImageClosurePoint_eq_zero_of_mem_orthogonal_l2 U V hξ2_closure hξ2_orth
  exact ⟨hz_zero, hξ2_zero⟩

/-- Helper for Remark 16.46: restricting the ambient horizontal-slice and graph-plus-quadratic
owners to the exact closed-span carrier already gives a same-space `Γ₀` pair whose conjugates
share the origin as a finite point. -/
private theorem restrictedProductGraphSameSpacePair_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    ∃ (fB gB : B → Set.Ioi (⊥ : EReal))
      (hfB : fB ∈ Γ₀(B)) (hgB : gB ∈ Γ₀(B)),
      (effectiveDomain fB ∩ effectiveDomain gB).Nonempty := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  letI : CompleteSpace B := subImageDifferenceClosedSpan_completeSpace s t (ContinuousLinearMap.id ℝ E)
  have hs : s ∈ Γ₀(E) := by
    -- Reuse the packaged `Γ₀` statement for the horizontal slice.
    simpa [E, s] using horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U
  have ht_graph :
      (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∈ Γ₀(E) := by
    -- Closedness of `V` upgrades the projected-image graph indicator to `Γ₀`.
    simpa [E] using projectedImageGraphIndicator_mem_gammaZero_l2 U V hV_closed
  have ht_half :
      (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal))) ∈ Γ₀(E) := by
    -- The quadratic tail is the pulled-back half-squared norm on the second coordinate.
    simpa [E] using secondCoordinateHalfSquaredNorm_mem_gammaZero_l2 U
  have ht_dom :
      (effectiveDomain (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∩
          effectiveDomain (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))).Nonempty := by
    -- The origin is a common finite point of the graph indicator and the quadratic tail.
    refine ⟨(0, 0), ?_, ?_⟩
    · simp [mem_effectiveDomain_iff, projectedImageGraphSet]
    · rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  have ht : t ∈ Γ₀(E) := by
    -- Adding the quadratic tail preserves the `Γ₀` structure on the graph owner.
    exact
      pointwiseAdd_mem_gammaZero
        (ι[projectedImageGraphSet U V])
        (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))
        ht_graph ht_half ht_dom
  have hs_zero : (0 : E) ∈ effectiveDomain s := by
    -- The origin belongs to the horizontal slice.
    simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff, indicator_apply]
  have ht_zero : (0 : E) ∈ effectiveDomain t := by
    -- The origin is also a projected-image graph point with zero quadratic value.
    simp [t, mem_effectiveDomain_iff, projectedImageGraphSet, halfSquaredNorm_apply]
  let sB : B → Set.Ioi (⊥ : EReal) := fun x ↦ s x
  let tB : B → Set.Ioi (⊥ : EReal) := fun x ↦ t x
  have hsB : sB ∈ Γ₀(B) := by
    -- Restrict the horizontal-slice owner to the exact closed-span carrier.
    simpa [sB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain s hs hs_zero B
  have htB : tB ∈ Γ₀(B) := by
    -- Restrict the graph-plus-quadratic owner to the same carrier.
    simpa [tB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain t ht ht_zero B
  let fB : B → Set.Ioi (⊥ : EReal) := tB∗[htB]
  let gB : B → Set.Ioi (⊥ : EReal) := sB∗[hsB]
  have hfB : fB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero htB
  have hgB : gB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero hsB
  have hsB_nonneg : ∀ x : B, (0 : EReal) ≤ (sB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ horizontalOrthogonalSliceSet U
    · simp [sB, s, indicator_apply, hx]
    · simp [sB, s, indicator_apply, hx]
  have htB_nonneg : ∀ x : B, (0 : EReal) ≤ (tB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ projectedImageGraphSet U V
    · rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = 0 by
        simp [indicator_apply, hx]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm (((x : B) : E).2) : EReal) ≠ ⊥ :=
        ne_of_gt (halfSquaredNorm (((x : B) : E).2)).2
      rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = ⊤ by
        simp [indicator_apply, hx]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp [tB, t]
  have hsB_zero : (sB 0 : EReal) = 0 := by
    -- Restricting the origin preserves the zero indicator value.
    simp [sB, s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have htB_zero : (tB 0 : EReal) = 0 := by
    -- The restricted graph-plus-quadratic owner also vanishes at the carrier origin.
    simp [tB, t, projectedImageGraphSet, halfSquaredNorm_apply]
  have hfB_zero : (0 : B) ∈ effectiveDomain fB := by
    -- A nonnegative owner with value `0` at the origin has a finite conjugate there.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        htB htB_nonneg htB_zero
  have hgB_zero : (0 : B) ∈ effectiveDomain gB := by
    -- The same zero-test works for the restricted horizontal-slice owner.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        hsB hsB_nonneg hsB_zero
  exact ⟨fB, gB, hfB, hgB, ⟨0, hfB_zero, hgB_zero⟩⟩

/-- Helper for Remark 16.46: if two same-space owners are finite at the origin, then each
effective domain already lies in the closed span of the difference surface used by
`subImageDifferenceClosedSpan`. -/
private theorem effectiveDomain_subset_sameSpaceDifferenceClosedSpan_of_zero_mem_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal))
    (hzero_f : (0 : E) ∈ effectiveDomain f)
    (hzero_g : (0 : E) ∈ effectiveDomain g) :
    effectiveDomain f ⊆
        (subImageDifferenceClosedSpan f g (ContinuousLinearMap.id ℝ E) : Set E) ∧
      effectiveDomain g ⊆
        (subImageDifferenceClosedSpan f g (ContinuousLinearMap.id ℝ E) : Set E) := by
  constructor
  · intro x hx
    -- Use the same-space witness `-x = 0 - x` to place `x` in the span of the support surface.
    have hnegx :
        -x ∈ effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f := by
      refine Set.mem_sub.mpr ?_
      exact ⟨0, hzero_g, x, ⟨x, hx, rfl⟩, by simp⟩
    have hx_span :
        x ∈ Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f) := by
      simpa using
        Submodule.neg_mem
          (Submodule.span ℝ
            (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f))
          (Submodule.subset_span hnegx)
    -- The closed-span carrier is exactly the topological closure of that span.
    simpa [subImageDifferenceClosedSpan] using
      (Submodule.span ℝ
        (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).le_topologicalClosure
        hx_span
  · intro y hy
    -- The generator `y = y - 0` already lies in the same-space difference surface.
    have hy_diff :
        y ∈ effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f := by
      refine Set.mem_sub.mpr ?_
      exact ⟨y, hy, 0, ⟨0, hzero_f, by simp⟩, by simp⟩
    have hy_span :
        y ∈ Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f) :=
      Submodule.subset_span hy_diff
    -- Passing from the span to its closure lands exactly in `subImageDifferenceClosedSpan`.
    simpa [subImageDifferenceClosedSpan] using
      (Submodule.span ℝ
        (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).le_topologicalClosure
        hy_span

/-- Helper for Remark 16.46: once the horizontal-slice and graph-plus-quadratic owners are finite
at the origin, both effective domains lie in the exact closed-span carrier used by the final
same-space restriction. -/
private theorem effectiveDomain_productGraphOwners_subset_restrictedCarrier_l2
    (U V : Submodule ℝ L2Nat) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    effectiveDomain s ⊆ (B : Set E) ∧ effectiveDomain t ⊆ (B : Set E) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  have hs_zero : (0 : E) ∈ effectiveDomain s := by
    -- The origin lies on the horizontal slice.
    simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff, indicator_apply]
  have ht_zero : (0 : E) ∈ effectiveDomain t := by
    -- The origin is also a projected-image graph point with zero quadratic value.
    simp [t, mem_effectiveDomain_iff, projectedImageGraphSet, halfSquaredNorm_apply]
  -- Specialize the same-space closed-span containment lemma to the product-graph owners.
  simpa [E, s, t, B] using
    effectiveDomain_subset_sameSpaceDifferenceClosedSpan_of_zero_mem_local s t hs_zero ht_zero

/-- Helper for Remark 16.46: if the ambient effective domain already lies in a closed subspace,
then conjugating after restriction to that subspace agrees with the ambient conjugate on subtype
points. -/
private theorem restrictedConjugate_eq_ambientConjugate_on_subtype_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) {B : ClosedSubmodule ℝ E}
    (hdom : effectiveDomain f ⊆ (B : Set E)) (v : B) :
    (fun x : (B : Submodule ℝ E) ↦ f x).asEReal∗ v = f.asEReal∗ (v : E) := by
  -- Read the restricted conjugate through the orthogonal-projection formula and then cancel the
  -- projection on subtype points.
  have hrestrict :
      ((fun x : (B : Submodule ℝ E) ↦ f x).asEReal∗) (B.orthogonalProjection (v : E)) =
        f.asEReal∗ (v : E) := by
    simpa [Function.comp] using
      congrFun (conjugate_restrict_comp_orthogonalProjection_of_dom_subset f.asEReal B hdom) (v : E)
  simpa [orthogonalProjection_subtype_eq_self] using hrestrict

/-- Helper for Remark 16.46: restricting a same-space owner to a closed subspace can only lower
its conjugate, because the defining supremum is taken over fewer primal points. -/
private theorem restrictedConjugate_le_ambientConjugate_on_subtype_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → Set.Ioi (⊥ : EReal)) {B : ClosedSubmodule ℝ E} (v : B) :
    (fun x : (B : Submodule ℝ E) ↦ f x).asEReal∗ v ≤ f.asEReal∗ (v : E) := by
  -- Compare the two conjugate suprema term-by-term by viewing each subtype witness as an ambient
  -- witness.
  rw [ERealFunction.conjugate_apply, ERealFunction.conjugate_apply]
  refine iSup_le ?_
  intro x
  refine le_iSup_of_le (x : E) ?_
  simp

/-- Helper for Remark 16.46: an ambient subgradient at a carrier point remains a subgradient after
restricting the owner to that closed carrier. -/
private theorem mem_subdifferential_restrict_of_mem_subdifferential_ambient_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : ClosedSubmodule ℝ E} {f : E → Set.Ioi (⊥ : EReal)} {x u : B}
    (hu : ((u : B) : E) ∈ (∂ f) ((x : B) : E)) :
    u ∈ (∂ (fun y : (B : Submodule ℝ E) ↦ f y)) x := by
  rw [mem_subdifferential_iff] at hu ⊢
  intro y
  -- Restrict the ambient subgradient inequality to subtype test points.
  simpa using hu (y : E)

/-- Helper for Remark 16.46: if an ambient owner is invariant under the carrier star projection,
then any subgradient of its restriction lifts back to an ambient subgradient. -/
private theorem liftAmbientSubgradientOfRestrictedCarrier_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : ClosedSubmodule ℝ E} {f : E → Set.Ioi (⊥ : EReal)}
    (hproj : f.asEReal = f.asEReal ∘ B.starProjection) {x u : B}
    (hu : u ∈ (∂ (fun y : (B : Submodule ℝ E) ↦ f y)) x) :
    ((u : B) : E) ∈ (∂ f) ((x : B) : E) := by
  rw [mem_subdifferential_iff] at hu ⊢
  intro z
  let zB : B := B.orthogonalProjection z
  have huB := hu zB
  have hres_orth :
      z - B.starProjection z ∈ (((B : Submodule ℝ E)ᗮ : Submodule ℝ E) : Set E) := by
    simpa using ((B : Submodule ℝ E).sub_starProjection_mem_orthogonal z)
  have hinner_res : ⟪z - B.starProjection z, (u : E)⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal u.2 hres_orth
  have hinner :
      ⟪z - (x : E), (u : E)⟫_ℝ = ⟪(zB : E) - (x : E), (u : E)⟫_ℝ := by
    calc
      ⟪z - (x : E), (u : E)⟫_ℝ
          = ⟪(z - B.starProjection z) + ((zB : E) - (x : E)), (u : E)⟫_ℝ := by
              congr 1
              change z - (x : E) = (z - B.starProjection z) + ((B.starProjection z : E) - (x : E))
              abel
      _ = ⟪z - B.starProjection z, (u : E)⟫_ℝ +
            ⟪(zB : E) - (x : E), (u : E)⟫_ℝ := by
              rw [inner_add_left]
      _ = ⟪(zB : E) - (x : E), (u : E)⟫_ℝ := by
              simp [hinner_res]
  have hz_proj : (f z : EReal) = (f zB : EReal) := by
    simpa [Function.comp, zB] using congrFun hproj z
  -- Compare the ambient test point `z` with its carrier projection `zB`.
  simpa [hinner, hz_proj] using huB

/-- Helper for Remark 16.46: the ambient bad point `((0), u₀)` already belongs to the exact
closed-span carrier, because vertical projected-image points lie on the difference surface and the
carrier is closed. -/
private theorem badVerticalPoint_mem_restrictedCarrier_l2
    (U V : Submodule ℝ L2Nat)
    {u0 : orthogonalClosedSubmodule U}
    (hu0_closure :
      u0 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    (((0 : L2Nat), u0) : E) ∈ (B : Set E) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  let A : Set (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
  have himage_subset :
      (fun u : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), u) : E)) '' A ⊆ (B : Set E) := by
    rintro _ ⟨u, hu, rfl⟩
    rcases projectedImageWitness_of_mem_projectedImage_l2 U V hu with ⟨a, haV, hproj⟩
    have hs_mem : (((-a), 0) : E) ∈ effectiveDomain s := by
      -- Every horizontal point lies in the slice indicator domain.
      simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
        LinearMap.mem_graph_iff, indicator_apply]
    have hgraph : (((-a), u) : E) ∈ projectedImageGraphSet U V := by
      -- Negating the source witness flips the projection to the graph point over `u`.
      constructor
      · exact V.neg_mem haV
      · simpa using congrArg Neg.neg hproj
    have ht_mem : (((-a), u) : E) ∈ effectiveDomain t := by
      -- On the projected-image graph, the indicator vanishes and the quadratic tail stays finite.
      rw [mem_effectiveDomain_iff]
      rw [show
          (ι[projectedImageGraphSet U V] (((-a), u) : E) : EReal) = 0 by
        simp [indicator_apply, hgraph]]
      simp [t, halfSquaredNorm_apply]
    have hdiff :
        (((0 : L2Nat), u) : E) ∈
          effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s := by
      refine Set.mem_sub.mpr ?_
      refine ⟨(((-a), u) : E), ht_mem, (((-a), 0) : E), ?_, ?_⟩
      · exact ⟨(((-a), 0) : E), hs_mem, rfl⟩
      · simp
    have hspan :
        (((0 : L2Nat), u) : E) ∈
          Submodule.span ℝ
            (effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s) :=
      Submodule.subset_span hdiff
    -- Points of the actual difference surface lie in the closed-span carrier by definition.
    simpa [B, subImageDifferenceClosedSpan] using
      (Submodule.span ℝ
        (effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s)).le_topologicalClosure
        hspan
  have hu0_image :
      (((0 : L2Nat), u0) : E) ∈
        (fun u : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), u) : E)) '' closure A := by
    exact ⟨u0, hu0_closure, rfl⟩
  have hcont_vertical :
      Continuous fun u : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), u) : E) := by
    exact continuous_const.prod_mk continuous_id
  have hclosure_image :
      (((0 : L2Nat), u0) : E) ∈
        closure ((fun u : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), u) : E)) '' A) :=
    image_closure_subset_closure_image hcont_vertical hu0_image
  have hclosure_subset :
      closure ((fun u : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), u) : E)) '' A) ⊆ (B : Set E) :=
    B.2.closure_subset_iff.mpr himage_subset
  -- Push the closure witness through the vertical embedding and use that the carrier is closed.
  exact hclosure_subset hclosure_image

/-- Helper for Remark 16.46: every pair `(z, u)` with `u ∈ P_{Uᗮ}(V)` already lies in the exact
closed-span carrier, because it is the difference of one graph point and one horizontal-slice
point. -/
private theorem pair_mem_restrictedCarrier_of_mem_projectedImage_l2
    (U V : Submodule ℝ L2Nat) {z : L2Nat} {u : orthogonalClosedSubmodule U}
    (hu : u ∈ projectedImageSubmodule U V) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    ((z, u) : E) ∈ (B : Set E) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  rcases projectedImageWitness_of_mem_projectedImage_l2 U V hu with ⟨a, haV, hproj⟩
  have hs_mem : (((-a - z), 0) : E) ∈ effectiveDomain s := by
    -- Every point with zero second coordinate lies on the horizontal slice.
    simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff, indicator_apply]
  have hgraph : (((-a), u) : E) ∈ projectedImageGraphSet U V := by
    -- Negating the projected-image witness gives the graph point over `u`.
    constructor
    · exact V.neg_mem haV
    · simpa using congrArg Neg.neg hproj
  have ht_mem : (((-a), u) : E) ∈ effectiveDomain t := by
    -- On the projected-image graph, the indicator vanishes and only the quadratic tail remains.
    rw [mem_effectiveDomain_iff]
    rw [show
        (ι[projectedImageGraphSet U V] (((-a), u) : E) : EReal) = 0 by
      simp [indicator_apply, hgraph]]
    simp [t, halfSquaredNorm_apply]
  have hdiff :
      ((z, u) : E) ∈
        effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s := by
    -- The desired point is exactly the difference between the graph witness and the slice witness.
    refine Set.mem_sub.mpr ?_
    refine ⟨(((-a), u) : E), ht_mem, (((-a - z), 0) : E), ?_, ?_⟩
    · exact ⟨(((-a - z), 0) : E), hs_mem, rfl⟩
    · ext <;> simp <;> abel
  have hspan :
      ((z, u) : E) ∈
        Submodule.span ℝ
          (effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s) :=
    Submodule.subset_span hdiff
  -- Passing from the difference surface to its closed span lands in the carrier by definition.
  simpa [B, subImageDifferenceClosedSpan] using
    (Submodule.span ℝ
      (effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s)).le_topologicalClosure
      hspan

/-- Helper for Remark 16.46: every point of the exact closed-span carrier has second coordinate in
`closure (projectedImageSubmodule U V)`. -/
private theorem restrictedCarrierSnd_mem_projectedImageClosure_l2
    (U V : Submodule ℝ L2Nat) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    ∀ x : B,
      ((x : B) : E).2 ∈
        closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  let A : Submodule ℝ (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
  let S : Set E :=
    effectiveDomain t - (ContinuousLinearMap.id ℝ E) '' effectiveDomain s
  have hS_snd :
      S ⊆ ((LinearMap.snd ℝ L2Nat (orthogonalClosedSubmodule U)).comap A : Set E) := by
    intro y hy
    rcases Set.mem_sub.mp hy with ⟨p, hp_t, q, hq, rfl⟩
    rcases hq with ⟨q0, hq0, rfl⟩
    have hp_graph : p ∈ projectedImageGraphSet U V := by
      -- Finiteness of the graph-plus-quadratic owner forces graph membership.
      simpa [t] using (mem_effectiveDomain_projectedImageGraphOwner_iff_l2 U V).1 hp_t
    have hp2_mem : p.2 ∈ (A : Set (orthogonalClosedSubmodule U)) := by
      exact Submodule.mem_map.mpr ⟨p.1, hp_graph.1, hp_graph.2⟩
    have hq0_second : q0.2 = 0 := by
      -- Points in the horizontal slice have zero second coordinate.
      simpa [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
        LinearMap.mem_graph_iff, indicator_apply] using hq0
    -- Subtracting a horizontal-slice point preserves the projected-image second coordinate.
    simpa [hq0_second] using hp2_mem
  have hspan_snd :
      (Submodule.span ℝ S : Set E) ⊆
        ((LinearMap.snd ℝ L2Nat (orthogonalClosedSubmodule U)).comap A : Set E) := by
    exact Submodule.span_le.mpr hS_snd
  intro x
  have hx_closure :
      ((x : B) : E) ∈ closure (Submodule.span ℝ S : Set E) := by
    -- Membership in the closed-span carrier is exactly the closure witness for the span.
    simpa [B, subImageDifferenceClosedSpan, S] using x.2
  have hx_snd_closure :
      ((x : B) : E).2 ∈ closure ((fun p : E ↦ p.2) '' (Submodule.span ℝ S : Set E)) := by
    -- Push the carrier closure witness through the continuous second projection.
    have hx_image :
        ((x : B) : E).2 ∈ (fun p : E ↦ p.2) '' closure (Submodule.span ℝ S : Set E) := by
      exact ⟨((x : B) : E), hx_closure, rfl⟩
    exact image_closure_subset_closure_image continuous_snd hx_image
  have hspan_image :
      (fun p : E ↦ p.2) '' (Submodule.span ℝ S : Set E) ⊆
        (A : Set (orthogonalClosedSubmodule U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hspan_snd hy
  -- The span image already lands in `A`, so its closure lands in `closure A`.
  exact (closure_mono hspan_image) hx_snd_closure

/-- Helper for Remark 16.46: once the second coordinate belongs to
`closure (projectedImageSubmodule U V)`, the exact closed-span carrier already contains the whole
horizontal translate `(z, u)`. -/
private theorem pair_mem_restrictedCarrier_of_mem_projectedImageClosure_l2
    (U V : Submodule ℝ L2Nat) {z : L2Nat} {u : orthogonalClosedSubmodule U}
    (hu_closure :
      u ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))) :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    ((z, u) : E) ∈ (B : Set E) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  have hz_zero :
      ((z, (0 : orthogonalClosedSubmodule U)) : E) ∈ (B : Set E) := by
    -- The horizontal slice already sits in the carrier because `0 ∈ P_{Uᗮ}(V)`.
    simpa using
      pair_mem_restrictedCarrier_of_mem_projectedImage_l2
        (U := U) (V := V) (z := z) (u := 0) (by simp)
  have hzero_u :
      (((0 : L2Nat), u) : E) ∈ (B : Set E) := by
    -- Vertical points over closure points belong to the carrier by closedness.
    simpa using badVerticalPoint_mem_restrictedCarrier_l2 (U := U) (V := V) hu_closure
  -- Add the horizontal and vertical carrier points to reach the desired pair.
  have hsum :
      ((z, u) : E) = ((z, (0 : orthogonalClosedSubmodule U)) : E) + (((0 : L2Nat), u) : E) := by
    ext <;> simp
  rw [hsum]
  exact B.add_mem hz_zero hzero_u

/-- Helper for Remark 16.46: the exact closed-span carrier is exactly the product of all first
coordinates with second coordinate in `closure (projectedImageSubmodule U V)`. -/
private theorem mem_restrictedCarrier_iff_snd_mem_projectedImageClosure_l2
    (U V : Submodule ℝ L2Nat)
    {x : L2Nat × orthogonalClosedSubmodule U} :
    let E := L2Nat × orthogonalClosedSubmodule U
    let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
    let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
      (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
    let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
    x ∈ (B : Set E) ↔
      x.2 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  constructor
  · intro hx
    -- Read the second-coordinate closure constraint from the existing carrier support lemma.
    simpa using restrictedCarrierSnd_mem_projectedImageClosure_l2 (U := U) (V := V) ⟨x, hx⟩
  · intro hx
    -- The new horizontal-translation lemma reconstructs the full carrier point from its second
    -- coordinate.
    simpa using
      pair_mem_restrictedCarrier_of_mem_projectedImageClosure_l2
        (U := U) (V := V) (z := x.1) (u := x.2) hx

/-- Helper for Remark 16.46: on the exact closed-span carrier, the restricted conjugate witness
pair already exposes the bad dual point where the conjugate sum stays finite while the raw dual
infimal convolution is forced to be `⊤`. -/
private theorem existsRestrictedCarrierCounterexampleGap_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        (f + g).asEReal∗ u < ⊤ ∧
        ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) = ⊤ := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  letI : CompleteSpace B := subImageDifferenceClosedSpan_completeSpace s t (ContinuousLinearMap.id ℝ E)
  have hs : s ∈ Γ₀(E) := by
    -- Reuse the packaged `Γ₀` structure of the horizontal slice.
    simpa [E, s] using horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U
  have ht_graph :
      (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∈ Γ₀(E) := by
    -- Closedness of `V` makes the projected-image graph owner a `Γ₀` function.
    simpa [E] using projectedImageGraphIndicator_mem_gammaZero_l2 U V hV_closed
  have ht_half :
      (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal))) ∈ Γ₀(E) := by
    -- The quadratic tail is the standard second-coordinate `Γ₀` owner.
    simpa [E] using secondCoordinateHalfSquaredNorm_mem_gammaZero_l2 U
  have ht_dom :
      (effectiveDomain (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∩
          effectiveDomain (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))).Nonempty := by
    -- The origin is a common finite point of the graph indicator and the quadratic tail.
    refine ⟨(0, 0), ?_, ?_⟩
    · simp [mem_effectiveDomain_iff, projectedImageGraphSet]
    · rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  have ht : t ∈ Γ₀(E) := by
    -- Adding the quadratic tail preserves the `Γ₀` structure on the graph owner.
    exact
      pointwiseAdd_mem_gammaZero
        (ι[projectedImageGraphSet U V])
        (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))
        ht_graph ht_half ht_dom
  have hs_zero : (0 : E) ∈ effectiveDomain s := by
    -- The horizontal slice contains the ambient origin.
    simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff, indicator_apply]
  have ht_zero : (0 : E) ∈ effectiveDomain t := by
    -- The graph-plus-quadratic owner is also finite at the origin.
    simp [t, mem_effectiveDomain_iff, projectedImageGraphSet, halfSquaredNorm_apply]
  let sB : B → Set.Ioi (⊥ : EReal) := fun x ↦ s x
  let tB : B → Set.Ioi (⊥ : EReal) := fun x ↦ t x
  have hsB : sB ∈ Γ₀(B) := by
    -- Restrict the slice owner to the exact closed-span carrier.
    simpa [sB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain s hs hs_zero B
  have htB : tB ∈ Γ₀(B) := by
    -- Restrict the graph-plus-quadratic owner to the same carrier.
    simpa [tB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain t ht ht_zero B
  let fB : B → Set.Ioi (⊥ : EReal) := tB∗[htB]
  let gB : B → Set.Ioi (⊥ : EReal) := sB∗[hsB]
  have hfB : fB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero htB
  have hgB : gB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero hsB
  have hsB_nonneg : ∀ x : B, (0 : EReal) ≤ (sB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ horizontalOrthogonalSliceSet U
    · simp [sB, s, indicator_apply, hx]
    · simp [sB, s, indicator_apply, hx]
  have htB_nonneg : ∀ x : B, (0 : EReal) ≤ (tB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ projectedImageGraphSet U V
    · rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = 0 by
        simp [indicator_apply, hx]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm (((x : B) : E).2) : EReal) ≠ ⊥ :=
        ne_of_gt (halfSquaredNorm (((x : B) : E).2)).2
      rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = ⊤ by
        simp [indicator_apply, hx]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp [tB, t]
  have hsB_zero : (sB 0 : EReal) = 0 := by
    -- Restricting to the carrier keeps the slice value `0` at the origin.
    simp [sB, s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have htB_zero : (tB 0 : EReal) = 0 := by
    -- The restricted graph owner still vanishes at the origin.
    simp [tB, t, projectedImageGraphSet, halfSquaredNorm_apply]
  have hfB_zero : (0 : B) ∈ effectiveDomain fB := by
    -- A nonnegative owner with value `0` at the origin has finite conjugate there.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        htB htB_nonneg htB_zero
  have hgB_zero : (0 : B) ∈ effectiveDomain gB := by
    -- The same origin test works for the restricted slice owner.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        hsB hsB_nonneg hsB_zero
  let uB : B := ⟨(((0 : L2Nat), u0) : E), badVerticalPoint_mem_restrictedCarrier_l2 U V hu0_closure⟩
  have hdom_subset : effectiveDomain s ⊆ (B : Set E) ∧ effectiveDomain t ⊆ (B : Set E) := by
    -- Both ambient effective domains already lie in the exact closed-span carrier.
    simpa [E, s, t, B] using effectiveDomain_productGraphOwners_subset_restrictedCarrier_l2 U V
  have hfB_eq_ambient (x : B) :
      (fB x : EReal) =
        (((t∗[ht]) (((x : B) : E)) : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- On subtype points, restricting before conjugating agrees with ambient conjugation.
    simpa [fB, tB] using
      restrictedConjugate_eq_ambientConjugate_on_subtype_local
        t hdom_subset.2 x
  have hgB_eq_ambient (x : B) :
      (gB x : EReal) =
        (((s∗[hs]) (((x : B) : E)) : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- The same restriction rewrite works for the slice conjugate.
    simpa [gB, sB] using
      restrictedConjugate_eq_ambientConjugate_on_subtype_local
        s hdom_subset.1 x
  have hfB_star_eq_tB :
      (fB∗[hfB]) = tB := by
    -- Biconjugation recovers the restricted graph-plus-quadratic owner.
    funext x
    apply Subtype.ext
    simpa [fB, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero htB) x
  have hgB_star_eq_sB :
      (gB∗[hgB]) = sB := by
    -- The restricted slice owner is the biconjugate of its conjugate witness.
    funext x
    apply Subtype.ext
    simpa [gB, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hsB) x
  have hraw_top :
      ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal) uB) = ⊤ := by
    -- If the restricted raw dual infimal convolution were finite, its finite decomposition would
    -- lift to an ambient finite decomposition, contradicting the packaged bad point.
    by_contra hne
    have huB_lt : ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal) uB) < ⊤ := by
      exact lt_top_iff_ne_top.mpr hne
    have huB_dom :
        uB ∈ dom ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal)) := by
      rw [mem_dom_iff]
      exact huB_lt
    rw [dom_infimalConvolution_eq_effectiveDomain_add] at huB_dom
    rcases Set.mem_add.mp huB_dom with ⟨y, hy, z, hz, hyz⟩
    have hy_tB : y ∈ effectiveDomain tB := by
      simpa [hfB_star_eq_tB, mem_effectiveDomain_iff] using hy
    have hz_sB : z ∈ effectiveDomain sB := by
      simpa [hgB_star_eq_sB, mem_effectiveDomain_iff] using hz
    have hy_t : ((y : B) : E) ∈ effectiveDomain t := by
      simpa [tB, mem_effectiveDomain_iff] using hy_tB
    have hz_s : ((z : B) : E) ∈ effectiveDomain s := by
      simpa [sB, mem_effectiveDomain_iff] using hz_sB
    have hu_ambient_dom :
        (((0 : L2Nat), u0) : E) ∈ dom (((t □ s) : E → EReal)) := by
      rw [dom_infimalConvolution_eq_effectiveDomain_add]
      refine Set.mem_add.2 ?_
      refine ⟨((y : B) : E), hy_t, ((z : B) : E), hz_s, ?_⟩
      exact congrArg (fun w : B ↦ ((w : B) : E)) hyz
    have hu_ambient_lt : (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E)) < ⊤ := by
      rw [mem_dom_iff] at hu_ambient_dom
      exact hu_ambient_dom
    have hraw_bad :
        (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E)) = ⊤ := by
      calc
        (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E))
            = (((s □ t) : E → EReal) (((0 : L2Nat), u0) : E)) := by
                simpa using congrFun (infimalConvolution_comm_ioi t s) ((((0 : L2Nat), u0) : E))
        _ = ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) := by
              simpa [E, s, t] using
                horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V
                  ((((0 : L2Nat), u0) : E))
        _ = ⊤ := by
              have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
              rw [projectedImageRawOwner]
              rw [show
                  (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u0 : EReal) = ⊤ by
                simp [indicator_apply, hu0_not_mem]]
              simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
    exact (ne_of_lt hu_ambient_lt) hraw_bad
  have hconj_finite :
      (fB + gB).asEReal∗ uB < ⊤ := by
    -- Route correction: first prove finiteness on the ambient product witness at `((0), u0)`,
    -- then descend that bound to the restricted carrier by comparing conjugates on subtype points.
    have hs_nonneg : ∀ x : E, (0 : EReal) ≤ (s x : EReal) := by
      intro x
      by_cases hx : x ∈ horizontalOrthogonalSliceSet U
      · simp [s, indicator_apply, hx]
      · simp [s, indicator_apply, hx]
    have ht_nonneg : ∀ x : E, (0 : EReal) ≤ (t x : EReal) := by
      intro x
      by_cases hx : x ∈ projectedImageGraphSet U V
      · -- On the graph, only the quadratic tail remains.
        rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = 0 by
          simp [indicator_apply, hx]]
        positivity
      · -- Off the graph, the indicator contributes `⊤`, so the total value is still nonnegative.
        have hhalf_ne_bot : (halfSquaredNorm x.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x.2).2
        rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = ⊤ by
          simp [indicator_apply, hx]]
        rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
        simp [t]
    have hs_conj_zero : (0 : E) ∈ effectiveDomain (s∗[hs]) := by
      -- Nonnegativity plus the zero value at the origin make the slice conjugate finite at `0`.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          hs hs_nonneg hs_zero
    have ht_conj_zero : (0 : E) ∈ effectiveDomain (t∗[ht]) := by
      -- The same origin test applies to the graph-plus-quadratic conjugate.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          ht ht_nonneg ht_zero
    have hdom_conj :
        (effectiveDomain (t∗[ht]) ∩ effectiveDomain (s∗[hs])).Nonempty := by
      -- Both ambient conjugate witnesses are finite at the product-space origin.
      exact ⟨0, ht_conj_zero, hs_conj_zero⟩
    have hf_ambient : (t∗[ht]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero ht
    have hg_ambient : (s∗[hs]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hs
    have ht_star_eq :
        ((t∗[ht])∗[hf_ambient]) = t := by
      -- Biconjugation recovers the original ambient graph-plus-quadratic owner.
      funext x
      apply Subtype.ext
      simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero ht) x
    have hs_star_eq :
        ((s∗[hs])∗[hg_ambient]) = s := by
      -- The same biconjugation rewrite recovers the ambient slice indicator.
      funext x
      apply Subtype.ext
      simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hs) x
    have hraw_snd :
        ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) =
          fun p : E ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
      funext p
      calc
        ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) p
            = (((t □ s) : E → EReal) p) := by
                rw [ht_star_eq, hs_star_eq]
        _ = (((s □ t) : E → EReal) p) := by
              simpa using congrFun (infimalConvolution_comm_ioi t s) p
        _ = ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
              simpa [E, s, t] using
                horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V p
    have hambient_pullback :
        ((t∗[ht]) + (s∗[hs])).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
      -- Proposition 15.1 rewrites the ambient conjugate sum to the envelope of the normalized raw
      -- projected-image owner.
      exact
        conjugatePointwiseAdd_eq_secondCoordinateEnvelopePullback_l2
          U V (t∗[ht]) (s∗[hs]) hf_ambient hg_ambient hdom_conj hraw_snd
    have hambient_env_finite :
        lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
            (((0 : L2Nat), u0) : E) < ⊤ := by
      let A : Set (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
      let q : orthogonalClosedSubmodule U → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
      have hcont_q : Continuous q := by
        have hnorm_sq : Continuous fun x : orthogonalClosedSubmodule U ↦ ‖x‖ ^ 2 := by
          simpa using
            (continuous_norm.pow 2 :
              Continuous fun x : orthogonalClosedSubmodule U ↦ ‖x‖ ^ 2)
        -- The quadratic graph is continuous, so closure points of the projected image stay closure
        -- points after adding the real height `‖x‖² / 2`.
        simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
          (continuous_const.mul hnorm_sq :
            Continuous fun x : orthogonalClosedSubmodule U ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
      have hgraph_closure :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            closure ((fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' A) := by
        have hu0_image :
            ((((0 : L2Nat), u0) : E), q u0) ∈
              (fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' closure A := by
          exact ⟨u0, hu0_closure, rfl⟩
        have hcont_graph :
            Continuous fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x) := by
          exact (continuous_const.prod_mk continuous_id).prodMk hcont_q
        -- Push the closure witness for `u0` through the product-space quadratic graph.
        exact image_closure_subset_closure_image hcont_graph hu0_image
      have hgraph_subset :
          (fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' A ⊆
            epigraph
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
        rintro _ ⟨x, hxA, rfl⟩
        rw [mem_epigraph_iff]
        -- On the projected image, the pullback owner is exactly the quadratic tail.
        rw [projectedImageRawOwner]
        change
          (ι[(A : Set (orthogonalClosedSubmodule U))] x : EReal) +
              (halfSquaredNorm x : EReal) ≤
            ((q x : ℝ) : EReal)
        rw [show (ι[(A : Set (orthogonalClosedSubmodule U))] x : EReal) = 0 by
          simp [indicator_apply, hxA]]
        rw [halfSquaredNorm_apply]
        simpa [q]
      have hraw_epi :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            closure
              (epigraph
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
        closure_mono hgraph_subset hgraph_closure
      have henv_epi :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            epigraph
              (lowerSemicontinuousConvexEnvelope
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
        have hepi_eq :
            epigraph
                (lowerSemicontinuousConvexEnvelope
                  (fun p : E ↦
                    ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) =
              closure
                (convexHull ℝ
                  (epigraph
                    (fun p : E ↦
                      ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
          exact
            epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
              (H := E)
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
        have hclosure_convexHull :
            ((((0 : L2Nat), u0) : E), q u0) ∈
              closure
                (convexHull ℝ
                  (epigraph
                    (fun p : E ↦
                      ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
          closure_mono
            (subset_convexHull ℝ
              (epigraph
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
            hraw_epi
        rw [hepi_eq]
        exact hclosure_convexHull
      have henv_le :
          lowerSemicontinuousConvexEnvelope
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
              (((0 : L2Nat), u0) : E) ≤
            ((q u0 : ℝ) : EReal) := by
        exact (mem_epigraph_iff _ _ _).mp henv_epi
      -- The real graph height bounds the ambient envelope value by a finite number.
      exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
    have hambient_finite :
        ((t∗[ht]) + (s∗[hs])).asEReal∗ (((0 : L2Nat), u0) : E) < ⊤ := by
      -- Repackage the finite envelope bound as finiteness of the ambient conjugate sum.
      simpa [hambient_pullback] using hambient_env_finite
    have hsum_restrict :
        (fun x : (B : Submodule ℝ E) ↦ (((t∗[ht]) + (s∗[hs])) x)) = fB + gB := by
      funext x
      apply Subtype.ext
      simp [pointwiseAdd_apply, hfB_eq_ambient x, hgB_eq_ambient x]
    have hrestrict_le :
        (fB + gB).asEReal∗ uB ≤ ((t∗[ht]) + (s∗[hs])).asEReal∗ ((uB : B) : E) := by
      -- Restricting the ambient sum to the closed carrier can only decrease its conjugate.
      simpa [hsum_restrict] using
        (restrictedConjugate_le_ambientConjugate_on_subtype_local
          (f := (t∗[ht]) + (s∗[hs])) (v := uB))
    -- Compare the restricted conjugate to the already finite ambient value at the same bad point.
    exact lt_of_le_of_lt hrestrict_le (by simpa [uB] using hambient_finite)
  exact ⟨B, inferInstance, inferInstance, inferInstance, fB, gB, hfB, hgB, uB,
    ⟨0, hfB_zero, hgB_zero⟩, hconj_finite, hraw_top⟩

/-- Helper for Remark 16.46: the live frontier has been reduced to one same-space witness package
on `Uᗮ`, namely a `Γ₀` pair whose raw dual infimal convolution is `projectedImageRawOwner U V`
and which already satisfies the Chapter 16 sum rule. The pointwise bad-point obstruction data are
packaged separately and consumed by the wrapper below. -/
private theorem existsProjectedImageSameSpaceWitnessSkeleton_l2 :
    ∃ (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat))
      (u0 : orthogonalClosedSubmodule U)
      (fK gK : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal))
      (hfK : fK ∈ Γ₀(orthogonalClosedSubmodule U))
      (hgK : gK ∈ Γ₀(orthogonalClosedSubmodule U)),
      (effectiveDomain fK ∩ effectiveDomain gK).Nonempty ∧
        ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  rcases orthogonalGraphSameSpaceWitnessPair_l2 U V hV_closed with
    ⟨fK, gK, hfK, hgK, hdom⟩
  have hgap :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ ∧
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤ :=
    -- Keep the geometric bad-point data explicit at the same `U,V,u0` used for the same-space
    -- witness pair, so the remaining blocker is only the structural witness package.
    projectedImageRawOwnerGapData_of_badPoint_l2 U V u0 hu0_closure hu0_not_mem
  exact ⟨U, V, hV_closed, u0, fK, gK, hfK, hgK, hdom, hgap.1, hgap.2⟩

/-- Helper for Remark 16.46: additive subgradients always give a subgradient of the pointwise
sum by specializing Proposition 16.6 to the identity map. -/
private theorem mem_subdifferential_pointwiseAdd_of_mem_add_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : H → Set.Ioi (⊥ : EReal)} {x u : H}
    (hu : u ∈ ((∂ f) + ∂ g) x) :
    u ∈ (∂ (f + g)) x := by
  -- Proposition 16.6 gives the easy inclusion once the linear map is the identity.
  have hu_id :
      u ∈ (∂ f) x +
        ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g x := by
    simpa [ContinuousLinearMap.adjointImageSubdifferential] using hu
  simpa [Function.comp] using
    (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
      f g (ContinuousLinearMap.id ℝ H) x hu_id)

/-- Helper for Remark 16.46: route correction. The orthogonal-graph raw-top target is false under
the current normal forms, so the live wrapper now reuses the already proved restricted closed-span
gap package and isolates the remaining blocker as the forward sum-rule inclusion on that carrier. -/
private theorem existsProjectedImageSameSpaceWitnessCore_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  rcases projectedImageBadPointData_l2 with
    ⟨U, V, _hU_closed, hV_closed, u0, hu0_closure, hu0_not_mem⟩
  let E := L2Nat × orthogonalClosedSubmodule U
  let s : E → Set.Ioi (⊥ : EReal) := ι[horizontalOrthogonalSliceSet U]
  let t : E → Set.Ioi (⊥ : EReal) := fun p ↦
    (ι[projectedImageGraphSet U V] p : Set.Ioi (⊥ : EReal)) + halfSquaredNorm p.2
  let B : ClosedSubmodule ℝ E := subImageDifferenceClosedSpan s t (ContinuousLinearMap.id ℝ E)
  letI : CompleteSpace B := subImageDifferenceClosedSpan_completeSpace s t (ContinuousLinearMap.id ℝ E)
  have hs : s ∈ Γ₀(E) := by
    -- Reuse the packaged `Γ₀` structure of the horizontal slice.
    simpa [E, s] using horizontalOrthogonalSliceIndicator_mem_gammaZero_l2 U
  have ht_graph :
      (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∈ Γ₀(E) := by
    -- Closedness of `V` makes the projected-image graph owner a `Γ₀` function.
    simpa [E] using projectedImageGraphIndicator_mem_gammaZero_l2 U V hV_closed
  have ht_half :
      (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal))) ∈ Γ₀(E) := by
    -- The quadratic tail is the standard second-coordinate `Γ₀` owner.
    simpa [E] using secondCoordinateHalfSquaredNorm_mem_gammaZero_l2 U
  have ht_dom :
      (effectiveDomain (ι[projectedImageGraphSet U V] : E → Set.Ioi (⊥ : EReal)) ∩
          effectiveDomain (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))).Nonempty := by
    -- The origin is a common finite point of the graph indicator and the quadratic tail.
    refine ⟨(0, 0), ?_, ?_⟩
    · simp [mem_effectiveDomain_iff, projectedImageGraphSet]
    · rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  have ht : t ∈ Γ₀(E) := by
    -- Adding the quadratic tail preserves the `Γ₀` structure on the graph owner.
    exact
      pointwiseAdd_mem_gammaZero
        (ι[projectedImageGraphSet U V])
        (fun p : E ↦ (halfSquaredNorm p.2 : Set.Ioi (⊥ : EReal)))
        ht_graph ht_half ht_dom
  have hs_zero : (0 : E) ∈ effectiveDomain s := by
    -- The horizontal slice contains the ambient origin.
    simp [s, mem_effectiveDomain_iff, horizontalOrthogonalSliceSet, linearGraphSet,
      LinearMap.mem_graph_iff, indicator_apply]
  have ht_zero : (0 : E) ∈ effectiveDomain t := by
    -- The graph-plus-quadratic owner is also finite at the origin.
    simp [t, mem_effectiveDomain_iff, projectedImageGraphSet, halfSquaredNorm_apply]
  let sB : B → Set.Ioi (⊥ : EReal) := fun x ↦ s x
  let tB : B → Set.Ioi (⊥ : EReal) := fun x ↦ t x
  have hsB : sB ∈ Γ₀(B) := by
    -- Restrict the slice owner to the exact closed-span carrier.
    simpa [sB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain s hs hs_zero B
  have htB : tB ∈ Γ₀(B) := by
    -- Restrict the graph-plus-quadratic owner to the same carrier.
    simpa [tB, B, subImageDifferenceClosedSpan] using
      restrict_mem_gammaZero_of_zero_mem_effectiveDomain t ht ht_zero B
  let fB : B → Set.Ioi (⊥ : EReal) := tB∗[htB]
  let gB : B → Set.Ioi (⊥ : EReal) := sB∗[hsB]
  have hfB : fB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero htB
  have hgB : gB ∈ Γ₀(B) := gammaZeroConjugate_mem_gammaZero hsB
  have hsB_nonneg : ∀ x : B, (0 : EReal) ≤ (sB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ horizontalOrthogonalSliceSet U
    · simp [sB, s, indicator_apply, hx]
    · simp [sB, s, indicator_apply, hx]
  have htB_nonneg : ∀ x : B, (0 : EReal) ≤ (tB x : EReal) := by
    intro x
    by_cases hx : ((x : B) : E) ∈ projectedImageGraphSet U V
    · rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = 0 by
        simp [indicator_apply, hx]]
      positivity
    · have hhalf_ne_bot : (halfSquaredNorm (((x : B) : E).2) : EReal) ≠ ⊥ :=
        ne_of_gt (halfSquaredNorm (((x : B) : E).2)).2
      rw [show
          (ι[projectedImageGraphSet U V] (((x : B) : E)) : EReal) = ⊤ by
        simp [indicator_apply, hx]]
      rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
      simp [tB, t]
  have hsB_zero : (sB 0 : EReal) = 0 := by
    -- Restricting to the carrier keeps the slice value `0` at the origin.
    simp [sB, s, horizontalOrthogonalSliceSet, linearGraphSet, LinearMap.mem_graph_iff, indicator_apply]
  have htB_zero : (tB 0 : EReal) = 0 := by
    -- The restricted graph owner still vanishes at the origin.
    simp [tB, t, projectedImageGraphSet, halfSquaredNorm_apply]
  have hfB_zero : (0 : B) ∈ effectiveDomain fB := by
    -- A nonnegative owner with value `0` at the origin has finite conjugate there.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        htB htB_nonneg htB_zero
  have hgB_zero : (0 : B) ∈ effectiveDomain gB := by
    -- The same origin test works for the restricted slice owner.
    exact
      zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
        hsB hsB_nonneg hsB_zero
  let uB : B := ⟨(((0 : L2Nat), u0) : E), badVerticalPoint_mem_restrictedCarrier_l2 U V hu0_closure⟩
  have hdom_subset : effectiveDomain s ⊆ (B : Set E) ∧ effectiveDomain t ⊆ (B : Set E) := by
    -- Both ambient effective domains already lie in the exact closed-span carrier.
    simpa [E, s, t, B] using effectiveDomain_productGraphOwners_subset_restrictedCarrier_l2 U V
  have hfB_eq_ambient (x : B) :
      (fB x : EReal) =
        (((t∗[ht]) (((x : B) : E)) : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- On subtype points, restricting before conjugating agrees with ambient conjugation.
    simpa [fB, tB] using
      restrictedConjugate_eq_ambientConjugate_on_subtype_local
        t hdom_subset.2 x
  have hgB_eq_ambient (x : B) :
      (gB x : EReal) =
        (((s∗[hs]) (((x : B) : E)) : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- The same restriction rewrite works for the slice conjugate.
    simpa [gB, sB] using
      restrictedConjugate_eq_ambientConjugate_on_subtype_local
        s hdom_subset.1 x
  have hfB_star_eq_tB :
      (fB∗[hfB]) = tB := by
    -- Biconjugation recovers the restricted graph-plus-quadratic owner.
    funext x
    apply Subtype.ext
    simpa [fB, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero htB) x
  have hgB_star_eq_sB :
      (gB∗[hgB]) = sB := by
    -- The restricted slice owner is the biconjugate of its conjugate witness.
    funext x
    apply Subtype.ext
    simpa [gB, gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hsB) x
  have hraw_top :
      ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal) uB) = ⊤ := by
    -- If the restricted raw dual infimal convolution were finite, its finite decomposition would
    -- lift to an ambient finite decomposition, contradicting the packaged bad point.
    by_contra hne
    have huB_lt : ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal) uB) < ⊤ := by
      exact lt_top_iff_ne_top.mpr hne
    have huB_dom :
        uB ∈ dom ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal)) := by
      rw [mem_dom_iff]
      exact huB_lt
    rw [dom_infimalConvolution_eq_effectiveDomain_add] at huB_dom
    rcases Set.mem_add.mp huB_dom with ⟨y, hy, z, hz, hyz⟩
    have hy_tB : y ∈ effectiveDomain tB := by
      simpa [hfB_star_eq_tB, mem_effectiveDomain_iff] using hy
    have hz_sB : z ∈ effectiveDomain sB := by
      simpa [hgB_star_eq_sB, mem_effectiveDomain_iff] using hz
    have hy_t : ((y : B) : E) ∈ effectiveDomain t := by
      simpa [tB, mem_effectiveDomain_iff] using hy_tB
    have hz_s : ((z : B) : E) ∈ effectiveDomain s := by
      simpa [sB, mem_effectiveDomain_iff] using hz_sB
    have hu_ambient_dom :
        (((0 : L2Nat), u0) : E) ∈ dom (((t □ s) : E → EReal)) := by
      rw [dom_infimalConvolution_eq_effectiveDomain_add]
      refine Set.mem_add.2 ?_
      refine ⟨((y : B) : E), hy_t, ((z : B) : E), hz_s, ?_⟩
      exact congrArg (fun w : B ↦ ((w : B) : E)) hyz
    have hu_ambient_lt : (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E)) < ⊤ := by
      rw [mem_dom_iff] at hu_ambient_dom
      exact hu_ambient_dom
    have hraw_bad :
        (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E)) = ⊤ := by
      calc
        (((t □ s) : E → EReal) (((0 : L2Nat), u0) : E))
            = (((s □ t) : E → EReal) (((0 : L2Nat), u0) : E)) := by
                simpa using congrFun (infimalConvolution_comm_ioi t s) ((((0 : L2Nat), u0) : E))
        _ = ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) := by
              simpa [E, s, t] using
                horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V
                  ((((0 : L2Nat), u0) : E))
        _ = ⊤ := by
              have hhalf_ne_bot : (halfSquaredNorm u0 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm u0).2
              rw [projectedImageRawOwner]
              rw [show
                  (ι[(projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U))] u0 : EReal) = ⊤ by
                simp [indicator_apply, hu0_not_mem]]
              simpa using EReal.top_add_of_ne_bot hhalf_ne_bot
    exact (ne_of_lt hu_ambient_lt) hraw_bad
  have hconj_finite :
      (fB + gB).asEReal∗ uB < ⊤ := by
    -- Route correction: first prove finiteness on the ambient product witness at `((0), u0)`,
    -- then descend that bound to the restricted carrier by comparing conjugates on subtype points.
    have hs_nonneg : ∀ x : E, (0 : EReal) ≤ (s x : EReal) := by
      intro x
      by_cases hx : x ∈ horizontalOrthogonalSliceSet U
      · simp [s, indicator_apply, hx]
      · simp [s, indicator_apply, hx]
    have ht_nonneg : ∀ x : E, (0 : EReal) ≤ (t x : EReal) := by
      intro x
      by_cases hx : x ∈ projectedImageGraphSet U V
      · rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = 0 by
          simp [indicator_apply, hx]]
        positivity
      · have hhalf_ne_bot : (halfSquaredNorm x.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x.2).2
        rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = ⊤ by
          simp [indicator_apply, hx]]
        rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
        simp [t]
    have hs_conj_zero : (0 : E) ∈ effectiveDomain (s∗[hs]) := by
      -- Nonnegativity plus the zero value at the origin make the slice conjugate finite at `0`.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          hs hs_nonneg hs_zero
    have ht_conj_zero : (0 : E) ∈ effectiveDomain (t∗[ht]) := by
      -- The same origin test applies to the graph-plus-quadratic conjugate.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          ht ht_nonneg ht_zero
    have hdom_conj :
        (effectiveDomain (t∗[ht]) ∩ effectiveDomain (s∗[hs])).Nonempty := by
      -- Both ambient conjugate witnesses are finite at the product-space origin.
      exact ⟨0, ht_conj_zero, hs_conj_zero⟩
    have hf_ambient : (t∗[ht]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero ht
    have hg_ambient : (s∗[hs]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hs
    have ht_star_eq :
        ((t∗[ht])∗[hf_ambient]) = t := by
      -- Biconjugation recovers the original ambient graph-plus-quadratic owner.
      funext x
      apply Subtype.ext
      simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero ht) x
    have hs_star_eq :
        ((s∗[hs])∗[hg_ambient]) = s := by
      -- The same biconjugation rewrite recovers the ambient slice indicator.
      funext x
      apply Subtype.ext
      simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hs) x
    have hraw_snd :
        ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) =
          fun p : E ↦
            ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
      funext p
      calc
        ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) p
            = (((t □ s) : E → EReal) p) := by
                rw [ht_star_eq, hs_star_eq]
        _ = (((s □ t) : E → EReal) p) := by
              simpa using congrFun (infimalConvolution_comm_ioi t s) p
        _ = ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
              simpa [E, s, t] using
                horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V p
    have hambient_pullback :
        ((t∗[ht]) + (s∗[hs])).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
      -- Proposition 15.1 rewrites the ambient conjugate sum to the envelope of the normalized raw
      -- projected-image owner.
      exact
        conjugatePointwiseAdd_eq_secondCoordinateEnvelopePullback_l2
          U V (t∗[ht]) (s∗[hs]) hf_ambient hg_ambient hdom_conj hraw_snd
    have hambient_env_finite :
        lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
            (((0 : L2Nat), u0) : E) < ⊤ := by
      let A : Set (orthogonalClosedSubmodule U) := projectedImageSubmodule U V
      let q : orthogonalClosedSubmodule U → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
      have hcont_q : Continuous q := by
        have hnorm_sq : Continuous fun x : orthogonalClosedSubmodule U ↦ ‖x‖ ^ 2 := by
          simpa using
            (continuous_norm.pow 2 :
              Continuous fun x : orthogonalClosedSubmodule U ↦ ‖x‖ ^ 2)
        -- The quadratic graph is continuous, so closure points of the projected image stay closure
        -- points after adding the real height `‖x‖² / 2`.
        simpa [q, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
          (continuous_const.mul hnorm_sq :
            Continuous fun x : orthogonalClosedSubmodule U ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
      have hgraph_closure :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            closure ((fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' A) := by
        have hu0_image :
            ((((0 : L2Nat), u0) : E), q u0) ∈
              (fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' closure A := by
          exact ⟨u0, hu0_closure, rfl⟩
        have hcont_graph :
            Continuous fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x) := by
          exact (continuous_const.prod_mk continuous_id).prodMk hcont_q
        -- Push the closure witness for `u0` through the product-space quadratic graph.
        exact image_closure_subset_closure_image hcont_graph hu0_image
      have hgraph_subset :
          (fun x : orthogonalClosedSubmodule U ↦ (((0 : L2Nat), x), q x)) '' A ⊆
            epigraph
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
        rintro _ ⟨x, hxA, rfl⟩
        rw [mem_epigraph_iff]
        -- On the projected image, the pullback owner is exactly the quadratic tail.
        rw [projectedImageRawOwner]
        change
          (ι[(A : Set (orthogonalClosedSubmodule U))] x : EReal) +
              (halfSquaredNorm x : EReal) ≤
            ((q x : ℝ) : EReal)
        rw [show (ι[(A : Set (orthogonalClosedSubmodule U))] x : EReal) = 0 by
          simp [indicator_apply, hxA]]
        rw [halfSquaredNorm_apply]
        simpa [q]
      have hraw_epi :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            closure
              (epigraph
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
        closure_mono hgraph_subset hgraph_closure
      have henv_epi :
          ((((0 : L2Nat), u0) : E), q u0) ∈
            epigraph
              (lowerSemicontinuousConvexEnvelope
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
        have hepi_eq :
            epigraph
                (lowerSemicontinuousConvexEnvelope
                  (fun p : E ↦
                    ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) =
              closure
                (convexHull ℝ
                  (epigraph
                    (fun p : E ↦
                      ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) := by
          exact
            epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
              (H := E)
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
        have hclosure_convexHull :
            ((((0 : L2Nat), u0) : E), q u0) ∈
              closure
                (convexHull ℝ
                  (epigraph
                    (fun p : E ↦
                      ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))) :=
          closure_mono
            (subset_convexHull ℝ
              (epigraph
                (fun p : E ↦
                  ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)))
            hraw_epi
        rw [hepi_eq]
        exact hclosure_convexHull
      have henv_le :
          lowerSemicontinuousConvexEnvelope
              (fun p : E ↦
                ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal))
              (((0 : L2Nat), u0) : E) ≤
            ((q u0 : ℝ) : EReal) := by
        exact (mem_epigraph_iff _ _ _).mp henv_epi
      -- The real graph height bounds the ambient envelope value by a finite number.
      exact lt_of_le_of_lt henv_le (EReal.coe_lt_top _)
    have hambient_finite :
        ((t∗[ht]) + (s∗[hs])).asEReal∗ (((0 : L2Nat), u0) : E) < ⊤ := by
      -- Repackage the finite envelope bound as finiteness of the ambient conjugate sum.
      simpa [hambient_pullback] using hambient_env_finite
    have hsum_restrict :
        (fun x : (B : Submodule ℝ E) ↦ (((t∗[ht]) + (s∗[hs])) x)) = fB + gB := by
      funext x
      apply Subtype.ext
      simp [pointwiseAdd_apply, hfB_eq_ambient x, hgB_eq_ambient x]
    have hrestrict_le :
        (fB + gB).asEReal∗ uB ≤ ((t∗[ht]) + (s∗[hs])).asEReal∗ ((uB : B) : E) := by
      -- Restricting the ambient sum to the closed carrier can only decrease its conjugate.
      simpa [hsum_restrict] using
        (restrictedConjugate_le_ambientConjugate_on_subtype_local
          (f := (t∗[ht]) + (s∗[hs])) (v := uB))
    -- Compare the restricted conjugate to the already finite ambient value at the same bad point.
    exact lt_of_le_of_lt hrestrict_le (by simpa [uB] using hambient_finite)
  have hsub :
      (∂ (fB + gB) : SetValuedOperator B B) = ∂ fB + ∂ gB := by
    have hs_nonneg : ∀ x : E, (0 : EReal) ≤ (s x : EReal) := by
      intro x
      by_cases hx : x ∈ horizontalOrthogonalSliceSet U
      · simp [s, indicator_apply, hx]
      · simp [s, indicator_apply, hx]
    have ht_nonneg : ∀ x : E, (0 : EReal) ≤ (t x : EReal) := by
      intro x
      by_cases hx : x ∈ projectedImageGraphSet U V
      · rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = 0 by
          simp [indicator_apply, hx]]
        positivity
      · have hhalf_ne_bot : (halfSquaredNorm x.2 : EReal) ≠ ⊥ := ne_of_gt (halfSquaredNorm x.2).2
        rw [show
            (ι[projectedImageGraphSet U V] x : EReal) = ⊤ by
          simp [indicator_apply, hx]]
        rw [EReal.top_add_of_ne_bot hhalf_ne_bot]
        simp [t]
    have hs_conj_zero : (0 : E) ∈ effectiveDomain (s∗[hs]) := by
      -- Nonnegativity plus the zero value at the origin make the slice conjugate finite at `0`.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          hs hs_nonneg hs_zero
    have ht_conj_zero : (0 : E) ∈ effectiveDomain (t∗[ht]) := by
      -- The same origin test applies to the graph-plus-quadratic conjugate.
      exact
        zero_mem_effectiveDomain_gammaZeroConjugate_of_nonneg_zero
          ht ht_nonneg ht_zero
    have hdom_conj :
        (effectiveDomain (t∗[ht]) ∩ effectiveDomain (s∗[hs])).Nonempty := by
      -- Both ambient conjugate witnesses are finite at the product-space origin.
      exact ⟨0, ht_conj_zero, hs_conj_zero⟩
    have hf_ambient : (t∗[ht]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero ht
    have hg_ambient : (s∗[hs]) ∈ Γ₀(E) := gammaZeroConjugate_mem_gammaZero hs
    have hambient_pullback :
        ((t∗[ht]) + (s∗[hs])).asEReal∗ =
          lowerSemicontinuousConvexEnvelope
            (fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
      have ht_star_eq :
          ((t∗[ht])∗[hf_ambient]) = t := by
        -- Biconjugation recovers the original ambient graph-plus-quadratic owner.
        funext x
        apply Subtype.ext
        simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero ht) x
      have hs_star_eq :
          ((s∗[hs])∗[hg_ambient]) = s := by
        -- The same biconjugation rewrite recovers the ambient slice indicator.
        funext x
        apply Subtype.ext
        simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hs) x
      have hraw_snd :
          ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) =
            fun p : E ↦
              ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
        funext p
        calc
          ((((t∗[ht])∗[hf_ambient]) □ ((s∗[hs])∗[hg_ambient])) : E → EReal) p
              = (((t □ s) : E → EReal) p) := by
                  rw [ht_star_eq, hs_star_eq]
          _ = (((s □ t) : E → EReal) p) := by
                simpa using congrFun (infimalConvolution_comm_ioi t s) p
          _ = ((projectedImageRawOwner U V p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
                simpa [E, s, t] using
                  horizontalSliceRawInfimalConvolution_eq_projectedImageRawOwner_snd_l2 U V p
      -- Reuse the same envelope normalization on the ambient product model.
      exact
        conjugatePointwiseAdd_eq_secondCoordinateEnvelopePullback_l2
          U V (t∗[ht]) (s∗[hs]) hf_ambient hg_ambient hdom_conj hraw_snd
    have hsum_restrict :
        (fun x : (B : Submodule ℝ E) ↦ (((t∗[ht]) + (s∗[hs])) x)) = fB + gB := by
      funext x
      apply Subtype.ext
      simp [pointwiseAdd_apply, hfB_eq_ambient x, hgB_eq_ambient x]
    have ht_proj :
        (t∗[ht]).asEReal = (t∗[ht]).asEReal ∘ B.starProjection := by
      funext z
      have hrestrict :
          ((fun x : (B : Submodule ℝ E) ↦ t x).asEReal∗) (B.orthogonalProjection z) =
            t.asEReal∗ z := by
        simpa [Function.comp] using
          congrFun
            (conjugate_restrict_comp_orthogonalProjection_of_dom_subset t.asEReal B hdom_subset.2) z
      have hrestrict_proj :
          ((fun x : (B : Submodule ℝ E) ↦ t x).asEReal∗) (B.orthogonalProjection z) =
            t.asEReal∗ (B.starProjection z) := by
        simpa using
          restrictedConjugate_eq_ambientConjugate_on_subtype_local
            t hdom_subset.2 (B.orthogonalProjection z)
      exact hrestrict.symm.trans hrestrict_proj
    have hs_proj :
        (s∗[hs]).asEReal = (s∗[hs]).asEReal ∘ B.starProjection := by
      funext z
      have hrestrict :
          ((fun x : (B : Submodule ℝ E) ↦ s x).asEReal∗) (B.orthogonalProjection z) =
            s.asEReal∗ z := by
        simpa [Function.comp] using
          congrFun
            (conjugate_restrict_comp_orthogonalProjection_of_dom_subset s.asEReal B hdom_subset.1) z
      have hrestrict_proj :
          ((fun x : (B : Submodule ℝ E) ↦ s x).asEReal∗) (B.orthogonalProjection z) =
            s.asEReal∗ (B.starProjection z) := by
        simpa using
          restrictedConjugate_eq_ambientConjugate_on_subtype_local
            s hdom_subset.1 (B.orthogonalProjection z)
      exact hrestrict.symm.trans hrestrict_proj
    have hsum_proj :
        (((t∗[ht]) + (s∗[hs])) : E → Set.Ioi (⊥ : EReal)).asEReal =
          (((t∗[ht]) + (s∗[hs])) : E → Set.Ioi (⊥ : EReal)).asEReal ∘ B.starProjection := by
      funext z
      simp [pointwiseAdd_apply, Function.comp, ht_proj, hs_proj]
    have hsupport :
        ∀ {x v : B}, v ∈ (∂ (fB + gB)) x →
          (((x : B) : E).1 = 0 ∧ ((x : B) : E).2 = ((v : B) : E).2) := by
      intro x v hv
      have hv_restrict :
          v ∈
            (∂ (fun y : (B : Submodule ℝ E) ↦ (((t∗[ht]) + (s∗[hs])) y))) x := by
        simpa [hsum_restrict] using hv
      have hv_ambient :
          ((v : B) : E) ∈ (∂ ((t∗[ht]) + (s∗[hs]))) ((x : B) : E) := by
        -- Lift the restricted active point back to the ambient sum using star-projection
        -- invariance of the ambient conjugate witnesses.
        exact liftAmbientSubgradientOfRestrictedCarrier_local hsum_proj hv_restrict
      rcases
          productGraphWitnessClosureSupport_of_mem_subdifferential_l2
            U V hV_closed hf_ambient hg_ambient hdom_conj hambient_pullback hv_ambient with
        ⟨hx1, hv2_closure, hx2_subv2_orth⟩
      let W : Submodule ℝ (orthogonalClosedSubmodule U) :=
        (projectedImageSubmodule U V).topologicalClosure
      have hx2_closure :
          ((x : B) : E).2 ∈ closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
        simpa using
          (mem_restrictedCarrier_iff_snd_mem_projectedImageClosure_l2
            (U := U) (V := V)).1 x.2
      have hdiff_closure :
          ((x : B) : E).2 - ((v : B) : E).2 ∈
            closure (projectedImageSubmodule U V : Set (orthogonalClosedSubmodule U)) := by
        have hxW : ((x : B) : E).2 ∈ W := by
          simpa [W, Submodule.topologicalClosure_coe] using hx2_closure
        have hvW : ((v : B) : E).2 ∈ W := by
          simpa [W, Submodule.topologicalClosure_coe] using hv2_closure
        have hdiffW : ((x : B) : E).2 - ((v : B) : E).2 ∈ W := W.sub_mem hxW hvW
        simpa [W, Submodule.topologicalClosure_coe] using hdiffW
      have hdiff_zero :
          ((x : B) : E).2 - ((v : B) : E).2 = 0 :=
        projectedImageClosurePoint_eq_zero_of_mem_orthogonal_l2
          U V hdiff_closure hx2_subv2_orth
      exact ⟨hx1, sub_eq_zero.mp hdiff_zero⟩
    ext x v
    constructor
    · intro hv
      have hactive := hsupport hv
      -- Route correction: the ambient lift and support collapse are now proved. The remaining
      -- blocker is to turn the normalized second coordinate `x.2 = v.2` into an actual
      -- projected-image witness `a ∈ V`, then use the explicit split
      -- `(v.1 + a, 0) + (-a, v.2) = v`.
      -- TODO: derive actual projected-image membership of `((v : B) : E).2` from the active
      -- restricted subgradient `hv`, then apply
      -- `mem_subdifferential_productGraphWitnessF_iff_l2` and
      -- `mem_subdifferential_productGraphWitnessG_of_projectedImageWitness`.
      sorry
    · intro hv
      -- The reverse inclusion is the standard easy branch from Proposition 16.6.
      exact mem_subdifferential_pointwiseAdd_of_mem_add_local hv
  have hu_dom :
      uB ∈ dom ((fB + gB).asEReal∗) := by
    -- Finite conjugate value is exactly domain membership.
    rw [mem_dom_iff]
    exact hconj_finite
  have hgap :
      (fB + gB).asEReal∗ uB ≠ ((((fB∗[hfB]) □ (gB∗[hgB])) : B → EReal) uB) := by
    -- The restricted closed-span witness keeps the conjugate finite while the raw dual value is
    -- forced to be `⊤`.
    intro hEq
    exact (ne_of_lt hconj_finite) (hEq.trans hraw_top)
  exact ⟨B, inferInstance, inferInstance, inferInstance, fB, gB, hfB, hgB, uB,
    ⟨0, hfB_zero, hgB_zero⟩, hsub, hu_dom, hgap⟩

/- Route correction for Remark 16.46: the stale closed-span carrier proof has been retired.
The remaining theorem is now only a wrapper that turns the smaller same-space core package into
the final existential counterexample using the generic projected-image packager proved earlier in
the file. -/
private theorem existsRestrictedProductGraphCounterexampleWithSumRule_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  exact existsProjectedImageSameSpaceWitnessCore_l2

/-- Helper for Remark 16.46: this wrapper now simply exposes the reduced same-space core through
the legacy theorem name used by the downstream alias chain. -/
private theorem existsOrthogonalGraphCounterexampleWithSumRule_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  exact existsRestrictedProductGraphCounterexampleWithSumRule_l2

/-- Helper for Remark 16.46: if the raw projected-image owner had a bad point with finite lower
semicontinuous convex envelope, then it could not itself belong to `Γ₀(Uᗮ)`. -/
private theorem projectedImageRawOwner_not_mem_gammaZero_of_badPoint_l2
    (U V : Submodule ℝ L2Nat) {u0 : orthogonalClosedSubmodule U}
    (hraw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤)
    (henv_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤) :
    projectedImageRawOwner U V ∉ Γ₀(orthogonalClosedSubmodule U) := by
  intro hraw_gamma
  have hdom_conj :
      (dom ((projectedImageRawOwner U V).asEReal∗)).Nonempty := by
    -- The conjugate of a `Γ₀` owner is again `Γ₀`, hence finite somewhere.
    rcases (gammaZeroConjugate_mem_gammaZero hraw_gamma).2.nonempty with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hy
  have henv_eq_biconj :
      (((projectedImageRawOwner U V).asEReal)∗∗) =
        lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) := by
    simpa using
      biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
        ((projectedImageRawOwner U V).asEReal) hdom_conj
  have hraw_eq_biconj :
      (((projectedImageRawOwner U V).asEReal)∗∗) =
        (projectedImageRawOwner U V).asEReal := by
    simpa using biconjugate_eq_of_mem_gammaZero hraw_gamma
  have henv_eq_raw :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 =
        ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- A `Γ₀` owner agrees with its own lower semicontinuous convex envelope pointwise.
    calc
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0
          = (((projectedImageRawOwner U V).asEReal)∗∗) u0 := by
              symm
              simpa using congrFun henv_eq_biconj u0
      _ = (projectedImageRawOwner U V).asEReal u0 := by
            simpa using congrFun hraw_eq_biconj u0
      _ = ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) := rfl
  -- Rewriting the bad point through the envelope equality contradicts finiteness.
  rw [henv_eq_raw, hraw_top] at henv_finite
  exact (lt_irrefl (⊤ : EReal)) henv_finite

/-- Helper for Remark 16.46: at a bad projected-image point, the raw owner cannot be the conjugate
of a single `Γ₀(Uᗮ)` owner. This rules out the collapsed zero-slice route. -/
private theorem projectedImageRawOwner_ne_gammaZeroConjugate_of_badPoint_l2
    (U V : Submodule ℝ L2Nat) {u0 : orthogonalClosedSubmodule U}
    (hraw_top :
      ((projectedImageRawOwner U V u0 : Set.Ioi (⊥ : EReal)) : EReal) = ⊤)
    (henv_finite :
      lowerSemicontinuousConvexEnvelope ((projectedImageRawOwner U V).asEReal) u0 < ⊤)
    {g : orthogonalClosedSubmodule U → Set.Ioi (⊥ : EReal)}
    (hg : g ∈ Γ₀(orthogonalClosedSubmodule U)) :
    (g∗[hg]) ≠ projectedImageRawOwner U V := by
  intro hEq
  have hraw_gamma : projectedImageRawOwner U V ∈ Γ₀(orthogonalClosedSubmodule U) := by
    simpa [hEq] using gammaZeroConjugate_mem_gammaZero hg
  exact
    projectedImageRawOwner_not_mem_gammaZero_of_badPoint_l2 U V hraw_top henv_finite hraw_gamma

/-- Helper for Remark 16.46: the old same-space `Uᗮ` witness package has been retired from the
active dependency chain after the proof pivot to the ambient product-space counterexample. -/
private theorem projectedImageCompositeSameSpaceWitnessPackage_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) : True := by
  let _ := U
  let _ := V
  let _ := hV_closed
  -- Route correction: the dead same-space descent remains only as a proved marker so the final
  -- theorem no longer depends on this retired branch.
  trivial

/-- Helper for Remark 16.46: the former same-space wrapper is also retired after the pivot to the
ambient product-space witness. -/
private theorem projectedImageComposite_toSameSpacePair_l2
    (U V : Submodule ℝ L2Nat) (hV_closed : IsClosed (V : Set L2Nat)) : True := by
  -- The wrapper now simply records that the retired same-space package is no longer needed.
  exact projectedImageCompositeSameSpaceWitnessPackage_l2 U V hV_closed

/-- Helper for Remark 16.46: the earlier reduced-space core is retired because the active proof
now packages the counterexample directly on the ambient product space. -/
private theorem existsProjectedImageSameSpaceCounterexampleCore_l2 :
    True := by
  -- Route correction: the direct ambient product-space package supersedes this same-space core.
  trivial

/-- Helper for Remark 16.46: the downstream exported theorem now factors through the reduced
same-space core wrapper above, rather than the retired ambient product-space branch. -/
private theorem existsReplacementAsymmetricCounterexampleCore_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  -- Route correction: the live frontier is again the same-space orthogonal-graph package, not the
  -- retired ambient product-space witness extraction route.
  exact existsOrthogonalGraphCounterexampleWithSumRule_l2

/-- Helper for Remark 16.46: the final existential now factors only through the replacement
ambient product-space core theorem. -/
private theorem existsRemark1646WitnessWithConjugateGap_l2 :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  -- The remaining work is exactly the replacement-core theorem above.
  exact existsReplacementAsymmetricCounterexampleCore_l2

/-- Helper for Remark 16.46: a replacement asymmetric witness should package the true missing
premise, namely a concrete `Γ₀` pair with intersecting domains, the Chapter 16 sum rule, and one
dual point where `(f + g)^*` differs from `f^* □ g^*`. -/
theorem existsRemark1646WitnessWithConjugateGap :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)) (u : K),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        u ∈ dom ((f + g).asEReal∗) ∧
        (f + g).asEReal∗ u ≠ ((((f∗[hf]) □ (g∗[hg])) : K → EReal) u) := by
  -- The local theorem packages the universe-lifted same-space witness once the single frontier
  -- theorem above is filled.
  exact existsRemark1646WitnessWithConjugateGap_l2

/-- Helper for Remark 16.46: package the final existential counterexample from the replacement
asymmetric witness family. -/
theorem existsAsymmetricCounterexampleDataFromRegularizedEpigraphPair :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        ¬ ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ K) := by
  -- The exported existential is now just a wrapper: once the replacement witness exposes a raw
  -- pointwise gap, the generic identity-map obstruction closes the nonexactness clause.
  rcases existsRemark1646WitnessWithConjugateGap with
    ⟨K, _, _, _, f, g, hf, hg, u, hdom, hsubdiff, _hu_dom, hgap⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, f, g, hf, hg, hdom, hsubdiff, ?_⟩
  exact notExactDualInfimalConvolutionFormulaId_of_conjugateGapAt hf hg hgap

/-- Remark 16.46 (3): there is a Hilbert-space counterexample showing that
`∂ (f + g) = ∂ f + ∂ g` does not imply the exact dual conjugate formula
`(f + g)^* = f^* \boxdot g^*` in general. -/
theorem exists_counterexample_to_conjugate_formula_of_subdifferential_add_eq_add :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K)
      (_ : CompleteSpace K) (f g : K → Set.Ioi (⊥ : EReal))
      (hf : f ∈ Γ₀(K)) (hg : g ∈ Γ₀(K)),
      (effectiveDomain f ∩ effectiveDomain g).Nonempty ∧
        ((∂ (f + g) : SetValuedOperator K K) = ∂ f + ∂ g) ∧
        ¬ ExactDualInfimalConvolutionFormula hf hg (ContinuousLinearMap.id ℝ K) := by
  -- Route correction: the target is reduced to one replacement witness-packaging helper after the
  -- exhausted Example 3.41 route was retired.
  exact existsAsymmetricCounterexampleDataFromRegularizedEpigraphPair

end SubdifferentialCalculus

end

end ERealFunction
