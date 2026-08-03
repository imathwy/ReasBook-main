import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap16.Proposition_16_5
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise translate

universe u v

namespace ERealFunction

open ContinuousLinearMap

noncomputable section

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Semantic search note: `lean_leansearch` was unavailable here; the source-faithful owner surface
-- is the Chapter 15 conjugate equality together with the domainwise attained split
-- `∃ v, (f + g ∘ L)^*(u) = f^*(u - L^* v) + g^*(v)`, since the source uses the exact dotted
-- operators rather than the raw non-attained `□` and `▷` owners.

/-- The shifted dual minimand from formula `(15.43)`, evaluated at a fixed dual point `u`. -/
def shiftedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) : K → EReal :=
  fun v ↦ f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v

/-- Evaluating `shiftedCompositeDualObjective` gives the explicit minimand
`f^*(u - L^* v) + g^*(v)`. -/
@[simp] theorem shiftedCompositeDualObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) (v : K) :
    shiftedCompositeDualObjective f g L u v =
      f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v := rfl

/-- Helper for Proposition 16.42: the dual infimal-convolution surface from the conjugate
formula. -/
private abbrev dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) : H → EReal :=
  f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)

/-- Helper for Proposition 16.42: the source's dotted outer operator is exact at `u` when some
split `y` attains the raw dual infimal-convolution value. -/
private def dualInfimalConvolutionExactAt
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) : Prop :=
  ∃ y : H, dualInfimalConvolution f g L u =
    f.asEReal∗ y + (L.adjoint ▷ g.asEReal∗) (u - y)

/-- Unfolding `dualInfimalConvolutionExactAt` gives the explicit attained split used in the
source proof. -/
@[simp] private theorem dualInfimalConvolutionExactAt_iff
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) :
    dualInfimalConvolutionExactAt f g L u ↔
      ∃ y : H, dualInfimalConvolution f g L u =
        f.asEReal∗ y + (L.adjoint ▷ g.asEReal∗) (u - y) :=
  Iff.rfl

/-- The source's dotted formula
`(f + g ∘ L)^* = f^* \boxdot (L^* \trianglerightdot g^*)`, recorded in the existing project API
as the raw Chapter 12/15 equality together with the exactness clauses carried by the dotted outer
and inner operators. -/
structure ExactDualInfimalConvolutionFormula
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K) : Prop where
  eq :
    (compositePrimalObjective f g L)∗ =
      dualInfimalConvolution f g L
  outerExact :
    ∀ ⦃u : H⦄, u ∈ dom ((compositePrimalObjective f g L)∗) →
      dualInfimalConvolutionExactAt f g L u
  innerExact :
    ∀ ⦃y : H⦄, y ∈ dom (L.adjoint ▷ (g∗[hg])) →
      infimalPostcomposition.ExactAt L.adjoint (g∗[hg]) y

/-- Helper for Proposition 16.42: if `L (effectiveDomain f)` meets `effectiveDomain g`, then the
effective domain of `f + g ∘ L` is nonempty. -/
private theorem effectiveDomain_nonempty_add_comp_of_image_inter_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K)
    (hdom : (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (effectiveDomain (f + g ∘ L)).Nonempty := by
  rcases hdom with ⟨y, ⟨x, hx, rfl⟩, hy⟩
  refine ⟨x, ?_⟩
  rw [mem_effectiveDomain_iff]
  -- Evaluate the composite objective at the witness supplied by the domain intersection.
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hgLx_top : (g (L x) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hsum_top : ((f x : EReal) + (g (L x) : EReal)) ≠ ⊤ :=
    EReal.add_ne_top hfx_top hgLx_top
  simpa [Function.comp_apply, add_apply] using lt_top_iff_ne_top.mpr hsum_top

/-- Helper for Proposition 16.42: the image-domain hypothesis for `L '' effectiveDomain f`
immediately gives the weaker range-domain hypothesis needed for the Chapter 15 composition
conjugate formula. -/
private theorem range_inter_effectiveDomain_nonempty_of_image_inter_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K)
    (hdom : (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  rcases hdom with ⟨y, hyImage, hyDom⟩
  rcases hyImage with ⟨x, _, rfl⟩
  exact ⟨L x, ⟨x, rfl⟩, hyDom⟩

/-- Helper for Proposition 16.42: the mixed primal-dual pairing splits through the adjoint as
`⟪x, u - L† v⟫ + ⟪L x, v⟫ = ⟪x, u⟫`. -/
private theorem compositeDualPairing_eq
    (L : H →L[ℝ] K) (x u : H) (v : K) :
    ⟪x, u - L.adjoint v⟫_ℝ + ⟪L x, v⟫_ℝ = ⟪x, u⟫_ℝ := by
  -- Expand the subtraction in the first slot and rewrite the adjoint pairing once.
  calc
    ⟪x, u - L.adjoint v⟫_ℝ + ⟪L x, v⟫_ℝ
        = (⟪x, u⟫_ℝ - ⟪x, L.adjoint v⟫_ℝ) + ⟪L x, v⟫_ℝ := by
            simp [inner_sub_right]
    _ = (⟪x, u⟫_ℝ - ⟪L x, v⟫_ℝ) + ⟪L x, v⟫_ℝ := by
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪x, u⟫_ℝ := by
          ring

/-- Helper for Proposition 16.42: the exact composite dual contact equality forces exact
Fenchel--Young contact for the `f` and `g` summands separately. -/
private theorem exactFenchelYoungContactsOfCompositeDualSplit
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K))
    {x u : H} {v : K}
    (hsplit :
      ((f x : EReal) + (g (L x) : EReal)) +
          shiftedCompositeDualObjective f g L u v =
        ((⟪x, u⟫_ℝ : ℝ) : EReal)) :
    ((f x : EReal) + f.asEReal∗ (u - L.adjoint v) =
        ((⟪x, u - L.adjoint v⟫_ℝ : ℝ) : EReal)) ∧
      ((g (L x) : EReal) + g.asEReal∗ v =
        ((⟪L x, v⟫_ℝ : ℝ) : EReal)) := by
  -- First rewrite the shifted objective so the contact equality has the standard four-term form.
  have hsplit' :
      ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [shiftedCompositeDualObjective_apply] using hsplit
  -- The conjugate terms stay above `⊥` because `Γ₀` functions have nonempty effective domains.
  have hc_bot : f.asEReal∗ (u - L.adjoint v) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty (u - L.adjoint v)
  have hd_bot : g.asEReal∗ v ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty v
  have hab_bot : (f x : EReal) + (g (L x) : EReal) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g (L x)).2⟩
  have hcd_bot : f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2
      ⟨bot_lt_iff_ne_bot.mpr hc_bot, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hsum_top :
      ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v) ≠ ⊤ := by
    intro htop
    exact EReal.coe_ne_top (⟪x, u⟫_ℝ : ℝ) (hsplit'.symm.trans htop)
  have hsum_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hab_bot hcd_bot).1 hsum_top
  have hab_top : (f x : EReal) + (g (L x) : EReal) ≠ ⊤ := hsum_top_parts.1
  have hcd_top : f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v ≠ ⊤ := hsum_top_parts.2
  have hab_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) (ne_of_gt (g (L x)).2)).1 hab_top
  have hcd_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hc_bot hd_bot).1 hcd_top
  have ha_top : (f x : EReal) ≠ ⊤ := hab_top_parts.1
  have hb_top : (g (L x) : EReal) ≠ ⊤ := hab_top_parts.2
  have hc_top : f.asEReal∗ (u - L.adjoint v) ≠ ⊤ := hcd_top_parts.1
  have hd_top : g.asEReal∗ v ≠ ⊤ := hcd_top_parts.2
  have hac_top : (f x : EReal) + f.asEReal∗ (u - L.adjoint v) ≠ ⊤ :=
    EReal.add_ne_top ha_top hc_top
  have hbd_top : (g (L x) : EReal) + g.asEReal∗ v ≠ ⊤ :=
    EReal.add_ne_top hb_top hd_top
  have hac_bot : (f x : EReal) + f.asEReal∗ (u - L.adjoint v) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, bot_lt_iff_ne_bot.mpr hc_bot⟩
  have hbd_bot : (g (L x) : EReal) + g.asEReal∗ v ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(g (L x)).2, bot_lt_iff_ne_bot.mpr hd_bot⟩
  -- Apply Fenchel--Young separately to the `f` and `g` contact pairs.
  have hfy_f :
      ((⟪x, u - L.adjoint v⟫_ℝ : ℝ) : EReal) ≤
        (f x : EReal) + f.asEReal∗ (u - L.adjoint v) :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hf) x (u - L.adjoint v)
  have hfy_g :
      ((⟪L x, v⟫_ℝ : ℝ) : EReal) ≤
        (g (L x) : EReal) + g.asEReal∗ v :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hg) (L x) v
  have hfy_f_toReal :
      ⟪x, u - L.adjoint v⟫_ℝ ≤
        (f x : EReal).toReal + (f.asEReal∗ (u - L.adjoint v)).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_f (EReal.coe_ne_bot _) hac_top
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot] at htmp
    exact htmp
  have hfy_g_toReal :
      ⟪L x, v⟫_ℝ ≤
        (g (L x) : EReal).toReal + (g.asEReal∗ v).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_g (EReal.coe_ne_bot _) hbd_top
    rw [EReal.toReal_add hb_top (ne_of_gt (g (L x)).2) hd_top hd_bot] at htmp
    exact htmp
  -- Move the four-term equality to `ℝ`, where linear arithmetic can separate the two contacts.
  have hsplit_toReal :
      ((f x : EReal).toReal + (g (L x) : EReal).toReal) +
          ((f.asEReal∗ (u - L.adjoint v)).toReal + (g.asEReal∗ v).toReal) =
        ⟪x, u⟫_ℝ := by
    have htmp := congrArg EReal.toReal hsplit'
    rw [EReal.toReal_add hab_top hab_bot hcd_top hcd_bot,
      EReal.toReal_add ha_top (ne_of_gt (f x).2) hb_top (ne_of_gt (g (L x)).2),
      EReal.toReal_add hc_top hc_bot hd_top hd_bot] at htmp
    exact htmp
  have hcomp_f_toReal :
      (f x : EReal).toReal + (f.asEReal∗ (u - L.adjoint v)).toReal =
        ⟪x, u - L.adjoint v⟫_ℝ := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, compositeDualPairing_eq L x u v]
  have hcomp_g_toReal :
      (g (L x) : EReal).toReal + (g.asEReal∗ v).toReal =
        ⟪L x, v⟫_ℝ := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, compositeDualPairing_eq L x u v]
  constructor
  · -- Convert the real equality back to the exact `EReal` Fenchel contact for `f`.
    apply (EReal.toReal_eq_toReal hac_top hac_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot]
    exact hcomp_f_toReal
  · -- Convert the real equality back to the exact `EReal` Fenchel contact for `g`.
    apply (EReal.toReal_eq_toReal hbd_top hbd_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add hb_top (ne_of_gt (g (L x)).2) hd_top hd_bot]
    exact hcomp_g_toReal

/-- Helper for Proposition 16.42: once the outer exact split is paired with an exact witness on
the adjoint fiber, the Fenchel--Young equality for `f + g ∘ L` separates into the two source-side
subgradient memberships. -/
private theorem componentSubgradientsOfCompositeDualSplit
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K))
    {x u : H} {v : K}
    (hsplit :
      ((f x : EReal) + (g (L x) : EReal)) +
          shiftedCompositeDualObjective f g L u v =
        ((⟪x, u⟫_ℝ : ℝ) : EReal)) :
    u - L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x) := by
  rcases exactFenchelYoungContactsOfCompositeDualSplit L hf hg hsplit with
    ⟨hfy_f_eq, hfy_g_eq⟩
  -- Convert the exact Fenchel--Young contacts back to the two subgradient memberships.
  constructor
  · exact
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x
        (u - L.adjoint v)).2 hfy_f_eq
  · exact
      (mem_subdifferential_iff_fenchel_young_eq (f := g) hg.2.nonempty (L x) v).2 hfy_g_eq

/-- Proposition 16.42: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, `L (effectiveDomain f)` meets
`effectiveDomain g`, and the exact dual conjugate formula
`(f + g ∘ L)^* = f^* \boxdot (L^* \trianglerightdot g^*)` holds, then
`∂ (f + g ∘ L) = ∂ f + L^* ∂ g L`, realized by the canonical owner
`(∂ f) + adjointImageSubdifferential L g`. -/
theorem subdifferential_add_comp_eq_add_adjoint_image_of_conjugate_formula
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hdom : (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hformula : ExactDualInfimalConvolutionFormula hf hg L) :
    ∂ (f + g ∘ L) = (∂ f) + adjointImageSubdifferential L g := by
  ext x u
  constructor
  · intro hu
    -- Route correction: use the active-point outer/inner exactness carried by `hformula`
    -- instead of rebuilding global biconjugacy and the full composition-conjugation API.
    have hdom_add_comp :
        (effectiveDomain (f + g ∘ L)).Nonempty :=
      effectiveDomain_nonempty_add_comp_of_image_inter_nonempty L hdom
    have hu_dom : u ∈ dom ((compositePrimalObjective f g L)∗) := by
      rw [mem_dom_iff]
      have htop :
          (f + g ∘ L).asEReal∗ u ≠ ⊤ :=
        conjugate_value_ne_top_of_mem_subdifferential
          (f := f + g ∘ L) hdom_add_comp hu
      simpa [compositePrimalObjective, primalObjective] using
        lt_top_iff_ne_top.mpr htop
    have hu_exact :
        ((f x : EReal) + (g (L x) : EReal)) + dualInfimalConvolution f g L u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      -- Rewrite the active Fenchel--Young equality through the assumed outer dual formula.
      calc
        ((f x : EReal) + (g (L x) : EReal)) + dualInfimalConvolution f g L u
            = ((f + g ∘ L) x : EReal) + (f + g ∘ L).asEReal∗ u := by
                simpa [add_apply, Function.comp_apply, compositePrimalObjective, primalObjective]
                  using
                    congrArg (fun z : EReal ↦ ((f x : EReal) + (g (L x) : EReal)) + z)
                      (congrFun hformula.eq u).symm
        _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
              exact
                (mem_subdifferential_iff_fenchel_young_eq
                  (f := f + g ∘ L) hdom_add_comp x u).1 hu
    have hu_dual_dom : u ∈ dom (dualInfimalConvolution f g L) := by
      simpa [hformula.eq] using hu_dom
    have hdual_top : dualInfimalConvolution f g L u ≠ ⊤ := by
      rw [mem_dom_iff] at hu_dual_dom
      exact lt_top_iff_ne_top.mp hu_dual_dom
    rcases hformula.outerExact hu_dom with ⟨y, hyExact⟩
    have hy_dom :
        u - y ∈ dom (L.adjoint ▷ g∗[hg]) :=
      by
        rw [mem_dom_iff]
        have hfy_bot : f.asEReal∗ y ≠ ⊥ :=
          conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty y
        have hpost_top : (L.adjoint ▷ g.asEReal∗) (u - y) ≠ ⊤ := by
          intro htop
          have hsum_top :
              f.asEReal∗ y + (L.adjoint ▷ g.asEReal∗) (u - y) = ⊤ := by
            rw [htop, EReal.add_top_of_ne_bot hfy_bot]
          exact hdual_top (hyExact.trans hsum_top)
        simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using
          lt_top_iff_ne_top.mpr hpost_top
    obtain ⟨_, ⟨v, hLv, hvalue⟩⟩ :=
      (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) (u - y)).1
        (hformula.innerExact hy_dom)
    have hvalueRaw :
        (L.adjoint ▷ g.asEReal∗) (u - y) = g.asEReal∗ v := by
      simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using hvalue
    have huLv : u - L.adjoint v = y := by
      rw [hLv]
      simp [sub_eq_add_neg]
    have hsplit :
        ((f x : EReal) + (g (L x) : EReal)) +
            shiftedCompositeDualObjective f g L u v =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      -- Combine the outer split and the exact adjoint-fiber witness into the source-side equality.
      calc
        ((f x : EReal) + (g (L x) : EReal)) + shiftedCompositeDualObjective f g L u v
            = ((f x : EReal) + (g (L x) : EReal)) +
                (f.asEReal∗ y + g.asEReal∗ v) := by
                  simp [shiftedCompositeDualObjective_apply, huLv]
        _ = ((f x : EReal) + (g (L x) : EReal)) + dualInfimalConvolution f g L u := by
              rw [← hvalueRaw, ← hyExact]
        _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hu_exact
    rcases componentSubgradientsOfCompositeDualSplit L hf hg hsplit with ⟨hyf', hvg⟩
    have hyf : y ∈ (∂ f) x := by
      simpa [huLv] using hyf'
    have hAdj :
        L.adjoint v ∈ adjointImageSubdifferential L g x := by
      rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
      exact ⟨v, hvg, rfl⟩
    refine Set.mem_add.mpr ?_
    refine ⟨y, hyf, L.adjoint v, hAdj, ?_⟩
    -- Reassemble the original subgradient from the two component pieces.
    calc
      y + L.adjoint v = y + (u - y) := by rw [hLv]
      _ = u := by simp [sub_eq_add_neg, add_left_comm]
  · intro hu
    -- Proposition 16.6 already gives the easy inclusion.
    exact
      subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g L x hu

end SubdifferentialCalculus

end

end ERealFunction
