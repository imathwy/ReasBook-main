import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap23.Proposition_23_32

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open Set
open SetValuedOperator
open scoped Gradient InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ERealFunction

open InfimalConvolutionRegularity

section ProximityOperatorComposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- `source-facing`: Proposition 24.18 consists of the four public sufficient conditions yielding
--   `Prox[f + g] = Prox[f] ∘ Prox[g]`.
-- `core/canonical`: the owner abstractions are the Chapter 23 resolvent identities `J[...]`,
--   the Chapter 16 subdifferential/proximity bridge, and the Chapter 20 maximal-monotonicity
--   surface for subdifferentials.
-- `bridge/view`: the private lemmas below only transport the source-facing proximity statement to
--   those owner abstractions.

-- Semantic recall: `lean_leansearch` only surfaced unrelated proximity results, so this item
-- keeps the source-facing Chapter 24 owner `Prox[...] = Prox[...] ∘ Prox[...]` and uses the
-- Chapter 23 resolvent surface only through the thin `J[∂f]`/`Prox[f]` bridge below.

private theorem resolvent_subdifferential_eq_proximityOperator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    J[(∂ f : SetValuedOperator H H)] = (Prox[f, hf]).toSetValuedOperator := by
  simpa [resolvent_def] using
    (singleton_proximityOperator_eq_inverse_add_subdifferential hf).symm

private theorem subdifferential_eq_singleton_of_gateauxGradient_on_effectiveDomain
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) (gradg : H → H)
    (hopen : IsOpen (effectiveDomain g))
    (hgateaux :
      HasGateauxDerivativeOn
        (fun y ↦ (g y : EReal).toReal)
        (fun y ↦ toDual ℝ H (gradg y))
        (effectiveDomain g))
    {y : H} (hy : y ∈ effectiveDomain g) :
    (∂ g) y = ({gradg y} : Set H) := by
  have hy_int : y ∈ interior (effectiveDomain g) := by
    simpa [hopen.interior_eq] using hy
  have hgradAt :
      HasGateauxDerivativeAt
        (fun z ↦ (g z : EReal).toReal)
        (toDualMap ℝ H (gradg y))
        y := by
    simpa [toDual_apply_eq_toDualMap_apply] using
      hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgateaux y hy)
  exact
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
      hg hy_int hgradAt

private theorem proximityOperator_add_eq_proximityOperator_comp_of_resolvent_add_eq_comp
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfg : f + g ∈ Γ₀(H))
    (hres :
      J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] =
        J[(∂ f : SetValuedOperator H H)].comp J[(∂ g : SetValuedOperator H H)]) :
    Prox[f + g, hfg] = Prox[f, hf] ∘ Prox[g, hg] := by
  funext x
  let p := (Prox[f, hf] ∘ Prox[g, hg]) x
  have hp_res :
      p ∈ J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] x := by
    have hprox :
        J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] =
          ((Prox[f, hf] ∘ Prox[g, hg]).toSetValuedOperator) := by
      calc
        J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] =
            J[(∂ f : SetValuedOperator H H)].comp J[(∂ g : SetValuedOperator H H)] := hres
        _ =
            (Prox[f, hf]).toSetValuedOperator.comp
              (Prox[g, hg]).toSetValuedOperator := by
                rw [resolvent_subdifferential_eq_proximityOperator hf,
                  resolvent_subdifferential_eq_proximityOperator hg]
        _ = ((Prox[f, hf] ∘ Prox[g, hg]).toSetValuedOperator) := by
              ext x z
              simp [Function.comp, SetValuedOperator.comp]
    have hp' : p ∈ ((Prox[f, hf] ∘ Prox[g, hg]).toSetValuedOperator) x := by
      simp [p, Function.comp]
    simpa [hprox] using hp'
  have hp_sum :
      x - p ∈ (((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H)) p) := by
    have hp_inv :
        x ∈
          (((id : H → H).toSetValuedOperator +
              ((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))) p) := by
      rwa [resolvent_def, mem_inverse_iff] at hp_res
    rcases Set.mem_add.mp hp_inv with ⟨y, hy, z, hz, hyz⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hy
    subst y
    have hz_eq : x - p = z := by
      rw [sub_eq_iff_eq_add]
      simpa [add_comm] using hyz.symm
    simpa [hz_eq] using hz
  have hp_sum' :
      x - p ∈
        (∂ f) p +
          ContinuousLinearMap.adjointImageSubdifferential
            (ContinuousLinearMap.id ℝ H) g p := by
    simpa [ContinuousLinearMap.adjointImageSubdifferential] using hp_sum
  have hp_add : x - p ∈ (∂ (f + g)) p := by
    exact
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) p) hp_sum'
  have hp_prox : p = Prox[f + g, hfg] x :=
    (eq_proximityOperator_iff_sub_mem_subdifferential hfg x p).2 hp_add
  simpa [p, Function.comp] using hp_prox.symm

/-- Helper for Proposition 24.18: under clause (1), the domain-inclusion hypothesis implies
`f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsubset :
      ∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y)) :
    f + g ∈ Γ₀(H) := by
  let y := Prox[g, hg] 0
  let p := Prox[f, hf] y
  -- The outer proximal point carries a concrete subgradient, so it belongs to `dom (∂ g)`.
  have hy_sub : -y ∈ (∂ g) y := by
    simpa [y] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hg 0 y).1 rfl
  have hy_dom : SubdifferentiableAt g y := by
    rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
    exact ⟨-y, hy_sub⟩
  -- Transport that same subgradient through the clause-(1) hypothesis to put `p` in `dom (∂ g)`.
  have hp_g_sub : -y ∈ (∂ g) p := by
    simpa [p] using (hsubset hy_dom hy_sub)
  have hp_g_dom : p ∈ SetValuedOperator.dom (∂ g) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨-y, hp_g_sub⟩
  -- The inner proximal characterization simultaneously puts `p` in `dom (∂ f)`.
  have hp_f_sub : y - p ∈ (∂ f) p := by
    simpa [p] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hf y p).1 rfl
  have hp_f_dom : p ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨y - p, hp_f_sub⟩
  -- Convert both subdifferential-domain facts to effective-domain facts and apply the Γ₀ sum API.
  have hp_f_eff : p ∈ effectiveDomain f :=
    subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hp_f_dom
  have hp_g_eff : p ∈ effectiveDomain g :=
    subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg hp_g_dom
  exact pointwiseAdd_mem_gammaZero f g hf hg ⟨p, hp_f_eff, hp_g_eff⟩

/-- Clause (1) of Proposition 24.18: if every `y ∈ dom (∂ g)` satisfies
`(∂ g) y ⊆ (∂ g) (Prox_f y)`, then `Prox_{f + g} = Prox_f ∘ Prox_g`. -/
theorem proximityOperator_add_eq_proximityOperator_comp_of_dom_subset_at_proximityOperator
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsubset :
      ∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y)) :
    Prox[f + g, pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hsubset] =
      Prox[f, hf] ∘ Prox[g, hg] := by
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hsubset
  exact
    proximityOperator_add_eq_proximityOperator_comp_of_resolvent_add_eq_comp hf hg hfg <|
      resolvent_add_eq_resolvent_comp_of_dom_subset_at_resolvent
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg)
        (fun {y p} hy hp ↦ by
          have hp_eq : p = Prox[f, hf] y := by
            have hp' : p ∈ (Prox[f, hf]).toSetValuedOperator y := by
              rw [← resolvent_subdifferential_eq_proximityOperator hf]
              exact hp
            simpa using hp'
          simpa [hp_eq] using hsubset hy)

/-- Helper for Proposition 24.18: under clause (2), the graph-step inclusion hypothesis implies
`f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_graph_step_subset
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) (x + u) ⊆ (∂ g) x) :
    f + g ∈ Γ₀(H) := by
  let y := Prox[g, hg] 0
  let p := Prox[f, hf] y
  -- The outer proximal point again gives a canonical element of `(∂ g) y`.
  have hy_sub : -y ∈ (∂ g) y := by
    simpa [y] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hg 0 y).1 rfl
  -- The inner proximal residual is exactly the graph step required by clause (2).
  have hp_f_sub : y - p ∈ (∂ f) p := by
    simpa [p] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hf y p).1 rfl
  have hp_graph : (p, y - p) ∈ gra (∂ f) := by
    simpa [mem_graph] using hp_f_sub
  have hp_g_sub : -y ∈ (∂ g) p := by
    have hy_step : -y ∈ (∂ g) (p + (y - p)) := by
      have hpy : p + (y - p) = y := by
        abel_nf
      simpa [hpy] using hy_sub
    exact hsubset hp_graph hy_step
  have hp_g_dom : p ∈ SetValuedOperator.dom (∂ g) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨-y, hp_g_sub⟩
  have hp_f_dom : p ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨y - p, hp_f_sub⟩
  -- As in clause (1), a common effective-domain witness yields `f + g ∈ Γ₀(H)`.
  have hp_f_eff : p ∈ effectiveDomain f :=
    subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hp_f_dom
  have hp_g_eff : p ∈ effectiveDomain g :=
    subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg hp_g_dom
  exact pointwiseAdd_mem_gammaZero f g hf hg ⟨p, hp_f_eff, hp_g_eff⟩

/-- Clause (2) of Proposition 24.18: if every graph point `(x, u) ∈ gra (∂ f)` satisfies
`(∂ g) (x + u) ⊆ (∂ g) x`, then `Prox_{f + g} = Prox_f ∘ Prox_g`. -/
theorem proximityOperator_add_eq_proximityOperator_comp_of_graph_step_subset
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) (x + u) ⊆ (∂ g) x) :
    Prox[f + g, pointwiseAdd_mem_gammaZero_of_graph_step_subset hf hg hsubset] =
      Prox[f, hf] ∘ Prox[g, hg] := by
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_graph_step_subset hf hg hsubset
  exact
    proximityOperator_add_eq_proximityOperator_comp_of_resolvent_add_eq_comp hf hg hfg <|
      resolvent_add_eq_resolvent_comp_of_graph_step_subset
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg)
        hsubset

/-- Helper for Proposition 24.18: under clause (3), the open-domain Gâteaux-gradient hypotheses
imply `f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_gateauxGradient_fixed
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (gradg : H → H) (hopen : IsOpen (effectiveDomain g))
    (hgateaux :
      HasGateauxDerivativeOn
        (fun y ↦ (g y : EReal).toReal)
        (fun y ↦ toDual ℝ H (gradg y))
        (effectiveDomain g))
    (hsubdom : SetValuedOperator.dom (∂ f) ⊆ effectiveDomain g)
    (hfix : ∀ ⦃y : H⦄, y ∈ effectiveDomain g → gradg y = gradg (Prox[f, hf] y)) :
    f + g ∈ Γ₀(H) := by
  -- Reduce clause (3) to clause (1) by identifying both subdifferentials with singleton gradients.
  have hsubset :
      ∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y) := by
    intro y hy_dom u hu
    have hy_eff : y ∈ effectiveDomain g :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg hy_dom
    -- The proximal residual places `Prox[f, hf] y` in `dom (∂ f)`, so `hsubdom` moves it into
    -- `effectiveDomain g`, where the singleton-subdifferential API is available.
    have hprox_sub : y - Prox[f, hf] y ∈ (∂ f) (Prox[f, hf] y) := by
      exact
        (eq_proximityOperator_iff_sub_mem_subdifferential hf y (Prox[f, hf] y)).1 rfl
    have hprox_dom : Prox[f, hf] y ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨y - Prox[f, hf] y, hprox_sub⟩
    have hprox_eff : Prox[f, hf] y ∈ effectiveDomain g := hsubdom hprox_dom
    have hy_single : (∂ g) y = ({gradg y} : Set H) :=
      subdifferential_eq_singleton_of_gateauxGradient_on_effectiveDomain
        hg gradg hopen hgateaux hy_eff
    have hprox_single : (∂ g) (Prox[f, hf] y) = ({gradg (Prox[f, hf] y)} : Set H) :=
      subdifferential_eq_singleton_of_gateauxGradient_on_effectiveDomain
        hg gradg hopen hgateaux hprox_eff
    have hu_grad : u = gradg y := by
      have : u ∈ ({gradg y} : Set H) := by
        simpa [hy_single] using hu
      simpa using this
    rw [hprox_single]
    simp [hfix hy_eff, hu_grad]
  -- The previously proved clause-(1) companion now yields the desired `Γ₀(H)` conclusion.
  exact pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hsubset

/-- Clause (3) of Proposition 24.18: if `effectiveDomain g` is open, if `gradg`
is a Gâteaux gradient field for the finite representative of `g` on
`effectiveDomain g`, if
`dom (∂ f) ⊆ effectiveDomain g`, and if `gradg y = gradg (Prox_f y)` for every
`y ∈ effectiveDomain g`, then
`Prox_{f + g} = Prox_f ∘ Prox_g`. -/
theorem proximityOperator_add_eq_proximityOperator_comp_of_gateauxGradient_fixed
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (gradg : H → H) (hopen : IsOpen (effectiveDomain g))
    (hgateaux :
      HasGateauxDerivativeOn
        (fun y ↦ (g y : EReal).toReal)
        (fun y ↦ toDual ℝ H (gradg y))
        (effectiveDomain g))
    (hsubdom : SetValuedOperator.dom (∂ f) ⊆ effectiveDomain g)
    (hfix : ∀ ⦃y : H⦄, y ∈ effectiveDomain g → gradg y = gradg (Prox[f, hf] y)) :
    Prox[f + g,
      pointwiseAdd_mem_gammaZero_of_gateauxGradient_fixed
        hf hg gradg hopen hgateaux hsubdom hfix] =
      Prox[f, hf] ∘ Prox[g, hg] := by
  have hsubset :
      ∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y) := by
    intro y hy_dom u hu
    have hy_eff : y ∈ effectiveDomain g :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg hy_dom
    have hprox_dom : Prox[f, hf] y ∈ SetValuedOperator.dom (∂ f) := by
      refine ⟨y - Prox[f, hf] y, ?_⟩
      exact
        (eq_proximityOperator_iff_sub_mem_subdifferential hf y (Prox[f, hf] y)).1 rfl
    have hprox_eff : Prox[f, hf] y ∈ effectiveDomain g := hsubdom hprox_dom
    have hy_single : (∂ g) y = ({gradg y} : Set H) :=
      subdifferential_eq_singleton_of_gateauxGradient_on_effectiveDomain
        hg gradg hopen hgateaux hy_eff
    have hprox_single : (∂ g) (Prox[f, hf] y) = ({gradg (Prox[f, hf] y)} : Set H) :=
      subdifferential_eq_singleton_of_gateauxGradient_on_effectiveDomain
        hg gradg hopen hgateaux hprox_eff
    have hu_grad : u = gradg y := by
      have : u ∈ ({gradg y} : Set H) := by
        simpa [hy_single] using hu
      simpa using this
    rw [hprox_single]
    simp [hfix hy_eff, hu_grad]
  have hgamma :
      pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hsubset =
        pointwiseAdd_mem_gammaZero_of_gateauxGradient_fixed
          hf hg gradg hopen hgateaux hsubdom hfix :=
    Subsingleton.elim _ _
  simpa [hgamma] using
    proximityOperator_add_eq_proximityOperator_comp_of_dom_subset_at_proximityOperator
      hf hg hsubset

omit [CompleteSpace H] in
private theorem component_subgradients_of_dual_sum_split
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x u w : H}
    (hsplit :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ (u - w) + g.asEReal∗ w) =
        ((inner ℝ x u : ℝ) : EReal)) :
    u - w ∈ (∂ f) x ∧ w ∈ (∂ g) x := by
  have hc_bot : f.asEReal∗ (u - w) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty (u - w)
  have hd_bot : g.asEReal∗ w ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty w
  have hab_bot : (f x : EReal) + (g x : EReal) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hcd_bot : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2
      ⟨bot_lt_iff_ne_bot.mpr hc_bot, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hsum_top :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ (u - w) + g.asEReal∗ w) ≠ ⊤ := by
    intro htop
    exact EReal.coe_ne_top (inner ℝ x u : ℝ) (hsplit.symm.trans htop)
  have hsum_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hab_bot hcd_bot).1 hsum_top
  have hab_top : (f x : EReal) + (g x : EReal) ≠ ⊤ := hsum_top_parts.1
  have hcd_top : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊤ := hsum_top_parts.2
  have hab_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) (ne_of_gt (g x).2)).1 hab_top
  have hcd_top_parts := (EReal.add_ne_top_iff_ne_top₂ hc_bot hd_bot).1 hcd_top
  have ha_top : (f x : EReal) ≠ ⊤ := hab_top_parts.1
  have hb_top : (g x : EReal) ≠ ⊤ := hab_top_parts.2
  have hc_top : f.asEReal∗ (u - w) ≠ ⊤ := hcd_top_parts.1
  have hd_top : g.asEReal∗ w ≠ ⊤ := hcd_top_parts.2
  have hac_top : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊤ :=
    EReal.add_ne_top ha_top hc_top
  have hbd_top : (g x : EReal) + g.asEReal∗ w ≠ ⊤ :=
    EReal.add_ne_top hb_top hd_top
  have hac_bot : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, bot_lt_iff_ne_bot.mpr hc_bot⟩
  have hbd_bot : (g x : EReal) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(g x).2, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hfy_f :
      ((inner ℝ x (u - w) : ℝ) : EReal) ≤
        (f x : EReal) + f.asEReal∗ (u - w) :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hf) x (u - w)
  have hfy_g :
      ((inner ℝ x w : ℝ) : EReal) ≤ (g x : EReal) + g.asEReal∗ w :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hg) x w
  have hfy_f_toReal :
      inner ℝ x (u - w) ≤
        (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal := by
    have htmp := EReal.toReal_le_toReal hfy_f (EReal.coe_ne_bot _) hac_top
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot] at htmp
    exact htmp
  have hfy_g_toReal :
      inner ℝ x w ≤ (g x : EReal).toReal + (g.asEReal∗ w).toReal := by
    have htmp := EReal.toReal_le_toReal hfy_g (EReal.coe_ne_bot _) hbd_top
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot] at htmp
    exact htmp
  have hsplit_toReal :
      ((f x : EReal).toReal + (g x : EReal).toReal) +
          ((f.asEReal∗ (u - w)).toReal + (g.asEReal∗ w).toReal) =
        inner ℝ x u := by
    have htmp := congrArg EReal.toReal hsplit
    rw [EReal.toReal_add hab_top hab_bot hcd_top hcd_bot,
      EReal.toReal_add ha_top (ne_of_gt (f x).2) hb_top (ne_of_gt (g x).2),
      EReal.toReal_add hc_top hc_bot hd_top hd_bot] at htmp
    exact htmp
  have hpair_real : inner ℝ x (u - w) + inner ℝ x w = inner ℝ x u := by
    calc
      inner ℝ x (u - w) + inner ℝ x w =
          (inner ℝ x u - inner ℝ x w) + inner ℝ x w := by
            simp [inner_sub_right]
      _ = inner ℝ x u := by ring
  have hcomp_f_toReal :
      (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal = inner ℝ x (u - w) := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hcomp_g_toReal :
      (g x : EReal).toReal + (g.asEReal∗ w).toReal = inner ℝ x w := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hfy_f_eq :
      (f x : EReal) + f.asEReal∗ (u - w) = ((inner ℝ x (u - w) : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hac_top hac_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot]
    exact hcomp_f_toReal
  have hfy_g_eq : (g x : EReal) + g.asEReal∗ w = ((inner ℝ x w : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hbd_top hbd_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot]
    exact hcomp_g_toReal
  constructor
  · exact (mem_subdifferential_iff_fenchel_young_eq f hf.2.nonempty x (u - w)).2 hfy_f_eq
  · exact (mem_subdifferential_iff_fenchel_young_eq g hg.2.nonempty x w).2 hfy_g_eq

private theorem dual_split_of_mem_subdifferential_pointwiseAdd_of_zero_mem_sri_sub_effectiveDomain
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    {x u : H} (hu : u ∈ (∂ (f + g)) x) :
    ∃ v : H, v ∈ (∂ f) x ∧ u - v ∈ (∂ g) x := by
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri
  have hconj :
      (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ :=
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri
  have hconj_gamma :
      (((f∗[hf]) □ (g∗[hg])) : H → EReal) = f.asEReal∗ □ g.asEReal∗ := by
    funext z
    simp
  have hfy :
      ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u =
        ((inner ℝ x u : ℝ) : EReal) := by
    simpa [pointwiseAdd_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f + g) hfg.2.nonempty x u).1 hu
  have hprimal_ne_bot : ((f x : EReal) + (g x : EReal)) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hdual_ne_top : (f + g).asEReal∗ u ≠ ⊤ := by
    intro hu_top
    have hsum_top :
        ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u = ⊤ := by
      rw [hu_top]
      exact EReal.add_top_of_ne_bot hprimal_ne_bot
    exact EReal.coe_ne_top _ (hfy.symm.trans hsum_top)
  have hu_dom : u ∈ dom (((f∗[hf]) □ (g∗[hg])) : H → EReal) := by
    rw [mem_dom_iff]
    rw [hconj_gamma, ← hconj]
    exact lt_top_iff_ne_top.mpr hdual_ne_top
  rcases
      infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri hu_dom with
    ⟨y, hy⟩
  let w := u - y
  have hsplit :
      ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ (u - w) + g.asEReal∗ w) =
        ((inner ℝ x u : ℝ) : EReal) := by
    calc
      ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ (u - w) + g.asEReal∗ w) =
          ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ □ g.asEReal∗) u := by
            rw [hy]
            simp [w, sub_sub_cancel]
      _ = ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u := by rw [← hconj]
      _ = ((inner ℝ x u : ℝ) : EReal) := hfy
  rcases component_subgradients_of_dual_sum_split hf hg hsplit with ⟨hvf, hwg⟩
  refine ⟨u - w, hvf, ?_⟩
  simpa [w, sub_sub_cancel] using hwg

private theorem subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain_local
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
  ext x u
  constructor
  · intro hu
    obtain ⟨v, hvf, hvg⟩ :=
      dual_split_of_mem_subdifferential_pointwiseAdd_of_zero_mem_sri_sub_effectiveDomain
        hf hg hsri hu
    exact Set.mem_add.2 ⟨v, hvf, u - v, hvg, by abel⟩
  · intro hu
    have hu_id :
        u ∈ (∂ f) x +
          ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g x := by
      simpa [ContinuousLinearMap.adjointImageSubdifferential] using hu
    simpa [Function.comp] using
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) x hu_id)

/-- Clause (4) of Proposition 24.18: if
`0 ∈ sri (effectiveDomain f - effectiveDomain g)` and every graph point
`(x, u) ∈ gra (∂ f)` satisfies `(∂ g) x ⊆ (∂ g) (x + u)`, then
`Prox_{f + g} = Prox_f ∘ Prox_g`. -/
theorem proximityOperator_add_eq_proximityOperator_comp_of_zero_mem_sri_sub_effectiveDomain
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) x ⊆ (∂ g) (x + u)) :
    Prox[f + g,
      pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri] =
      Prox[f, hf] ∘ Prox[g, hg] := by
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri
  have hsubdiff :
      (∂ (f + g) : SetValuedOperator H H) =
        (∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H) :=
    subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain_local hf hg hsri
  have hsum_max :
      Maximal IsMonotone
        ((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H)) := by
    simpa [hsubdiff] using subdifferential_isMaximallyMonotone_of_mem_gammaZero hfg
  exact
    proximityOperator_add_eq_proximityOperator_comp_of_resolvent_add_eq_comp hf hg hfg <|
      resolvent_add_eq_resolvent_comp_of_maximal_add_and_graph_step_superset
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg)
        hsum_max
        hsubset

/-- Helper for Proposition 24.18: any one of the four textbook hypotheses implies
`f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcondition :
      (∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y)) ∨
        (∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) (x + u) ⊆ (∂ g) x) ∨
          (∃ gradg : H → H,
            IsOpen (effectiveDomain g) ∧
              HasGateauxDerivativeOn
                (fun y ↦ (g y : EReal).toReal)
                (fun y ↦ toDual ℝ H (gradg y))
                (effectiveDomain g) ∧
              SetValuedOperator.dom (∂ f) ⊆ effectiveDomain g ∧
              ∀ ⦃y : H⦄,
                y ∈ effectiveDomain g → gradg y = gradg (Prox[f, hf] y)) ∨
            ((0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) ∧
              ∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) x ⊆ (∂ g) (x + u))) :
    f + g ∈ Γ₀(H) := by
  rcases hcondition with hdom | hcondition
  · exact pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hdom
  rcases hcondition with hgraph | hcondition
  · exact pointwiseAdd_mem_gammaZero_of_graph_step_subset hf hg hgraph
  rcases hcondition with ⟨gradg, hopen, hgateaux, hsubdom, hfix⟩ | ⟨hsri, _⟩
  · exact
      pointwiseAdd_mem_gammaZero_of_gateauxGradient_fixed
        hf hg gradg hopen hgateaux hsubdom hfix
  · exact pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri

/-- Proposition 24.18. If any one of clauses (1)-(4) holds, then
`Prox_{f + g} = Prox_f ∘ Prox_g`. -/
theorem proximityOperator_add_eq_proximityOperator_comp
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcondition :
      (∀ ⦃y : H⦄, SubdifferentiableAt g y → (∂ g) y ⊆ (∂ g) (Prox[f, hf] y)) ∨
        (∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) (x + u) ⊆ (∂ g) x) ∨
          (∃ gradg : H → H,
            IsOpen (effectiveDomain g) ∧
              HasGateauxDerivativeOn
                (fun y ↦ (g y : EReal).toReal)
                (fun y ↦ toDual ℝ H (gradg y))
                (effectiveDomain g) ∧
              SetValuedOperator.dom (∂ f) ⊆ effectiveDomain g ∧
              ∀ ⦃y : H⦄,
                y ∈ effectiveDomain g → gradg y = gradg (Prox[f, hf] y)) ∨
            ((0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) ∧
              ∀ ⦃x u : H⦄, (x, u) ∈ gra (∂ f) → (∂ g) x ⊆ (∂ g) (x + u))) :
    Prox[f + g, pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis hf hg hcondition] =
      Prox[f, hf] ∘ Prox[g, hg] := by
  rcases hcondition with hdom | hcondition
  · have hgamma :
      pointwiseAdd_mem_gammaZero_of_dom_subset_at_proximityOperator hf hg hdom =
        pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis hf hg (Or.inl hdom) :=
      Subsingleton.elim _ _
    simpa [hgamma] using
      proximityOperator_add_eq_proximityOperator_comp_of_dom_subset_at_proximityOperator
        hf hg hdom
  rcases hcondition with hgraph | hcondition
  · have hgamma :
      pointwiseAdd_mem_gammaZero_of_graph_step_subset hf hg hgraph =
        pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis
          hf hg (Or.inr <| Or.inl hgraph) :=
      Subsingleton.elim _ _
    simpa [hgamma] using
      proximityOperator_add_eq_proximityOperator_comp_of_graph_step_subset
        hf hg hgraph
  rcases hcondition with ⟨gradg, hopen, hgateaux, hsubdom, hfix⟩ | ⟨hsri, hgraph⟩
  · have hgamma :
      pointwiseAdd_mem_gammaZero_of_gateauxGradient_fixed
          hf hg gradg hopen hgateaux hsubdom hfix =
        pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis
          hf hg (Or.inr <| Or.inr <| Or.inl ⟨gradg, hopen, hgateaux, hsubdom, hfix⟩) :=
      Subsingleton.elim _ _
    simpa [hgamma] using
      proximityOperator_add_eq_proximityOperator_comp_of_gateauxGradient_fixed
        hf hg gradg hopen hgateaux hsubdom hfix
  · have hgamma :
      pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri =
        pointwiseAdd_mem_gammaZero_of_proximityCompositionHypothesis
          hf hg (Or.inr <| Or.inr <| Or.inr ⟨hsri, hgraph⟩) :=
      Subsingleton.elim _ _
    simpa [hgamma] using
      proximityOperator_add_eq_proximityOperator_comp_of_zero_mem_sri_sub_effectiveDomain
        hf hg hsri hgraph

end ProximityOperatorComposition

end ERealFunction
