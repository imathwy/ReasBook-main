import Mathlib
import BauschkeLean.Chap03.Corollary_3_24
import BauschkeLean.Chap06.Theorem_6_30
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap12.Proposition_12_30
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace Pointwise Set

universe u

local instance : OfNat (Set.Ioi (0 : ℝ)) 1 :=
  ⟨⟨1, by simp⟩⟩

namespace ERealFunction

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Remark 14 4: every subgradient of `g` at `p` becomes a subgradient of the
Fenchel conjugate of `g` at the same dual point. -/
theorem mem_subdifferential_gammaZeroConjugate_of_mem_subdifferential
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) {p u : H} (hu : u ∈ (∂ g) p) :
    p ∈ (∂ (gammaZeroConjugate g hg)) u := by
  have hp_subdom : p ∈ SetValuedOperator.dom (∂ g) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hp_dom : p ∈ effectiveDomain g := by
    exact subdifferential_domain_subset_effectiveDomain g hg.2.nonempty hp_subdom
  have hp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (g p).2
  have hu_halfspace :
      ∀ y ∈ effectiveDomain g,
        ⟪y - p, u⟫_ℝ ≤ (g y : EReal).toReal - (g p : EReal).toReal := by
    rw [subdifferential_eq_iInter_affine_halfspaces g p hp_dom] at hu
    exact Set.mem_iInter₂.mp hu
  have hconj_upper :
      (gammaZeroConjugate g hg u : EReal) ≤
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) := by
    rw [gammaZeroConjugate_apply, conjugate_eq_sSup_image_dom]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy_dom : y ∈ effectiveDomain g := by
      simpa [effectiveDomain, dom] using hy
    have hy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
    have hy_bot : (g y : EReal) ≠ ⊥ := ne_of_gt (g y).2
    have hreal :
        ⟪y, u⟫_ℝ - (g y : EReal).toReal ≤
          ⟪p, u⟫_ℝ - (g p : EReal).toReal := by
      have hy_le := hu_halfspace y hy_dom
      have hinner : ⟪y - p, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪p, u⟫_ℝ := by
        simpa using inner_sub_left y p u
      nlinarith
    have hy_defect :
        (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) y =
          (((⟪y, u⟫_ℝ - (g y : EReal).toReal : ℝ) : EReal)) := by
      change ((⟪y, u⟫_ℝ : EReal) - (g y : EReal)) =
        (((⟪y, u⟫_ℝ - (g y : EReal).toReal : ℝ) : EReal))
      rw [← EReal.coe_toReal hy_top hy_bot, EReal.coe_sub]
      simp
    rw [hy_defect]
    exact_mod_cast hreal
  have hconj_lower :
      (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) ≤
        (gammaZeroConjugate g hg u : EReal) := by
    have hp_mem_dom : p ∈ dom (g : H → EReal) := by
      simpa [effectiveDomain, dom] using hp_dom
    rw [gammaZeroConjugate_apply, conjugate_eq_sSup_image_dom]
    have hp_defect :
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) =
          (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) p := by
      change (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) =
        ((⟪p, u⟫_ℝ : EReal) - (g p : EReal))
      rw [← EReal.coe_toReal hp_top hp_bot, EReal.coe_sub]
      simp
    rw [hp_defect]
    exact le_sSup (Set.mem_image_of_mem
      (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) hp_mem_dom)
  have hconj_eq :
      (gammaZeroConjugate g hg u : EReal) =
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) :=
    le_antisymm hconj_upper hconj_lower
  -- Reinsert the Fenchel--Young equality into the subgradient inequality for the conjugate.
  rw [mem_subdifferential_iff]
  intro y
  have hfy :
      ((⟪p, y⟫_ℝ : ℝ) : EReal) ≤ (g p : EReal) + (gammaZeroConjugate g hg y : EReal) := by
    simpa [gammaZeroConjugate_apply, add_comm] using
      fenchel_young_inequality (f := (g : H → EReal)) (isProper_of_mem_gammaZero hg) p y
  calc
    (⟪y - u, p⟫_ℝ : EReal) + (gammaZeroConjugate g hg u : EReal) =
        (((⟪p, y⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) := by
          rw [hconj_eq, ← EReal.coe_add]
          congr 1
          rw [inner_sub_left, real_inner_comm u p, real_inner_comm p y]
          ring
    _ = ((⟪p, y⟫_ℝ : ℝ) : EReal) - (g p : EReal) := by
          rw [← EReal.coe_toReal hp_top hp_bot, EReal.coe_sub]
          simp
    _ ≤ (gammaZeroConjugate g hg y : EReal) := by
          exact (EReal.sub_le_iff_le_add (.inl hp_bot) (.inl hp_top)).2 <| by
            simpa [add_comm] using hfy

/-- Helper for Remark 14 4: the proximal point of the Fenchel conjugate is the residual
`x - Prox_f x`. -/
theorem conjugate_proximityOperator_eq_sub_proximityOperator
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (x : H) :
    Prox[g∗[hg], gammaZeroConjugate_mem_gammaZero hg] x = x - Prox[g, hg] x := by
  let p := Prox[g, hg] x
  let pStar := x - p
  have hsub :
      pStar ∈ (∂ g) p := by
    -- The primal proximal point gives the residual subgradient inclusion.
    simpa [p, pStar] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (hf := hg) (x := x) (p := p)).1 rfl
  have hconj :
      p ∈ (∂ (gammaZeroConjugate g hg)) pStar := by
    -- Transport the primal subgradient to the conjugate side.
    exact mem_subdifferential_gammaZeroConjugate_of_mem_subdifferential g hg hsub
  have hpStar :
      pStar = Prox[g∗[hg], gammaZeroConjugate_mem_gammaZero hg] x := by
    -- The conjugate residual inclusion characterizes the conjugate proximal point.
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (hf := gammaZeroConjugate_mem_gammaZero hg) (x := x) (p := pStar)).2
    simpa [p, pStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconj
  exact hpStar.symm

/-- Helper for Remark 14 4: at the unit parameter, the scaled proximal operator is the ordinary
proximal operator. -/
theorem unit_scaledProx_eq_prox
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    Prox[((1 : PosReal) • g), smul_mem_gammaZero g hg (1 : PosReal)] = Prox[g, hg] := by
  -- At `γ = 1`, the scaled function is definitionally `g`, so the proximal maps agree.
  funext x
  simp

/-- Helper for Remark 14 4: the unit Moreau envelope is obtained by evaluating the proximal
objective at the ordinary proximal point. -/
private theorem unit_moreauEnvelope_eq_proxValue_add_sqDist_of_mem_gammaZero
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (x : H) :
    ({}^[1] g) x =
      (g (Prox[g, hg] x) : EReal) +
        ((((‖x - Prox[g, hg] x‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := by
  let p := Prox[g, hg] x
  have hp : IsProxPoint g x p := by
    -- Read the ordinary proximal operator as the canonical proximal point.
    simpa [p] using
      proximityOperator_isProxPoint g (hasUniqueProxPoint_of_mem_gammaZero g hg) x
  -- Evaluate the unit Moreau envelope at that proximal point.
  simpa [p, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (isProxPoint_iff_moreauEnvelope_eq g x p).1 hp

/-- Helper for Remark 14 4: Proposition 12.30 at `γ = 1` first lands on the unit scaled
proximal operator. -/
theorem gradient_unit_moreauEnvelope_toReal_eq_sub_unit_scaledProx
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    ∇ (fun y : H ↦ (({}^[1] g) y).toReal) =
      fun x ↦
        x - Prox[((1 : PosReal) • g), smul_mem_gammaZero g hg (1 : PosReal)] x := by
  -- Route correction: keep Proposition 12.30 on its unit scaled-prox surface before collapsing
  -- that unit-scaled map to the ordinary proximal operator.
  funext x
  have hgrad :=
    congrFun
      (gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
        (f := g) (γ := (1 : PosReal)) (hf := hg))
      x
  refine hgrad.trans ?_
  have hone : (((1 : PosReal) : ℝ)⁻¹) = 1 := by
    norm_num
  rw [hone, one_smul]
  change
    x - proximityOperator ((1 : PosReal) • g) _ x =
      x - proximityOperator ((1 : PosReal) • g)
        (hasUniqueProxPoint_of_mem_gammaZero
          ((1 : PosReal) • g) (smul_mem_gammaZero g hg (1 : PosReal))) x
  exact
    congrArg
      (fun h : HasUniqueProxPoint ((1 : PosReal) • g) ↦
        x - proximityOperator ((1 : PosReal) • g) h x)
      (Subsingleton.elim _ _)

/-- Helper for Remark 14 4: Proposition 12.30 at `γ = 1` identifies the gradient of the unit
Moreau envelope with the residual `Id - Prox`. -/
theorem gradient_unit_moreauEnvelope_toReal_eq_sub_prox
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    ∇ (fun y : H ↦ (({}^[1] g) y).toReal) =
      fun x ↦ x - Prox[g, hg] x := by
  -- Rewrite the unit scaled proximal map to the ordinary proximal map.
  simpa [unit_scaledProx_eq_prox (g := g) (hg := hg)] using
    (gradient_unit_moreauEnvelope_toReal_eq_sub_unit_scaledProx (g := g) (hg := hg))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Remark 14 4: the unit quadratic Moreau kernel is exactly `halfSquaredNorm`. -/
private theorem moreauQuadraticKernel_one_asEReal_eq_halfSquaredNorm_asEReal :
    (moreauQuadraticKernel (H := H) (1 : PosReal)).asEReal =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
  ext x
  -- Evaluate both kernels at `x` and normalize the unit coefficient.
  rw [Function.asEReal_apply, Function.asEReal_apply, moreauQuadraticKernel_apply,
    halfSquaredNorm_apply]
  have hreal :
      (1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by
    ring
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Remark 14 4: the unit Moreau envelopes of `f` and `f*` add pointwise to the
unit quadratic kernel. -/
private theorem unit_moreauEnvelope_add_conjugate_pointwise_eq_unit_moreauQuadraticKernel
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    (({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf))) x =
      (moreauQuadraticKernel (H := H) (1 : PosReal)).asEReal x := by
  let p := Prox[f, hf] x
  let pStar := x - p
  have hpStar :
      pStar = Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf] x := by
    -- The conjugate proximal point is the residual `x - Prox_f x`.
    simpa [p, pStar] using
      (conjugate_proximityOperator_eq_sub_proximityOperator (g := f) (hg := hf) x).symm
  have hmoreau :
      ({}^[1] f) x =
        (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := by
    -- Evaluate the unit envelope of `f` at its proximal point.
    simpa [p] using
      unit_moreauEnvelope_eq_proxValue_add_sqDist_of_mem_gammaZero
        (g := f) (hg := hf) x
  have hmoreauStar :
      ({}^[1] (gammaZeroConjugate f hf)) x =
        (gammaZeroConjugate f hf pStar : EReal) +
          ((((‖x - pStar‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := by
    -- Evaluate the unit envelope of `f*` at the conjugate proximal point.
    simpa [pStar, hpStar] using
      unit_moreauEnvelope_eq_proxValue_add_sqDist_of_mem_gammaZero
        (g := gammaZeroConjugate f hf) (hg := gammaZeroConjugate_mem_gammaZero hf) x
  have hsub :
      x - p ∈ (∂ f) p := by
    -- The primal proximal point yields the contact subgradient.
    simpa [p] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (hf := hf) (x := x) (p := p)).1 rfl
  have hfy :
      (f p : EReal) + (gammaZeroConjugate f hf pStar : EReal) =
        ((⟪p, pStar⟫_ℝ : ℝ) : EReal) := by
    have hsub' : pStar ∈ (∂ f) p := by
      simpa [pStar] using hsub
    -- Fenchel--Young is exact at the primal/conjugate proximal pair.
    simpa [gammaZeroConjugate_apply] using
      (ERealFunction.mem_subdifferential_iff_fenchel_young_eq
        (f := f) hf.2.nonempty p pStar).1 hsub'
  have hdual_res : x - pStar = p := by
    -- Solving for the residual recovers the primal proximal point.
    simp [pStar]
  have hquad1 :
      ((((‖x - p‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) =
        ((((‖pStar‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := by
    -- The first quadratic term is the norm of the residual defining `pStar`.
    simp [pStar]
  have hquad2 :
      ((((‖x - pStar‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) =
        ((((‖p‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := by
    -- The second quadratic term reduces to the primal proximal point.
    simp [hdual_res]
  have hdecomp : x = p + pStar := by
    -- The primal and dual proximal points decompose `x`.
    simp [pStar]
  have hnorm :
      ‖x‖ ^ 2 = ‖p‖ ^ 2 + 2 * ⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 := by
    -- Expand the squared norm of `x = p + pStar`.
    calc
      ‖x‖ ^ 2 = ‖p + pStar‖ ^ 2 := by rw [hdecomp]
      _ = ‖p‖ ^ 2 + 2 * ⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 := by
            simpa using norm_add_sq_real p pStar
  have hfinal :
      ((((‖x‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) =
        (((⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 / 2 + ‖p‖ ^ 2 / 2 : ℝ) : EReal)) := by
    -- Divide the real norm identity by `2` and then cast once to `EReal`.
    have hreal :
        ‖x‖ ^ 2 / (2 * (1 : ℝ)) =
          ⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 / 2 + ‖p‖ ^ 2 / 2 := by
      nlinarith [hnorm]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hsum :
      (({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf))) x =
        (((⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 / 2 + ‖p‖ ^ 2 / 2 : ℝ) : EReal)) := by
    let qStar : EReal := ((((‖pStar‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal))
    let qPrimal : EReal := ((((‖p‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal))
    have hsum' := congrArg (fun t : EReal ↦ qStar + (t + qPrimal)) hfy
    -- Freeze the two finite quadratic terms and insert the Fenchel--Young equality between them.
    rw [Pi.add_apply, hmoreau, hmoreauStar, hquad1, hquad2]
    simpa [qStar, qPrimal, add_assoc, add_left_comm, add_comm] using hsum'
  -- Replace the pointwise sum by the unit quadratic kernel evaluated at `x`.
  calc
    (({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf))) x =
        (((⟪p, pStar⟫_ℝ + ‖pStar‖ ^ 2 / 2 + ‖p‖ ^ 2 / 2 : ℝ) : EReal)) := hsum
    _ = ((((‖x‖ ^ 2) / (2 * (1 : ℝ)) : ℝ) : EReal)) := hfinal.symm
    _ = (moreauQuadraticKernel (H := H) (1 : PosReal)).asEReal x := by
          rw [Function.asEReal_apply, moreauQuadraticKernel_apply]
          simp [div_eq_mul_inv, mul_comm]

-- Proof sketch: specialize Theorem 14.3 (1) to the unit parameter `γ = 1`, so that both Moreau
-- envelopes are regularized by the kernel `q = (1 / 2) ‖·‖²`.
/-- Remark 14.4 (1): for `f ∈ Γ₀(H)` and `q = (1 / 2) ‖·‖²`, Moreau's decomposition gives
`(f □ q) + (f^* □ q) = q`, written here as an identity between the unit Moreau envelopes of `f`
and `f^*` and the unit quadratic kernel. -/
theorem moreauEnvelope_add_conjugateMoreauEnvelope_eq_unitMoreauQuadraticKernel
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf)) =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
  -- Route correction: first prove the pointwise identity at the unit quadratic kernel, and only
  -- then rewrite that kernel to the canonical `halfSquaredNorm` owner.
  funext x
  calc
    (({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf))) x =
        (moreauQuadraticKernel (H := H) (1 : PosReal)).asEReal x := by
          exact
            unit_moreauEnvelope_add_conjugate_pointwise_eq_unit_moreauQuadraticKernel
              (f := f) (hf := hf) x
    _ = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal x := by
          exact
            congrFun
              (moreauQuadraticKernel_one_asEReal_eq_halfSquaredNorm_asEReal (H := H))
              x

-- Proof sketch: specialize Theorem 14.3 (2) to `γ = 1` and identify the resulting unit scaled
-- proximal operators with the ordinary proximal operators of `f` and `f^*`.
/-- Remark 14.4 (2): for `f ∈ Γ₀(H)`, Moreau's decomposition gives the operator identity
`Prox_f + Prox_{f^*} = Id`. -/
theorem proximityOperator_add_conjugateProximityOperator_eq_id_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] + Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf] = id := by
  funext x
  -- Curry the pointwise conjugate proximal identity into an operator equality.
  change Prox[f, hf] x + Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf] x = id x
  rw [conjugate_proximityOperator_eq_sub_proximityOperator (g := f) (hg := hf) x]
  simp

-- Proof sketch: combine Proposition 12.30 at the unit parameter with Remark 14.4 (2), which
-- rewrites the residual map `Id - Prox_f` as the gradient of the unit Moreau envelope.
/-- Remark 14.4 (3): using Proposition 12.30, the proximal operator is the residual
`Id - ∇ (f □ q)` of the gradient of the unit Moreau envelope. -/
theorem proximityOperator_eq_id_sub_gradient_moreauEnvelope_toReal_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] =
      id - ∇ (fun y : H ↦ (({}^[1] f) y).toReal) := by
  funext x
  change Prox[f, hf] x = id x - ∇ (fun y : H ↦ (({}^[1] f) y).toReal) x
  have hgrad :=
    congrFun (gradient_unit_moreauEnvelope_toReal_eq_sub_prox (g := f) (hg := hf)) x
  -- Rearrange `x - (x - Prox_f x)` to isolate `Prox_f x`.
  calc
    Prox[f, hf] x = x - (x - Prox[f, hf] x) := by abel_nf
    _ = id x - ∇ (fun y : H ↦ (({}^[1] f) y).toReal) x := by
          simp [hgrad]

-- Proof sketch: apply Proposition 12.30 to `f^*`, use `γ = 1`, and substitute the identity from
-- Remark 14.4 (2) to replace `Id - Prox_{f^*}` by `Prox_f`.
/-- Remark 14.4 (4): using Proposition 12.30, the proximal operator of `f` is also the gradient of
the unit Moreau envelope of `f^*`. -/
theorem proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] =
      ∇ (fun y : H ↦ (({}^[1] (gammaZeroConjugate f hf)) y).toReal) := by
  funext x
  have hgrad :=
    congrFun
      (gradient_unit_moreauEnvelope_toReal_eq_sub_prox
        (g := gammaZeroConjugate f hf) (hg := gammaZeroConjugate_mem_gammaZero hf)) x
  have hproxStar :
      Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf] x = x - Prox[f, hf] x := by
    simpa using conjugate_proximityOperator_eq_sub_proximityOperator (g := f) (hg := hf) x
  -- Rewrite the conjugate envelope gradient as the residual of the conjugate proximal operator.
  calc
    Prox[f, hf] x = x - (x - Prox[f, hf] x) := by abel_nf
    _ = x - Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf] x := by rw [hproxStar]
    _ = ∇ (fun y : H ↦ (({}^[1] (gammaZeroConjugate f hf)) y).toReal) x := by
          simpa using hgrad.symm

end MoreauDecomposition

end ERealFunction

section

open ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For a nonempty closed convex cone, the Chebyshev theorem for the negative polar reads equally
as the Chebyshev theorem for the textbook polar-cone notation `Kᵒ⊖`. -/
theorem isChebyshev_negativePolar_of_nonempty_isClosed_convexCone
    (K : ConvexCone ℝ H) (hK_nonempty : (K : Set H).Nonempty) (hK_closed : IsClosed (K : Set H)) :
    IsChebyshev ((K : Set H)ᵒ⊖) := by
  -- The negative polar is again nonempty, closed, and convex, so Chapter 3 applies directly.
  let _ := hK_nonempty
  let _ := hK_closed
  have hnonempty : (((K : Set H)ᵒ⊖ : Set H)).Nonempty := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_nonempty (K : Set H)
  have hclosed : IsClosed (((K : Set H)ᵒ⊖ : Set H)) := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_isClosed (K : Set H)
  have hconvex : Convex ℝ (((K : Set H)ᵒ⊖ : Set H)) := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_convex (K : Set H)
  exact
    isChebyshev_of_nonempty_isClosed_convex hnonempty hclosed hconvex

-- Semantic recall: Proposition 12.32 already uses the source-level nonempty closed convex cone
-- surface for `K` and `Kᵒ⊖`; Remark 14.4 keeps that same level rather than strengthening to
-- `ProperCone ℝ H`.
-- Proof sketch: specialize the conical decomposition from Remark 14.4 to the source-level
-- nonempty closed convex cone `K`, viewed in the project through its metric projections.
/-- Remark 14.4 (5): when `f = ι_K` for a nonempty closed convex cone `K`, Moreau's decomposition
recovers the conical decomposition of Theorem 6.30:
`x = P_K x + P_{Kᵒ⊖} x`. -/
theorem eq_projectionPoint_add_projectionPoint_negativePolar_of_nonempty_isClosed_convexCone
    (K : ConvexCone ℝ H) (hK_nonempty : (K : Set H).Nonempty) (hK_closed : IsClosed (K : Set H))
    (x : H) :
    x =
      projectionPoint (K : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed K.convex) x +
        projectionPoint ((K : Set H)ᵒ⊖)
          (isChebyshev_negativePolar_of_nonempty_isClosed_convexCone
            K hK_nonempty hK_closed) x := by
  classical
  let hKp : ∃ C : ProperCone ℝ H, (C : ConvexCone ℝ H) = K :=
    CanLift.prf K ⟨hK_nonempty, hK_closed⟩
  let Kp : ProperCone ℝ H := Classical.choose hKp
  have hKp_cone : (Kp : ConvexCone ℝ H) = K := Classical.choose_spec hKp
  have hKp_set : (Kp : Set H) = (K : Set H) := by
    change (((Kp : ConvexCone ℝ H) : Set H)) = ((K : ConvexCone ℝ H) : Set H)
    simpa using congrArg (fun C : ConvexCone ℝ H ↦ (C : Set H)) hKp_cone
  have hpolar_eq : Set.negativePolar (Kp : Set H) = ((K : Set H)ᵒ⊖ : Set H) := by
    simpa [Set.negativePolar, hKp_set] using (Set.polarCone_eq_innerDual_neg (K : Set H)).symm
  have hbest :
      IsBestApproximation x (K : Set H)
        (projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x) := by
    refine ⟨?_, ?_⟩
    · rw [← hKp_set]
      exact
        (projectionPoint_isBestApproximation
          (Kp : Set H) (isChebyshev_of_properCone Kp) x).1
    · rw [← hKp_set]
      exact
        (projectionPoint_isBestApproximation
          (Kp : Set H) (isChebyshev_of_properCone Kp) x).2
  have hproj_eq :
      projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x =
        projectionPoint (K : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed K.convex) x := by
    exact
      eq_projectionPoint_of_isBestApproximation
        (K : Set H)
        (isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed K.convex)
        hbest
  have hpolar_best :
      IsBestApproximation x ((K : Set H)ᵒ⊖ : Set H)
        (projectionPoint (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x) := by
    refine ⟨?_, ?_⟩
    · rw [← hpolar_eq]
      exact
        (projectionPoint_isBestApproximation
          (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x).1
    · rw [← hpolar_eq]
      exact
        (projectionPoint_isBestApproximation
          (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x).2
  have hpolar_proj_eq :
      projectionPoint (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x =
        projectionPoint ((K : Set H)ᵒ⊖)
          (isChebyshev_negativePolar_of_nonempty_isClosed_convexCone
            K hK_nonempty hK_closed) x := by
    exact
      eq_projectionPoint_of_isBestApproximation
        ((K : Set H)ᵒ⊖)
        (isChebyshev_negativePolar_of_nonempty_isClosed_convexCone K hK_nonempty hK_closed)
        hpolar_best
  -- Transport Theorem 6.30 across the carrier equalities of the lifted proper cone.
  calc
    x =
        projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x +
          projectionPoint (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x := by
      simpa using eq_projectionPoint_add_projectionPoint_negativePolar Kp x
    _ =
        projectionPoint (K : Set H)
            (isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed K.convex) x +
          projectionPoint ((K : Set H)ᵒ⊖)
            (isChebyshev_negativePolar_of_nonempty_isClosed_convexCone
              K hK_nonempty hK_closed) x := by
      rw [hproj_eq, hpolar_proj_eq]

-- Proof sketch: curry the pointwise conical decomposition from
-- `eq_projectionPoint_add_projectionPoint_negativePolar_of_nonempty_isClosed_convexCone`.
/-- Companion to Remark 14.4 (5): the source-level conical decomposition also yields the operator
identity `P_K + P_{Kᵒ⊖} = Id`. -/
theorem projectionPoint_add_projectionPoint_negativePolar_eq_id
    (K : ConvexCone ℝ H) (hK_nonempty : (K : Set H).Nonempty) (hK_closed : IsClosed (K : Set H)) :
    projectionPoint (K : Set H)
        (isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed K.convex) +
        projectionPoint ((K : Set H)ᵒ⊖)
          (isChebyshev_negativePolar_of_nonempty_isClosed_convexCone K hK_nonempty hK_closed) =
      id := by
  funext x
  -- Curry the pointwise conical decomposition into an operator identity.
  simpa using
    eq_projectionPoint_add_projectionPoint_negativePolar_of_nonempty_isClosed_convexCone
      K hK_nonempty hK_closed x |>.symm

-- Proof sketch: transport Theorem 6.30 (3) from the proper-cone presentation back to the
-- source-level nonempty closed convex cone `K`.
/-- Companion to Remark 14.4 (5): the same conical decomposition recovers the squared-distance
identity `‖x‖^2 = d(x,K)^2 + d(x,Kᵒ⊖)^2`. -/
theorem norm_sq_eq_infDist_sq_add_infDist_sq_negativePolar_of_nonempty_isClosed_convexCone
    (K : ConvexCone ℝ H) (hK_nonempty : (K : Set H).Nonempty) (hK_closed : IsClosed (K : Set H))
    (x : H) :
    ‖x‖ ^ 2 = Metric.infDist x (K : Set H) ^ 2 + Metric.infDist x ((K : Set H)ᵒ⊖) ^ 2 := by
  classical
  let hKp : ∃ C : ProperCone ℝ H, (C : ConvexCone ℝ H) = K :=
    CanLift.prf K ⟨hK_nonempty, hK_closed⟩
  let Kp : ProperCone ℝ H := Classical.choose hKp
  have hKp_cone : (Kp : ConvexCone ℝ H) = K := Classical.choose_spec hKp
  have hKp_set : (Kp : Set H) = (K : Set H) := by
    change (((Kp : ConvexCone ℝ H) : Set H)) = ((K : ConvexCone ℝ H) : Set H)
    simpa using congrArg (fun C : ConvexCone ℝ H ↦ (C : Set H)) hKp_cone
  have hpolar_eq : Set.negativePolar (K : Set H) = ((K : Set H)ᵒ⊖ : Set H) := by
    simpa [Set.negativePolar] using (Set.polarCone_eq_innerDual_neg (K : Set H)).symm
  -- Transport Theorem 6.30(3) across the same carrier identifications.
  simpa [hKp_set, hpolar_eq] using
    norm_sq_eq_infDist_sq_add_infDist_sq_negativePolar Kp x

-- Proof sketch: combine Corollary 3.24's distance formulas
-- `d(x,V) = ‖P_{Vᗮ} x‖` and `d(x,Vᗮ) = ‖P_V x‖` with the Pythagorean identity
-- `‖x‖² = ‖P_V x‖² + ‖P_{Vᗮ} x‖²`.
/-- Remark 14.4 (6): if `V` is a closed linear subspace, then the squared distances to `V` and
`Vᗮ` add up to the squared norm: `d_V^2 + d_{Vᗮ}^2 = ‖·‖^2`. -/
theorem sq_infDist_add_sq_infDist_orthogonal_eq_norm_sq
    (V : ClosedSubmodule ℝ H) :
    (fun x : H ↦ Metric.infDist x (V : Set H) ^ 2 + Metric.infDist x (Vᗮ : Set H) ^ 2) =
      fun x : H ↦ ‖x‖ ^ 2 := by
  funext x
  -- Rewrite both distances by Corollary 3.24 and finish with the orthogonal Pythagorean identity.
  rw [infDist_eq_norm_orthogonalProjection_orthogonal (V := V) (x := x),
    infDist_orthogonal_eq_norm_orthogonalProjection (V := V) (x := x)]
  simpa [add_comm] using
    (norm_sq_eq_add_norm_sq_orthogonalProjection (V := V) (x := x)).symm

-- Proof sketch: rewrite Corollary 3.24 (7), namely `P_{Vᗮ} = Id - P_V`, into the equivalent
-- projector decomposition `P_V + P_{Vᗮ} = Id`.
/-- Remark 14.4 (7): if `V` is a closed linear subspace, then the orthogonal projectors satisfy
`P_V + P_{Vᗮ} = Id`. -/
theorem starProjection_add_starProjection_orthogonal_eq_one
    (V : ClosedSubmodule ℝ H) :
    V.starProjection + Vᗮ.starProjection = 1 := by
  ext x
  -- Rewrite `P_{Vᗮ}` as `Id - P_V` and simplify the resulting pointwise identity.
  change V.starProjection x + Vᗮ.starProjection x = x
  rw [starProjection_orthogonal_eq_one_sub (V := V)]
  simp [sub_eq_add_neg]

end
