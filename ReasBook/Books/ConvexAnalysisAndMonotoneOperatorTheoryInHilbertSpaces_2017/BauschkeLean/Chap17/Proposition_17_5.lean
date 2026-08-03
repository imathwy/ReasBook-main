import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_33
import BauschkeLean.Chap16.Proposition_16_45
import BauschkeLean.Chap16.Theorem_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The contact set `C = {x | f x = {}^γ f x}` of `f` with its `γ`-Moreau envelope. -/
def moreauEnvelopeContactSet
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) : Set H :=
  {x | (f x : EReal) = ({}^[γ] f) x}

-- Proof sketch: unfold `moreauEnvelopeContactSet`; membership is exactly the defining equality
-- `f x = {}^γ f x`.
omit [CompleteSpace H] in
/-- Membership in the Moreau-envelope contact set is exactly the equality `f x = {}^γ f x`. -/
theorem mem_moreauEnvelopeContactSet_iff
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x : H} :
    x ∈ moreauEnvelopeContactSet f γ ↔ (f x : EReal) = ({}^[γ] f) x := by
  -- The contact set is defined by this equality.
  rfl

omit [CompleteSpace H] in
/-- Helper for Proposition 17 5: a point is a proximal point of the scaled function `γ • f` at
itself exactly when it lies in the Moreau-envelope contact set of `f`. -/
theorem self_scaled_proxPoint_iff_mem_moreauEnvelopeContactSet
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x : H} :
    IsProxPoint (γ • f) x x ↔ x ∈ moreauEnvelopeContactSet f γ := by
  have hone : γ * (1 : PosReal) = γ := by
    ext
    simp
  have hscale := congrArg (fun g : H → EReal ↦ g x)
    (moreauEnvelope_smul_eq_smul_moreauEnvelope f γ (1 : PosReal))
  have hscale' : {}^[(1 : PosReal)] (γ • f) x = (γ : EReal) * ({}^[γ] f) x := by
    simpa [hone, smul_eq_mul] using hscale
  have hγ_bot : ((γ : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hγ_top : ((γ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hγ_zero : ((γ : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt γ.2)
  constructor
  · intro hx
    -- Rewrite the unit-envelope identity for `γ • f` and cancel the positive scalar `γ`.
    have hunit := (isProxPoint_iff_moreauEnvelope_eq (γ • f) x x).1 hx
    have hmul : ((γ : ℝ) : EReal) * ({}^[γ] f) x = ((γ : ℝ) : EReal) * (f x : EReal) := by
      calc
        ((γ : ℝ) : EReal) * ({}^[γ] f) x = {}^[(1 : PosReal)] (γ • f) x := hscale'.symm
        _ = ((γ • f) x : EReal) + ((((1 / 2 : ℝ) * ‖x - x‖ ^ 2 : ℝ) : EReal)) := hunit
        _ = ((γ : ℝ) : EReal) * (f x : EReal) := by
          simp
    have hdiv := congrArg (fun t : EReal => t / ((γ : ℝ) : EReal)) hmul
    have hcancel_left :
        ((((γ : ℝ) : EReal) * ({}^[γ] f) x) / ((γ : ℝ) : EReal)) = ({}^[γ] f) x := by
      rw [EReal.div_eq_iff hγ_bot hγ_top hγ_zero]
      simp [mul_comm]
    have hcancel_right :
        ((((γ : ℝ) : EReal) * (f x : EReal)) / ((γ : ℝ) : EReal)) = (f x : EReal) := by
      rw [EReal.div_eq_iff hγ_bot hγ_top hγ_zero]
      simp [mul_comm]
    rw [mem_moreauEnvelopeContactSet_iff]
    have hEq : ({}^[γ] f) x = (f x : EReal) := by
      simpa [hcancel_left, hcancel_right] using hdiv
    exact hEq.symm
  · intro hx
    -- Rescale the contact equality back into the unit-envelope identity for `γ • f`.
    rw [mem_moreauEnvelopeContactSet_iff] at hx
    rw [isProxPoint_iff_moreauEnvelope_eq]
    calc
      {}^[(1 : PosReal)] (γ • f) x = (γ : EReal) * ({}^[γ] f) x := hscale'
      _ = (γ : EReal) * (f x : EReal) := by rw [hx]
      _ = ((γ • f) x : EReal) + ((((1 / 2 : ℝ) * ‖x - x‖ ^ 2 : ℝ) : EReal)) := by
        simp

/- The local helper below replaces the direct import of Chapter 12 Proposition 12.29, whose
current file-level dependency is broken upstream. The statement is the same ordinary fixed-point /
argmin identification needed in this file. -/
/-- Helper for Proposition 17 5: for `f ∈ Γ₀(H)`, the fixed points of the ordinary proximity
operator coincide with the global minimizers of `f`. -/
private theorem fixedPoints_proximityOperator_eq_argmin_local_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Function.fixedPoints (Prox[f, hf]) = Argmin f.asEReal := by
  ext x
  rw [Function.mem_fixedPoints_iff, mem_argmin_iff, isMinOn_univ_iff]
  constructor
  · intro hx y
    have hx_prox : IsProxPoint f x x := by
      simpa [hx] using
        proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
    simpa using (isProxPoint_iff_forall_inner_add_le f hf.2 x x).1 hx_prox y
  · intro hx
    have hx_prox : IsProxPoint f x x := by
      rw [isProxPoint_iff_forall_inner_add_le f hf.2 x x]
      intro y
      simpa using hx y
    have hx_eq : x = Prox[f, hf] x := by
      simpa [eq_comm] using
        eq_proximityOperator_of_isProxPoint
          f
          (hasUniqueProxPoint_of_mem_gammaZero f hf)
          hx_prox
    simpa [Function.mem_fixedPoints_iff] using hx_eq.symm

-- Proof sketch: combine the self-proximality/contact-set equivalence with the pointwise fixed
-- point characterization of the proximity operator of `γ • f`.
/-- Proposition 17 5: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the fixed points of
`Prox_{γ f}` are exactly the points `x` where `f x = {}^γ f x`, i.e. the
textbook set `C`. -/
theorem fixedPoints_scaledProximityOperator_eq_moreauEnvelopeContactSet_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = moreauEnvelopeContactSet f γ := by
  ext x
  constructor
  · intro hx_fix
    -- A fixed point of `Prox_{γ f}` is a self-proximal point for `γ • f`.
    have hx_prox_raw : IsProxPoint (γ • f) x (Prox[γ, f, hf] x) := by
      simpa [scaledProximityOperator] using
        proximityOperator_isProxPoint (γ • f)
          (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ)) x
    have hx_prox : IsProxPoint (γ • f) x x := by
      rw [Function.mem_fixedPoints_iff] at hx_fix
      simpa [hx_fix] using hx_prox_raw
    exact (self_scaled_proxPoint_iff_mem_moreauEnvelopeContactSet f γ).1 hx_prox
  · intro hx_contact
    -- The contact-set characterization identifies the unique scaled proximal point with `x`.
    have hx_prox : IsProxPoint (γ • f) x x :=
      (self_scaled_proxPoint_iff_mem_moreauEnvelopeContactSet f γ).2 hx_contact
    have hx_eq : x = Prox[γ, f, hf] x := by
      simpa [scaledProximityOperator] using
        eq_proximityOperator_of_isProxPoint (γ • f)
          (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ)) hx_prox
    simpa [Function.mem_fixedPoints_iff] using hx_eq.symm

-- Proof sketch: view `Prox[γ, f, hf]` as the ordinary proximity operator of the scaled function
-- `γ • f`, then apply the ordinary fixed-point/minimizer theorem.
/-- The fixed points of `Prox_{γ f}` are exactly the global minimizers of the scaled function
`γ f`. -/
theorem fixedPoints_scaledProximityOperator_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = Argmin (γ • f).asEReal := by
  -- `Prox_{γ f}` is the ordinary proximity operator of `γ • f`.
  simpa [scaledProximityOperator] using
    fixedPoints_proximityOperator_eq_argmin_local_of_mem_gammaZero
      (γ • f) (smul_mem_gammaZero f hf γ)

/-- Helper for Proposition 17 5: a positive common right factor can be canceled from an `EReal`
inequality. -/
private theorem le_of_mul_le_mul_of_pos_right
    {a b : EReal} {c : ℝ} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  -- Divide by the positive factor and simplify both quotients.
  have hdiv :
      (a * c) / (c : EReal) ≤ (b * c) / (c : EReal) := by
    exact EReal.div_le_div_right_of_nonneg
      (show (0 : EReal) ≤ (c : EReal) by exact_mod_cast hc.le) h
  have hc_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hc_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hc_zero : ((c : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hcancel_a : (a * c) / (c : EReal) = a := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  have hcancel_b : (b * c) / (c : EReal) = b := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  simpa [hcancel_a, hcancel_b] using hdiv

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 17 5: positive pointwise scaling preserves global minimality on the
whole space. -/
theorem isMinOn_univ_posReal_smul_iff
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x : H} :
    IsMinOn (γ • f).asEReal Set.univ x ↔ IsMinOn f.asEReal Set.univ x := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx y
    -- Cancel the common positive factor `γ` from the scaled minimizing inequality.
    have hscaled : (f x : EReal) * (γ : ℝ) ≤ (f y : EReal) * (γ : ℝ) := by
      simpa [Function.asEReal, posReal_smul_apply, mul_comm] using hx y
    exact le_of_mul_le_mul_of_pos_right hscaled γ.2
  · intro hx y
    -- Multiply the original minimizing inequality by the nonnegative scalar `γ`.
    have hmul :
        ((γ : ℝ) : EReal) * (f x : EReal) ≤ ((γ : ℝ) : EReal) * (f y : EReal) := by
      exact mul_le_mul_of_nonneg_left (hx y) (by exact_mod_cast γ.2.le)
    simpa [Function.asEReal, posReal_smul_apply] using hmul

-- Proof sketch: positive pointwise scaling by `γ ∈ ℝ_{++}` preserves the order relation on
-- `EReal`, so the minimizers of `γ f` and `f` coincide.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Positive scaling does not change the global minimizers of a function. -/
theorem argmin_posReal_smul_eq_argmin
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    Argmin (γ • f).asEReal = Argmin f.asEReal := by
  ext x
  -- Reduce argmin membership to the whole-space minimizing predicate.
  rw [mem_argmin_iff, mem_argmin_iff, isMinOn_univ_posReal_smul_iff]

-- Proof sketch: combine the scaled-argmin clause above with the invariance of argmin sets under
-- positive scaling.
/-- The fixed points of `Prox_{γ f}` are exactly the global minimizers of `f`. -/
theorem fixedPoints_scaledProximityOperator_eq_argmin_original_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = Argmin f.asEReal := by
  rw [fixedPoints_scaledProximityOperator_eq_argmin_of_mem_gammaZero,
    argmin_posReal_smul_eq_argmin f γ]

/-- Helper for Proposition 17 5: minimizing the Moreau envelope is equivalent to being a fixed
point of the scaled proximity operator. -/
private theorem mem_argmin_moreauEnvelope_iff_mem_fixedPoints_scaledProximityOperator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) {x : H} :
    x ∈ Argmin ({}^[γ] f) ↔ x ∈ Function.fixedPoints (Prox[γ, f, hf]) := by
  rw [Function.mem_fixedPoints_iff, mem_argmin_iff, isMinOn_univ_iff]
  constructor
  · intro hx_argmin
    let p := Prox[γ, f, hf] x
    have hmoreau_x :
        ({}^[γ] f) x =
          (f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      -- Remark 12.24 gives the exact Moreau-envelope value at `x`.
      simpa [p] using moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero f hf γ x
    have hmoreau_p_le : ({}^[γ] f) p ≤ (f p : EReal) := by
      -- Evaluating the infimum at `y = p` bounds the envelope above by the function value.
      calc
        ({}^[γ] f) p =
            ⨅ y : H,
              (f y : EReal) +
                ((((1 / (2 * (γ : ℝ))) * ‖p - y‖ ^ 2 : ℝ) : EReal)) := by
          simpa using moreauEnvelope_apply (f := f) (γ := γ) (x := p)
        _ ≤
            (f p : EReal) +
              ((((1 / (2 * (γ : ℝ))) * ‖p - p‖ ^ 2 : ℝ) : EReal)) := by
          exact iInf_le _ p
        _ = (f p : EReal) := by
          simp
    have hsum :
        (f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) ≤
          (f p : EReal) := by
      rw [← hmoreau_x]
      exact le_trans (hx_argmin p) hmoreau_p_le
    rcases hf.2.nonempty with ⟨z, hz⟩
    have hmoreau_x_top : ({}^[γ] f) x ≠ ⊤ := by
      -- A finite comparison point in the effective domain bounds the envelope away from `⊤`.
      let q : EReal :=
        (f z : EReal) +
          ((((1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ 2 : ℝ) : EReal))
      have hbound : ({}^[γ] f) x ≤ q := by
        rw [moreauEnvelope_apply]
        exact iInf_le _ z
      have hq_ne_top : q ≠ ⊤ := by
        dsimp [q]
        exact EReal.add_ne_top (ne_of_lt (mem_effectiveDomain_iff.mp hz)) (EReal.coe_ne_top _)
      intro hx_top
      have hq_top : q = ⊤ := by
        exact le_antisymm le_top (by simpa [hx_top] using hbound)
      exact hq_ne_top hq_top
    have hfp_top : (f p : EReal) ≠ ⊤ := by
      intro hfp_top
      exact hmoreau_x_top (by simp [hmoreau_x, hfp_top])
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hsum_bot :
        (f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) ≠ ⊥ := by
      exact (EReal.add_ne_bot_iff).2 ⟨hfp_bot, EReal.coe_ne_bot _⟩
    have hsum_top :
        (f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) ≠ ⊤ := by
      exact EReal.add_ne_top hfp_top (EReal.coe_ne_top _)
    have hsum_real_eq :
        ((f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal))).toReal =
          (f p : EReal).toReal + (‖x - p‖ ^ 2) / (2 * (γ : ℝ)) := by
      rw [EReal.toReal_add hfp_top hfp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    have hsum_real :
        (f p : EReal).toReal + (‖x - p‖ ^ 2) / (2 * (γ : ℝ)) ≤ (f p : EReal).toReal := by
      -- Once both sides are finite, `toReal` preserves the inequality.
      simpa [hsum_real_eq] using EReal.toReal_le_toReal hsum hsum_bot hfp_top
    have hsq_div_zero : (‖x - p‖ ^ 2) / (2 * (γ : ℝ)) = 0 := by
      have hden_pos : 0 < 2 * (γ : ℝ) := by
        nlinarith [γ.2]
      have hsq_div_nonneg : 0 ≤ (‖x - p‖ ^ 2) / (2 * (γ : ℝ)) := by
        exact div_nonneg (by positivity) hden_pos.le
      linarith
    have hsq_zero : ‖x - p‖ ^ 2 = 0 := by
      have hden_ne : (2 * (γ : ℝ)) ≠ 0 := by
        exact ne_of_gt (by nlinarith [γ.2])
      rcases (div_eq_zero_iff.mp hsq_div_zero) with hsq_zero | hden_zero
      · exact hsq_zero
      · exact False.elim (hden_ne hden_zero)
    have hsub_zero : x - p = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero)
    have hx_eq : x = p := sub_eq_zero.mp hsub_zero
    simpa [p] using hx_eq.symm
  · intro hx_fix
    have hx_argmin_f : x ∈ Argmin f.asEReal := by
      rw [← fixedPoints_scaledProximityOperator_eq_argmin_original_of_mem_gammaZero f hf γ]
      exact hx_fix
    rw [mem_argmin_iff, isMinOn_univ_iff] at hx_argmin_f
    have hx_contact : x ∈ moreauEnvelopeContactSet f γ := by
      rw [←
        fixedPoints_scaledProximityOperator_eq_moreauEnvelopeContactSet_of_mem_gammaZero
          f hf γ]
      exact hx_fix
    have hx_moreau : ({}^[γ] f) x = (f x : EReal) := by
      exact (mem_moreauEnvelopeContactSet_iff f γ).1 hx_contact |>.symm
    intro y
    have hfx_le_moreau_y : (f x : EReal) ≤ ({}^[γ] f) y := by
      -- Any pointwise minimizer of `f` bounds every translated quadratic objective from below.
      rw [moreauEnvelope_apply]
      refine le_iInf ?_
      intro z
      have hcoeff_nonneg : 0 ≤ (1 / (2 * (γ : ℝ)) : ℝ) := by
        exact one_div_nonneg.mpr (by nlinarith [γ.2])
      have hquad_nonneg :
          (0 : EReal) ≤
            ((((1 / (2 * (γ : ℝ))) * ‖y - z‖ ^ 2 : ℝ) : EReal)) := by
        exact_mod_cast
          (mul_nonneg hcoeff_nonneg (sq_nonneg ‖y - z‖))
      calc
        (f x : EReal) ≤ (f z : EReal) := hx_argmin_f z
        _ ≤
            (f z : EReal) +
              ((((1 / (2 * (γ : ℝ))) * ‖y - z‖ ^ 2 : ℝ) : EReal)) := by
          exact le_add_of_nonneg_right hquad_nonneg
    rw [hx_moreau]
    exact hfx_le_moreau_y

-- Proof sketch: Proposition 17.4 identifies the minimizers of the differentiable convex function
-- `{}^γ f` with the zeros of its gradient, and Proposition 12.30 rewrites that gradient as the
-- residual `γ⁻¹ • (Id - Prox_{γ f})`. The vanishing-gradient condition is therefore exactly
-- `f x = {}^γ f x`.
/-- The Moreau-envelope contact set is exactly the set of minimizers of the `γ`-Moreau envelope. -/
theorem moreauEnvelopeContactSet_eq_argmin_moreauEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (γ : PosReal) :
    moreauEnvelopeContactSet f γ = Argmin ({}^[γ] f) := by
  -- Route correction: identify argmin points of the Moreau envelope with fixed points of
  -- `Prox_{γ f}`, then rewrite those fixed points as the contact set.
  rw [← fixedPoints_scaledProximityOperator_eq_moreauEnvelopeContactSet_of_mem_gammaZero f _hf γ]
  ext x
  exact (mem_argmin_moreauEnvelope_iff_mem_fixedPoints_scaledProximityOperator f _hf γ).symm

-- Proof sketch: combine Proposition 12.30 with Proposition 17.4 to identify
-- `Argmin ({}^γ f)` with `Function.fixedPoints (Prox[γ, f, hf])`, then use the
-- previous fixed-point description by minimizers of `f`.
/-- The minimizers of the `γ`-Moreau envelope coincide with the minimizers of `f`. -/
theorem argmin_moreauEnvelope_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Argmin ({}^[γ] f) = Argmin f.asEReal := by
  -- Both argmin sets are already identified with the same fixed-point set of `Prox_{γ f}`.
  calc
    Argmin ({}^[γ] f) = moreauEnvelopeContactSet f γ := by
      symm
      exact moreauEnvelopeContactSet_eq_argmin_moreauEnvelope_of_mem_gammaZero f _hf γ
    _ = Function.fixedPoints (Prox[γ, f, _hf]) := by
      symm
      exact
        fixedPoints_scaledProximityOperator_eq_moreauEnvelopeContactSet_of_mem_gammaZero
          f _hf γ
    _ = Argmin f.asEReal := by
      exact fixedPoints_scaledProximityOperator_eq_argmin_original_of_mem_gammaZero f _hf γ

/-- Helper for Proposition 17 5: the zeros of `Prox_{f*}` are exactly the points lying in the
subdifferential of `f*` at `0`. -/
theorem mem_zeros_conjugateProximityOperator_iff_mem_subdifferential_gammaZeroConjugate_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) {x : H} :
    x ∈ (Function.toSetValuedOperator (Prox⋆[f, hf])).zeros ↔
      x ∈ (∂ (f∗[hf])) 0 := by
  constructor
  · intro hx_zero
    -- Unfold the singleton-valued zero set and rewrite it as a proximal-point condition at `0`.
    rw [SetValuedOperator.mem_zeros_iff, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hx_zero
    have hx_prox : IsProxPoint (f∗[hf]) x 0 := by
      simpa [hx_zero] using
        proximityOperator_isProxPoint (f∗[hf])
          (hasUniqueProxPoint_of_mem_gammaZero (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)) x
    -- At `p = 0`, Proposition 12.26 is exactly the subgradient inequality for `f*`.
    refine (mem_subdifferential_iff (f := f∗[hf]) (x := (0 : H)) (u := x)).2 ?_
    intro y
    have hzero : (f∗[hf] (0 : H) : EReal) = f.asEReal∗ (0 : H) := gammaZeroConjugate_apply f hf 0
    have hy : (f∗[hf] y : EReal) = f.asEReal∗ y := gammaZeroConjugate_apply f hf y
    calc
      (⟪y - (0 : H), x⟫_ℝ : EReal) + (f∗[hf] (0 : H) : EReal)
          = (⟪y, x⟫_ℝ : EReal) + f.asEReal∗ (0 : H) := by
        rw [hzero]
        simp
      _ ≤ f.asEReal∗ y := by
        simpa [conjugate_apply] using
          (isProxPoint_iff_forall_inner_add_le (f∗[hf])
            (gammaZeroConjugate_mem_gammaZero hf).2 x 0).1 hx_prox y
      _ = (f∗[hf] y : EReal) := hy.symm
  · intro hx_sub
    -- Rewrite the subgradient condition at `0` back into self-proximality of `0` for `f*`.
    have hx_sub' :
        ∀ y : H, (⟪y - (0 : H), x⟫_ℝ : EReal) + (f∗[hf] (0 : H) : EReal) ≤ (f∗[hf] y : EReal) :=
      (mem_subdifferential_iff (f := f∗[hf]) (x := (0 : H)) (u := x)).1 hx_sub
    have hx_prox : IsProxPoint (f∗[hf]) x 0 := by
      rw [isProxPoint_iff_forall_inner_add_le (f∗[hf])
        (gammaZeroConjugate_mem_gammaZero hf).2 x 0]
      simpa [gammaZeroConjugate_apply] using hx_sub'
    have hx_eq : 0 = Prox⋆[f, hf] x := by
      simpa using
        eq_proximityOperator_of_isProxPoint (f∗[hf])
          (hasUniqueProxPoint_of_mem_gammaZero (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf))
          hx_prox
    -- The singleton-valued zero condition is exactly `Prox_{f*} x = 0`.
    rw [SetValuedOperator.mem_zeros_iff, Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    exact hx_eq

-- Proof sketch: identify the zero set of `Prox_{f*}` with `∂f*(0)`, then use the previous
-- minimizer/subgradient theorem.
/-- The zeros of the proximity operator of the Fenchel conjugate `f*` are exactly the minimizers
of `f`. -/
theorem conjugateProximityOperator_zeroSet_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (Function.toSetValuedOperator (Prox⋆[f, hf])).zeros = Argmin f.asEReal := by
  -- The final clause is the zero-set bridge above plus the minimizer/subgradient owner theorem.
  ext x
  rw [mem_zeros_conjugateProximityOperator_iff_mem_subdifferential_gammaZeroConjugate_zero,
    ← argmin_eq_subdifferential_gammaZeroConjugate_zero f hf]

/- Proposition 17.5, final clause: the minimizers of `f` are exactly the subgradients of the
Fenchel conjugate `f*` at `0`. This is the earlier canonical owner theorem
`argmin_eq_subdifferential_gammaZeroConjugate_zero`. -/
recall argmin_eq_subdifferential_gammaZeroConjugate_zero

end

end ERealFunction
