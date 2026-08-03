import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Proposition_12_29
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap16.Proposition_16_33
import BauschkeLean.Chap24.Definition_24_48

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section ProximalThresholding

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H}
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))

-- Semantic recall/local precedent: clause `(i)` uses the Chapter 24 source-facing owner
-- `Function.IsProximalThresholderOn`, with the zero-set identity kept as a bridge companion;
-- clauses `(ii)` and `(iii)` use the fixed-point and argmin owners `Function.fixedPoints`,
-- `Prox⋆[f, hf]`, and `Argmin`; clause `(iv)` uses the project support-function notation `σ[Ω]`.

/-- Helper for Proposition 24.49: membership in the zero set of `Prox[f, hf]` is exactly
membership in `(∂ f) 0`. -/
lemma mem_proxZeros_iff_mem_subdifferential_zero {x : H} :
    x ∈ (Prox[f, hf]).toSetValuedOperator.zeros ↔ x ∈ (∂ f) 0 := by
  -- Unfold the singleton-valued zero set and rewrite `0 = Prox[f, hf] x` via Proposition 24.1.
  rw [SetValuedOperator.mem_zeros_iff, Function.toSetValuedOperator_apply,
    Set.mem_singleton_iff]
  simpa [sub_zero, eq_comm] using
    (eq_proximityOperator_iff_sub_mem_subdifferential f hf :
      0 = Prox[f, hf] x ↔ x - 0 ∈ (∂ f) 0)

/-- Helper for Proposition 24.49: the minimizers of `f∗[hf]` are exactly the subgradients of `f`
at `0`. -/
lemma conjugateArgmin_eq_subdifferentialZero :
    Argmin ((f∗[hf]).asEReal) = (∂ f) 0 := by
  -- First express the argmin of `f∗` as the subdifferential of its conjugate at `0`.
  calc
    Argmin ((f∗[hf]).asEReal) = (∂ ((f∗[hf])∗[gammaZeroConjugate_mem_gammaZero hf])) 0 := by
      simpa using
        argmin_eq_subdifferential_gammaZeroConjugate_zero
          (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)
    _ = (∂ f) 0 := by
      -- Fenchel--Moreau identifies the double conjugate of `f` with `f` itself.
      have hbiconj :
          (f∗[hf])∗[gammaZeroConjugate_mem_gammaZero hf] = f := by
        funext x
        apply Subtype.ext
        simpa [Function.asEReal, gammaZeroConjugate_apply] using
          congrFun (biconjugate_eq_of_mem_gammaZero hf) x
      rw [hbiconj]

/-- Clause `(i) ⇔ (ii)` of Proposition 24.49: for `Ω.Nonempty` and `f ∈ Γ₀(H)`, the proximity
operator `Prox[f, hf]` is a proximal thresholder on `Ω` if and only if `(∂ f) 0 = Ω`. -/
theorem prox_isProximalThresholderOn_iff_subdifferential_zero_eq
    (hΩ_nonempty : Ω.Nonempty) :
    Function.IsProximalThresholderOn (Prox[f, hf]) Ω ↔ (∂ f) 0 = Ω := by
  constructor
  · intro hthresh
    -- Recover the thresholder set from the zero set, then translate that zero set to `(∂ f) 0`.
    calc
      (∂ f) 0 = (Prox[f, hf]).toSetValuedOperator.zeros := by
        ext x
        exact (mem_proxZeros_iff_mem_subdifferential_zero (hf := hf) (x := x)).symm
      _ = Ω := hthresh.zeros_eq
  · intro hsub
    -- Build the Chapter 24 witness directly from `f` and the translated zero-set equality.
    refine ⟨hΩ_nonempty, f, hf, rfl, ?_⟩
    calc
      (Prox[f, hf]).toSetValuedOperator.zeros = (∂ f) 0 := by
        ext x
        exact mem_proxZeros_iff_mem_subdifferential_zero (hf := hf) (x := x)
      _ = Ω := hsub

/-- Canonical bridge for Proposition 24.49 (1): the zero set of `Prox[f, hf]`, written as
`(Prox[f, hf]).toSetValuedOperator.zeros`, coincides with `Ω` if and only if `(∂ f) 0 = Ω`. -/
theorem prox_zeroSet_eq_iff_subdifferential_zero_eq :
    (Prox[f, hf]).toSetValuedOperator.zeros = Ω ↔ (∂ f) 0 = Ω := by
  constructor
  · intro hzeros
    -- The pointwise zero-set bridge turns equality of sets into equality of the subdifferential.
    calc
      (∂ f) 0 = (Prox[f, hf]).toSetValuedOperator.zeros := by
        ext x
        exact (mem_proxZeros_iff_mem_subdifferential_zero (hf := hf) (x := x)).symm
      _ = Ω := hzeros
  · intro hsub
    -- Run the same bridge in the forward direction.
    calc
      (Prox[f, hf]).toSetValuedOperator.zeros = (∂ f) 0 := by
        ext x
        exact mem_proxZeros_iff_mem_subdifferential_zero (hf := hf) (x := x)
      _ = Ω := hsub

/-- Clause `(ii) ⇔ (iii)` of Proposition 24.49: for `f ∈ Γ₀(H)`, the identity `(∂ f) 0 = Ω` is
equivalent to the fixed-point set formula `Fix Prox⋆[f, hf] = Ω`, written
canonically as `Function.fixedPoints (Prox⋆[f, hf]) = Ω`. -/
theorem subdifferential_zero_eq_iff_fixedPoints_conjugateProx_eq :
    (∂ f) 0 = Ω ↔ Function.fixedPoints (Prox⋆[f, hf]) = Ω := by
  have hfixed :
      Function.fixedPoints (Prox⋆[f, hf]) = Argmin ((f∗[hf]).asEReal) := by
    -- Normalize fixed points of `Prox⋆` to minimizers of the conjugate.
    simpa using
      fixedPoints_proximityOperator_eq_argmin_of_mem_gammaZero
        (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)
  constructor
  · intro hsub
    -- Then transport minimizers of `f∗` back to the subdifferential of `f` at `0`.
    calc
      Function.fixedPoints (Prox⋆[f, hf]) = Argmin ((f∗[hf]).asEReal) := hfixed
      _ = (∂ f) 0 := conjugateArgmin_eq_subdifferentialZero (hf := hf)
      _ = Ω := hsub
  · intro hfixedEq
    -- Run the same two bridges in reverse.
    calc
      (∂ f) 0 = Argmin ((f∗[hf]).asEReal) := by
        symm
        exact conjugateArgmin_eq_subdifferentialZero (hf := hf)
      _ = Function.fixedPoints (Prox⋆[f, hf]) := by
        symm
        exact hfixed
      _ = Ω := hfixedEq

/-- Clause `(ii) ⇔ (iv)` of Proposition 24.49: for `f ∈ Γ₀(H)`, the identity `(∂ f) 0 = Ω` is
equivalent to the minimizer formula `Argmin ((f∗[hf]).asEReal) = Ω`, written canonically as
`Argmin ((f∗[hf]).asEReal) = Ω`. -/
theorem subdifferential_zero_eq_iff_argmin_conjugate_eq :
    (∂ f) 0 = Ω ↔ Argmin ((f∗[hf]).asEReal) = Ω := by
  constructor
  · intro hsub
    -- Clause `(iv)` is just the conjugate-argmin bridge restated with `Ω`.
    calc
      Argmin ((f∗[hf]).asEReal) = (∂ f) 0 := conjugateArgmin_eq_subdifferentialZero (hf := hf)
      _ = Ω := hsub
  · intro hargmin
    -- The reverse implication is the same normalization read backwards.
    calc
      (∂ f) 0 = Argmin ((f∗[hf]).asEReal) := by
        symm
        exact conjugateArgmin_eq_subdifferentialZero (hf := hf)
      _ = Ω := hargmin

/-- Helper for Proposition 24.49: the subdifferential at `0` of the proper support function of a
nonempty closed convex set is the set itself. -/
lemma subdifferential_supportOwner_eq_self_at_zero_of_nonempty_isClosed_convex
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (∂ properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)) 0 = C := by
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hpack :
      (ι[C])∗[hC_gamma] =
        properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty) := by
    -- The packaged conjugate of the indicator is exactly the packaged support function.
    funext x
    apply Subtype.ext
    change (((ι[C])∗[hC_gamma] x : EReal)) = (σ[C] x : EReal)
    simpa [gammaZeroConjugate_apply] using
      congrFun (conjugate_indicator_eq_supportFunction (C := C)) x
  have hargmin : Argmin ((ι[C]).asEReal) = C := by
    -- Minimizers of the indicator are precisely the points of the set.
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
  -- Apply Proposition 16.33 to the indicator and rewrite its conjugate to the support function.
  calc
    (∂ properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)) 0 =
        (∂ ((ι[C])∗[hC_gamma])) 0 := by
          rw [hpack.symm]
    _ = Argmin ((ι[C]).asEReal) := by
      simpa using
        (argmin_eq_subdifferential_gammaZeroConjugate_zero (ι[C]) hC_gamma).symm
    _ = C := hargmin

/-- Proposition 24.49. If `f = g + σ[Ω]` with `g ∈ Γ₀(H)`, if `g` is finite on a neighborhood of
`0`, and if the finite representative of `g` has Gâteaux derivative `0` at `0`, then the
equivalent conditions of Proposition 24.49 hold, via the identity `(∂ f) 0 = Ω`. -/
theorem subdifferential_zero_eq_of_eq_add_supportFunction_and_zero_gradient
    (hΩ_nonempty : Ω.Nonempty) (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H))
    (hzero_int : (0 : H) ∈ interior (effectiveDomain g))
    (hzeroDeriv :
      HasGateauxDerivativeAt
        (fun y ↦ (g y : EReal).toReal)
        (toDualMap ℝ H (0 : H))
        (0 : H))
    (hf_eq :
      f =
        g + properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty)) :
    (∂ f) 0 = Ω := by
  let σΩ : H → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty)
  have hσΩ_zero : (σ[Ω]) 0 = 0 :=
    supportFunction_zero_eq_zero_of_nonempty Ω hΩ_nonempty
  have h0f_mem : (0 : H) ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    have h0g_mem : (0 : H) ∈ effectiveDomain g := interior_subset hzero_int
    simpa [hf_eq, σΩ, hσΩ_zero] using mem_effectiveDomain_iff.mp h0g_mem
  have hσΩ_mem : (0 : H) ∈ effectiveDomain σΩ := by
    -- The support value at `0` is finite, so `0` lies in the effective domain of `σΩ`.
    rw [mem_effectiveDomain_iff]
    simp [σΩ, hσΩ_zero]
  have hσ_sub :
      (∂ σΩ) 0 = Ω := by
    -- The local support-function helper gives the zero-slice of the support subdifferential.
    simpa [σΩ] using
      subdifferential_supportOwner_eq_self_at_zero_of_nonempty_isClosed_convex
        Ω hΩ_nonempty hΩ_closed hΩ_convex
  have hg_sub :
      (∂ g) 0 = ({0} : Set H) := by
    -- The zero Gâteaux gradient makes the subdifferential of `g` at `0` a singleton.
    simpa using
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
        hg hzero_int hzeroDeriv
  have hzero_sub : (0 : H) ∈ (∂ g) 0 := by
    simp [hg_sub]
  apply Set.Subset.antisymm
  · intro u hu
    have hsupport :
        ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ σ[Ω] y := by
      intro y
      by_cases hσ_top : σ[Ω] y = ⊤
      · simp [hσ_top]
      · have hσ_bot : σ[Ω] y ≠ ⊥ :=
          ne_of_gt (bot_lt_supportFunction_of_nonempty Ω hΩ_nonempty y)
        have hquot_tendsto :
            Filter.Tendsto
              (fun α : ℝ ↦
                (((g (α • y) : EReal).toReal - (g 0 : EReal).toReal) / α + (σ[Ω] y).toReal))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0))
              (nhds ((σ[Ω] y).toReal)) := by
          -- The directional quotient of `g` at `0` tends to the zero gradient.
          have hquot_zero :
              Filter.Tendsto
                (fun α : ℝ ↦ (((g (α • y) : EReal).toReal - (g 0 : EReal).toReal) / α : ℝ))
                (nhdsWithin (0 : ℝ) (Set.Ioi 0))
                (nhds (0 : ℝ)) := by
            simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
              real_inner_comm] using hzeroDeriv.tendsto_directionalDifferenceQuotient y
          simpa using hquot_zero.add_const ((σ[Ω] y).toReal)
        have hineq_eventually :
            ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              ⟪y, u⟫_ℝ ≤
                ((g (α • y) : EReal).toReal - (g 0 : EReal).toReal) / α + (σ[Ω] y).toReal := by
          filter_upwards
            [eventually_mem_effectiveDomain_along_ray_of_mem_interior
              (f := g) (x := (0 : H)) (d := y) hzero_int, self_mem_nhdsWithin] with α hαeff hαpos
          have hαdom : α • y ∈ effectiveDomain g := by
            simpa using hαeff
          have hscale :
              σ[Ω] (α • y) = ((α : ℝ) : EReal) * σ[Ω] y := by
            simpa [Function.comp, EReal.real_smul_def] using
              congrFun
                (supportFunction_comp_pos_smul_eq_mul_supportFunction (C := Ω) hαpos) y
          have hασ_top : (((α : ℝ) : EReal) * σ[Ω] y) ≠ ⊤ := by
            rw [EReal.mul_ne_top]
            refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl ?_, Or.inl (EReal.coe_ne_top α),
              Or.inr hσ_top⟩
            exact_mod_cast hαpos.le
          have hασ_bot : (((α : ℝ) : EReal) * σ[Ω] y) ≠ ⊥ := by
            rw [EReal.mul_ne_bot]
            refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inr hσ_bot, Or.inl (EReal.coe_ne_top α),
              Or.inl ?_⟩
            exact_mod_cast hαpos.le
          have hαf : α • y ∈ effectiveDomain f := by
            rw [mem_effectiveDomain_iff]
            have hαg_top : (g (α • y) : EReal) ≠ ⊤ :=
              ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
            rw [lt_top_iff_ne_top]
            simpa [hf_eq, σΩ, hscale] using EReal.add_ne_top hαg_top hασ_top
          have hsub_real :
              α * ⟪y, u⟫_ℝ ≤ (f (α • y) : EReal).toReal - (f 0 : EReal).toReal := by
            simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
              inner_smul_left] using
              inner_le_sub_of_mem_subdifferential_real
                (f := f) h0f_mem hαf hu
          have hαg_top : (g (α • y) : EReal) ≠ ⊤ :=
            ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
          have hαg_bot : (g (α • y) : EReal) ≠ ⊥ := by
            exact ne_of_gt (show (⊥ : EReal) < (g (α • y) : EReal) from (g (α • y)).2)
          have hg0_top : (g 0 : EReal) ≠ ⊤ :=
            ne_of_lt (mem_effectiveDomain_iff.mp (interior_subset hzero_int))
          have hg0_bot : (g 0 : EReal) ≠ ⊥ := by
            exact ne_of_gt (show (⊥ : EReal) < (g 0 : EReal) from (g 0).2)
          have hfα_toReal :
              (f (α • y) : EReal).toReal =
                (g (α • y) : EReal).toReal + α * (σ[Ω] y).toReal := by
            have htmp :
                (f (α • y) : EReal) =
                  (g (α • y) : EReal) + (((α : ℝ) : EReal) * σ[Ω] y) := by
              simp [hf_eq, hscale]
            have htmp' := congrArg EReal.toReal htmp
            rw [EReal.toReal_add hαg_top hαg_bot hασ_top hασ_bot, EReal.toReal_mul] at htmp'
            simpa using htmp'
          have hf0_toReal : (f 0 : EReal).toReal = (g 0 : EReal).toReal := by
            have htmp : (f 0 : EReal) = (g 0 : EReal) := by
              simp [hf_eq, hσΩ_zero]
            simpa using congrArg EReal.toReal htmp
          rw [hfα_toReal, hf0_toReal] at hsub_real
          have haux :
              α * (⟪y, u⟫_ℝ - (σ[Ω] y).toReal) ≤
                (g (α • y) : EReal).toReal - (g 0 : EReal).toReal := by
            nlinarith [hsub_real]
          have hineq_real :
              ⟪y, u⟫_ℝ ≤
                ((g (α • y) : EReal).toReal - (g 0 : EReal).toReal) / α + (σ[Ω] y).toReal := by
            have hdiv :
                ⟪y, u⟫_ℝ - (σ[Ω] y).toReal ≤
                  ((g (α • y) : EReal).toReal - (g 0 : EReal).toReal) / α := by
              exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using haux)
            linarith
          exact hineq_real
        have hreal :
            ⟪y, u⟫_ℝ ≤ (σ[Ω] y).toReal := by
          exact le_of_tendsto_of_tendsto tendsto_const_nhds hquot_tendsto hineq_eventually
        have hcast : (⟪y, u⟫_ℝ : EReal) ≤ (((σ[Ω] y).toReal : ℝ) : EReal) := by
          exact_mod_cast hreal
        simpa [EReal.coe_toReal hσ_top hσ_bot] using hcast
    have huσ : u ∈ (∂ σΩ) 0 := by
      -- The support inequalities are exactly the zero-point subgradient inequalities for `σΩ`.
      rw [mem_subdifferential_iff]
      intro y
      have hyσ : (⟪y, u⟫_ℝ : EReal) + (σΩ 0 : EReal) ≤ (σΩ y : EReal) := by
        simpa [σΩ, hσΩ_zero] using hsupport y
      simpa [sub_zero] using hyσ
    simpa [hσ_sub] using huσ
  · intro u hu
    have huσ : u ∈ (∂ σΩ) 0 := by
      simpa [hσ_sub] using hu
    -- Add the support-function and `g` subgradient inequalities directly at the origin.
    rw [mem_subdifferential_iff]
    intro y
    have hσy :=
      (mem_subdifferential_iff (f := σΩ) (x := (0 : H)) (u := u)).1 huσ y
    have hgy :=
      (mem_subdifferential_iff (f := g) (x := (0 : H)) (u := (0 : H))).1 hzero_sub y
    have hσy' : (⟪y, u⟫_ℝ : EReal) + (σΩ 0 : EReal) ≤ (σΩ y : EReal) := by
      simpa [sub_zero] using hσy
    have hgy' : (g 0 : EReal) ≤ (g y : EReal) := by
      simpa [sub_zero] using hgy
    have hsum : (⟪y, u⟫_ℝ : EReal) + (σΩ 0 : EReal) + (g 0 : EReal) ≤
        (σΩ y : EReal) + (g y : EReal) := by
      exact add_le_add hσy' hgy'
    have hsum' :
        (⟪y, u⟫_ℝ : EReal) + (f 0 : EReal) ≤ (f y : EReal) := by
      simpa [hf_eq, σΩ, hσΩ_zero, add_assoc, add_left_comm, add_comm] using hsum
    simpa [sub_zero] using hsum'

end ProximalThresholding

end

end ERealFunction
