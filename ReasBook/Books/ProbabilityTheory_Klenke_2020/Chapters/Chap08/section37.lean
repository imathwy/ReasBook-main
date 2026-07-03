

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_after_Theorem_8_37 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section

variable (n : ℕ) (P : Measure Ω) {X : Ω → ↑I} {Y : Ω → Fin n → Bool}

/-- Example after Theorem 8.37: if `X` is uniformly distributed on `[0,1]` and, for `P.map X`-
almost every `x`, the regular conditional law of the Boolean vector `Y` given `X = x` has
independent coordinates with one-coordinate Bernoulli law on `Bool` of parameter `x`, then the
whole conditional law is the canonical Bernoulli product kernel `coinTossingKernel n`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      condDistrib Y X P =ᵐ[volume] coinTossingKernel n := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  sorry

/-- Pointwise form of
`condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel`. For `volume`-almost every
`x : ↑I`, the regular conditional distribution of `Y` given `X = x` is the Bernoulli product law
`coinTossingKernel n x` on `Fin n → Bool`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel_apply
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      ∀ᵐ x ∂volume, condDistrib Y X P x = coinTossingKernel n x := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  simpa using
    condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel n P hX_law hcond_indep
      hcond_marg

end

/-! ### Theorem_8_37 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E] [StandardBorelSpace E]

-- Proof sketch: in the nonempty case, view `id : Ω → Ω` as a measurable map from `(Ω, mΩ)` to
-- `(Ω, m)` using `hm` and reuse the canonical owner construction `condDistrib Y id P`; if `Ω` is
-- empty, the theorem is witnessed internally by the zero kernel.
/-- Theorem 8.37: If `Y` takes values in a Borel space `E`, then given a sub-σ-algebra `m` of the
ambient σ-algebra there exists a regular conditional distribution of `Y` given `m`. -/
theorem exists_regular_conditional_distribution_borel_given
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {Y : Ω → E} (hY : Measurable[mΩ, mE] Y) :
    ∃ κ : Kernel[m, mE] Ω E, IsRegularCondDistrib P m Y κ := by
  by_cases hΩ : Nonempty Ω
  · letI : Nonempty Ω := hΩ
    letI : Nonempty E := ⟨Y (Classical.choice hΩ)⟩
    have hX : Measurable[mΩ, m] id := by
      rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
      exact hm
    have hκ :
        @IsRegularCondDistrib Ω E mE mΩ P inferInstance (MeasurableSpace.comap id m) Y
          ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl)) :=
      @ProbabilityTheory.isRegularCondDistrib_condDistrib Ω E mE mΩ Ω m inferInstance
        inferInstance P inferInstance Y hY id hX
    have hm_id : MeasurableSpace.comap id m = m := MeasurableSpace.comap_id
    let κ : Kernel[m, mE] Ω E := by
      exact hm_id ▸ ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl))
    refine ⟨κ, ?_⟩
    subst κ
    convert hκ using 1 <;> simp [hm_id]
  · letI : IsEmpty Ω := not_nonempty_iff.mp hΩ
    refine ⟨0, ?_⟩
    refine
      { toIsMarkovKernel := inferInstance
        le_ambient := hm
        measurable_Y := hY
        ae_eq_conditionalProbability := ?_ }
    intro B hB
    exact Filter.EventuallyEq.of_eq <| funext fun ω ↦ False.elim (isEmptyElim ω)
