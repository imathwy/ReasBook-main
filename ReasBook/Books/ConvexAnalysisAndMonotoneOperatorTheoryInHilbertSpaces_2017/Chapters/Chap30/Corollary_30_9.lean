import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Theorem_13_37
import BauschkeLean.Chap14.Proposition_14_15
import BauschkeLean.Chap16.Proposition_16_5
import BauschkeLean.Chap29.Proposition_29_49
import BauschkeLean.Chap30.Theorem_30_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology
open ERealFunction

universe u v

noncomputable section

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

/- Source/core/bridge triage:
- `source-facing`: Corollary 30.9 is the Haugazeau recursion for the finite family of continuous
  convex subgradient projectors and its convergence to the projection onto the common feasibility
  set.
- `core/canonical`: the reusable Chapter 29/30 owners are
  `cyclicSubgradientProjectorConstraintSet`, `cyclicSubgradientProjectorFamily`,
  `commonFixedPointSet`, and `haugazeauIteration`.
- `bridge/view`: this file identifies the Chapter 30 common fixed-point set of the Chapter 29
  projector family with the source feasibility set, then feeds that bridge into Theorem 30.8. -/

/-- The Chapter 30 common fixed-point set of the Chapter 29 cyclic subgradient projector family is
exactly the source feasibility set `C = ⋂ i, lev_{≤ 0} fᵢ`. -/
@[simp] theorem commonFixedPointSet_cyclicSubgradientProjectorFamily_eq_constraintSet
    (f : I → H → ℝ)
    (hcont : ∀ i : I, Continuous (f i))
    (hconv : ∀ i : I, _root_.ConvexOn ℝ Set.univ (f i))
    (hC_nonempty : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ i : I, Selection (∂ (f i).toEReal)) :
    commonFixedPointSet (cyclicSubgradientProjectorFamily f hcont hconv hC_nonempty s) =
      cyclicSubgradientProjectorConstraintSet f := by
  simpa [commonFixedPointSet] using
    iInter_fixedPoints_cyclicSubgradientProjectorFamily_eq_constraintSet
      f hcont hconv hC_nonempty s

/-- Each member of the Chapter 29 cyclic subgradient projector family satisfies the Chapter 30
demiclosedness hypothesis under the source branch condition from Corollary 30.9. -/
theorem demiclosedAt_zero_residual_cyclicSubgradientProjectorFamily
    (f : I → H → ℝ)
    (hcont : ∀ i : I, Continuous (f i))
    (hconv : ∀ i : I, _root_.ConvexOn ℝ Set.univ (f i))
    (hC_nonempty : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (hcase :
      (∀ i : I, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((f i) '' B)) ∨
      (∀ i : I, Supercoercive ((f i).toEReal.asEReal∗)) ∨
      FiniteDimensional ℝ H)
    (s : ∀ i : I, Selection (∂ (f i).toEReal)) :
    ∀ i : I,
      DemiclosedAt (Set.univ : Set H)
        (residualMapOnUniv (cyclicSubgradientProjectorFamily f hcont hconv hC_nonempty s i))
        0 := by
  intro i
  have hbounded :
      ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded ((f i) '' B) := by
    rcases hcase with hbounded | hsuper | hfdim
    · exact hbounded i
    · have hf : (f i).toEReal ∈ Γ₀(H) := by
        rw [mem_gammaZero_iff]
        constructor
        · simpa using (continuous_coe_real_ereal.comp (hcont i)).lowerSemicontinuous
        · refine ⟨
            by simp [Function.effectiveDomain_toEReal],
            by simp [Function.effectiveDomain_toEReal],
            ?_⟩
          intro x hx y hy a ha0 ha1
          have hreal :
              (f i) (a • x + (1 - a) • y) ≤ a * (f i) x + (1 - a) * (f i) y := by
            simpa [smul_eq_mul] using
              (hconv i).2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
                (sub_nonneg.mpr ha1.le) (by linarith)
          have hcast :
              (((f i) (a • x + (1 - a) • y) : ℝ) : EReal) ≤
                (((a * (f i) x + (1 - a) * (f i) y : ℝ) : EReal)) := by
            exact_mod_cast hreal
          simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast
      have hdom : (dom (f i).toEReal.asEReal∗).Nonempty := by
        exact
          (conjugate_is_proper_of_mem_gamma
            (isProper_of_mem_gammaZero hf)
            (asEReal_mem_gamma_of_mem_gammaZero hf)).2
      intro B hB
      rcases exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
          (f i).toEReal.asEReal hdom B hB with ⟨m, hm⟩
      let g : H → Set.Ioi (⊥ : EReal) :=
        properIoi ((f i).toEReal.asEReal∗)
          (conjugate_is_proper_of_mem_gamma
            (isProper_of_mem_gammaZero hf)
            (asEReal_mem_gamma_of_mem_gammaZero hf))
      have hg : g ∈ Γ₀(H) := by
        exact properIoi_mem_gammaZero_of_mem_gamma
          (conjugate_is_proper_of_mem_gamma
            (isProper_of_mem_gammaZero hf)
            (asEReal_mem_gamma_of_mem_gammaZero hf))
          (conjugate_mem_gamma ((f i).toEReal.asEReal))
      rcases ((supercoercive_iff_conjugate_boundedOnEveryBoundedSet g hg).1 <| by
          simpa [g, Function.asEReal] using hsuper i) B hB with ⟨M, hM⟩
      let R : ℝ := max (-m) M
      refine
        (Metric.isBounded_closedBall :
          Bornology.IsBounded (Metric.closedBall (0 : ℝ) R)).subset ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hfx_lower : m ≤ f i x := by
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [Function.asEReal, Function.toEReal_apply] using hm x hx
      have hsubx : SubdifferentiableAt (f i).toEReal x := by
        simpa using subgradientProjector_mem_dom (f i) (hcont i) (hconv i) x
      have hconj : (f i).toEReal.asEReal∗∗ x = ((f i x : ℝ) : EReal) := by
        simpa [Function.asEReal, Function.toEReal_apply] using
          biconjugate_eq_self_at_of_subdifferentiableAt ((f i).toEReal) x hsubx
      have hfx_upper : f i x ≤ M := by
        have hMx_raw : g.asEReal∗ x ≤ M := hM x hx
        have hMx : (f i).toEReal.asEReal∗∗ x ≤ M := by
          change conjugate ((f i).toEReal.asEReal∗) x ≤ M
          simpa [g, asEReal_properIoi] using hMx_raw
        have hMx' : ((f i x : ℝ) : EReal) ≤ M := by
          calc
            ((f i x : ℝ) : EReal) = (f i).toEReal.asEReal∗∗ x := hconj.symm
            _ ≤ M := hMx
        exact EReal.coe_le_coe_iff.mp hMx'
      rw [Metric.mem_closedBall, Real.dist_eq]
      refine abs_le.mpr ?_
      constructor
      · have hR_lower : -R ≤ m := by
          dsimp [R]
          linarith [le_max_left (-m) M]
        linarith
      · linarith [hfx_upper, le_max_right (-m) M]
    · letI : FiniteDimensional ℝ H := hfdim
      intro B hB
      haveI : ProperSpace H := FiniteDimensional.proper ℝ H
      have hcompact : IsCompact (closure B) := by
        simpa [isClosed_closure.closure_eq] using hB.isCompact_closure
      have himage_compact : IsCompact ((f i) '' closure B) := hcompact.image (hcont i)
      exact himage_compact.isBounded.subset <| by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨x, subset_closure hx, rfl⟩
  simpa [residualMapOnUniv, cyclicSubgradientProjectorFamily] using
    demiclosedAt_zero_id_sub_continuousConvexSubgradientProjector
      (f i) 0 (hcont i) (hconv i)
      (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty
        f hC_nonempty i)
      (s i) hbounded

/-- The source feasibility set `C = ⋂ i, lev_{≤ 0} fᵢ` in Corollary 30.9 is Chebyshev. -/
theorem cyclicSubgradientProjectorConstraintSet_isChebyshev
    (f : I → H → ℝ)
    (hcont : ∀ i : I, Continuous (f i))
    (hconv : ∀ i : I, _root_.ConvexOn ℝ Set.univ (f i))
    (hC_nonempty : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ i : I, Selection (∂ (f i).toEReal)) :
    IsChebyshev (cyclicSubgradientProjectorConstraintSet f) := by
  let T := cyclicSubgradientProjectorFamily f hcont hconv hC_nonempty s
  have hT : ∀ i : I, FirmlyQuasinonexpansive (T i) := by
    intro i
    simpa [T, cyclicSubgradientProjectorFamily] using
      firmlyQuasinonexpansive_continuousConvexSubgradientProjector
        (f i) 0 (hcont i) (hconv i)
        (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty
          f hC_nonempty i)
        (s i)
  have hFix_nonempty : (commonFixedPointSet T).Nonempty := by
    rw [commonFixedPointSet_cyclicSubgradientProjectorFamily_eq_constraintSet
      f hcont hconv hC_nonempty s]
    exact hC_nonempty
  have hChebyshev :
      IsChebyshev (commonFixedPointSet T) :=
    iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive T hT hFix_nonempty
  rw [commonFixedPointSet_cyclicSubgradientProjectorFamily_eq_constraintSet
    f hcont hconv hC_nonempty s] at hChebyshev
  simpa [T] using hChebyshev

/-- Corollary 30.9: let `(fᵢ)ᵢ` be a finite family of continuous convex functions on the real
Hilbert space `H`, let
`C = cyclicSubgradientProjectorConstraintSet f = ⋂ i, lev_{≤ 0} fᵢ` be nonempty, and assume
either that every `fᵢ` is bounded on every bounded subset of `H`, or that every Fenchel conjugate
`fᵢ*` is supercoercive, or that `H` is finite-dimensional. If `control : ℕ → I` visits every
index in each block, if `sᵢ` is a chosen selection of `∂ fᵢ`, and if `xₙ` is generated by
Haugazeau's recursion `xₙ₊₁ = Q(x₀, xₙ, G_{control n}(xₙ))` with `Gᵢ` the associated subgradient
projector onto `lev_{≤ 0} fᵢ`, then `xₙ` converges strongly to the metric projection of `x₀`
onto `C`. -/
theorem haugazeau_iteration_tendsto_projection_iInter_lowerLevelSet_of_continuousConvex
    (f : I → H → ℝ)
    (hcont : ∀ i : I, Continuous (f i))
    (hconv : ∀ i : I, _root_.ConvexOn ℝ Set.univ (f i))
    (hC_nonempty : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (hcase :
      (∀ i : I, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((f i) '' B)) ∨
      (∀ i : I, Supercoercive (f i).toEReal.asEReal∗) ∨
      FiniteDimensional ℝ H)
    (s : ∀ i : I, Selection (∂ (f i).toEReal))
    {m : ℕ} (control : ℕ → I)
    (hcontrol : VisitsEveryIndexInEachBlock control m)
    (x0 : H) :
    Tendsto
      (haugazeauIteration
        (cyclicSubgradientProjectorFamily f hcont hconv hC_nonempty s)
        control x0)
      atTop
      (𝓝 (P[cyclicSubgradientProjectorConstraintSet f,
        cyclicSubgradientProjectorConstraintSet_isChebyshev
          f hcont hconv hC_nonempty s] x0)) := by
  let T := cyclicSubgradientProjectorFamily f hcont hconv hC_nonempty s
  have hT : ∀ i : I, FirmlyQuasinonexpansive (T i) := by
    intro i
    simpa [T, cyclicSubgradientProjectorFamily] using
      firmlyQuasinonexpansive_continuousConvexSubgradientProjector
        (f i) 0 (hcont i) (hconv i)
        (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty
          f hC_nonempty i)
        (s i)
  have hFix_nonempty : (commonFixedPointSet T).Nonempty := by
    rw [commonFixedPointSet_cyclicSubgradientProjectorFamily_eq_constraintSet
      f hcont hconv hC_nonempty s]
    exact hC_nonempty
  let hCommonCheb :=
    iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive T hT hFix_nonempty
  have hbest :
      IsBestApproximation x0 (cyclicSubgradientProjectorConstraintSet f)
        (P[commonFixedPointSet T, hCommonCheb] x0) := by
    rw [← commonFixedPointSet_cyclicSubgradientProjectorFamily_eq_constraintSet
      f hcont hconv hC_nonempty s]
    exact projectionPoint_isBestApproximation (commonFixedPointSet T) hCommonCheb x0
  have hproj_eq :
      P[commonFixedPointSet T, hCommonCheb] x0 =
        P[cyclicSubgradientProjectorConstraintSet f,
          cyclicSubgradientProjectorConstraintSet_isChebyshev
            f hcont hconv hC_nonempty s] x0 := by
    apply eq_projectionPoint_of_isBestApproximation
      (cyclicSubgradientProjectorConstraintSet f)
      (cyclicSubgradientProjectorConstraintSet_isChebyshev
        f hcont hconv hC_nonempty s)
    exact hbest
  have hlimit :=
    haugazeau_iteration_tendsto_projection_iInter_fixedPoints
      T hT
      (demiclosedAt_zero_residual_cyclicSubgradientProjectorFamily
        f hcont hconv hC_nonempty hcase s)
      hFix_nonempty
      control hcontrol x0
  simpa only [T, hproj_eq] using hlimit

end
