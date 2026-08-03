import Mathlib
import BauschkeLean.Chap10.Proposition_10_8
import BauschkeLean.Chap12.Proposition_12_29
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap17.Proposition_17_16
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap22.Example_22_4
import BauschkeLean.Chap23.Example_23_3
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap24.Proposition_24_31
import BauschkeLean.Chap24.Proposition_24_32

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

variable (ψ : ℝ → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(ℝ))

/-- Helper for Proposition 24.33: if `0` minimizes `ψ`, then `0` is a fixed point of
`Prox[ψ, hψ]`. -/
private lemma prox_zero_eq_zero_of_mem_argmin
    (hmin : (0 : ℝ) ∈ Argmin ψ.asEReal) :
    Prox[ψ, hψ] 0 = 0 := by
  -- Fixed points of the prox map are exactly argmin points, so the minimizer at `0` is fixed.
  have hfix : (0 : ℝ) ∈ Function.fixedPoints (Prox[ψ, hψ]) := by
    rw [fixedPoints_proximityOperator_eq_argmin_of_mem_gammaZero ψ hψ]
    exact hmin
  exact Function.mem_fixedPoints_iff.mp hfix

/-- Helper for Proposition 24.33: the prox map preserves the interval `[-ρ, ρ]` once `0` is a
minimizer of `ψ`. -/
private lemma prox_mem_Icc_of_mem_Icc
    {ρ x : ℝ} (hmin : (0 : ℝ) ∈ Argmin ψ.asEReal)
    (hx : x ∈ Set.Icc (-ρ) ρ) :
    Prox[ψ, hψ] x ∈ Set.Icc (-ρ) ρ := by
  -- Proposition 24.32 places `Prox[ψ, hψ] x` on the segment joining `0` and `x`.
  have hseg :
      Prox[ψ, hψ] x ∈ Set.uIcc (0 : ℝ) x :=
    prox_mem_uIcc_zero_self_of_zero_mem_argmin hψ hmin x
  have hrho_nonneg : 0 ≤ ρ := by
    linarith [hx.1, hx.2]
  rw [Set.mem_uIcc] at hseg
  rcases hseg with hseg | hseg
  · have hnegRho : -ρ ≤ 0 := by linarith [hrho_nonneg]
    exact ⟨le_trans hnegRho hseg.1, le_trans hseg.2 hx.2⟩
  · have hzeroLeRho : 0 ≤ ρ := hrho_nonneg
    exact ⟨le_trans hx.1 hseg.1, le_trans hseg.2 hzeroLeRho⟩

/-- Helper for Proposition 24.33: every real proximity operator is monotone. -/
private lemma prox_monotone :
    Monotone (Prox[ψ, hψ]) := by
  -- Proposition 24.31 packages real prox maps as exactly the nonexpansive monotone maps.
  exact
    (exists_eq_proximityOperator_iff_lipschitzWith_one_and_monotone_real (Prox[ψ, hψ])).1
      ⟨ψ, hψ, rfl⟩ |>.2

/-- Helper for Proposition 24.33: on one side of `0`, the lower bound on `ψ''` integrates to a
gap estimate for the ordinary derivative of the finite representative of `ψ`. -/
private lemma derivGap_sameSide_on_Icc
    {ρ : ℝ} (θ : PosReal)
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun ξ : ℝ ↦ (ψ ξ : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ)
    {a b : ℝ}
    (ha : a ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ))
    (hb : b ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ))
    (hab : a ≤ b) (h_sameSide : 0 ≤ a * b) :
    (θ : ℝ) * (b - a) ≤
      deriv (fun ξ : ℝ ↦ (ψ ξ : EReal).toReal) b -
        deriv (fun ξ : ℝ ↦ (ψ ξ : EReal).toReal) a := by
  -- Route correction: the main theorem only needs the derivative gap on each open half-interval,
  -- so isolate the mean-value step here instead of differentiating `Prox` directly.
  let φ : ℝ → ℝ := fun ξ ↦ (ψ ξ : EReal).toReal
  have ha0 : a ≠ 0 := by simpa using ha.2
  have hb0 : b ≠ 0 := by simpa using hb.2
  have hsub :
      Set.Icc a b ⊆ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    intro z hz
    refine ⟨⟨le_trans ha.1.1 hz.1, le_trans hz.2 hb.1.2⟩, ?_⟩
    by_cases ha_nonneg : 0 ≤ a
    · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha0)
      have hz_pos : 0 < z := lt_of_lt_of_le ha_pos hz.1
      exact hz_pos.ne'
    · have ha_neg : a < 0 := lt_of_not_ge ha_nonneg
      have hb_nonpos : b ≤ 0 := by
        by_contra hb_pos
        have hb_pos' : 0 < b := lt_of_not_ge hb_pos
        have habsurd : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos'
        linarith
      have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb0
      have hz_neg : z < 0 := lt_of_le_of_lt hz.2 hb_neg
      exact hz_neg.ne
  by_cases hEq : a = b
  · subst hEq
    simp
  · have hlt : a < b := lt_of_le_of_ne hab hEq
    have hcont :
        ContinuousOn (deriv φ) (Set.Icc a b) := by
      intro z hz
      exact ((hderiv z (hsub hz)).continuousWithinAt).mono hsub
    have hhasDeriv :
        ∀ z ∈ Set.Ioo a b, HasDerivAt (deriv φ) ((deriv^[2] φ) z) z := by
      intro z hz
      have hzsub : z ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := hsub ⟨hz.1.le, hz.2.le⟩
      have hdom_nhds : Set.Icc (-ρ) ρ \ ({0} : Set ℝ) ∈ nhds z := by
        apply Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hz)
        intro y hy
        exact hsub ⟨hy.1.le, hy.2.le⟩
      exact ((hderiv z hzsub).differentiableAt hdom_nhds).hasDerivAt
    rcases
        exists_hasDerivAt_eq_slope (f := deriv φ) (f' := fun z ↦ (deriv^[2] φ) z)
          hlt hcont hhasDeriv with
      ⟨c, hc, hcSlope⟩
    have hcsub : c ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := hsub ⟨hc.1.le, hc.2.le⟩
    have htheta : (θ : ℝ) ≤ (deriv^[2] φ) c := h_deriv2_lb hcsub
    rw [hcSlope] at htheta
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp htheta

/-- Helper for Proposition 24.33: on the open punctured interval `(-ρ, ρ) \ {0}`, prox
optimality identifies the residual with the ordinary derivative of the finite representative
of `ψ`. -/
private lemma proxResidual_eq_deriv_of_ne_zero
    {ρ ξ p : ℝ}
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hp : p = Prox[ψ, hψ] ξ)
    (hp_mem : p ∈ Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) :
    ξ - p = deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) p := by
  -- First place `p` in the interior effective domain via the open punctured interval.
  let φ : ℝ → ℝ := fun t ↦ (ψ t : EReal).toReal
  have hpIcc : p ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨hp_mem.1.1.le, hp_mem.1.2.le⟩, hp_mem.2⟩
  have hp_int : p ∈ interior (effectiveDomain ψ) := by
    rw [mem_interior_iff_mem_nhds]
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    apply Filter.mem_of_superset
      (IsOpen.mem_nhds hopen hp_mem)
    intro y hy
    exact hIcc_dom ⟨hy.1.1.le, hy.1.2.le⟩
  have hp_diff : DifferentiableAt ℝ φ p := by
    have hopenSub :
        Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ⊆ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
      intro y hy
      exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    have hopen_nhds : Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ∈ nhds p :=
      IsOpen.mem_nhds hopen hp_mem
    exact ((hdiff p hpIcc).mono hopenSub).differentiableAt hopen_nhds
  have hp_grad :
      HasGateauxDerivativeAt φ (InnerProductSpace.toDualMap ℝ ℝ (deriv φ p)) p := by
    simpa [φ, HasGateauxDerivativeAt] using hp_diff.hasDerivAt.hasFDerivAt.hasGateauxDerivativeAt
  have hp_sub :
      ξ - p ∈ (∂ ψ) p := by
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hψ ξ p).1 hp
  have hsingle :
      (∂ ψ) p = ({deriv φ p} : Set ℝ) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
      hψ hp_int hp_grad
  rw [hsingle, Set.mem_singleton_iff] at hp_sub
  simpa [φ] using hp_sub

/-- Helper for Proposition 24.33: at a nonzero point of `(-ρ, ρ)`, differentiability of the
finite representative collapses the subdifferential to the ordinary derivative. -/
private lemma subgradient_eq_deriv_of_mem_Ioo_ne_zero
    (hψ : ψ ∈ Γ₀(ℝ))
    {ρ z u : ℝ}
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hz : z ∈ Set.Ioo (-ρ) ρ \ ({0} : Set ℝ))
    (hu : u ∈ (∂ ψ) z) :
    u = deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z := by
  let φ : ℝ → ℝ := fun t ↦ (ψ t : EReal).toReal
  have hzIcc : z ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
  -- The open punctured interval stays inside the effective domain, so `z` is an interior point.
  have hz_int : z ∈ interior (effectiveDomain ψ) := by
    rw [mem_interior_iff_mem_nhds]
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    apply Filter.mem_of_superset (IsOpen.mem_nhds hopen hz)
    intro y hy
    exact hIcc_dom ⟨hy.1.1.le, hy.1.2.le⟩
  -- Differentiate the finite representative at the interior point `z`.
  have hz_diff : DifferentiableAt ℝ φ z := by
    have hopenSub :
        Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ⊆ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
      intro y hy
      exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    have hz_nhds : Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ∈ nhds z :=
      IsOpen.mem_nhds hopen hz
    exact ((hdiff z hzIcc).mono hopenSub).differentiableAt hz_nhds
  have hz_grad :
      HasGateauxDerivativeAt φ
        (InnerProductSpace.toDualMap ℝ ℝ (deriv φ z)) z := by
    simpa [φ, HasGateauxDerivativeAt] using
      hz_diff.hasDerivAt.hasFDerivAt.hasGateauxDerivativeAt
  have hsingle :
      (∂ ψ) z = ({deriv φ z} : Set ℝ) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
      hψ hz_int hz_grad
  rw [hsingle, Set.mem_singleton_iff] at hu
  simpa [φ] using hu

/-- Helper for Proposition 24.33: at a nonzero point of `(-ρ, ρ)`, the ordinary derivative of the
finite representative belongs to the subdifferential. -/
private lemma deriv_mem_subdifferential_of_mem_Ioo_ne_zero
    (hψ : ψ ∈ Γ₀(ℝ))
    {ρ z : ℝ}
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hz : z ∈ Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) :
    deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z ∈ (∂ ψ) z := by
  let φ : ℝ → ℝ := fun t ↦ (ψ t : EReal).toReal
  have hz_int : z ∈ interior (effectiveDomain ψ) := by
    rw [mem_interior_iff_mem_nhds]
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    apply Filter.mem_of_superset (IsOpen.mem_nhds hopen hz)
    intro y hy
    exact hIcc_dom ⟨hy.1.1.le, hy.1.2.le⟩
  have hz_diff : DifferentiableAt ℝ φ z := by
    have hzIcc : z ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
    have hopenSub :
        Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ⊆ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
      intro y hy
      exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩
    have hopen :
        IsOpen (Set.Ioo (-ρ) ρ \ ({0} : Set ℝ)) := by
      simpa [Set.diff_eq, Set.mem_compl_iff] using
        isOpen_Ioo.inter isClosed_singleton.isOpen_compl
    have hz_nhds : Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) ∈ nhds z :=
      IsOpen.mem_nhds hopen hz
    exact ((hdiff z hzIcc).mono hopenSub).differentiableAt hz_nhds
  have hz_grad :
      HasGateauxDerivativeAt φ
        (InnerProductSpace.toDualMap ℝ ℝ (deriv φ z)) z := by
    simpa [φ, HasGateauxDerivativeAt] using
      hz_diff.hasDerivAt.hasFDerivAt.hasGateauxDerivativeAt
  have hsingle :
      (∂ ψ) z = ({deriv φ z} : Set ℝ) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
      hψ hz_int hz_grad
  rw [hsingle]
  simp [φ]

/-- Helper for Proposition 24.33: a subgradient at `0` lies below every interior derivative on the
positive half-interval. -/
private lemma subgradient_le_deriv_of_pos
    (hψ : ψ ∈ Γ₀(ℝ))
    {ρ u z : ℝ}
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hu : u ∈ (∂ ψ) 0)
    (hz : z ∈ Set.Ioo (0 : ℝ) ρ) :
    u ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z := by
  have hz_sub :
      deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z ∈ (∂ ψ) z := by
    exact
      deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
        ⟨⟨by linarith [hz.1, hz.2], hz.2⟩, by simp [hz.1.ne']⟩
  have hsub_mono : (∂ ψ).IsMonotone :=
    SetValuedOperator.Maximal.isMonotone
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hψ)
  have hpair :
      0 ≤ inner ℝ (z - 0) (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u) :=
    (SetValuedOperator.isMonotone_iff (∂ ψ)).1 hsub_mono hz_sub hu
  -- The positive sign of `z` turns the monotonicity pairing into the scalar order.
  have hmul :
      0 ≤ z * (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u) := by
    have hpair' :
        0 ≤ inner ℝ z (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u) := by
      simpa using hpair
    rw [show inner ℝ z (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u) =
        z * (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u) by
      simpa using RCLike.inner_apply' z (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z - u)] at hpair'
    exact hpair'
  have hz_pos : 0 < z := hz.1
  nlinarith

/-- Helper for Proposition 24.33: a subgradient at `0` lies above every interior derivative on the
negative half-interval. -/
private lemma deriv_le_subgradient_of_neg
    (hψ : ψ ∈ Γ₀(ℝ))
    {ρ u z : ℝ}
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hu : u ∈ (∂ ψ) 0)
    (hz : z ∈ Set.Ioo (-ρ) (0 : ℝ)) :
    deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z ≤ u := by
  have hz_sub :
      deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z ∈ (∂ ψ) z := by
    exact
      deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
        ⟨⟨hz.1, by linarith [hz.1, hz.2]⟩, by simp [hz.2.ne]⟩
  have hsub_mono : (∂ ψ).IsMonotone :=
    SetValuedOperator.Maximal.isMonotone
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hψ)
  have hpair :
      0 ≤ inner ℝ (0 - z) (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z) :=
    (SetValuedOperator.isMonotone_iff (∂ ψ)).1 hsub_mono hu hz_sub
  -- The factor `-z` is positive on the negative half-interval.
  have hmul :
      0 ≤ (-z) * (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z) := by
    have hpair' :
        0 ≤ inner ℝ (-z) (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z) := by
      simpa using hpair
    rw [show inner ℝ (-z) (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z) =
        (-z) * (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z) by
      simpa using RCLike.inner_apply' (-z) (u - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z)] at hpair'
    exact hpair'
  have hz_neg : z < 0 := hz.2
  nlinarith

/-- Helper for Proposition 24.33: along the ordered graph of `∂ ψ`, subgradients increase with
their base points on `ℝ`. -/
private lemma subgradient_mono_le
    (hψ : ψ ∈ Γ₀(ℝ))
    {x y u v : ℝ} (hxy : x < y)
    (hu : u ∈ (∂ ψ) x) (hv : v ∈ (∂ ψ) y) :
    u ≤ v := by
  -- Convert graph monotonicity on `ℝ` into the scalar order relation `u ≤ v`.
  have hsub_mono : (∂ ψ).IsMonotone :=
    SetValuedOperator.Maximal.isMonotone
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hψ)
  have hpair :
      0 ≤ inner ℝ (y - x) (v - u) :=
    (SetValuedOperator.isMonotone_iff (∂ ψ)).1 hsub_mono hv hu
  have hmul :
      0 ≤ (y - x) * (v - u) := by
    rw [show inner ℝ (y - x) (v - u) = (y - x) * (v - u) by
      simpa using RCLike.inner_apply' (y - x) (v - u)] at hpair
    exact hpair
  have hpos : 0 < y - x := sub_pos.mpr hxy
  nlinarith

/-- Helper for Proposition 24.33: a strict positive-side curvature gap yields an interior witness
whose remaining interval length still dominates the gap. -/
private lemma positiveEndpointWitnessBounds
    {θ z δ : ℝ} (hθ : 0 < θ) (hz : 0 < z) (hδ : δ < θ * z) :
    ∃ w, w ∈ Set.Ioo (0 : ℝ) z ∧ δ < θ * (z - w) := by
  by_cases hδ_nonpos : δ ≤ 0
  · refine ⟨z / 2, ?_, ?_⟩
    · -- The midpoint of `(0, z)` stays on the positive half-interval.
      refine ⟨?_, ?_⟩ <;> nlinarith
    · -- A nonpositive gap is dominated by the positive midpoint curvature term.
      have hmid_pos : 0 < θ * (z - z / 2) := by
        nlinarith
      nlinarith
  · have hδ_pos : 0 < δ := lt_of_not_ge hδ_nonpos
    have hfrac_pos : 0 < δ / θ := div_pos hδ_pos hθ
    have hfrac_lt : δ / θ < z := by
      exact (div_lt_iff₀ hθ).2 (by simpa [mul_comm] using hδ)
    refine ⟨(z - δ / θ) / 2, ?_, ?_⟩
    · -- This witness sits strictly between `0` and `z`.
      refine ⟨?_, ?_⟩
      · nlinarith
      · nlinarith
    · -- Rewriting `θ * (z - w)` gives a midpoint between `δ` and `θ * z`.
      have hscale :
          θ * (z - (z - δ / θ) / 2) = (θ * z + δ) / 2 := by
        field_simp [hθ.ne']
        ring
      have hsmall' : δ < (θ * z + δ) / 2 := by
        nlinarith [hδ]
      simpa [hscale]
        using hsmall'

/-- Helper for Proposition 24.33: a strict negative-side curvature gap yields an interior witness
whose offset from the left endpoint still dominates the gap. -/
private lemma negativeEndpointWitnessBounds
    {θ z δ : ℝ} (hθ : 0 < θ) (hz : z < 0) (hδ : δ < -(θ * z)) :
    ∃ w, w ∈ Set.Ioo z (0 : ℝ) ∧ δ < θ * (w - z) := by
  by_cases hδ_nonpos : δ ≤ 0
  · refine ⟨z / 2, ?_, ?_⟩
    · -- The midpoint of `(z, 0)` stays on the negative half-interval.
      refine ⟨?_, ?_⟩ <;> nlinarith
    · -- A nonpositive gap is dominated by the positive curvature earned on `(z, z / 2)`.
      have hmid_pos : 0 < θ * (z / 2 - z) := by
        nlinarith
      nlinarith
  · have hδ_pos : 0 < δ := lt_of_not_ge hδ_nonpos
    have hfrac_pos : 0 < δ / θ := div_pos hδ_pos hθ
    have hδ_negform : δ < θ * (-z) := by
      simpa [neg_mul, mul_comm] using hδ
    have hfrac_lt : δ / θ < -z := by
      exact (div_lt_iff₀ hθ).2 (by simpa [mul_comm] using hδ_negform)
    refine ⟨(z + δ / θ) / 2, ?_, ?_⟩
    · -- This witness sits strictly between `z` and `0`.
      refine ⟨?_, ?_⟩
      · nlinarith
      · nlinarith
    · -- Rewriting `θ * (w - z)` gives a midpoint between `δ` and `-(θ * z)`.
      have hscale :
          θ * ((z + δ / θ) / 2 - z) = (δ - θ * z) / 2 := by
        field_simp [hθ.ne']
        ring
      have hsmall' : δ < (δ - θ * z) / 2 := by
        nlinarith [hδ]
      simpa [hscale]
        using hsmall'

/-- Helper for Proposition 24.33: an endpoint subgradient at `0` picks up the full curvature term
before any positive interior point of `(-ρ, ρ)`. -/
private lemma endpointSubgradient_add_curvature_le_deriv_of_pos
    {ρ : ℝ} (θ : PosReal)
    (hψ : ψ ∈ Γ₀(ℝ))
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ)
    {u z : ℝ}
    (hu : u ∈ (∂ ψ) 0)
    (hz : z ∈ Set.Ioo (0 : ℝ) ρ) :
    u + (θ : ℝ) * z ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z := by
  -- Route correction: isolate the witness arithmetic in `positiveEndpointWitnessBounds`,
  -- then keep the contradiction here purely at the derivative/subgradient level.
  let φ : ℝ → ℝ := fun t ↦ (ψ t : EReal).toReal
  have hθpos : 0 < (θ : ℝ) := θ.2
  have hz_closed : z ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨by linarith [hz.1, hz.2], hz.2.le⟩, hz.1.ne'⟩
  by_contra hgoal
  have hdelta : deriv φ z - u < (θ : ℝ) * z := by
    have hlt : deriv φ z < u + (θ : ℝ) * z := lt_of_not_ge hgoal
    nlinarith
  obtain ⟨w, hw, hsmall⟩ :=
    positiveEndpointWitnessBounds hθpos hz.1 hdelta
  have hw_mem : w ∈ Set.Ioo (0 : ℝ) ρ := by
    exact ⟨hw.1, lt_of_lt_of_le hw.2 hz.2.le⟩
  have hw_closed : w ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2.le⟩, hw.1.ne'⟩
  have hgap_wz :
      (θ : ℝ) * (z - w) ≤ deriv φ z - deriv φ w := by
    -- The second-derivative lower bound upgrades from `w` to `z` on the positive half-line.
    exact
      derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
        hw_closed hz_closed hw.2.le (mul_nonneg hw.1.le hz.1.le)
  have hderiv_lt : deriv φ w < u := by
    nlinarith [hsmall, hgap_wz]
  have hsub_le : u ≤ deriv φ w := by
    -- Any endpoint subgradient lies below every positive-side interior derivative.
    simpa [φ] using
      subgradient_le_deriv_of_pos (ψ := ψ) hψ hIcc_dom hdiff hu hw_mem
  linarith

/-- Helper for Proposition 24.33: an endpoint subgradient at `0` dominates the derivative after
subtracting the full curvature term on the negative half-interval. -/
private lemma deriv_le_endpointSubgradient_add_curvature_of_neg
    {ρ : ℝ} (θ : PosReal)
    (hψ : ψ ∈ Γ₀(ℝ))
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ)
    {u z : ℝ}
    (hu : u ∈ (∂ ψ) 0)
    (hz : z ∈ Set.Ioo (-ρ) (0 : ℝ)) :
    deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) z ≤ u + (θ : ℝ) * z := by
  -- Route correction: isolate the witness arithmetic in `negativeEndpointWitnessBounds`,
  -- then keep the contradiction here purely at the derivative/subgradient level.
  let φ : ℝ → ℝ := fun t ↦ (ψ t : EReal).toReal
  have hθpos : 0 < (θ : ℝ) := θ.2
  have hz_closed : z ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨hz.1.le, by linarith [hz.1, hz.2]⟩, hz.2.ne⟩
  by_contra hgoal
  have hdelta : u - deriv φ z < -((θ : ℝ) * z) := by
    have hlt : u + (θ : ℝ) * z < deriv φ z := lt_of_not_ge hgoal
    nlinarith
  obtain ⟨w, hw, hsmall⟩ :=
    negativeEndpointWitnessBounds hθpos hz.2 hdelta
  have hw_mem : w ∈ Set.Ioo (-ρ) (0 : ℝ) := by
    exact ⟨lt_of_le_of_lt hz.1.le hw.1, hw.2⟩
  have hw_closed : w ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
    exact ⟨⟨hw_mem.1.le, by linarith [hw_mem.1, hw_mem.2]⟩, hw.2.ne⟩
  have hgap_zw :
      (θ : ℝ) * (w - z) ≤ deriv φ w - deriv φ z := by
    -- The second-derivative lower bound upgrades from `z` to `w` on the negative half-line.
    exact
      derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
        hz_closed hw_closed hw.1.le
        (mul_nonneg_of_nonpos_of_nonpos hz.2.le hw.2.le)
  have hu_lt : u < deriv φ w := by
    nlinarith [hsmall, hgap_zw]
  have hderiv_le : deriv φ w ≤ u := by
    -- Any endpoint subgradient lies above every negative-side interior derivative.
    simpa [φ] using
      deriv_le_subgradient_of_neg (ψ := ψ) hψ hIcc_dom hdiff hu hw_mem
  linarith

/-- Helper for Proposition 24.33: on the nonnegative half-interval, the prox gap is bounded by
`(η - ξ) / (1 + θ)`. -/
private lemma orderedProxGap_le_on_nonnegSide
    {ρ : ℝ} (θ : PosReal)
    (hmin : (0 : ℝ) ∈ Argmin ψ.asEReal)
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ)
    {ξ η : ℝ}
    (hξ0 : 0 ≤ ξ) (hξη : ξ ≤ η) (hηρ : η ≤ ρ) :
    Prox[ψ, hψ] η - Prox[ψ, hψ] ξ ≤ (η - ξ) / ((θ : ℝ) + 1) := by
  -- Split according to whether the left prox value is the endpoint `0`.
  let p : ℝ := Prox[ψ, hψ] ξ
  let q : ℝ := Prox[ψ, hψ] η
  let u : ℝ := ξ - p
  let v : ℝ := η - q
  have hθpos : 0 < (θ : ℝ) := θ.2
  have hzero : Prox[ψ, hψ] 0 = 0 := prox_zero_eq_zero_of_mem_argmin (ψ := ψ) (hψ := hψ) hmin
  have hp_le_hq : p ≤ q := by
    simpa [p, q] using (prox_monotone (ψ := ψ) (hψ := hψ) hξη)
  have hp_nonneg : 0 ≤ p := by
    simpa [p, hzero] using (prox_monotone (ψ := ψ) (hψ := hψ) hξ0)
  have hη0 : 0 ≤ η := le_trans hξ0 hξη
  have hq_nonneg : 0 ≤ q := by
    simpa [q, hzero] using (prox_monotone (ψ := ψ) (hψ := hψ) hη0)
  have hp_sub : u ∈ (∂ ψ) p := by
    simpa [p, u] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hψ ξ (Prox[ψ, hψ] ξ)).1 rfl
  have hq_sub : v ∈ (∂ ψ) q := by
    simpa [q, v] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hψ η (Prox[ψ, hψ] η)).1 rfl
  have hξ_mem : ξ ∈ Set.Icc (-ρ) ρ := by
    refine ⟨?_, le_trans hξη hηρ⟩
    linarith [hξ0, hηρ]
  have hη_mem : η ∈ Set.Icc (-ρ) ρ := by
    refine ⟨?_, hηρ⟩
    linarith [hη0, hηρ]
  have hp_Icc : p ∈ Set.Icc (-ρ) ρ :=
    prox_mem_Icc_of_mem_Icc (ψ := ψ) (hψ := hψ) hmin hξ_mem
  have hq_Icc : q ∈ Set.Icc (-ρ) ρ :=
    prox_mem_Icc_of_mem_Icc (ψ := ψ) (hψ := hψ) hmin hη_mem
  have htheta_gap : (θ : ℝ) * (q - p) ≤ v - u := by
    by_cases hp_zero : p = 0
    · by_cases hq_zero : q = 0
      · nlinarith [hξη]
      · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
        have hu0 : ξ ∈ (∂ ψ) 0 := by
          simpa [p, u, hp_zero] using hp_sub
        by_contra hgap
        have hlt : v - ξ < (θ : ℝ) * q := by
          have hgap' : ¬ (↑θ * (q - 0) ≤ v - ξ) := by
            simpa [p, u, hp_zero, sub_eq_add_neg] using hgap
          have hlt' : v - ξ < (↑θ : ℝ) * (q - 0) := lt_of_not_ge hgap'
          simpa using hlt'
        by_cases hnonpos : v - ξ ≤ 0
        · let w : ℝ := q / 2
          have hw_q : w ∈ Set.Ioo (0 : ℝ) q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith
            · dsimp [w]
              nlinarith
          have hw_mem : w ∈ Set.Ioo (0 : ℝ) ρ := by
            exact ⟨hw_q.1, lt_of_lt_of_le hw_q.2 hq_Icc.2⟩
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2⟩, hw_mem.1.ne'⟩
          have hcurv :
              ξ + (θ : ℝ) * w ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              endpointSubgradient_add_curvature_le_deriv_of_pos
                (ψ := ψ) θ hψ hIcc_dom hdiff hderiv h_deriv2_lb hu0 hw_mem
          have hmono :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ v := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_q.2 hw_sub hq_sub
          have hsmall : v - ξ < (θ : ℝ) * w := by
            dsimp [w]
            have hhalf : 0 < (θ : ℝ) * w := by
              positivity
            nlinarith
          nlinarith
        · have hpos_gap : 0 < v - ξ := lt_of_not_ge hnonpos
          let w : ℝ := ((v - ξ) / (θ : ℝ) + q) / 2
          have hfrac : (v - ξ) / (θ : ℝ) < q := by
            exact (div_lt_iff₀ hθpos).2 (by simpa [mul_comm] using hlt)
          have hfrac_pos : 0 < (v - ξ) / (θ : ℝ) := by
            exact div_pos hpos_gap hθpos
          have hw_q : w ∈ Set.Ioo (0 : ℝ) q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith [hfrac_pos, hq_pos]
            · dsimp [w]
              nlinarith [hfrac]
          have hw_mem : w ∈ Set.Ioo (0 : ℝ) ρ := by
            exact ⟨hw_q.1, lt_of_lt_of_le hw_q.2 hq_Icc.2⟩
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2⟩, hw_mem.1.ne'⟩
          have hcurv :
              ξ + (θ : ℝ) * w ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              endpointSubgradient_add_curvature_le_deriv_of_pos
                (ψ := ψ) θ hψ hIcc_dom hdiff hderiv h_deriv2_lb hu0 hw_mem
          have hmono :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ v := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_q.2 hw_sub hq_sub
          have hsmall : v - ξ < (θ : ℝ) * w := by
            have hscale :
                (θ : ℝ) * w = ((v - ξ) + (θ : ℝ) * q) / 2 := by
              dsimp [w]
              field_simp [hθpos.ne']
            have hsmall' : v - ξ < ((v - ξ) + (θ : ℝ) * q) / 2 := by
              nlinarith [hlt]
            simpa [hscale] using hsmall'
          nlinarith [hcurv, hmono, hsmall]
    · by_cases hpq : p = q
      · nlinarith [hξη]
      · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_zero)
        have hp_mem :
            p ∈ Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) := by
          refine ⟨⟨?_, ?_⟩, hp_pos.ne'⟩
          · linarith [hp_pos, hp_Icc.2]
          · have hp_lt_q : p < q := lt_of_le_of_ne hp_le_hq hpq
            linarith [hp_lt_q, hq_Icc.2]
        have hu_eq :
            u = deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) p := by
          exact
            subgradient_eq_deriv_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff hp_mem hp_sub
        have hp_lt_q : p < q := lt_of_le_of_ne hp_le_hq hpq
        by_contra hgap
        have hlt : v - u < (θ : ℝ) * (q - p) := by
          linarith
        by_cases hnonpos : v - u ≤ 0
        · let w : ℝ := (p + q) / 2
          have hw_pq : w ∈ Set.Ioo p q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              linarith
            · dsimp [w]
              linarith
          have hw_mem : w ∈ Set.Ioo (0 : ℝ) ρ := by
            refine ⟨?_, ?_⟩
            · linarith [hp_pos, hw_pq.1]
            · linarith [hw_pq.2, hq_Icc.2]
          have hw_closed : w ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
            exact ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2.le⟩, hw_mem.1.ne'⟩
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2⟩, hw_mem.1.ne'⟩
          have hgap_pw :
              (θ : ℝ) * (w - p) ≤
                deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) p := by
            exact
              derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
                ⟨⟨hp_mem.1.1.le, hp_mem.1.2.le⟩, hp_mem.2⟩ hw_closed hw_pq.1.le
                (by positivity)
          have hmono :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ v := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_pq.2 hw_sub hq_sub
          have hsmall : v - u < (θ : ℝ) * (w - p) := by
            dsimp [w]
            have hhalf : 0 < (θ : ℝ) * (w - p) := by
              nlinarith [hθpos, hw_pq.1]
            nlinarith
          nlinarith [hu_eq, hgap_pw, hmono, hsmall]
        · have hpos_gap : 0 < v - u := lt_of_not_ge hnonpos
          let w : ℝ := p + ((v - u) / (θ : ℝ) + (q - p)) / 2
          have hfrac : (v - u) / (θ : ℝ) < q - p := by
            exact (div_lt_iff₀ hθpos).2 (by simpa [mul_comm] using hlt)
          have hfrac_pos : 0 < (v - u) / (θ : ℝ) := by
            exact div_pos hpos_gap hθpos
          have hqp_pos : 0 < q - p := sub_pos.mpr hp_lt_q
          have hsum_pos : 0 < (v - u) / (θ : ℝ) + (q - p) := by
            nlinarith [hfrac_pos, hqp_pos]
          have hmargin : 0 < (q - p) - (v - u) / (θ : ℝ) := by
            nlinarith [hfrac]
          have hw_pq : w ∈ Set.Ioo p q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith [hsum_pos]
            · dsimp [w]
              nlinarith [hmargin]
          have hw_mem : w ∈ Set.Ioo (0 : ℝ) ρ := by
            refine ⟨?_, ?_⟩
            · linarith [hp_pos, hw_pq.1]
            · linarith [hw_pq.2, hq_Icc.2]
          have hw_closed : w ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) := by
            exact ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2.le⟩, hw_mem.1.ne'⟩
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨by linarith [hw_mem.1, hw_mem.2], hw_mem.2⟩, hw_mem.1.ne'⟩
          have hgap_pw :
              (θ : ℝ) * (w - p) ≤
                deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) p := by
            exact
              derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
                ⟨⟨hp_mem.1.1.le, hp_mem.1.2.le⟩, hp_mem.2⟩ hw_closed hw_pq.1.le
                (mul_nonneg hp_pos.le hw_mem.1.le)
          have hmono :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ v := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_pq.2 hw_sub hq_sub
          have hsmall : v - u < (θ : ℝ) * (w - p) := by
            have hrewrite :
                w - p = ((v - u) / (θ : ℝ) + (q - p)) / 2 := by
              dsimp [w]
              ring
            have hscale :
                (θ : ℝ) * (((v - u) / (θ : ℝ) + (q - p)) / 2) =
                  ((v - u) + (θ : ℝ) * (q - p)) / 2 := by
              field_simp [hθpos.ne']
            have hsmall' :
                v - u < ((v - u) + (θ : ℝ) * (q - p)) / 2 := by
              nlinarith [hlt]
            simpa [hrewrite, hscale] using hsmall'
          nlinarith [hu_eq, hgap_pw, hmono, hsmall]
  have hfinal : q - p ≤ (η - ξ) / ((θ : ℝ) + 1) := by
    have haux : (q - p) * ((θ : ℝ) + 1) ≤ η - ξ := by
      nlinarith [htheta_gap]
    exact (le_div_iff₀ (by positivity)).2 haux
  simpa [p, q] using hfinal

/-- Helper for Proposition 24.33: on the nonpositive half-interval, the prox gap is bounded by
`(η - ξ) / (1 + θ)`. -/
private lemma orderedProxGap_le_on_nonposSide
    {ρ : ℝ} (θ : PosReal)
    (hmin : (0 : ℝ) ∈ Argmin ψ.asEReal)
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦ (ψ t : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun t : ℝ ↦ (ψ t : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ)
    {ξ η : ℝ}
    (hρξ : -ρ ≤ ξ) (hξη : ξ ≤ η) (hη0 : η ≤ 0) :
    Prox[ψ, hψ] η - Prox[ψ, hψ] ξ ≤ (η - ξ) / ((θ : ℝ) + 1) := by
  -- This is the negative-half companion, with the right endpoint handled at `0`.
  let p : ℝ := Prox[ψ, hψ] ξ
  let q : ℝ := Prox[ψ, hψ] η
  let u : ℝ := ξ - p
  let v : ℝ := η - q
  have hθpos : 0 < (θ : ℝ) := θ.2
  have hzero : Prox[ψ, hψ] 0 = 0 := prox_zero_eq_zero_of_mem_argmin (ψ := ψ) (hψ := hψ) hmin
  have hp_le_hq : p ≤ q := by
    simpa [p, q] using (prox_monotone (ψ := ψ) (hψ := hψ) hξη)
  have hξ0 : ξ ≤ 0 := le_trans hξη hη0
  have hp_nonpos : p ≤ 0 := by
    simpa [p, hzero] using (prox_monotone (ψ := ψ) (hψ := hψ) hξ0)
  have hq_nonpos : q ≤ 0 := by
    simpa [q, hzero] using (prox_monotone (ψ := ψ) (hψ := hψ) hη0)
  have hp_sub : u ∈ (∂ ψ) p := by
    simpa [p, u] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hψ ξ (Prox[ψ, hψ] ξ)).1 rfl
  have hq_sub : v ∈ (∂ ψ) q := by
    simpa [q, v] using
      (eq_proximityOperator_iff_sub_mem_subdifferential hψ η (Prox[ψ, hψ] η)).1 rfl
  have hξ_mem : ξ ∈ Set.Icc (-ρ) ρ := by
    exact ⟨hρξ, by linarith [hρξ, hη0]⟩
  have hη_mem : η ∈ Set.Icc (-ρ) ρ := by
    exact ⟨by linarith [hρξ, hη0], by linarith [hρξ, hη0]⟩
  have hp_Icc : p ∈ Set.Icc (-ρ) ρ :=
    prox_mem_Icc_of_mem_Icc (ψ := ψ) (hψ := hψ) hmin hξ_mem
  have hq_Icc : q ∈ Set.Icc (-ρ) ρ :=
    prox_mem_Icc_of_mem_Icc (ψ := ψ) (hψ := hψ) hmin hη_mem
  have htheta_gap : (θ : ℝ) * (q - p) ≤ v - u := by
    by_cases hq_zero : q = 0
    · by_cases hp_zero : p = 0
      · nlinarith [hξη]
      · have hp_neg : p < 0 := lt_of_le_of_ne hp_nonpos hp_zero
        have hv0 : η ∈ (∂ ψ) 0 := by
          simpa [q, v, hq_zero] using hq_sub
        by_contra hgap
        have hlt : η - u < -(θ : ℝ) * p := by
          have hgap' : ¬ (↑θ * (0 - p) ≤ η - u) := by
            simpa [q, v, hq_zero] using hgap
          have hlt' : η - u < (↑θ : ℝ) * (0 - p) := lt_of_not_ge hgap'
          nlinarith
        by_cases hneg_gap : η - u < 0
        · let w : ℝ := p / 2
          have hw_p : w ∈ Set.Ioo p (0 : ℝ) := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith
            · dsimp [w]
              nlinarith
          have hw_mem : w ∈ Set.Ioo (-ρ) (0 : ℝ) := by
            refine ⟨?_, hw_p.2⟩
            linarith [hp_Icc.1, hw_p.1]
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨hw_mem.1, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
          have hcurv :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ η + (θ : ℝ) * w := by
            exact
              deriv_le_endpointSubgradient_add_curvature_of_neg
                (ψ := ψ) θ hψ hIcc_dom hdiff hderiv h_deriv2_lb hv0 hw_mem
          have hmono :
              u ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_p.1 hp_sub hw_sub
          have hsmall : η - u < -(θ : ℝ) * w := by
            dsimp [w]
            have hhalf : 0 < -(θ : ℝ) * w := by
              nlinarith [hθpos, hw_p.2]
            nlinarith
          nlinarith
        · let w : ℝ := (p - (η - u) / (θ : ℝ)) / 2
          have hgap_nonneg : 0 ≤ η - u := le_of_not_gt hneg_gap
          have hfrac_nonneg : 0 ≤ (η - u) / (θ : ℝ) := by
            exact div_nonneg hgap_nonneg hθpos.le
          have hfrac_lt : (η - u) / (θ : ℝ) < -p := by
            exact (div_lt_iff₀ hθpos).2 (by simpa [mul_comm] using hlt)
          have hw_p : w ∈ Set.Ioo p (0 : ℝ) := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith [hfrac_lt]
            · dsimp [w]
              nlinarith [hp_neg, hfrac_nonneg]
          have hw_mem : w ∈ Set.Ioo (-ρ) (0 : ℝ) := by
            refine ⟨?_, hw_p.2⟩
            linarith [hp_Icc.1, hw_p.1]
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨hw_mem.1, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
          have hcurv :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ≤ η + (θ : ℝ) * w := by
            exact
              deriv_le_endpointSubgradient_add_curvature_of_neg
                (ψ := ψ) θ hψ hIcc_dom hdiff hderiv h_deriv2_lb hv0 hw_mem
          have hmono :
              u ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_p.1 hp_sub hw_sub
          have hsmall : η - u < -(θ : ℝ) * w := by
            have hscale :
                -(θ : ℝ) * w = ((η - u) - (θ : ℝ) * p) / 2 := by
              dsimp [w]
              field_simp [hθpos.ne']
              ring
            have hsmall' : η - u < ((η - u) - (θ : ℝ) * p) / 2 := by
              nlinarith [hlt]
            simpa [hscale] using hsmall'
          nlinarith [hcurv, hmono, hsmall]
    · by_cases hpq : p = q
      · nlinarith [hξη]
      · have hq_neg : q < 0 := lt_of_le_of_ne hq_nonpos hq_zero
        have hq_mem :
            q ∈ Set.Ioo (-ρ) ρ \ ({0} : Set ℝ) := by
          refine ⟨⟨?_, ?_⟩, hq_neg.ne⟩
          · have hp_lt_q : p < q := lt_of_le_of_ne hp_le_hq hpq
            linarith [hp_Icc.1, hp_lt_q]
          · linarith [hq_neg, hq_Icc.1]
        have hv_eq :
            v = deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) q := by
          exact
            subgradient_eq_deriv_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff hq_mem hq_sub
        have hp_lt_q : p < q := lt_of_le_of_ne hp_le_hq hpq
        by_contra hgap
        have hlt : v - u < (θ : ℝ) * (q - p) := by
          linarith
        by_cases hnonpos : v - u ≤ 0
        · let w : ℝ := (p + q) / 2
          have hw_pq : w ∈ Set.Ioo p q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              linarith
            · dsimp [w]
              linarith
          have hw_mem : w ∈ Set.Ioo (-ρ) (0 : ℝ) := by
            refine ⟨?_, ?_⟩
            · linarith [hp_Icc.1, hw_pq.1]
            · linarith [hw_pq.2, hq_neg]
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨hw_mem.1, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
          have hgap_wq :
              (θ : ℝ) * (q - w) ≤
                deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) q - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
                ⟨⟨hw_mem.1.le, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
                ⟨⟨hq_mem.1.1.le, hq_mem.1.2.le⟩, hq_mem.2⟩ hw_pq.2.le
                (mul_nonneg_of_nonpos_of_nonpos hw_mem.2.le hq_neg.le)
          have hmono :
              u ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_pq.1 hp_sub hw_sub
          have hsmall : v - u < (θ : ℝ) * (q - w) := by
            dsimp [w]
            have hhalf : 0 < (θ : ℝ) * (q - w) := by
              nlinarith [hθpos, hw_pq.2]
            nlinarith
          nlinarith [hv_eq, hgap_wq, hmono, hsmall]
        · let w : ℝ := q - ((v - u) / (θ : ℝ) + (q - p)) / 2
          have hpos_gap : 0 < v - u := lt_of_not_ge hnonpos
          have hfrac : (v - u) / (θ : ℝ) < q - p := by
            exact (div_lt_iff₀ hθpos).2 (by simpa [mul_comm] using hlt)
          have hmargin : 0 < (q - p) - (v - u) / (θ : ℝ) := by
            nlinarith
          have hfrac_pos : 0 < (v - u) / (θ : ℝ) := by
            exact div_pos hpos_gap hθpos
          have hqp_pos : 0 < q - p := sub_pos.mpr hp_lt_q
          have hsum_pos : 0 < (v - u) / (θ : ℝ) + (q - p) := by
            nlinarith [hfrac_pos, hqp_pos]
          have hw_pq : w ∈ Set.Ioo p q := by
            refine ⟨?_, ?_⟩
            · dsimp [w]
              nlinarith [hmargin]
            · dsimp [w]
              nlinarith [hsum_pos]
          have hw_mem : w ∈ Set.Ioo (-ρ) (0 : ℝ) := by
            refine ⟨?_, ?_⟩
            · linarith [hp_Icc.1, hw_pq.1]
            · linarith [hw_pq.2, hq_neg]
          have hw_sub :
              deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w ∈ (∂ ψ) w := by
            exact
              deriv_mem_subdifferential_of_mem_Ioo_ne_zero (ψ := ψ) hψ hIcc_dom hdiff
                ⟨⟨hw_mem.1, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
          have hgap_wq :
              (θ : ℝ) * (q - w) ≤
                deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) q - deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              derivGap_sameSide_on_Icc (ψ := ψ) θ hderiv h_deriv2_lb
                ⟨⟨hw_mem.1.le, by linarith [hw_mem.1, hw_mem.2]⟩, hw_mem.2.ne⟩
                ⟨⟨hq_mem.1.1.le, hq_mem.1.2.le⟩, hq_mem.2⟩ hw_pq.2.le
                (mul_nonneg_of_nonpos_of_nonpos hw_mem.2.le hq_neg.le)
          have hmono :
              u ≤ deriv (fun t : ℝ ↦ (ψ t : EReal).toReal) w := by
            exact
              subgradient_mono_le (ψ := ψ) hψ hw_pq.1 hp_sub hw_sub
          have hsmall : v - u < (θ : ℝ) * (q - w) := by
            have hrewrite :
                q - w = ((v - u) / (θ : ℝ) + (q - p)) / 2 := by
              dsimp [w]
              ring
            have hscale :
                (θ : ℝ) * (((v - u) / (θ : ℝ) + (q - p)) / 2) =
                  ((v - u) + (θ : ℝ) * (q - p)) / 2 := by
              field_simp [hθpos.ne']
            have hsmall' :
                v - u < ((v - u) + (θ : ℝ) * (q - p)) / 2 := by
              nlinarith [hlt]
            simpa [hrewrite, hscale] using hsmall'
          nlinarith [hv_eq, hgap_wq, hmono, hsmall]
  have hfinal : q - p ≤ (η - ξ) / ((θ : ℝ) + 1) := by
    have haux : (q - p) * ((θ : ℝ) + 1) ≤ η - ξ := by
      nlinarith [htheta_gap]
    exact (le_div_iff₀ (by positivity)).2 haux
  simpa [p, q] using hfinal

-- `source-facing`: Proposition 24.33 is the interval theorem stated with the source second-
-- derivative hypotheses on the finite representative of `ψ`.
-- `core/canonical`: the owner abstractions underneath are `StronglyConvex ψ β`,
-- `subdifferential_isStronglyMonotone_of_stronglyConvex`,
-- `resolvent_subdifferential_eq_scaledProximityOperator`, and
-- `resolventMap_contractingWith_of_isStronglyMonotone`.
-- `bridge/view`: this file keeps no separate public real-line bridge API; the interval proof
-- should invoke those owner-level Chapter 10/22/23 bridges directly.

/-- Proposition 24.33: if `ψ ∈ Γ₀(ℝ)` has `0 ∈ Argmin ψ.asEReal`, if `ψ` is finite on
`[-ρ, ρ]`, and if its finite representative is twice differentiable on `[-ρ, ρ] \ {0}` with
second derivative bounded below there by `θ > 0`, then the proximity operator of `ψ` is
`1 / (1 + θ)`-Lipschitz on `[-ρ, ρ]`. -/
theorem prox_lipschitzOnWith_on_Icc_of_deriv2_lower_bound_off_zero
    {ρ : ℝ} (θ : PosReal)
    (hmin : (0 : ℝ) ∈ Argmin ψ.asEReal)
    (hIcc_dom : Set.Icc (-ρ) ρ ⊆ effectiveDomain ψ)
    (hdiff :
      DifferentiableOn ℝ
        (fun ξ : ℝ ↦ (ψ ξ : EReal).toReal)
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (hderiv :
      DifferentiableOn ℝ
        (deriv (fun ξ : ℝ ↦ (ψ ξ : EReal).toReal))
        (Set.Icc (-ρ) ρ \ ({0} : Set ℝ)))
    (h_deriv2_lb :
      ∀ ⦃ξ : ℝ⦄, ξ ∈ Set.Icc (-ρ) ρ \ ({0} : Set ℝ) →
        (θ : ℝ) ≤
          (deriv^[2] fun t : ℝ ↦ (ψ t : EReal).toReal) ξ) :
    LipschitzOnWith (Real.toNNReal (1 / ((θ : ℝ) + 1))) (Prox[ψ, hψ]) (Set.Icc (-ρ) ρ) := by
  -- Route correction: keep the main theorem at the ordered-gap level and delegate all
  -- near-endpoint curvature upgrades to the local half-interval helpers above.
  have hzero : Prox[ψ, hψ] 0 = 0 :=
    prox_zero_eq_zero_of_mem_argmin (ψ := ψ) (hψ := hψ) hmin
  refine LipschitzOnWith.of_dist_le' fun ξ hξ η hη ↦ ?_
  by_cases hξη : ξ ≤ η
  · have hprox_order : Prox[ψ, hψ] ξ ≤ Prox[ψ, hψ] η := by
      exact prox_monotone (ψ := ψ) (hψ := hψ) hξη
    have hgap :
        Prox[ψ, hψ] η - Prox[ψ, hψ] ξ ≤ (η - ξ) / ((θ : ℝ) + 1) := by
      by_cases hη_nonpos : η ≤ 0
      · -- The ordered pair stays on the nonpositive side, so use the negative-side helper.
        exact
          orderedProxGap_le_on_nonposSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
            hderiv h_deriv2_lb hξ.1 hξη hη_nonpos
      · have hη_pos : 0 < η := lt_of_not_ge hη_nonpos
        by_cases hξ_nonneg : 0 ≤ ξ
        · -- The ordered pair stays on the nonnegative side, so use the positive-side helper.
          exact
            orderedProxGap_le_on_nonnegSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
              hderiv h_deriv2_lb hξ_nonneg hξη hη.2
        · have hleft :
              Prox[ψ, hψ] 0 - Prox[ψ, hψ] ξ ≤ (0 - ξ) / ((θ : ℝ) + 1) := by
            exact
              orderedProxGap_le_on_nonposSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                hderiv h_deriv2_lb hξ.1 (by linarith) le_rfl
          have hright :
              Prox[ψ, hψ] η - Prox[ψ, hψ] 0 ≤ (η - 0) / ((θ : ℝ) + 1) := by
            exact
              orderedProxGap_le_on_nonnegSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                hderiv h_deriv2_lb le_rfl hη_pos.le hη.2
          -- Assemble the cross-zero estimate by splitting at the fixed point `Prox 0 = 0`.
          have hleft' :
              0 - Prox[ψ, hψ] ξ ≤ (0 - ξ) / ((θ : ℝ) + 1) := by
            simpa [hzero] using hleft
          have hright' :
              Prox[ψ, hψ] η - 0 ≤ (η - 0) / ((θ : ℝ) + 1) := by
            simpa [hzero] using hright
          calc
            Prox[ψ, hψ] η - Prox[ψ, hψ] ξ
                = (Prox[ψ, hψ] η - 0) + (0 - Prox[ψ, hψ] ξ) := by ring
            _ ≤ (η - 0) / ((θ : ℝ) + 1) + (0 - ξ) / ((θ : ℝ) + 1) :=
                add_le_add hright' hleft'
            _ = (η - ξ) / ((θ : ℝ) + 1) := by ring
    -- Rewrite the ordered scalar estimate into the distance form expected by `LipschitzOnWith`.
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hprox_order)]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hξη)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hgap
  · have hηξ : η ≤ ξ := le_of_not_ge hξη
    have hdist :
        dist (Prox[ψ, hψ] η) (Prox[ψ, hψ] ξ) ≤
          (1 / ((θ : ℝ) + 1)) * dist η ξ := by
      -- Reuse the ordered case after swapping the two inputs.
      have hordered :
          dist (Prox[ψ, hψ] η) (Prox[ψ, hψ] ξ) ≤
            (1 / ((θ : ℝ) + 1)) * dist η ξ := by
        by_cases hηξ_nonpos : ξ ≤ 0
        · have hprox_order : Prox[ψ, hψ] η ≤ Prox[ψ, hψ] ξ := by
            exact prox_monotone (ψ := ψ) (hψ := hψ) hηξ
          have hgap :
              Prox[ψ, hψ] ξ - Prox[ψ, hψ] η ≤ (ξ - η) / ((θ : ℝ) + 1) := by
            exact
              orderedProxGap_le_on_nonposSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                hderiv h_deriv2_lb hη.1 hηξ hηξ_nonpos
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hprox_order)]
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hηξ)]
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hgap
        · have hξ_pos : 0 < ξ := lt_of_not_ge hηξ_nonpos
          by_cases hη_nonneg : 0 ≤ η
          · have hprox_order : Prox[ψ, hψ] η ≤ Prox[ψ, hψ] ξ := by
              exact prox_monotone (ψ := ψ) (hψ := hψ) hηξ
            have hgap :
                Prox[ψ, hψ] ξ - Prox[ψ, hψ] η ≤ (ξ - η) / ((θ : ℝ) + 1) := by
              exact
                orderedProxGap_le_on_nonnegSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                  hderiv h_deriv2_lb hη_nonneg hηξ hξ.2
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hprox_order)]
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hηξ)]
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hgap
          · have hleft :
                Prox[ψ, hψ] 0 - Prox[ψ, hψ] η ≤ (0 - η) / ((θ : ℝ) + 1) := by
              exact
                orderedProxGap_le_on_nonposSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                  hderiv h_deriv2_lb hη.1 (by linarith) le_rfl
            have hright :
                Prox[ψ, hψ] ξ - Prox[ψ, hψ] 0 ≤ (ξ - 0) / ((θ : ℝ) + 1) := by
              exact
                orderedProxGap_le_on_nonnegSide (ψ := ψ) (hψ := hψ) θ hmin hIcc_dom hdiff
                  hderiv h_deriv2_lb le_rfl hξ_pos.le hξ.2
            have hgap :
                Prox[ψ, hψ] ξ - Prox[ψ, hψ] η ≤ (ξ - η) / ((θ : ℝ) + 1) := by
              have hleft' :
                  0 - Prox[ψ, hψ] η ≤ (0 - η) / ((θ : ℝ) + 1) := by
                simpa [hzero] using hleft
              have hright' :
                  Prox[ψ, hψ] ξ - 0 ≤ (ξ - 0) / ((θ : ℝ) + 1) := by
                simpa [hzero] using hright
              calc
                Prox[ψ, hψ] ξ - Prox[ψ, hψ] η
                    = (Prox[ψ, hψ] ξ - 0) + (0 - Prox[ψ, hψ] η) := by ring
                _ ≤ (ξ - 0) / ((θ : ℝ) + 1) + (0 - η) / ((θ : ℝ) + 1) :=
                    add_le_add hright' hleft'
                _ = (ξ - η) / ((θ : ℝ) + 1) := by ring
            have hprox_order : Prox[ψ, hψ] η ≤ Prox[ψ, hψ] ξ := by
              exact prox_monotone (ψ := ψ) (hψ := hψ) hηξ
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hprox_order)]
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hηξ)]
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hgap
      exact hordered
    simpa [dist_comm, mul_comm] using hdist

end ERealFunction
