import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»
import DifferentialForms_Cartan_1970.III.section11.«0013_Proposition_5_2».WeightedLogResidues

open Filter
open scoped BigOperators Topology unitInterval
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: for a meromorphic normal-form representative, order zero forces
analyticity. -/
lemma analyticAt_of_meromorphicOrderAt_eq_zero
    {g : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicNFAt g z) (horder : meromorphicOrderAt g z = (0 : ℤ)) :
    AnalyticAt ℂ g z := by
  -- Route correction: order zero does not control the actual center value of an arbitrary
  -- meromorphic germ, so the analytic conclusion is valid only for a normal-form representative.
  exact (hg.meromorphicOrderAt_nonneg_iff_analyticAt).1 (by simpa using le_of_eq horder.symm)

/-- Helper for Proposition 5.2: when the meromorphic order is zero, the weighted logarithmic
derivative of a normal-form representative is holomorphic at the point. -/
lemma differentiableAt_weighted_logDeriv_of_order_zero
    {g : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicNFAt g z) (horder : meromorphicOrderAt g z = (0 : ℤ)) :
    DifferentiableAt ℂ (fun w ↦ w * logDeriv g w) z := by
  have hanalytic : AnalyticAt ℂ g z :=
    analyticAt_of_meromorphicOrderAt_eq_zero hg horder
  -- In normal form, order zero is equivalent to a nonzero center value, so `logDeriv g` is
  -- holomorphic and remains so after multiplication by the identity map.
  have hnonzero : g z ≠ 0 := by
    exact (hg.meromorphicOrderAt_eq_zero_iff).1 (by simpa using horder)
  exact differentiableAt_id.mul
    (differentiableAt_logDeriv_of_analyticAt_nonzero hanalytic hnonzero)

/-- Helper for Proposition 5.2: at a zero or pole of finite nonzero order inside the translated
period parallelogram, the weighted logarithmic derivative has local residue `(k : ℂ) * z`. -/
lemma localResidueCircle_weighted_logDeriv_of_order
    {Q D : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {k : ℤ}
    (hzQ : z ∈ interior Q)
    (hzD : z ∈ D) (hD : IsOpen D)
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = k) :
    LocalResidueCircle Q D (fun w ↦ w * logDeriv g w) z ((k : ℂ) * z) := by
  obtain ⟨h, hh_analytic, hlog⟩ :=
    logDeriv_eventuallyEq_order_principalPart_add_analytic hg horder
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzQ) with ⟨rQ, hrQ, hballQ⟩
  rcases Metric.mem_nhds_iff.1 (hD.mem_nhds hzD) with ⟨rD, hrD, hballD⟩
  obtain ⟨rH, hrH, hh_ball⟩ := hh_analytic.exists_ball_analyticOnNhd
  have hlog_nhds :
      ∀ᶠ w in 𝓝 z, w ≠ z → logDeriv g w = (k : ℂ) / (w - z) + h w := by
    simpa [Filter.EventuallyEq, eventually_nhdsWithin_iff] using hlog
  rcases Metric.mem_nhds_iff.1 hlog_nhds with ⟨rLog, hrLog, hballLog⟩
  let r : ℝ := min (rQ / 2) (min (rD / 2) (min (rH / 2) (rLog / 2)))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hrQ)
      (lt_min (half_pos hrD) (lt_min (half_pos hrH) (half_pos hrLog)))
  have hr_le_Q : r ≤ rQ / 2 := by
    dsimp [r]
    exact min_le_left _ _
  have hr_le_D : r ≤ rD / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_H : r ≤ rH / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_Log : r ≤ rLog / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrQ_lt : r < rQ := lt_of_le_of_lt hr_le_Q (by linarith)
  have hrD_lt : r < rD := lt_of_le_of_lt hr_le_D (by linarith)
  have hrH_lt : r < rH := lt_of_le_of_lt hr_le_H (by linarith)
  have hrLog_lt : r < rLog := lt_of_le_of_lt hr_le_Log (by linarith)
  have hclosedQ : Metric.closedBall z r ⊆ interior Q := by
    exact (Metric.closedBall_subset_ball hrQ_lt).trans hballQ
  have hclosedD : Metric.closedBall z r ⊆ D := by
    exact (Metric.closedBall_subset_ball hrD_lt).trans hballD
  have hh_diff : DifferentiableOn ℂ h (Metric.closedBall z r) := by
    -- Shrink the analytic remainder to the closed ball that will support the residue circle.
    exact (hh_ball.mono (Metric.closedBall_subset_ball hrH_lt)).differentiableOn
  let G : ℂ → ℂ := fun w ↦ w * ((k : ℂ) + (w - z) * h w)
  have hG_diff : DifferentiableOn ℂ G (Metric.closedBall z r) := by
    intro w hw
    have hh_w : DifferentiableWithinAt ℂ h (Metric.closedBall z r) w := hh_diff w hw
    -- The numerator is a product of holomorphic factors on the chosen closed ball.
    fun_prop
  have hG_center : G z = (k : ℂ) * z := by
    simp [G, mul_comm]
  have hcongr :
      (∮ w in C(z, r), w * logDeriv g w) = ∮ w in C(z, r), G w / (w - z) := by
    refine circleIntegral.integral_congr hr.le ?_
    intro w hwSphere
    have hw_closed : w ∈ Metric.closedBall z r := Metric.sphere_subset_closedBall hwSphere
    have hw_ballLog : w ∈ Metric.ball z rLog := by
      exact (Metric.closedBall_subset_ball hrLog_lt) hw_closed
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hwSphere hr.ne'
    have hsub_ne : w - z ≠ 0 := sub_ne_zero.mpr hw_ne
    have hlog_w : logDeriv g w = (k : ℂ) / (w - z) + h w := hballLog hw_ballLog hw_ne
    -- On the residue circle, the weighted logarithmic derivative has the kernel form `G/(w-z)`.
    calc
      w * logDeriv g w = w * ((k : ℂ) / (w - z) + h w) := by rw [hlog_w]
      _ = G w / (w - z) := by
        field_simp [G, hsub_ne]
        ring
  have hkernel :
      (∮ w in C(z, r), G w / (w - z)) = (2 * Real.pi * Complex.I : ℂ) * G z := by
    have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hG_diff.circleIntegral_sub_inv_smul hz_ball
  -- Combine the circle-integral comparison with the Cauchy kernel evaluation at the center.
  refine ⟨r, hr, hclosedQ, hclosedD, ?_⟩
  calc
    (∮ w in C(z, r), w * logDeriv g w) = ∮ w in C(z, r), G w / (w - z) := hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) * G z := hkernel
    _ = (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) * z) := by rw [hG_center]

/-- Helper for Proposition 5.2: translating by a lattice period preserves meromorphic order. -/
lemma meromorphicOrderAt_add_period_eq
    {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    meromorphicOrderAt g (z + ω) = meromorphicOrderAt g z := by
  have hcomp :
      meromorphicOrderAt (fun w : ℂ ↦ g (w + ω)) z =
        meromorphicOrderAt g (z + ω) := by
    -- Compose with the translation map `w ↦ w + ω`, whose derivative is `1`.
    simpa [Function.comp] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := g) (g := fun w : ℂ ↦ w + ω) (x := z)
        (show AnalyticAt ℂ (fun w : ℂ ↦ w + ω) z by fun_prop)
        (by simpa using (one_ne_zero : (1 : ℂ) ≠ 0)))
  have hcongr :
      meromorphicOrderAt (fun w : ℂ ↦ g (w + ω)) z = meromorphicOrderAt g z := by
    -- On every punctured neighborhood, periodicity identifies the translated germ with `g`.
    apply meromorphicOrderAt_congr
    filter_upwards [Filter.Eventually.of_forall (fun w : ℂ ↦ hperiods ω hω w)] with w hw
    simpa using hw
  exact hcomp.symm.trans hcongr

/-- Helper for Proposition 5.2: divisor values agree for points differing by a lattice period,
even when they are read on different representative sections. -/
lemma divisor_eq_of_sub_mem_period_lattice
    {g : ℂ → ℂ} {Q : Set ℂ} {z z' : ℂ}
    (hg : Meromorphic g) (hperiods : HasPeriodLattice L g)
    (hzP : z ∈ P) (hz'Q : z' ∈ Q) (hsub : z' - z ∈ L.lattice) :
    divisor g Q z' = divisor g P z := by
  -- Read both divisor values as local orders, then translate the local germ by the period
  -- vector `z' - z`.
  rw [hg.meromorphicOn.divisor_apply hz'Q, hg.meromorphicOn.divisor_apply hzP]
  exact congrArg (fun w : WithTop ℤ ↦ w.untop₀) <|
    by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (meromorphicOrderAt_add_period_eq
          (L := L) (g := g) hperiods (z := z) (ω := z' - z) hsub)

/-- Helper for Proposition 5.2: translating by a lattice period preserves the derivative of a
periodic function. -/
lemma deriv_add_period_eq
    {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    deriv g (z + ω) = deriv g z := by
  have htranslate : (fun w : ℂ ↦ g (w + ω)) = g := by
    -- Periodicity identifies the translated function with the original one pointwise.
    funext w
    exact hperiods ω hω w
  -- Compare the derivative of the translated function in the two canonical ways.
  calc
    deriv g (z + ω) = deriv (fun w : ℂ ↦ g (w + ω)) z := by
      symm
      simpa [add_comm] using (deriv_comp_add_const (f := g) (a := ω) (x := z))
    _ = deriv g z := by
      exact congrArg (fun F : ℂ → ℂ ↦ deriv F z) htranslate

/-- Helper for Proposition 5.2: translating by a lattice period preserves the logarithmic
derivative. -/
lemma logDeriv_add_period_eq
    {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    logDeriv g (z + ω) = logDeriv g z := by
  -- Rewrite `logDeriv` as `deriv / value` and transport both terms through periodicity.
  rw [logDeriv_apply, logDeriv_apply]
  simp [deriv_add_period_eq (L := L) (g := g) hperiods hω, hperiods ω hω z]

/-- Helper for Proposition 5.2: shifting the weighted logarithmic derivative by a lattice period
produces the original value plus the period-weighted correction term. -/
lemma weighted_logDeriv_add_period_eq
    {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    (z + ω) * logDeriv g (z + ω) = z * logDeriv g z + ω * logDeriv g z := by
  -- After identifying the shifted logarithmic derivative with the original one, only bilinearity
  -- of multiplication remains.
  rw [logDeriv_add_period_eq (L := L) (g := g) hperiods hω]
  ring

/-- Helper for Proposition 5.2: the difference between opposite translated edge integrands is the
period times the unweighted logarithmic derivative. -/
lemma weighted_logDeriv_add_period_sub_eq_period_mul_logDeriv
    {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    (z + ω) * logDeriv g (z + ω) - z * logDeriv g z = ω * logDeriv g z := by
  -- Route correction: isolate the edge-pairing algebra in a flat rewrite lemma instead of
  -- rederiving it inside the translated boundary theorem.
  calc
    (z + ω) * logDeriv g (z + ω) - z * logDeriv g z =
        (z * logDeriv g z + ω * logDeriv g z) - z * logDeriv g z := by
          rw [weighted_logDeriv_add_period_eq (L := L) (g := g) hperiods hω]
    _ = ω * logDeriv g z := by
          ring

/-- Helper for Proposition 5.2: replacing a meromorphic function on an open owner by its
normal-form representative preserves the weighted logarithmic derivative on a codiscrete subset of
that owner. -/
lemma weightedLogDeriv_toMeromorphicNFOn_eq_codiscrete
    {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g U) :
    (fun z ↦ z * logDeriv g z) =ᶠ[Filter.codiscreteWithin U]
      (fun z ↦ z * logDeriv (toMeromorphicNFOn g U) z) := by
  -- Route correction: keep the weighted integrand in the single global owner spelling
  -- `toMeromorphicNFOn g U` instead of mixing it with pointwise normal forms.
  filter_upwards [logDeriv_toMeromorphicNFOn_eq_codiscrete (U := U) hg] with z hz
  exact congrArg (fun w : ℂ ↦ z * w) hz

/-- Helper for Proposition 5.2: once the divisor of the normal-form owner vanishes on `V`, the
weighted logarithmic derivative is differentiable throughout `V`. -/
lemma differentiableOn_weightedLogDeriv_toMeromorphicNFOn_of_divisor_zero
    {U V : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g U)
    (hV : V ⊆ U)
    (hdiv : ∀ z ∈ V, MeromorphicOn.divisor g U z = 0) :
    DifferentiableOn ℂ (fun w ↦ w * logDeriv (toMeromorphicNFOn g U) w) V := by
  have hgNF : MeromorphicNFOn (toMeromorphicNFOn g U) U := by
    simpa using meromorphicNFOn_toMeromorphicNFOn g U
  intro z hzV
  have hzU : z ∈ U := hV hzV
  have hdiv_nf :
      MeromorphicOn.divisor (toMeromorphicNFOn g U) U z = 0 := by
    -- The owner-change identity lets the divisor-zero hypothesis be read directly on the
    -- normal-form owner.
    have hdiv_eq :
        MeromorphicOn.divisor (toMeromorphicNFOn g U) U z =
          MeromorphicOn.divisor g U z := by
      simpa using
        congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
          (hg.divisor_of_toMeromorphicNFOn)
    simpa [hdiv_eq] using hdiv z hzV
  have horder :
      meromorphicOrderAt (toMeromorphicNFOn g U) z = 0 ∨
        meromorphicOrderAt (toMeromorphicNFOn g U) z = ⊤ :=
    meromorphicOrderAt_eq_zero_or_top_of_divisor_eq_zero hgNF.meromorphicOn hzU hdiv_nf
  have hlog :
      DifferentiableAt ℂ (logDeriv (toMeromorphicNFOn g U)) z :=
    differentiableAt_logDeriv_of_meromorphicNFAt_order_zero_or_top (hgNF hzU) horder
  -- Multiply the holomorphic logarithmic derivative by the identity map at the point of `V`.
  exact (differentiableAt_id.mul hlog).differentiableWithinAt

/-- Helper for Proposition 5.2: translating a segment integral of a periodic integrand by one
period does not change the value. -/
lemma curveIntegral_segment_translate_eq_of_periodic
    {φ : ℂ → ℂ} {a b ω : ℂ} (hperiodic : Function.Periodic φ ω) :
    ∫ᶜ z in Path.segment (a + ω) (b + ω), ((φ dz) z) =
      ∫ᶜ z in Path.segment a b, ((φ dz) z) := by
  -- Rewrite both contour integrals through the affine segment parameterization.
  rw [curveIntegral_segment, curveIntegral_segment]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro t _
  have hline :
      AffineMap.lineMap (a + ω) (b + ω) t = AffineMap.lineMap a b t + ω := by
    -- Translating both endpoints translates the whole affine line segment by the same period.
    simp [AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
  have hdiff : (b + ω) - (a + ω) = b - a := by
    -- The segment direction is invariant under common translation.
    abel
  -- Periodicity removes the translated basepoint from the segment integrand.
  simpa [Complex.scalarOneForm_apply, hline, hdiff, add_comm] using
    congrArg (fun c : ℂ ↦ c * (b - a)) (hperiodic (AffineMap.lineMap a b t))

/-- Helper for Proposition 5.2: unpacking `toClosedPath.toPath` on a genuine loop only inserts
the endpoint cast forced by the closed-path wrapper. -/
lemma loopToClosedPathToPathEqCast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  -- The closed-path wrapper does not change the underlying path of an actual loop.
  cases γ
  rfl

/-- Helper for Proposition 5.2: if two weighted representatives differ by a lattice vector, then
their weighted classes agree modulo the period lattice. -/
lemma zsmul_eq_mod_period_lattice_of_sub_mem
    {n : ℤ} {z z' : ℂ} (hsub : z - z' ∈ L.lattice) :
    (((n • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
      (((n • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
  -- Pass equality in the quotient to membership of the difference in the lattice subgroup.
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa [sub_eq_add_neg, smul_sub] using L.lattice.smul_mem n hsub

/-- Helper for Proposition 5.2: if two points on representative sections differ by a lattice
period, then their divisor-weighted classes agree modulo the period lattice. -/
lemma divisor_weighted_eq_mod_period_lattice_of_sub_mem
    {g : ℂ → ℂ} {Q : Set ℂ} {z z' : ℂ}
    (hg : Meromorphic g) (hperiods : HasPeriodLattice L g)
    (hzP : z ∈ P) (hz'Q : z' ∈ Q) (hsub : z' - z ∈ L.lattice) :
    (((divisor g Q z' • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
      (((divisor g P z • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hdiv : divisor g Q z' = divisor g P z :=
    divisor_eq_of_sub_mem_period_lattice
      (L := L) (P := P) (g := g) hg hperiods hzP hz'Q hsub
  -- First align the multiplicity, then transport the weighted point itself through the quotient.
  calc
    (((divisor g Q z' • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
        (((divisor g P z • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp [hdiv]
    _ = (((divisor g P z • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          have hsub' : z' - z ∈ L.lattice := hsub
          simpa using
            (zsmul_eq_mod_period_lattice_of_sub_mem
              (L := L) (n := divisor g P z) (z := z') (z' := z) hsub')

/-- Helper for Proposition 5.2: the same transport works for the pole weights
`-divisor g • z`. -/
lemma neg_divisor_weighted_eq_mod_period_lattice_of_sub_mem
    {g : ℂ → ℂ} {Q : Set ℂ} {z z' : ℂ}
    (hg : Meromorphic g) (hperiods : HasPeriodLattice L g)
    (hzP : z ∈ P) (hz'Q : z' ∈ Q) (hsub : z' - z ∈ L.lattice) :
    ((((-divisor g Q z') • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
      ((((-divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
  -- Reuse the weighted transport lemma with the negated divisor multiplicity.
  simpa [neg_smul] using
    (divisor_weighted_eq_mod_period_lattice_of_sub_mem
      (L := L) (P := P) (g := g) (Q := Q) hg hperiods hzP hz'Q hsub)

