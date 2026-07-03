import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

-- Semantic recall note: the section already fixes `PeriodPair`, `PeriodPair.periodParallelogram`,
-- `IsZeroRepresentativeSet`, and `IsPoleRepresentativeSet` as the source-facing owners, with
-- weights read from the canonical divisor owner `MeromorphicOn.divisor`; the quotient by
-- `L.lattice.toAddSubgroup` remains the congruence-mod-period-lattice bridge.

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: subtracting a constant preserves the meromorphic order at a genuine
pole. -/
lemma meromorphicOrderAt_sub_const_eq_of_lt_zero
    {f : ℂ → ℂ} {a z : ℂ}
    (hz : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z := by
  have hconst_nonneg : 0 ≤ meromorphicOrderAt (fun _ ↦ (-a : ℂ)) z := by
    by_cases ha : a = 0
    · simp [meromorphicOrderAt_const, ha]
    · have hne : (-a : ℂ) ≠ 0 := by simpa using ha
      simp [meromorphicOrderAt_const, hne]
  have hlt_const : meromorphicOrderAt f z < meromorphicOrderAt (fun _ ↦ (-a : ℂ)) z :=
    lt_of_lt_of_le hz hconst_nonneg
  simpa [sub_eq_add_neg] using
    (meromorphicOrderAt_add_eq_left_of_lt
      (f₁ := f) (f₂ := fun _ ↦ (-a : ℂ)) (x := z)
      (MeromorphicAt.const (-a) z) hlt_const)

/-- Helper for Proposition 5.2: subtracting a constant preserves the period lattice. -/
lemma hasPeriodLattice_sub_const
    {f : ℂ → ℂ} {a : ℂ}
    (hperiods : HasPeriodLattice L f) :
    HasPeriodLattice L (fun w ↦ f w - a) := by
  intro ω hω z
  -- Apply the original periodicity relation and subtract the same constant on both sides.
  simpa using congrArg (fun x : ℂ ↦ x - a) (hperiods ω hω z)

/-- Helper for Proposition 5.2: subtracting a constant does not change the chosen pole
representatives on `P`. -/
lemma isPoleRepresentativeSet_sub_const
    {f : ℂ → ℂ} {a : ℂ} {poles : Finset ℂ}
    (hf : Meromorphic f)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    IsPoleRepresentativeSet (fun w ↦ f w - a) P poles := by
  have hsub_meromorphic : MeromorphicOn (fun w ↦ f w - a) P := by
    -- Meromorphicity is stable under subtracting an analytic constant.
    simpa using hf.meromorphicOn.sub
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ a) P).meromorphicOn)
  intro z
  rw [hpoles.mem_iff z]
  constructor
  · rintro ⟨hzP, hzneg⟩
    have horder_neg : meromorphicOrderAt f z < 0 := by
      exact lt_of_not_ge (by simpa using not_le_of_gt (show (meromorphicOrderAt f z).untop₀ < 0 by
        simpa [hf.meromorphicOn.divisor_apply hzP] using hzneg))
    have horder_eq :
        meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z :=
      meromorphicOrderAt_sub_const_eq_of_lt_zero (a := a) horder_neg
    -- Once the negative order is unchanged, the divisor value and hence pole membership agree.
    refine ⟨hzP, ?_⟩
    simpa [hsub_meromorphic.divisor_apply hzP, hf.meromorphicOn.divisor_apply hzP, horder_eq] using
      hzneg
  · rintro ⟨hzP, hzneg⟩
    have horder_neg : meromorphicOrderAt (fun w ↦ f w - a) z < 0 := by
      exact lt_of_not_ge (by
        simpa using not_le_of_gt (show (meromorphicOrderAt (fun w ↦ f w - a) z).untop₀ < 0 by
          simpa [hsub_meromorphic.divisor_apply hzP] using hzneg))
    have horder_eq :
        meromorphicOrderAt f z = meromorphicOrderAt (fun w ↦ f w - a) z := by
      -- Add back the same constant to recover the original meromorphic germ.
      simpa using
        (meromorphicOrderAt_sub_const_eq_of_lt_zero
          (f := fun w ↦ f w - a) (a := -a) horder_neg)
    refine ⟨hzP, ?_⟩
    simpa [hf.meromorphicOn.divisor_apply hzP, hsub_meromorphic.divisor_apply hzP, horder_eq] using
      hzneg

/-- Helper for Proposition 5.2: subtracting a constant does not change the divisor value at a
genuine pole inside the chosen representative set. -/
lemma divisor_sub_const_eq_of_divisor_lt_zero
    {f : ℂ → ℂ} {a z : ℂ}
    (hf : Meromorphic f)
    (hzP : z ∈ P)
    (hzneg : divisor f P z < 0) :
    divisor (fun w ↦ f w - a) P z = divisor f P z := by
  have hsub_meromorphic : MeromorphicOn (fun w ↦ f w - a) P := by
    -- Meromorphicity is stable under subtracting an analytic constant.
    simpa using hf.meromorphicOn.sub
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ a) P).meromorphicOn)
  have horder_neg : meromorphicOrderAt f z < 0 := by
    exact lt_of_not_ge (by
      simpa [hf.meromorphicOn.divisor_apply hzP] using not_le_of_gt (show
        (meromorphicOrderAt f z).untop₀ < 0 by
          simpa [hf.meromorphicOn.divisor_apply hzP] using hzneg))
  have horder_eq :
      meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z :=
    meromorphicOrderAt_sub_const_eq_of_lt_zero (a := a) horder_neg
  -- Once the negative meromorphic order agrees, the divisor value agrees as well.
  simp [hsub_meromorphic.divisor_apply hzP, hf.meromorphicOn.divisor_apply hzP, horder_eq]

/-- Helper for Proposition 5.2: the weighted logarithmic derivative has the expected local limit
that later feeds the residue computation. -/
lemma tendsto_sub_mul_weighted_logDeriv_eq_order_mul_point
    {g : ℂ → ℂ} {z₀ : ℂ} {k : ℤ}
    (hg : MeromorphicAt g z₀) (horder : meromorphicOrderAt g z₀ = k) :
    Tendsto (fun z ↦ (z - z₀) * (z * logDeriv g z)) (𝓝[≠] z₀) (𝓝 ((k : ℂ) * z₀)) := by
  have hz :
      Tendsto (fun z : ℂ ↦ z) (𝓝[≠] z₀) (𝓝 z₀) := by
    -- The identity map still tends to `z₀` along the punctured neighborhood.
    simpa using continuousAt_id.continuousWithinAt.tendsto
  have hlog :
      Tendsto (fun z ↦ (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 (k : ℂ)) :=
    tendsto_sub_mul_logDeriv_eq_order (𝕜 := ℂ) (f := g) (z₀ := z₀) (k := k) hg horder
  have hmul :
      Tendsto (fun z ↦ z * ((z - z₀) * logDeriv g z)) (𝓝[≠] z₀) (𝓝 (z₀ * (k : ℂ))) :=
    hz.mul hlog
  -- Reassociate the product so the limit matches the residue-style weighting by `z`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 5.2: a holomorphic kernel of the form `g(w) / (w - z)` realizes the
residue `g z` on any sufficiently small circle contained in the chosen domain. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hD : Metric.closedBall z r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun w ↦ g w / (w - z)) z (g z) := by
  -- Use the given circle as the source-faithful local contour and apply the standard Cauchy
  -- kernel integral to the holomorphic numerator `g`.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall z r) := hg.mono hD
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul hz_ball

/-- Helper for Proposition 5.2: if `g` is analytic and nonzero at `z`, then `logDeriv g` is
holomorphic at `z`. -/
lemma differentiableAt_logDeriv_of_analyticAt_nonzero
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    DifferentiableAt ℂ (logDeriv g) z := by
  have hlog : AnalyticAt ℂ (logDeriv g) z := by
    -- Rewrite `logDeriv` as `deriv g / g`; analyticity follows because the denominator does not
    -- vanish at the center.
    simpa [logDeriv] using (hg.deriv.div hg hgz)
  exact hlog.differentiableAt

/-- Helper for Proposition 5.2: meromorphic order zero forces analyticity. -/
lemma analyticAt_of_meromorphicOrderAt_eq_zero
    {g : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = (0 : ℤ)) :
    AnalyticAt ℂ g z := by
  -- TODO: promote the punctured-neighborhood equality `hg.eq_nhdsNE_toMeromorphicNFAt` to an
  -- ordinary neighborhood equality, then transfer `MeromorphicNFAt` from the normal form back to
  -- `g` and conclude by `meromorphicOrderAt_nonneg_iff_analyticAt`.
  sorry

/-- Helper for Proposition 5.2: when the meromorphic order is zero, the weighted logarithmic
derivative is holomorphic at the point. -/
lemma differentiableAt_weighted_logDeriv_of_order_zero
    {g : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = (0 : ℤ)) :
    DifferentiableAt ℂ (fun w ↦ w * logDeriv g w) z := by
  -- TODO: combine the analytic/nonvanishing statement from
  -- `analyticAt_of_meromorphicOrderAt_eq_zero` with the normal-form characterization of order
  -- zero to prove that `logDeriv g` is holomorphic at `z`, then multiply by the identity map.
  sorry

/-- Helper for Proposition 5.2: at a zero or pole of finite nonzero order inside the translated
period parallelogram, the weighted logarithmic derivative has local residue `(k : ℂ) * z`. -/
lemma localResidueCircle_weighted_logDeriv_of_order
    {Q : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {k : ℤ}
    (hzQ : z ∈ interior Q)
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = k) (hk : k ≠ 0) :
    LocalResidueCircle Q Set.univ (fun w ↦ w * logDeriv g w) z ((k : ℂ) * z) := by
  -- TODO: choose a small closed ball contained in `interior Q`, use
  -- `logDeriv_eventuallyEq_order_principalPart_add_analytic` to rewrite
  -- `w * logDeriv g w` as `G w / (w - z)` on that circle, invoke
  -- `localResidueCircle_div_sub_of_differentiableOn`, and simplify `G z = (k : ℂ) * z`.
  sorry

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

/-- Helper for Proposition 5.2: every lattice class has a representative in any chosen period
parallelogram. -/
lemma exists_mem_periodParallelogram_sub_lattice
    (z z₀ : ℂ) :
    ∃ w : ℂ, w ∈ L.periodParallelogram z₀ ∧ w - z ∈ L.lattice := by
  let c : Fin 2 → ℝ := L.basis.equivFun (z - z₀)
  let w : ℂ := z₀ + Int.fract (c 0) • L.ω₁ + Int.fract (c 1) • L.ω₂
  refine ⟨w, ?_, ?_⟩
  · -- The fractional coordinates stay in `[0, 1)`, so they define a point of the chosen
    -- period parallelogram.
    refine ⟨Int.fract (c 0), Int.fract (c 1), Int.fract_nonneg _, ?_, Int.fract_nonneg _, ?_, rfl⟩
    · exact le_of_lt (Int.fract_lt_one _)
    · exact le_of_lt (Int.fract_lt_one _)
  · -- Subtracting the integer parts of the basis coordinates produces the required lattice
    -- translation from `z` to the chosen representative `w`.
    have hcoords : z - z₀ = c 0 * L.ω₁ + c 1 * L.ω₂ := by
      simpa [c, smul_eq_mul] using (L.basis.sum_equivFun (z - z₀)).symm
    have hz' : z = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by
      calc
        z = z₀ + (z - z₀) := by ring
        _ = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by rw [hcoords]
    have hwz :
        w - z = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
      calc
        w - z =
            (Int.fract (c 0) - c 0) * L.ω₁ + (Int.fract (c 1) - c 1) * L.ω₂ := by
              rw [hz']
              simp [w]
              ring
        _ = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
              have h0 :
                  ((↑(Int.fract (c 0)) : ℂ) - ↑(c 0)) = (((-⌊c 0⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h0r : (c 0 - (⌊c 0⌋ : ℝ)) - c 0 = (-((⌊c 0⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h0r
              have h1 :
                  ((↑(Int.fract (c 1)) : ℂ) - ↑(c 1)) = (((-⌊c 1⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h1r : (c 1 - (⌊c 1⌋ : ℝ)) - c 1 = (-((⌊c 1⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h1r
              rw [h0, h1]
    exact L.mem_lattice.mpr ⟨-⌊c 0⌋, -⌊c 1⌋, hwz.symm⟩

/-- Helper for Proposition 5.2: every period parallelogram is compact. -/
lemma isCompact_periodParallelogram (z₀ : ℂ) :
    IsCompact (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ → ℂ := fun t ↦ z₀ + t.1 • L.ω₁ + t.2 • L.ω₂
  have he : Continuous e := by
    -- The affine-coordinate parametrization is continuous in both real variables.
    continuity
  have himage :
      e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = L.periodParallelogram z₀ := by
    ext z
    constructor
    · rintro ⟨⟨t₁, t₂⟩, ht, rfl⟩
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨t₁, t₂, ht₁.1, ht₁.2, ht₂.1, ht₂.2, rfl⟩
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      exact ⟨⟨t₁, t₂⟩, ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, rfl⟩
  -- Compactness comes from the closed unit square via the affine parametrization.
  rw [← himage]
  exact (isCompact_Icc.prod isCompact_Icc).image he

/-- Helper for Proposition 5.2: the basis-coordinate homeomorphism identifies a real pair
`(t₁, t₂)` with the linear combination `t₁ ω₁ + t₂ ω₂`. -/
lemma basis_pair_homeomorph_apply (p : ℝ × ℝ) :
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the inverse basis map through the standard `Fin 2` coordinates.
  calc
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
        L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) := by
          rfl
    _ = ∑ i : Fin 2,
          L.basis.equivFun
            (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i •
            L.basis i := by
          simpa using
            (L.basis.sum_equivFun
              (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p))).symm
    _ = ∑ i : Fin 2, ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) i • L.basis i := by
          congr with i
          exact congrArg (fun a : ℝ ↦ a • L.basis i)
            (congrFun
              (L.basis.equivFunL.apply_symm_apply
                ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i)
    _ = p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simp [Fin.sum_univ_two]

/-- Helper for Proposition 5.2: the inverse basis map sends the first `Fin 2` coordinate to the
first basis coefficient. -/
lemma basis_equivFunL_symm_apply_zero (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 0 = a := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 0
  simpa using h

/-- Helper for Proposition 5.2: the inverse basis map sends the second `Fin 2` coordinate to the
second basis coefficient. -/
lemma basis_equivFunL_symm_apply_one (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 1 = b := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 1
  simpa using h

/-- Helper for Proposition 5.2: a frontier point of a period parallelogram has affine coordinates
in `[0, 1]^2`, and at least one coordinate lies on the boundary `{0, 1}`. -/
lemma frontier_periodParallelogram_coord_eq_zero_or_one {z z₀ : ℂ}
    (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    ∃ t₁ t₂ : ℝ,
      0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      z = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ ∧
      (t₁ = 0 ∨ t₁ = 1 ∨ t₂ = 0 ∨ t₂ = 1) := by
  let e : ℝ × ℝ ≃ₜ ℂ :=
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀)
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have himage : e '' square = L.periodParallelogram z₀ := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp₁, hp₂⟩
      refine ⟨p.1, p.2, hp₁.1, hp₁.2, hp₂.1, hp₂.2, ?_⟩
      -- Read the image point in period-basis coordinates.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
          z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [add_assoc]
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      refine ⟨(t₁, t₂), ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, ?_⟩
      -- The converse direction is the same affine-coordinate expansion.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (t₁, t₂) : ℂ) =
          z₀ + t₁ • L.ω₁ + t₂ • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [add_assoc]
  have hz' : z ∈ e '' frontier square := by
    rw [e.image_frontier, himage]
    exact hz
  rcases hz' with ⟨p, hpfrontier, rfl⟩
  have hpcoords :
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) := by
    -- Transport the frontier condition back to the unit square.
    change p ∈ frontier (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) at hpfrontier
    have hpfrontier' :
        ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (p.2 = 0 ∨ p.2 = 1)) ∨
          ((p.1 = 0 ∨ p.1 = 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)) := by
      simpa only [frontier_prod_eq, closure_Icc, frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num),
        Set.mem_union, Set.mem_prod, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
        using hpfrontier
    rcases hpfrontier' with h | h
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₂ with hp₂ | hp₂
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inl hp₂))⟩
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inr hp₂))⟩
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₁ with hp₁ | hp₁
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inl hp₁⟩
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inr (Or.inl hp₁)⟩
  refine ⟨p.1, p.2, hpcoords.1, hpcoords.2.1, hpcoords.2.2.1, hpcoords.2.2.2.1, ?_,
    hpcoords.2.2.2.2⟩
  -- Translate the recovered square coordinates back to the actual period parallelogram.
  change
    z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
  rw [basis_pair_homeomorph_apply]
  simp [add_assoc]

/-- Helper for Proposition 5.2: lattice points have integral coordinates in the period basis. -/
lemma exists_int_basis_coords_of_mem_lattice {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, L.basis.equivFun z 0 = m ∧ L.basis.equivFun z 1 = n := by
  obtain ⟨m, n, hmn⟩ := L.mem_lattice.mp hz
  have hmn' : z = (L.basis.equivFunL.symm ![(m : ℝ), (n : ℝ)] : ℂ) := by
    -- Repackage the lattice expansion through the inverse basis map.
    calc
      z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := hmn.symm
      _ = (L.basis.equivFunL.symm ![(m : ℝ), (n : ℝ)] : ℂ) := by
            symm
            simpa [smul_eq_mul] using
              (basis_pair_homeomorph_apply (L := L) ((m : ℝ), (n : ℝ)))
  refine ⟨m, n, ?_, ?_⟩
  · -- Read the first basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using basis_equivFunL_symm_apply_zero (L := L) (m : ℝ) (n : ℝ)
  · -- Read the second basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using basis_equivFunL_symm_apply_one (L := L) (m : ℝ) (n : ℝ)

/-- Helper for Proposition 5.2: a point of a period parallelogram has basis coordinates in
`[0, 1]^2` after subtracting the basepoint. -/
lemma basis_coords_sub_of_mem_periodParallelogram {z z₀ : ℂ}
    (hz : z ∈ L.periodParallelogram z₀) :
    ∃ u v : ℝ,
      0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      L.basis.equivFun (z - z₀) 0 = u ∧
      L.basis.equivFun (z - z₀) 1 = v := by
  rcases hz with ⟨u, v, hu0, hu1, hv0, hv1, hz⟩
  have hsub :
      z - z₀ = u • L.ω₁ + v • L.ω₂ := by
    -- Subtract the basepoint from the affine-coordinate description of `z`.
    calc
      z - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz]
      _ = u • L.ω₁ + v • L.ω₂ := by ring
  have hsub_coords : z - z₀ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
    -- Repackage the affine combination through the inverse basis map.
    calc
      z - z₀ = u • L.ω₁ + v • L.ω₂ := hsub
      _ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
            symm
            simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (u, v))
  have hcoord0 : L.basis.equivFun (z - z₀) 0 = u := by
    -- Read the first basis coordinate from the inverse basis map.
    rw [hsub_coords]
    simpa using basis_equivFunL_symm_apply_zero (L := L) u v
  have hcoord1 : L.basis.equivFun (z - z₀) 1 = v := by
    -- Read the second basis coordinate from the inverse basis map.
    rw [hsub_coords]
    simpa using basis_equivFunL_symm_apply_one (L := L) u v
  exact ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩

/-- Helper for Proposition 5.2: if a translated-boundary point is represented by `w` in the base
period parallelogram, then one of the representative coordinates must equal the chosen shift. -/
lemma representative_coord_eq_shift_of_translated_frontier
    {u v : ℝ} {z₀ z z₁ w : ℂ}
    (hz₁ : z₁ = z₀ + u • L.ω₁ + v • L.ω₂)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (hz : z ∈ frontier (L.periodParallelogram z₁))
    (hw : w ∈ L.periodParallelogram z₀)
    (hsub : w - z ∈ L.lattice) :
    L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v := by
  obtain ⟨m, n, hm, hn⟩ := exists_int_basis_coords_of_mem_lattice (L := L) hsub
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hcoord0, hcoord1⟩ :=
    basis_coords_sub_of_mem_periodParallelogram (L := L) hw
  obtain ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, hz_eq, hedge⟩ :=
    frontier_periodParallelogram_coord_eq_zero_or_one (L := L) hz
  have hz_sub_eq : z - z₁ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
    -- The frontier coordinates are the basis coordinates after subtracting the translated basepoint.
    calc
      z - z₁ = t₁ • L.ω₁ + t₂ • L.ω₂ := by
        calc
          z - z₁ = (z₁ + t₁ • L.ω₁ + t₂ • L.ω₂) - z₁ := by rw [hz_eq]
          _ = t₁ • L.ω₁ + t₂ • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (t₁, t₂))
  have hz_coord0 : L.basis.equivFun (z - z₁) 0 = t₁ := by
    -- Read the first frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using basis_equivFunL_symm_apply_zero (L := L) t₁ t₂
  have hz_coord1 : L.basis.equivFun (z - z₁) 1 = t₂ := by
    -- Read the second frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using basis_equivFunL_symm_apply_one (L := L) t₁ t₂
  have hz₁_sub_eq : z₁ - z₀ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
    -- The chosen translation vector has basis coordinates `(u, v)`.
    calc
      z₁ - z₀ = u • L.ω₁ + v • L.ω₂ := by
        calc
          z₁ - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz₁]
          _ = u • L.ω₁ + v • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (u, v))
  have hz₁_coord0 : L.basis.equivFun (z₁ - z₀) 0 = u := by
    -- Read the first coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using basis_equivFunL_symm_apply_zero (L := L) u v
  have hz₁_coord1 : L.basis.equivFun (z₁ - z₀) 1 = v := by
    -- Read the second coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using basis_equivFunL_symm_apply_one (L := L) u v
  have hsum0 : a = m + t₁ + u := by
    -- The first representative coordinate splits into lattice, frontier, and translation parts.
    calc
      a = L.basis.equivFun (w - z₀) 0 := hcoord0.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 0 := by
            congr 1
            ring
      _ = L.basis.equivFun (w - z) 0 + (L.basis.equivFun (z - z₁) 0 + L.basis.equivFun (z₁ - z₀) 0) := by
            simp
      _ = m + t₁ + u := by
            rw [hm, hz_coord0, hz₁_coord0]
            ring
  have hsum1 : b = n + t₂ + v := by
    -- The second representative coordinate splits in the same way.
    calc
      b = L.basis.equivFun (w - z₀) 1 := hcoord1.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 1 := by
            congr 1
            ring
      _ = L.basis.equivFun (w - z) 1 + (L.basis.equivFun (z - z₁) 1 + L.basis.equivFun (z₁ - z₀) 1) := by
            simp
      _ = n + t₂ + v := by
            rw [hn, hz_coord1, hz₁_coord1]
            ring
  rcases hedge with ht₁ | ht₁ | ht₂ | ht₂
  · -- On the `t₁ = 0` edge, the first representative coordinate must be the chosen shift `u`.
    left
    have hm_gt_neg_one : (-1 : ℝ) < m := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hm_lt_one : (m : ℝ) < 1 := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hm_gt_neg_one' : (-1 : ℤ) < m := by exact_mod_cast hm_gt_neg_one
    have hm_lt_one' : m < 1 := by exact_mod_cast hm_lt_one
    have hm_zero : m = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + m := by
            have hsum0' : a = m + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hm_zero]
  · -- On the `t₁ = 1` edge, integrality forces the lattice correction to be `-1`.
    left
    have hk_gt_neg_one : (-1 : ℝ) < (m + 1 : ℤ) := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hk_lt_one : (((m + 1 : ℤ) : ℝ)) < 1 := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hk_gt_neg_one' : (-1 : ℤ) < m + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : m + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : m + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + ((m + 1 : ℤ) : ℝ) := by
            have hsum0' : a = (m + 1 : ℤ) + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hk_zero]
  · -- On the `t₂ = 0` edge, the second representative coordinate must be the chosen shift `v`.
    right
    have hn_gt_neg_one : (-1 : ℝ) < n := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hn_lt_one : (n : ℝ) < 1 := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hn_gt_neg_one' : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    have hn_lt_one' : n < 1 := by exact_mod_cast hn_lt_one
    have hn_zero : n = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + n := by
            have hsum1' : b = n + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hn_zero]
  · -- On the `t₂ = 1` edge, integrality forces the second lattice correction to be `-1`.
    right
    have hk_gt_neg_one : (-1 : ℝ) < (n + 1 : ℤ) := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hk_lt_one : (((n + 1 : ℤ) : ℝ)) < 1 := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hk_gt_neg_one' : (-1 : ℤ) < n + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : n + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : n + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + ((n + 1 : ℤ) : ℝ) := by
            have hsum1' : b = (n + 1 : ℤ) + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hk_zero]

/-- Helper for Proposition 5.2: every finite subset of `ℝ` misses some point of the open unit
interval. -/
lemma exists_point_Ioo_not_mem_finset (s : Finset ℝ) :
    ∃ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∉ s := by
  -- TODO: choose `s.card + 1` rational points in `(0,1)` and apply a pigeonhole/cardinality
  -- argument to obtain one outside the finite set `s`.
  sorry

/-- Helper for Proposition 5.2: one can choose a translate of the period parallelogram whose two
shift coordinates avoid the finitely many coordinates of a prescribed finite support. -/
lemma period_parallelogram_shift_avoids_finite_boundary_coordinates
    {z₀ : ℂ} {S : Finset ℂ}
    (hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀) :
    ∃ u v : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ v ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ s ∈ S, L.basis.equivFun (s - z₀) 0 ≠ u ∧ L.basis.equivFun (s - z₀) 1 ≠ v := by
  classical
  let firstCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 0
  let secondCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 1
  obtain ⟨u, hu, hu_not_mem⟩ := exists_point_Ioo_not_mem_finset firstCoords
  obtain ⟨v, hv, hv_not_mem⟩ := exists_point_Ioo_not_mem_finset secondCoords
  refine ⟨u, v, hu, hv, ?_⟩
  intro s hs
  constructor
  · -- The first shift coordinate was chosen outside the first-coordinate image of `S`.
    intro hs_eq
    exact hu_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩
  · -- The second shift coordinate was chosen outside the second-coordinate image of `S`.
    intro hs_eq
    exact hv_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩

/-- Helper for Proposition 5.2: the quotient-section bijection `hπ` supplies a representative in
`P` for every lattice class. -/
lemma exists_section_representative_sub_mem_lattice
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (z : ℂ) :
    ∃ w : ℂ, w ∈ P ∧ w - z ∈ L.lattice := by
  rcases hπ.surjOn (show ((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) ∈ Set.univ by simp) with
    ⟨w, hwP, hwz⟩
  refine ⟨w, hwP, ?_⟩
  -- Equality in the quotient is exactly congruence modulo the lattice subgroup.
  rw [QuotientAddGroup.eq_iff_sub_mem] at hwz
  simpa using hwz

/-- Helper for Proposition 5.2: if one point has infinite meromorphic order, connectedness of `ℂ`
forces the divisor-weighted sums to vanish trivially. -/
lemma periodic_meromorphic_order_top_trivializes_weighted_divisor_sum
    {g : ℂ → ℂ}
    (hg : Meromorphic g)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (htop : ∃ z, meromorphicOrderAt g z = ⊤) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hnone_finite : ¬ ∃ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ := by
    intro hfinite
    have hforall_finite :
        ∀ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ :=
      (hg.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1 hfinite
    rcases htop with ⟨z, hz⟩
    exact hforall_finite ⟨z, by simp⟩ hz
  have htop_all : ∀ z : ℂ, meromorphicOrderAt g z = ⊤ := by
    intro z
    by_contra hz
    exact hnone_finite ⟨⟨z, by simp⟩, hz⟩
  have hroots_empty : roots = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hroots.mem_iff z).1 hz with ⟨hzP, hzpos⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ 0 < divisor g P z by simpa [hdiv]) hzpos
  have hpoles_empty : poles = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hpoles.mem_iff z).1 hz with ⟨hzP, hzneg⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ divisor g P z < 0 by simpa [hdiv]) hzneg
  -- Once both representative finsets are empty, the quotient-valued sums are both zero.
  simp [hroots_empty, hpoles_empty]

/-- Helper for Proposition 5.2: in the finite-order branch, one can translate the period
parallelogram so that its boundary avoids every zero and pole represented by the fixed section
`P`. -/
lemma exists_boundary_regular_translate_for_finite_order_support
    {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    ∃ z₁ : ℂ, ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ) := by
  -- Route correction: the source proof first chooses a translated period parallelogram whose
  -- boundary misses the divisor support before any contour integral is computed.
  let S : Finset ℂ := roots ∪ poles
  have hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀ := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hP ((hroots.mem_iff z).1 hz).1
    · exact hP ((hpoles.mem_iff z).1 hz).1
  obtain ⟨u, v, hu, hv, havoid⟩ :=
    period_parallelogram_shift_avoids_finite_boundary_coordinates
      (L := L) (z₀ := z₀) (S := S) hS
  let z₁ : ℂ := z₀ + u • L.ω₁ + v • L.ω₂
  refine ⟨z₁, ?_⟩
  intro z hz
  by_contra hz_ne_zero
  obtain ⟨w, hwP, hwsub⟩ :=
    exists_section_representative_sub_mem_lattice (L := L) (P := P) hπ z
  have hwPar : w ∈ L.periodParallelogram z₀ := hP hwP
  have hcoord :
      L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v :=
    representative_coord_eq_shift_of_translated_frontier
      (L := L) (z₀ := z₀) (z₁ := z₁) (z := z) (w := w) rfl hu hv hz hwPar hwsub
  have horder_w :
      meromorphicOrderAt g w = meromorphicOrderAt g z := by
    -- Transport the boundary order back to the chosen section representative.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (meromorphicOrderAt_add_period_eq
        (L := L) (g := g) hperiods (z := z) (ω := w - z) hwsub)
  have hdiv_ne_zero : divisor g P w ≠ 0 := by
    intro hdiv_zero
    have horder_zero_or_top :
        meromorphicOrderAt g w = (0 : WithTop ℤ) ∨ meromorphicOrderAt g w = ⊤ := by
      have horder_untop_zero : (meromorphicOrderAt g w).untop₀ = 0 := by
        simpa [hg.meromorphicOn.divisor_apply hwP] using hdiv_zero
      exact WithTop.untop₀_eq_zero.mp horder_untop_zero
    rcases horder_zero_or_top with horder_zero | horder_top
    · exact hz_ne_zero (by simpa [horder_w] using horder_zero)
    · exact hfinite w horder_top
  have hw_mem_support : w ∈ S := by
    -- A nonzero finite divisor at the section representative forces membership in `roots ∪ poles`.
    rcases lt_or_gt_of_ne hdiv_ne_zero with hdiv_neg | hdiv_pos
    · exact Finset.mem_union.mpr <| Or.inr ((hpoles.mem_iff w).2 ⟨hwP, hdiv_neg⟩)
    · exact Finset.mem_union.mpr <| Or.inl ((hroots.mem_iff w).2 ⟨hwP, hdiv_pos⟩)
  have havoid_w := havoid w hw_mem_support
  rcases hcoord with hcoord0 | hcoord1
  · exact havoid_w.1 hcoord0
  · exact havoid_w.2 hcoord1

/-- Helper for Proposition 5.2: on a boundary-generic translated period parallelogram, the source
four-edge contour computation yields the weighted divisor identity modulo the period lattice. -/
lemma weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate
    {g : ℂ → ℂ} {z₀ z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  -- Route correction: the weighted Abel relation should now be proved in one theorem-local
  -- contour package instead of re-splitting residue, edge-pairing, and section-transport steps.
  -- TODO: build the explicit four-edge boundary of `L.periodParallelogram z₁`, apply the residue
  -- theorem to `fun w ↦ w * logDeriv g w`, use
  -- `weighted_logDeriv_add_period_sub_eq_period_mul_logDeriv` together with Proposition 5.1 to
  -- pair opposite edges modulo `L.lattice`, and finally transport the translated-parallelogram
  -- divisor identity back to `P` using `divisor_weighted_eq_mod_period_lattice_of_sub_mem` and
  -- `neg_divisor_weighted_eq_mod_period_lattice_of_sub_mem`.
  sorry

/-- Helper for Proposition 5.2: the core Abel relation for a periodic meromorphic function `g`
identified on one full set of representatives `P` for the quotient by the period lattice. -/
lemma sum_divisor_weighted_mod_period_lattice_eq_zero
    {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  by_cases htop : ∃ z, meromorphicOrderAt g z = ⊤
  · -- In the globally degenerate branch, connectedness forces every divisor value to vanish.
    exact periodic_meromorphic_order_top_trivializes_weighted_divisor_sum
      (L := L) (P := P) hg roots poles hroots hpoles htop
  · have hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤ := by
      intro z hz
      exact htop ⟨z, hz⟩
    obtain ⟨z₁, hboundary⟩ :=
      exists_boundary_regular_translate_for_finite_order_support
        (L := L) (P := P) hg hperiods hfinite hP hπ roots poles hroots hpoles
    -- Route correction: after removing the `⊤` branch, the remaining source-faithful proof is the
    -- translated boundary-generic contour computation.
    exact weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate
      (L := L) (P := P) (z₀ := z₀) (z₁ := z₁) hg hperiods hP hπ roots poles hroots hpoles
        hboundary

/-- Proposition 5.2 (1): for a meromorphic function on `ℂ` that is periodic with respect to every
element of the lattice generated by the period pair `L`, the divisor-weighted sum of a chosen set
of representatives `P` inside a period parallelogram of the solutions of `f = a` is congruent
modulo the period lattice to the corresponding divisor-weighted sum of the poles. -/
theorem sum_preimages_eq_sum_poles_mod_period_lattice
    (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (a : ℂ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet (fun w ↦ f w - a) P roots)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    (((roots.sum fun z ↦ divisor (fun w ↦ f w - a) P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor f P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  let g : ℂ → ℂ := fun w ↦ f w - a
  have hg : Meromorphic g := by
    -- Subtracting a constant preserves meromorphicity of the ambient periodic function.
    simpa [g] using (by fun_prop : Meromorphic (fun w ↦ f w - a))
  have hperiods_g : HasPeriodLattice L g := by
    -- The constant shift does not alter the lattice of periods.
    simpa [g] using hasPeriodLattice_sub_const (L := L) (a := a) hperiods
  have hpoles_g : IsPoleRepresentativeSet g P poles := by
    -- The pole divisor is unchanged by subtracting a constant.
    simpa [g] using isPoleRepresentativeSet_sub_const (P := P) (a := a) hf hpoles
  have hpole_sums :
      poles.sum (fun z ↦ (-divisor g P z) • z) =
        poles.sum (fun z ↦ (-divisor f P z) • z) := by
    -- On each pole representative, the shifted divisor agrees with the original divisor.
    refine Finset.sum_congr rfl ?_
    intro z hz
    have hzP : z ∈ P := (hpoles.mem_iff z).1 hz |>.1
    have hzneg : divisor f P z < 0 := (hpoles.mem_iff z).1 hz |>.2
    have hdiv : divisor g P z = divisor f P z := by
      simpa [g] using
        divisor_sub_const_eq_of_divisor_lt_zero (P := P) (a := a) hf hzP hzneg
    simp [hdiv]
  -- Reduce the public theorem to the core Abel relation for the translated meromorphic function.
  calc
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
        (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := by
      simpa [g] using
        sum_divisor_weighted_mod_period_lattice_eq_zero
          (L := L) (P := P) (z₀ := z₀) hg hperiods_g hP hπ roots poles hroots hpoles_g
    _ =
        (((poles.sum fun z ↦ (-divisor f P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := by
      exact congrArg (fun w : ℂ ↦ ((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) hpole_sums

/-- Derived exact-period reformulation of Proposition 5.2 (1). -/
theorem sum_preimages_eq_sum_poles_mod_period_lattice_of_periods_eq_lattice
    (z₀ : ℂ)
    (hf : Meromorphic f)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (hperiods_eq : ∀ ω : ℂ, Function.Periodic f ω ↔ ω ∈ L.lattice.toAddSubgroup)
    (a : ℂ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet (fun w ↦ f w - a) P roots)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    (((roots.sum fun z ↦ divisor (fun w ↦ f w - a) P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor f P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) :=
  sum_preimages_eq_sum_poles_mod_period_lattice L P z₀ hf
    (fun ω hω ↦ (hperiods_eq ω).2 hω) hP hπ a roots poles hroots hpoles

/-- Proposition 5.2 (2): modulo the period lattice of `L`, the divisor-weighted sum of the
representatives in a chosen period parallelogram of the solutions of `f = a` is independent of the
value `a`. -/
theorem sum_preimages_mod_period_lattice_independent_of_value
    (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (a b : ℂ)
    (rootsA rootsB poles : Finset ℂ)
    (hrootsA : IsZeroRepresentativeSet (fun w ↦ f w - a) P rootsA)
    (hrootsB : IsZeroRepresentativeSet (fun w ↦ f w - b) P rootsB)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    (((rootsA.sum fun z ↦ divisor (fun w ↦ f w - a) P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((rootsB.sum fun z ↦ divisor (fun w ↦ f w - b) P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  calc
    (((rootsA.sum fun z ↦ divisor (fun w ↦ f w - a) P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
        (((poles.sum fun z ↦ (-divisor f P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) :=
      sum_preimages_eq_sum_poles_mod_period_lattice L P z₀ hf hperiods hP hπ
        a rootsA poles hrootsA hpoles
    _ =
        (((rootsB.sum fun z ↦ divisor (fun w ↦ f w - b) P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) :=
      (sum_preimages_eq_sum_poles_mod_period_lattice L P z₀ hf hperiods hP hπ
        b rootsB poles hrootsB hpoles).symm

/-- Derived exact-period reformulation of Proposition 5.2 (2). -/
theorem sum_preimages_mod_period_lattice_independent_of_value_of_periods_eq_lattice
    (z₀ : ℂ)
    (hf : Meromorphic f)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (hperiods_eq : ∀ ω : ℂ, Function.Periodic f ω ↔ ω ∈ L.lattice.toAddSubgroup)
    (a b : ℂ)
    (rootsA rootsB poles : Finset ℂ)
    (hrootsA : IsZeroRepresentativeSet (fun w ↦ f w - a) P rootsA)
    (hrootsB : IsZeroRepresentativeSet (fun w ↦ f w - b) P rootsB)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    (((rootsA.sum fun z ↦ divisor (fun w ↦ f w - a) P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((rootsB.sum fun z ↦ divisor (fun w ↦ f w - b) P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) :=
  sum_preimages_mod_period_lattice_independent_of_value L P z₀ hf
    (fun ω hω ↦ (hperiods_eq ω).2 hω) hP hπ a b rootsA rootsB poles hrootsA hrootsB hpoles
