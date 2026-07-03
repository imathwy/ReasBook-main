import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

noncomputable section

universe u

-- The source-facing boundary owner is `IsOrientedBoundaryOf`; the zero/pole count is expressed by
-- mathlib's canonical divisor owner `MeromorphicOn.divisor`; and the logarithmic derivative is the
-- canonical integrand owner for `f' / (f - a)`.

/-- Helper for Proposition 4.1: once `f - a` is analytic and nonvanishing at `z`, its logarithmic
derivative is analytic, hence differentiable, at `z`. This is the boundary-regularity step used by
the source proof after the boundary hypothesis is strengthened from a pointwise value condition to a
germ-stable analytic/nonvanishing condition. -/
lemma differentiableAt_logDeriv_sub_const_of_analyticAt
    {f : ℂ → ℂ} {a z : ℂ} (hf : AnalyticAt ℂ f z) (hvalue : f z ≠ a) :
    DifferentiableAt ℂ (logDeriv (fun w ↦ f w - a)) z := by
  have hsub : AnalyticAt ℂ (fun w ↦ f w - a) z := hf.sub analyticAt_const
  have hsub_ne : (fun w ↦ f w - a) z ≠ 0 := by
    simpa [sub_eq_zero] using hvalue
  -- The denominator stays nonzero at the center, so the quotient `deriv / (f - a)` is analytic.
  have hlog : AnalyticAt ℂ (logDeriv (fun w ↦ f w - a)) z := by
    simpa [logDeriv] using (hsub.deriv.div hsub hsub_ne)
  exact hlog.differentiableAt

/-- Helper for Proposition 4.1: once `f` is analytic on a neighborhood of a set `U` and avoids the
value `a` on `U`, the logarithmic derivative of `f - a` is differentiable throughout `U`. This is
the set-level form of the boundary-strip step in the source proof. -/
lemma differentiableOn_logDeriv_sub_const_of_analyticOnNhd
    {f : ℂ → ℂ} {a : ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hvalue : ∀ z ∈ U, f z ≠ a) :
    DifferentiableOn ℂ (logDeriv (fun w ↦ f w - a)) U := by
  intro z hz
  -- Reduce the set-level statement to the pointwise analytic/nonvanishing lemma above.
  exact
    (differentiableAt_logDeriv_sub_const_of_analyticAt
      (hf z hz) (hvalue z hz)).differentiableWithinAt

/-- Helper for Proposition 4.1: the divisor of a meromorphic function on a compact owner has finite
support. This is the finiteness input needed when the source proof chooses finitely many small
residue circles around the singular points inside `K`. -/
lemma divisor_support_finite_of_isCompact
    {K : Set ℂ} {g : ℂ → ℂ} (hK : IsCompact K) :
    (MeromorphicOn.divisor g K).support.Finite := by
  -- The divisor is a locally finitely supported function within `K`, and compactness upgrades that
  -- local finiteness to ordinary finiteness.
  simpa using (MeromorphicOn.divisor g K).finiteSupport hK

/-- Helper for Proposition 4.1: if `g` is analytic on a neighborhood of `U` and does not vanish at
`z ∈ U`, then its divisor on `U` vanishes at `z`. This is the boundary-elimination step that would
remove nonzero analytic points from the singular support in the source proof. -/
lemma divisor_eq_zero_of_analyticOnNhd_nonvanishing
    {U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hz : z ∈ U) (hgz : g z ≠ 0) :
    MeromorphicOn.divisor g U z = 0 := by
  -- Read the divisor through the analytic-order API and use that nonvanishing forces order `0`.
  rw [hg.meromorphicOn.divisor_apply hz, (hg z hz).meromorphicOrderAt_eq,
    (hg z hz).analyticOrderAt_eq_zero.mpr hgz]
  simp

/-- Helper for Proposition 4.1: an analytic nonvanishing point does not belong to the divisor
support. This packages the previous vanishing computation in the form needed for support
exclusions. -/
lemma not_mem_divisor_support_of_analyticOnNhd_nonvanishing
    {U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hz : z ∈ U) (hgz : g z ≠ 0) :
    z ∉ (MeromorphicOn.divisor g U).support := by
  -- The support condition is exactly the negation of the pointwise divisor vanishing.
  rw [Function.mem_support]
  simp [divisor_eq_zero_of_analyticOnNhd_nonvanishing hg hz hgz]

/-- Helper for Proposition 4.1: the finite sum over the divisor support finset is the ambient
`finsum` of the divisor values. This is the final rewrite after the residue theorem produces a
finite support sum. -/
lemma finset_sum_divisor_eq_finsum_support
    {K : Set ℂ} {g : ℂ → ℂ} (hK : IsCompact K) :
    let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
    Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ)) =
      ∑ᶠ z, (MeromorphicOn.divisor g K z : ℂ) := by
  classical
  let hsupport :=
    divisor_support_finite_of_isCompact (K := K) (g := g) hK
  let s : Finset ℂ := hsupport.toFinset
  -- Rewrite the `finsum` through the finite divisor support provided by compactness.
  rw [finsum_eq_sum_of_support_subset (s := s)]
  intro z hz
  have hz' : z ∈ (MeromorphicOn.divisor g K).support := by
    simpa using hz
  simpa [s] using (Set.Finite.mem_toFinset hsupport).2 hz'

/-- Helper for Proposition 4.1: a holomorphic kernel of the form `g(w) / (w - z)` realizes the
residue `g z` on any sufficiently small circle contained in the chosen domain. This is the local
circle model used after rewriting the logarithmic derivative into a principal-part form. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hD : Metric.closedBall z r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun w ↦ g w / (w - z)) z (g z) := by
  -- Use the chosen circle directly and apply the Cauchy integral formula to the differentiable
  -- numerator `g`.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall z r) := hg.mono hD
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul hz_ball

/-- Helper for Proposition 4.1: a spherewise identity `φ(w) = G(w) / (w - z)` on one closed ball
already packages the source proof's local kernel model into `LocalResidueCircle`. This avoids the
overly strong requirement that the auxiliary numerator `G` be differentiable on all of `U`. -/
lemma localResidueCircle_of_circle_kernel_model_closedBall
    {K U : Set ℂ} {φ G : ℂ → ℂ} {z c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hU : Metric.closedBall z r ⊆ U)
    (hG : DifferentiableOn ℂ G (Metric.closedBall z r))
    (hGc : G z = c)
    (hφ : ∀ w ∈ Metric.sphere z r, φ w = G w / (w - z)) :
    LocalResidueCircle K U φ z c := by
  refine ⟨r, hr, hK, hU, ?_⟩
  have hcongr :
      (∮ w in C(z, r), φ w) = ∮ w in C(z, r), G w / (w - z) := by
    -- Replace the source integrand by the explicit kernel model on the chosen residue circle.
    refine circleIntegral.integral_congr hr.le ?_
    intro w hw
    exact hφ w hw
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hkernel :
      (∮ w in C(z, r), G w / (w - z)) = (2 * Real.pi * Complex.I : ℂ) * G z := by
    -- Once the numerator is holomorphic on the closed ball, the Cauchy circle formula computes
    -- the local integral exactly.
    simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hG.circleIntegral_sub_inv_smul hz_ball
  -- Combine the circle-integral comparison with the Cauchy kernel evaluation and the center
  -- value `G z = c`.
  calc
    (∮ w in C(z, r), φ w) = ∮ w in C(z, r), G w / (w - z) := hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) * G z := hkernel
    _ = (2 * Real.pi * Complex.I : ℂ) * c := by rw [hGc]

/-- Helper for Proposition 4.1: at a meromorphic normal-form point of order `0`, the function is
analytic and nonvanishing, so its logarithmic derivative is differentiable there. This is the
pointwise normal-form bridge needed before the residue theorem can be applied off the divisor
support. -/
lemma differentiableAt_logDeriv_of_meromorphicNFAt_order_zero
    {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicNFAt g z)
    (horder : meromorphicOrderAt g z = 0) :
    DifferentiableAt ℂ (logDeriv g) z := by
  have hg_nonzero : g z ≠ 0 := (hg.meromorphicOrderAt_eq_zero_iff.1 horder)
  have hg_analytic : AnalyticAt ℂ g z := by
    -- Order `0` is in particular nonnegative, so the normal form is analytic at the center.
    exact hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq horder.symm)
  have hlog : AnalyticAt ℂ (logDeriv g) z := by
    -- Once the denominator stays nonzero, `logDeriv = deriv / g` is analytic.
    simpa [logDeriv] using (hg_analytic.deriv.div hg_analytic hg_nonzero)
  exact hlog.differentiableAt

/-- Helper for Proposition 4.1: on a meromorphic normal form, pointwise order `0` upgrades to
differentiability of the logarithmic derivative on the whole owner. This packages the pointwise
normal-form bridge in the set-level shape used by the residue theorem. -/
lemma differentiableOn_logDeriv_of_meromorphicNFOn_order_zero
    {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicNFOn g U)
    (horder : ∀ z ∈ U, meromorphicOrderAt g z = 0) :
    DifferentiableOn ℂ (logDeriv g) U := by
  intro z hz
  -- Reduce the set-level claim to the pointwise order-zero bridge for the normal form at `z`.
  exact
    (differentiableAt_logDeriv_of_meromorphicNFAt_order_zero
      (hg hz) (horder z hz)).differentiableWithinAt

/-- Helper for Proposition 4.1: for a meromorphic normal form, genuine neighborhood nonvanishing
forces meromorphic order `0`. This is the pointwise bridge from the boundary hypothesis
`∀ᶠ w in 𝓝 z, f w ≠ a` to the divisor-vanishing conclusion once the boundary integrand has been
replaced by a normal-form representative. -/
lemma meromorphicOrderAt_eq_zero_of_meromorphicNFAt_eventually_ne_zero
    {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicNFAt g z)
    (hne : ∀ᶠ w in 𝓝 z, g w ≠ 0) :
    meromorphicOrderAt g z = 0 := by
  have hgz : g z ≠ 0 := by
    -- A neighborhood statement in `𝓝 z` records the center point itself.
    exact hne.self_of_nhds
  -- In normal form, order `0` is equivalent to nonvanishing at the center.
  exact (hg.meromorphicOrderAt_eq_zero_iff).2 hgz

/-- Helper for Proposition 4.1: divisor value `0` means that the local meromorphic order is either
exactly `0` or infinite. This converts support-complement information into the order dichotomy
used to control the logarithmic derivative off the divisor support. -/
lemma meromorphicOrderAt_eq_zero_or_top_of_divisor_eq_zero
    {U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicOn g U)
    (hz : z ∈ U) (hdiv : MeromorphicOn.divisor g U z = 0) :
    meromorphicOrderAt g z = 0 ∨ meromorphicOrderAt g z = ⊤ := by
  -- Read the divisor through its defining `untop₀` value.
  rw [hg.divisor_apply hz] at hdiv
  simpa using (WithTop.untop₀_eq_zero).1 hdiv

/-- Helper for Proposition 4.1: for a meromorphic normal form, neighborhood nonvanishing already
forces the divisor to vanish. This is the divisor-side form of the previous order-zero criterion. -/
lemma divisor_eq_zero_of_meromorphicNFAt_eventually_ne_zero
    {U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicNFOn g U)
    (hz : z ∈ U) (hne : ∀ᶠ w in 𝓝 z, g w ≠ 0) :
    MeromorphicOn.divisor g U z = 0 := by
  -- Convert neighborhood nonvanishing to order `0`, then read back through the divisor formula.
  rw [hg.meromorphicOn.divisor_apply hz,
    meromorphicOrderAt_eq_zero_of_meromorphicNFAt_eventually_ne_zero (hg hz) hne]
  simp

/-- Helper for Proposition 4.1: for a meromorphic normal form, the logarithmic derivative is
differentiable whenever the local order is `0` or `⊤`. The `⊤` branch is harmless because the
function is locally zero, so the logarithmic derivative is locally the constant zero function. -/
lemma differentiableAt_logDeriv_of_meromorphicNFAt_order_zero_or_top
    {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicNFAt g z)
    (horder : meromorphicOrderAt g z = 0 ∨ meromorphicOrderAt g z = ⊤) :
    DifferentiableAt ℂ (logDeriv g) z := by
  rcases horder with hzero | htop
  · -- The order-zero branch is the ordinary analytic nonvanishing case.
    exact differentiableAt_logDeriv_of_meromorphicNFAt_order_zero hg hzero
  · have hzero_nhdsNE : g =ᶠ[𝓝[≠] z] fun _ : ℂ ↦ 0 := by
      -- Infinite order means the function vanishes on a punctured neighborhood.
      simpa [Filter.EventuallyEq, eq_comm] using
        (meromorphicOrderAt_eq_top_iff (f := g) (x := z)).1 htop
    have hzero_nhds : g =ᶠ[𝓝 z] fun _ : ℂ ↦ 0 := by
      -- Normal forms satisfy the local identity theorem, so punctured equality upgrades to
      -- ordinary neighborhood equality.
      exact
        (hg.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
          ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (0 : ℂ)) z).meromorphicNFAt)).1
          hzero_nhdsNE
    have hlog_zero : logDeriv g =ᶠ[𝓝 z] fun _ : ℂ ↦ 0 := by
      -- Once the function is locally zero, both the value and derivative vanish locally.
      filter_upwards [hzero_nhds, hzero_nhds.deriv] with w hw hderiv
      simp [logDeriv_apply, hw, hderiv]
    exact
      (differentiableAt_const (𝕜 := ℂ) (c := (0 : ℂ))).congr_of_eventuallyEq
        hlog_zero

/-- Helper for Proposition 4.1: if a meromorphic normal-form representative has vanishing divisor
throughout a set, then its logarithmic derivative is differentiable on that whole set. This is the
set-level punctured-holomorphic package needed on the boundary strip in the residue-theorem route.
-/
lemma differentiableOn_logDeriv_of_meromorphicNFOn_divisor_zero
    {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicNFOn g U)
    (hdiv : ∀ z ∈ U, MeromorphicOn.divisor g U z = 0) :
    DifferentiableOn ℂ (logDeriv g) U := by
  intro z hz
  have horder :
      meromorphicOrderAt g z = 0 ∨ meromorphicOrderAt g z = ⊤ :=
    meromorphicOrderAt_eq_zero_or_top_of_divisor_eq_zero hg.meromorphicOn hz (hdiv z hz)
  -- Reduce the set-level claim to the pointwise order `0/⊤` bridge.
  exact
    (differentiableAt_logDeriv_of_meromorphicNFAt_order_zero_or_top
      (hg hz) horder).differentiableWithinAt

/-- Helper for Proposition 4.1: at an analytic point of a meromorphic function on `U`, replacing
the function by its normal form on `U` does not change the logarithmic derivative. This isolates
the pointwise boundary comparison used in the source-faithful normal-form route. -/
lemma logDeriv_toMeromorphicNFOn_eq_of_analyticAt
    {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g U) {z : ℂ}
    (hz : z ∈ U) (hanalytic : AnalyticAt ℂ g z) :
    logDeriv g z = logDeriv (toMeromorphicNFOn g U) z := by
  have hEq_nf : toMeromorphicNFOn g U =ᶠ[𝓝 z] g := by
    -- First identify the owner normal form with the pointwise normal form, then collapse the
    -- pointwise normal form back to `g` at an analytic point.
    calc
      toMeromorphicNFOn g U =ᶠ[𝓝 z] toMeromorphicNFAt g z :=
        toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hg hz
      _ =ᶠ[𝓝 z] g := by
        simpa [toMeromorphicNFAt_eq_self.2 hanalytic.meromorphicNFAt]
          using (Filter.EventuallyEq.rfl : toMeromorphicNFAt g z =ᶠ[𝓝 z] toMeromorphicNFAt g z)
  have hEq : g =ᶠ[𝓝 z] toMeromorphicNFOn g U := hEq_nf.symm
  have hlog :
      logDeriv g =ᶠ[𝓝 z] logDeriv (toMeromorphicNFOn g U) := by
    -- Neighborhood equality transports both the derivative and the value in `logDeriv`.
    filter_upwards [hEq, hEq.deriv] with w hw hderiv
    simp [logDeriv_apply, hw, hderiv]
  exact hlog.eq_of_nhds

/-- Helper for Proposition 4.1: on a codiscrete subset of `U`, the logarithmic derivative of a
meromorphic function agrees with the logarithmic derivative of its normal-form representative on
`U`. This packages the boundary-integrand replacement needed before the residue theorem is
applied. -/
lemma logDeriv_toMeromorphicNFOn_eq_codiscrete
    {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g U) :
    logDeriv g =ᶠ[Filter.codiscreteWithin U] logDeriv (toMeromorphicNFOn g U) := by
  have hU : U ∈ Filter.codiscreteWithin U := by
    simp
  filter_upwards [hg.analyticAt_mem_codiscreteWithin, hU] with z hanalytic hz
  -- On the codiscrete set of analytic points, the pointwise normal-form comparison applies.
  exact logDeriv_toMeromorphicNFOn_eq_of_analyticAt hg hz hanalytic

/-- Helper for Proposition 4.1: once two parameter integrands agree on a codiscrete subset of the
unit interval, the corresponding curve integrals agree. This isolates the pathwise comparison step
needed to replace the raw logarithmic derivative by a normal-form representative along the
boundary. -/
lemma curveIntegral_eq_of_codiscrete_param_integrand
    {z₀ z₁ : ℂ} (γ : Path z₀ z₁) {φ ψ : ℂ → ℂ}
    (hEq :
      (fun t : ℝ ↦ (((φ dz) (γ.extend t)) (deriv γ.extend t)))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ (((ψ dz) (γ.extend t)) (deriv γ.extend t)))) :
    ∫ᶜ z in γ, ((φ dz) z) = ∫ᶜ z in γ, ((ψ dz) z) := by
  -- Rewrite both curve integrals as interval integrals of the parameterized integrands.
  rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv]
  -- Codiscrete equality on `[0,1]` is enough because interval integrals ignore a codiscrete
  -- subset of the parameter interval.
  exact intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_le_codiscreteWithin measurableSet_uIoc hEq)

/-- Helper for Proposition 4.1: on the half-open parameter interval `Set.uIoc (0,1]`, each
boundary component extension is injective because the only endpoint identifications allowed by
`simple_loops` involve the excluded parameter `0`. Therefore the preimage of a finite bad image
set is finite on `Set.uIoc (0,1]`. -/
lemma boundary_component_finite_preimage_uIoc
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) {E : Set ℂ} (hE : E.Finite) :
    (((Γ i).toPath.extend ⁻¹' E) ∩ Set.uIoc (0 : ℝ) 1).Finite := by
  let F : Set.uIoc (0 : ℝ) 1 → ℂ := fun t ↦ (Γ i).toPath.extend t
  have hF_inj : Function.Injective F := by
    intro s t hst
    have hsU : (s : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using s.2
    have htU : (t : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using t.2
    have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hsU.1.le, hsU.2⟩
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨htU.1.le, htU.2⟩
    have hPath :
        (Γ i).toPath ⟨(s : ℝ), hsI⟩ = (Γ i).toPath ⟨(t : ℝ), htI⟩ := by
      simpa [F, Path.extend_apply (γ := (Γ i).toPath) hsI,
        Path.extend_apply (γ := (Γ i).toPath) htI] using hst
    rcases hΓ.simple_loops i hPath with hEq | hEnds | hEnds
    · cases s
      cases t
      cases hEq
      rfl
    · have hs0 : (s : ℝ) = 0 := by
        exact congrArg Subtype.val (congrArg Prod.fst hEnds)
      exfalso
      linarith [hsU.1, hs0]
    · have ht0 : (t : ℝ) = 0 := by
        exact congrArg Subtype.val (congrArg Prod.snd hEnds)
      exfalso
      linarith [htU.1, ht0]
  have hSubtype :
      {t : Set.uIoc (0 : ℝ) 1 | F t ∈ E}.Finite := by
    exact hE.preimage hF_inj.injOn
  have hImage :
      (Subtype.val '' {t : Set.uIoc (0 : ℝ) 1 | F t ∈ E}).Finite := by
    exact hSubtype.image Subtype.val
  -- Forgetting the subtype identifies the finite subtype preimage with the desired real-parameter
  -- preimage intersected with `Set.uIoc (0,1]`.
  convert hImage using 1
  ext t
  constructor
  · intro ht
    refine ⟨⟨t, ht.2⟩, ?_, rfl⟩
    simpa [F] using ht.1
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa [F] using ht, t.2⟩

/-- Helper for Proposition 4.1: a finite divisor-support owner inside `interior K` admits a
positive closed-ball radius around each chosen point that still lies in `interior K` and avoids
every other support point. This is the correct separation input for the source proof before the
local residue circle is constructed. -/
lemma exists_separating_radius_closedBall_subset_interior
    {K : Set ℂ} {s : Finset ℂ} {z : ℂ} (hz : z ∈ s)
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    ∃ r > 0,
      Metric.closedBall z r ⊆ interior K ∧
        ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r := by
  have hzK : z ∈ interior K := hsK (by simpa using hz)
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzK) with ⟨R, hR, hRsub⟩
  let t : Set ℂ := (↑s : Set ℂ) \ ({z} : Set ℂ)
  have htfinite : t.Finite := s.finite_toSet.subset (by
    intro w hw
    exact hw.1)
  have htclosed : IsClosed t := htfinite.isClosed
  have hz_not_closure_t : z ∉ closure t := by
    simp [t, htclosed.closure_eq]
  obtain ⟨ε, hε, hεlt⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure hz_not_closure_t
  let r : ℝ := min (R / 2) ε
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hR) hε
  have hrR : r < R := by
    have hhalf : R / 2 < R := by linarith
    exact lt_of_le_of_lt (by exact min_le_left _ _) hhalf
  have hrε : r ≤ ε := by
    dsimp [r]
    exact min_le_right _ _
  refine ⟨r, hr, ?_, ?_⟩
  · -- The interior membership gives a metric ball inside `interior K`; shrink to a closed ball.
    exact (Metric.closedBall_subset_ball hrR).trans hRsub
  · -- Any other support point would contradict the positive `infEDist` separation of `t`.
    intro w hw hwz hwball
    have hwt : w ∈ t := by
      refine ⟨by simpa using hw, ?_⟩
      simpa [Set.mem_singleton_iff] using hwz
    have hInf : Metric.infEDist z t ≤ edist z w := Metric.infEDist_le_edist_of_mem hwt
    have hdist : dist z w ≤ ε := by
      have hdist_r : dist z w ≤ r := by
        simpa [Metric.mem_closedBall, dist_comm] using hwball
      exact hdist_r.trans hrε
    have hedist : edist z w ≤ ENNReal.ofReal ε := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hdist
    exact (not_lt_of_ge hedist) (lt_of_lt_of_le hεlt hInf)

/-- Helper for Proposition 4.1: once the source proof has chosen a circle radius inside `D` that
avoids the rest of the finite divisor support, the global punctured differentiability off that
support restricts to the small punctured ball around `z`. -/
lemma differentiableOn_punctured_ball_of_finite_support_separation
    {D : Set ℂ} {s : Finset ℂ} {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hD : Metric.closedBall z r ⊆ D)
    (hsep : ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r)
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    DifferentiableOn ℂ f (Metric.ball z r \ ({z} : Set ℂ)) := by
  -- Restrict the global punctured differentiability to the chosen small punctured ball.
  refine hhol.mono ?_
  intro w hw
  refine ⟨hD (Metric.ball_subset_closedBall hw.1), ?_⟩
  intro hwS
  by_cases hwz : w = z
  · exact hw.2 hwz
  · exact hsep w hwS hwz (Metric.ball_subset_closedBall hw.1)

/-- Helper for Proposition 4.1: if the divisor already vanishes on `frontier K`, then every point
of its finite support lies in `interior K`. This isolates the geometric step needed before the
oriented-boundary residue theorem can be applied. -/
lemma divisor_support_subset_interior_of_frontier_zero
    {K : Set ℂ} {g : ℂ → ℂ} (hK : IsCompact K)
    (hfrontier_zero : ∀ z ∈ frontier K, MeromorphicOn.divisor g K z = 0) :
    let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
    (↑s : Set ℂ) ⊆ interior K := by
  classical
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
  change (↑s : Set ℂ) ⊆ interior K
  intro z hz
  have hz_support : z ∈ (MeromorphicOn.divisor g K).support := by
    simpa [s] using hz
  have hzK : z ∈ K := by
    -- Outside `K`, the divisor is definitionally zero, so support points must lie in `K`.
    by_contra hzK
    rw [Function.mem_support] at hz_support
    simp [hzK] at hz_support
  by_contra hzInterior
  -- For a compact owner, points of `K` outside `interior K` are exactly boundary points.
  have hz_frontier : z ∈ frontier K := by
    exact (mem_frontier_iff_notMem_interior hzK).2 hzInterior
  have hz_zero : MeromorphicOn.divisor g K z = 0 := hfrontier_zero z hz_frontier
  rw [Function.mem_support] at hz_support
  exact hz_support hz_zero

/-- Helper for Proposition 4.1: if a finite support set lies in `interior K`, then every boundary
path of an oriented boundary of `K` is disjoint from that support. This is the exact boundary
separation hypothesis required by the imported oriented-boundary residue theorem. -/
lemma boundary_path_disjoint_of_finset_subset_interior
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {s : Finset ℂ}
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    ∀ i, Disjoint (Set.range ⇑(Γ i).toPath) (↑s : Set ℂ) := by
  intro i
  refine Set.disjoint_left.2 ?_
  intro z hzRange hzS
  have hzFrontier : z ∈ frontier K := hΓ.range_toPath_subset_frontier i hzRange
  have hzInterior : z ∈ interior K := hsK hzS
  exact (Set.disjoint_left.1 disjoint_interior_frontier hzInterior hzFrontier)

/-- Helper for Proposition 4.1: once the divisor vanishes on `frontier K`, the boundary paths are
disjoint from the divisor support finset. This packages the previous interior-support lemma in the
exact form required by `orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue`. -/
lemma boundary_path_disjoint_of_divisor_frontier_zero
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {g : ℂ → ℂ}
    (hfrontier_zero : ∀ z ∈ frontier K, MeromorphicOn.divisor g K z = 0) :
    let s : Finset ℂ :=
      (divisor_support_finite_of_isCompact (K := K) (g := g) hΓ.isCompact).toFinset
    ∀ i,
      Disjoint
        (Set.range ⇑(Γ i).toPath)
        (↑s : Set ℂ) := by
  classical
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hΓ.isCompact).toFinset
  change ∀ i, Disjoint (Set.range ⇑(Γ i).toPath) (↑s : Set ℂ)
  -- First move the divisor support into `interior K`, then reuse the generic boundary-separation
  -- lemma for finite subsets of `interior K`.
  have hsK :
      (↑s : Set ℂ) ⊆ interior K := by
    simpa [s] using divisor_support_subset_interior_of_frontier_zero
      (K := K) (g := g) hΓ.isCompact hfrontier_zero
  simpa using
    (boundary_path_disjoint_of_finset_subset_interior
      (K := K) (Γ := Γ) hΓ (s := s) hsK)

/-- Helper for Proposition 4.1: a compact set `K ⊆ D` admits an open owner `U` whose divisor
support agrees with the divisor support on `K`. Concretely, `U` is obtained by taking a compact
metric collar of `K` inside `D` and deleting the finitely many collar support points that do not
already lie in the divisor support finset on `K`. -/
lemma exists_open_owner_with_divisor_zero_off_support
    {D K : Set ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g D) (hD_open : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
    ∃ U, IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
      ∀ z, z ∈ U → z ∉ (↑s : Set ℂ) → MeromorphicOn.divisor g U z = 0 := by
  classical
  let hsupportK :=
    divisor_support_finite_of_isCompact (K := K) (g := g) hK
  let s : Finset ℂ := hsupportK.toFinset
  -- Choose a compact metric collar of `K` still contained in `D`.
  obtain ⟨ε, hε, hεD⟩ := hK.exists_cthickening_subset_open hD_open hKD
  let L : Set ℂ := Metric.cthickening ε K
  let V : Set ℂ := Metric.thickening ε K
  have hLcompact : IsCompact L := by
    simpa [L] using hK.cthickening
  have hKL : K ⊆ L := by
    simpa [L] using Metric.self_subset_cthickening K
  have hKV : K ⊆ V := by
    simpa [V] using Metric.self_subset_thickening hε K
  have hVL : V ⊆ L := by
    simpa [V, L] using Metric.thickening_subset_cthickening ε K
  have hLD : L ⊆ D := by
    simpa [L] using hεD
  have hgL : MeromorphicOn g L := hg.mono_set hLD
  let hsupportL :=
    divisor_support_finite_of_isCompact (K := L) (g := g) hLcompact
  let t : Finset ℂ := hsupportL.toFinset \ s
  let U : Set ℂ := V \ (↑t : Set ℂ)
  have hU_open : IsOpen U := by
    -- The thickened collar is open, and removing a finite set preserves openness.
    simpa [U, V] using IsOpen.sdiff Metric.isOpen_thickening t.finite_toSet.isClosed
  have hU_sub_L : U ⊆ L := by
    -- The deleted open owner still sits inside the compact collar `L`.
    intro z hz
    exact hVL hz.1
  refine ⟨U, hU_open, ?_, ?_, ?_⟩
  · -- Points of `K` survive the finite deletion because every collar support point of `K`
    -- already belongs to the original divisor support finset `s`.
    intro z hzK
    refine ⟨hKV hzK, ?_⟩
    intro hzT
    have hz_not_s : z ∉ s := (Finset.mem_sdiff.mp hzT).2
    have hz_not_supportK : z ∉ (MeromorphicOn.divisor g K).support := by
      intro hz_supportK
      exact hz_not_s ((Set.Finite.mem_toFinset hsupportK).2 hz_supportK)
    have hdivK : MeromorphicOn.divisor g K z = 0 := by
      rw [Function.mem_support] at hz_not_supportK
      exact not_ne_iff.mp hz_not_supportK
    have hrestrictLK :=
      congrArg (fun F : Function.locallyFinsuppWithin K ℤ ↦ F z)
        (MeromorphicOn.divisor_restrict (U := L) (V := K) hgL hKL)
    have hdivL : MeromorphicOn.divisor g L z = 0 := by
      -- Restricting the collar divisor to `K` shows that collar support points of `K` are exactly
      -- the support points already recorded in `s`.
      have hdivLK :
          MeromorphicOn.divisor g L z = MeromorphicOn.divisor g K z := by
        simpa [Function.locallyFinsuppWithin.restrict_apply, hzK] using hrestrictLK
      rw [hdivLK, hdivK]
    have hz_supportL : z ∈ (MeromorphicOn.divisor g L).support := by
      exact (Set.Finite.mem_toFinset hsupportL).1 ((Finset.mem_sdiff.mp hzT).1)
    rw [Function.mem_support] at hz_supportL
    exact hz_supportL hdivL
  · -- The owner `U` stays inside the original open domain because the whole collar does.
    intro z hzU
    exact hLD (hU_sub_L hzU)
  · -- Outside the original support finset `s`, the deleted collar removes all remaining divisor
    -- support points, so the divisor on `U` vanishes identically.
    intro z hzU hz_not_s
    have hz_not_t : z ∉ t := hzU.2
    have hz_not_supportL : z ∉ (MeromorphicOn.divisor g L).support := by
      intro hz_supportL
      have hz_supportL_fin : z ∈ hsupportL.toFinset :=
        (Set.Finite.mem_toFinset hsupportL).2 hz_supportL
      exact hz_not_t (Finset.mem_sdiff.mpr ⟨hz_supportL_fin, hz_not_s⟩)
    have hdivL : MeromorphicOn.divisor g L z = 0 := by
      rw [Function.mem_support] at hz_not_supportL
      exact not_ne_iff.mp hz_not_supportL
    have hrestrictLU :=
      congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
        (MeromorphicOn.divisor_restrict (U := L) (V := U) hgL hU_sub_L)
    -- Restrict the vanishing collar divisor from `L` to the open owner `U`.
    simpa [Function.locallyFinsuppWithin.restrict_apply, hzU, hdivL] using hrestrictLU.symm

/-- Helper for Proposition 4.1: after passing to a normal-form representative on an open owner
`U`, the divisor read on `U` agrees with the original divisor read on the compact owner `K`.
This is the owner-change bridge needed in the local residue computation. -/
lemma divisor_toMeromorphicNFOn_eq_divisor_on_compact_owner
    {D K U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g D)
    (hKU : K ⊆ U) (hUD : U ⊆ D) {z : ℂ} (hz : z ∈ K) :
    MeromorphicOn.divisor (toMeromorphicNFOn g U) U z =
      MeromorphicOn.divisor g K z := by
  have hgU : MeromorphicOn g U := hg.mono_set hUD
  have hrestrict :=
    congrArg (fun F : Function.locallyFinsuppWithin K ℤ ↦ F z)
      (MeromorphicOn.divisor_restrict (U := U) (V := K) hgU hKU)
  -- First remove the normal-form replacement on `U`, then restrict the divisor from `U` to `K`.
  calc
    MeromorphicOn.divisor (toMeromorphicNFOn g U) U z
        = MeromorphicOn.divisor g U z := by
            simpa using congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
              hgU.divisor_of_toMeromorphicNFOn
    _ = MeromorphicOn.divisor g K z := by
      simpa [Function.locallyFinsuppWithin.restrict_apply, hz] using hrestrict

/-- Helper for Proposition 4.1: at a support point of the divisor on `K`, the meromorphic order
of the normal-form owner `toMeromorphicNFOn g U` is exactly the finite divisor value read on `K`.
This isolates the `WithTop` conversion that feeds the local principal-part model. -/
lemma meromorphicOrderAt_toMeromorphicNFOn_eq_of_divisor_ne_zero
    {D K U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicOn g D)
    (hKU : K ⊆ U) (hUD : U ⊆ D) (hzK : z ∈ K) (hzU : z ∈ U)
    (hdiv_ne : MeromorphicOn.divisor g K z ≠ 0) :
    meromorphicOrderAt (toMeromorphicNFOn g U) z =
      (MeromorphicOn.divisor g K z : WithTop ℤ) := by
  let gNF : ℂ → ℂ := toMeromorphicNFOn g U
  have hgNF : MeromorphicNFOn gNF U := by
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g U
  have hdivisor :
      MeromorphicOn.divisor gNF U z = MeromorphicOn.divisor g K z := by
    -- First read the normal-form divisor on `U`, then restrict back to the compact owner `K`.
    simpa [gNF] using
      divisor_toMeromorphicNFOn_eq_divisor_on_compact_owner
        (D := D) (K := K) (U := U) (g := g) hg hKU hUD hzK
  have horder_untop :
      (meromorphicOrderAt gNF z).untop₀ = MeromorphicOn.divisor g K z := by
    -- The divisor owner on `U` is the `untop₀` of the local meromorphic order.
    calc
      (meromorphicOrderAt gNF z).untop₀ = MeromorphicOn.divisor gNF U z := by
        rw [hgNF.meromorphicOn.divisor_apply hzU]
      _ = MeromorphicOn.divisor g K z := hdivisor
  have hnot_top : meromorphicOrderAt gNF z ≠ ⊤ := by
    intro htop
    have hzero : MeromorphicOn.divisor g K z = 0 := by
      rw [← horder_untop, htop]
      simp
    exact hdiv_ne hzero
  -- Once the order is known to be finite, `WithTop.coe_untop₀_of_ne_top` recovers the exact
  -- integer value from the divisor.
  calc
    meromorphicOrderAt gNF z = ↑((meromorphicOrderAt gNF z).untop₀) := by
      symm
      exact WithTop.coe_untop₀_of_ne_top hnot_top
    _ = (MeromorphicOn.divisor g K z : WithTop ℤ) := by
      exact congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) horder_untop

/-- Helper for Proposition 4.1: a finite-order logarithmic derivative admits the explicit source
circle model `G(w) / (w - z)` on one closed ball contained in both owners. This is the direct
principal-part reduction from the source proof. -/
lemma exists_logDeriv_circle_kernel_model_of_order
    {K U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {k : ℤ}
    (hzK : z ∈ interior K) (hzU : z ∈ U) (hU_open : IsOpen U)
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = k) :
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.closedBall z r ⊆ interior K ∧
        Metric.closedBall z r ⊆ U ∧
          DifferentiableOn ℂ G (Metric.closedBall z r) ∧
            G z = (k : ℂ) ∧
              ∀ w ∈ Metric.sphere z r, logDeriv g w = G w / (w - z) := by
  obtain ⟨h, hh_analytic, hlog⟩ :=
    logDeriv_eventuallyEq_order_principalPart_add_analytic hg horder
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzK) with ⟨rK, hrK, hballK⟩
  rcases Metric.mem_nhds_iff.1 (hU_open.mem_nhds hzU) with ⟨rU, hrU, hballU⟩
  obtain ⟨rH, hrH, hh_ball⟩ := hh_analytic.exists_ball_analyticOnNhd
  have hlog_nhds :
      ∀ᶠ w in 𝓝 z, w ≠ z → logDeriv g w = (k : ℂ) / (w - z) + h w := by
    simpa [Filter.EventuallyEq, eventually_nhdsWithin_iff] using hlog
  rcases Metric.mem_nhds_iff.1 hlog_nhds with ⟨rLog, hrLog, hballLog⟩
  let r : ℝ := min (rK / 2) (min (rU / 2) (min (rH / 2) (rLog / 2)))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hrK) (lt_min (half_pos hrU) (lt_min (half_pos hrH) (half_pos hrLog)))
  have hr_le_K : r ≤ rK / 2 := by
    dsimp [r]
    exact min_le_left _ _
  have hr_le_U : r ≤ rU / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_H : r ≤ rH / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_Log : r ≤ rLog / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrK_lt : r < rK := lt_of_le_of_lt hr_le_K (by linarith)
  have hrU_lt : r < rU := lt_of_le_of_lt hr_le_U (by linarith)
  have hrH_lt : r < rH := lt_of_le_of_lt hr_le_H (by linarith)
  have hrLog_lt : r < rLog := lt_of_le_of_lt hr_le_Log (by linarith)
  have hclosedK : Metric.closedBall z r ⊆ interior K := by
    exact (Metric.closedBall_subset_ball hrK_lt).trans hballK
  have hclosedU : Metric.closedBall z r ⊆ U := by
    exact (Metric.closedBall_subset_ball hrU_lt).trans hballU
  have hh_diff :
      DifferentiableOn ℂ h (Metric.closedBall z r) := by
    -- Shrink the analytic remainder to the chosen closed ball before converting to
    -- differentiability.
    exact (hh_ball.mono (Metric.closedBall_subset_ball hrH_lt)).differentiableOn
  let G : ℂ → ℂ := fun w ↦ (k : ℂ) + (w - z) * h w
  have hG_diff : DifferentiableOn ℂ G (Metric.closedBall z r) := by
    intro w hw
    -- The source numerator `G` is the sum of a constant and a product of holomorphic factors.
    have hsub :
        DifferentiableWithinAt ℂ (fun u : ℂ ↦ u - z) (Metric.closedBall z r) w := by
      change DifferentiableWithinAt ℂ ((fun u : ℂ ↦ u) - fun _ : ℂ ↦ z)
        (Metric.closedBall z r) w
      exact
        (((differentiableAt_id : DifferentiableAt ℂ (fun u : ℂ ↦ u) w)).sub
          (differentiableAt_const z)).differentiableWithinAt
    simpa [G] using ((hsub.mul (hh_diff w hw)).const_add (k : ℂ))
  have hG_center : G z = (k : ℂ) := by
    simp [G]
  refine ⟨r, hr, G, hclosedK, hclosedU, hG_diff, hG_center, ?_⟩
  intro w hwSphere
  have hw_closed : w ∈ Metric.closedBall z r := Metric.sphere_subset_closedBall hwSphere
  have hw_ballLog : w ∈ Metric.ball z rLog := by
    exact (Metric.closedBall_subset_ball hrLog_lt) hw_closed
  have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hwSphere hr.ne'
  have hlog_w :
      logDeriv g w = (k : ℂ) / (w - z) + h w := hballLog hw_ballLog hw_ne
  have hsub_ne : w - z ≠ 0 := sub_ne_zero.mpr hw_ne
  -- On the chosen circle, the punctured-neighborhood principal part becomes the explicit kernel
  -- model with numerator `G`.
  calc
    logDeriv g w = (k : ℂ) / (w - z) + h w := hlog_w
    _ = G w / (w - z) := by
      have hrewrite :
          (k : ℂ) / (w - z) + h w =
            ((k : ℂ) + (w - z) * h w) / (w - z) := by
        field_simp [hsub_ne]
      simpa [G] using hrewrite

/-- Helper for Proposition 4.1: every support point of the divisor on `K` yields a local residue
circle for the logarithmic derivative of the normal-form owner on `U`. This is the exact local
input needed by the frozen oriented-boundary residue theorem. -/
lemma localResidueCircle_logDeriv_toMeromorphicNFOn_at_support
    {D K U : Set ℂ} {g : ℂ → ℂ} {s : Finset ℂ} (hg : MeromorphicOn g D)
    (hKU : K ⊆ U) (hUD : U ⊆ D) (hU_open : IsOpen U)
    (hsK : (↑s : Set ℂ) ⊆ interior K)
    (hsupport : ∀ z, z ∈ s ↔ z ∈ (MeromorphicOn.divisor g K).support) :
    ∀ z ∈ s,
      LocalResidueCircle K U (logDeriv (toMeromorphicNFOn g U))
        z ((MeromorphicOn.divisor g K z : ℂ)) := by
  intro z hzS
  have hzInterior : z ∈ interior K := hsK (by simpa using hzS)
  have hzK : z ∈ K := interior_subset hzInterior
  have hzU : z ∈ U := hKU hzK
  have hz_support : z ∈ (MeromorphicOn.divisor g K).support := (hsupport z).1 hzS
  have hdiv_ne : MeromorphicOn.divisor g K z ≠ 0 := by
    simpa [Function.mem_support] using hz_support
  let gNF : ℂ → ℂ := toMeromorphicNFOn g U
  have hgNF : MeromorphicNFOn gNF U := by
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g U
  have horder :
      meromorphicOrderAt gNF z = (MeromorphicOn.divisor g K z : WithTop ℤ) := by
    -- Route correction: previous attempts bundled the finite-order extraction with the radius
    -- construction. The order is now identified first, directly from the divisor owner on `K`.
    simpa [gNF] using
      meromorphicOrderAt_toMeromorphicNFOn_eq_of_divisor_ne_zero
        (D := D) (K := K) (U := U) (g := g) hg hKU hUD hzK hzU hdiv_ne
  have hgNF_at : MeromorphicAt gNF z := (hgNF hzU).meromorphicAt
  rcases exists_logDeriv_circle_kernel_model_of_order
      (K := K) (U := U) (g := gNF) (z := z)
      (k := MeromorphicOn.divisor g K z)
      hzInterior hzU hU_open hgNF_at horder with
    ⟨r, hr, G, hballK, hballU, hG_diff, hG_center, hkernel⟩
  -- The explicit kernel model on the chosen closed ball is exactly the `LocalResidueCircle`
  -- witness demanded by the oriented-boundary residue theorem.
  exact
    localResidueCircle_of_circle_kernel_model_closedBall
      (K := K) (U := U) (φ := logDeriv gNF) (G := G) (z := z)
      (c := (MeromorphicOn.divisor g K z : ℂ)) hr hballK hballU hG_diff hG_center hkernel

/-- Helper for Proposition 4.1: codiscrete equality on an open owner `U` transfers to equality of
each actual oriented-boundary component integral once the whole path image lies in `U`. This is
the pathwise owner-replacement step in the source-faithful normal-form route. -/
lemma curveIntegral_eq_of_codiscrete_boundary_component
    {ι : Type u} [Fintype ι] {K U : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) {φ ψ : ℂ → ℂ}
    (hEq : φ =ᶠ[Filter.codiscreteWithin U] ψ)
    (hRange : Set.range ((Γ i).toPath) ⊆ U) :
    ∫ᶜ z in (Γ i).toPath, ((φ dz) z) = ∫ᶜ z in (Γ i).toPath, ((ψ dz) z) := by
  let γ := (Γ i).toPath
  let A : Set ℂ := {z | φ z = ψ z}
  have hA_U : A ∈ Filter.codiscreteWithin U := by
    simpa [A, Filter.EventuallyEq] using hEq
  have hA_range : A ∈ Filter.codiscreteWithin (Set.range γ) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA_U ⊢
    intro z hzRange
    have hzU : z ∈ U := hRange (by simpa [γ] using hzRange)
    -- Restrict the codiscrete equality from the ambient owner `U` to the compact path image.
    refine Filter.mem_of_superset (hA_U z hzU) ?_
    intro w hw
    rcases hw with hwA | hwUc
    · exact Or.inl hwA
    · exact Or.inr fun hwRange ↦ hwUc (hRange (by simpa [γ] using hwRange))
  have hBadImage : (Set.range γ \ A).Finite := by
    -- Compactness of the path image turns codiscrete equality into finiteness of the bad image.
    exact (isCompact_range γ.continuous).finite_diff_of_mem_codiscreteWithin hA_range
  let B : Set ℝ := (γ.extend ⁻¹' (Set.range γ \ A)) ∩ Set.uIoc (0 : ℝ) 1
  have hBadParam : B.Finite := by
    -- On `Set.uIoc (0,1]`, the boundary component parametrization is injective.
    simpa [B, γ] using
      boundary_component_finite_preimage_uIoc
        (K := K) (Γ := Γ) hΓ i hBadImage
  have hParamEq :
      (fun t : ℝ ↦ (((φ dz) (γ.extend t)) (deriv γ.extend t)))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ (((ψ dz) (γ.extend t)) (deriv γ.extend t))) := by
    change
      {t : ℝ |
          (((φ dz) (γ.extend t)) (deriv γ.extend t)) =
            (((ψ dz) (γ.extend t)) (deriv γ.extend t))} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    have hBadParam_cod :
        ({t : ℝ | t ∉ B} : Set ℝ) ∈
          Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1) :=
      compl_finite_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) 1) hBadParam
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hBadParam_cod
    intro t ht
    -- Outside the finite bad parameter set, either we are off the interval owner or the two
    -- integrands agree because the path value avoids the finite bad image.
    refine Filter.mem_of_superset (hBadParam_cod t ht) ?_
    intro u hu
    rcases hu with huNotB | huOutside
    · by_cases huI : u ∈ Set.uIoc (0 : ℝ) 1
      · have huNotPre : u ∉ γ.extend ⁻¹' (Set.range γ \ A) := by
          intro huPre
          exact huNotB ⟨huPre, huI⟩
        have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa using huI
        have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt huIoc.1, huIoc.2⟩
        have huRange : γ.extend u ∈ Set.range γ := by
          refine ⟨⟨u, huIcc⟩, ?_⟩
          simpa [γ, Path.extend_apply (γ := γ) huIcc]
        have huA : γ.extend u ∈ A := by
          by_contra huA
          exact huNotPre ⟨huRange, huA⟩
        have huEq : φ (γ.extend u) = ψ (γ.extend u) := by
          simpa [A] using huA
        have huParam :
            u ∈
              {t : ℝ |
                (((φ dz) (γ.extend t)) (deriv γ.extend t)) =
                  (((ψ dz) (γ.extend t)) (deriv γ.extend t))} := by
          simp [huEq]
        exact Or.inl huParam
      · exact Or.inr huI
    · exact Or.inr huOutside
  -- Once the parameter integrands agree codiscretely on `Set.uIoc (0,1]`, the two component
  -- curve integrals are equal.
  simpa [γ] using curveIntegral_eq_of_codiscrete_param_integrand γ hParamEq

/-- Proposition 4.1: argument principle on an oriented boundary. For a meromorphic function `f` on
an open set `D`, if `Γ` is the oriented boundary of a compact set `K ⊆ D`, and if the meromorphic
divisor of `f - a` has no support on `frontier K` (the germ-stable formal version of the source
condition that `f` has no poles on `Γ` and does not take the value `a` there), then the normalized
contour integral of the logarithmic derivative of `z ↦ f z - a` along `Γ` equals the signed sum of
the orders of the zeros and poles of `f - a` inside `K`, encoded by the divisor of
`z ↦ f z - a` on `K`. -/
theorem argument_principle_on_oriented_boundary
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f D) (hD_open : IsOpen D) (hKD : K ⊆ D)
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hboundary_divisor_zero :
      ∀ z ∈ frontier K, MeromorphicOn.divisor (fun w ↦ f w - a) K z = 0) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (fun z ↦ f z - a) dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) =
      ∑ᶠ z, (MeromorphicOn.divisor (fun z ↦ f z - a) K z : ℂ) := by
  let g : ℂ → ℂ := fun z ↦ f z - a
  have hg : MeromorphicOn g D := by
    intro z hz
    simpa [g] using (hf z hz).sub (MeromorphicAt.const a z)
  have hK_compact : IsCompact K := hΓ.isCompact
  have hsupport_finite :
      (MeromorphicOn.divisor g K).support.Finite :=
    divisor_support_finite_of_isCompact (K := K) (g := g) hK_compact
  let s : Finset ℂ := hsupport_finite.toFinset
  have hboundary_disjoint :
      ∀ i,
        Disjoint
          (Set.range ⇑(Γ i).toPath)
          (↑s : Set ℂ) := by
    simpa [s, g] using
      boundary_path_disjoint_of_divisor_frontier_zero
        (K := K) (Γ := Γ) hΓ (g := g) hboundary_divisor_zero
  have hsupport_sum :
      Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ)) =
        ∑ᶠ z, (MeromorphicOn.divisor g K z : ℂ) := by
    -- This is the last algebraic rewrite once the residue theorem returns a finite support sum.
    simpa [s] using finset_sum_divisor_eq_finsum_support (K := K) (g := g) hK_compact
  have hsK :
      (↑s : Set ℂ) ⊆ interior K := by
    -- The boundary divisor hypothesis moves the whole support finset strictly inside `K`.
    simpa [s, g] using
      divisor_support_subset_interior_of_frontier_zero
        (K := K) (g := g) hK_compact hboundary_divisor_zero
  obtain ⟨U, hU_open, hKU, hUD, hdivU_zero⟩ :=
    exists_open_owner_with_divisor_zero_off_support
      (D := D) (K := K) (g := g) hg hD_open hK_compact hKD
  let gNF : ℂ → ℂ := toMeromorphicNFOn g U
  have hgU : MeromorphicOn g U := hg.mono_set hUD
  have hgNF : MeromorphicNFOn gNF U := by
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g U
  have hhol_nf : DifferentiableOn ℂ (logDeriv gNF) (U \ (↑s : Set ℂ)) := by
    intro z hz
    have hdiv_nf : MeromorphicOn.divisor gNF U z = 0 := by
      -- Off the support finset `s`, the normal-form divisor vanishes on the open owner `U`.
      have hdiv_eq :=
        congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
          hgU.divisor_of_toMeromorphicNFOn
      simpa [gNF] using hdiv_eq.trans (by simp [hdivU_zero z hz.1 hz.2])
    have horder_zero_or_top :
        meromorphicOrderAt gNF z = 0 ∨ meromorphicOrderAt gNF z = ⊤ :=
      meromorphicOrderAt_eq_zero_or_top_of_divisor_eq_zero
        hgNF.meromorphicOn hz.1 hdiv_nf
    -- The order `0/⊤` dichotomy is exactly the differentiability criterion for `logDeriv` on a
    -- meromorphic normal form.
    exact
      (differentiableAt_logDeriv_of_meromorphicNFAt_order_zero_or_top
        (hgNF hz.1) horder_zero_or_top).differentiableWithinAt
  have hdivisor_nf_on_K :
      ∀ z, z ∈ K → MeromorphicOn.divisor gNF U z = MeromorphicOn.divisor g K z := by
    intro z hzK
    -- This is the owner-change bridge from the open collar owner back to the compact source owner.
    simpa [gNF] using
      divisor_toMeromorphicNFOn_eq_divisor_on_compact_owner
        (D := D) (K := K) (U := U) (g := g) hg hKU hUD hzK
  have hboundary_transfer :
      ∀ i,
        ∫ᶜ z in (Γ i).toPath, ((logDeriv g dz) z) =
          ∫ᶜ z in (Γ i).toPath, ((logDeriv gNF dz) z) := by
    intro i
    have hRangeU : Set.range ((Γ i).toPath) ⊆ U := by
      intro z hz
      exact hKU (hK_compact.isClosed.frontier_subset (hΓ.range_toPath_subset_frontier i hz))
    -- Replace each boundary component integral by the corresponding normal-form integral on `U`.
    simpa [gNF] using
      curveIntegral_eq_of_codiscrete_boundary_component
        (K := K) (U := U) (Γ := Γ) hΓ i
        (φ := logDeriv g) (ψ := logDeriv gNF)
        (logDeriv_toMeromorphicNFOn_eq_codiscrete (U := U) hgU) hRangeU
  have hboundary_sum_transfer :
      ∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv g dz) z) =
        ∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv gNF dz) z) := by
    -- Sum the componentwise boundary-integral replacements over the oriented boundary family.
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hboundary_transfer i
  have hsupport_iff :
      ∀ z, z ∈ s ↔ z ∈ (MeromorphicOn.divisor g K).support := by
    intro z
    simpa [s] using (Set.Finite.mem_toFinset hsupport_finite)
  have hlocal_residue :
      ∀ z ∈ s, LocalResidueCircle K U (logDeriv gNF) z ((MeromorphicOn.divisor g K z : ℂ)) := by
    -- Route correction: with the order-extraction and closed-ball kernel lemmas separated, the
    -- source proof closes by packaging each support point into one local residue circle.
    simpa [gNF] using
      localResidueCircle_logDeriv_toMeromorphicNFOn_at_support
        (D := D) (K := K) (U := U) (g := g) (s := s)
        hg hKU hUD hU_open hsK hsupport_iff
  have hboundary_nf :
      ∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv gNF dz) z) =
        (2 * Real.pi * Complex.I : ℂ) *
          Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ)) := by
    -- Apply the frozen oriented-boundary residue theorem to the normal-form logarithmic
    -- derivative on the open owner `U`.
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (s := s) (residue := fun z ↦ (MeromorphicOn.divisor g K z : ℂ))
        hΓ hKU hU_open hboundary_disjoint hhol_nf hlocal_residue
  calc
    (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv g dz) z)) /
        (2 * Real.pi * Complex.I : ℂ)
        =
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv gNF dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) := by
          rw [hboundary_sum_transfer]
    _ =
        ((2 * Real.pi * Complex.I : ℂ) *
            Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ))) /
          (2 * Real.pi * Complex.I : ℂ) := by
            rw [hboundary_nf]
    _ = Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ)) := by
      simpa [mul_comm] using
        (mul_div_cancel_left₀
          (Finset.sum s (fun z ↦ (MeromorphicOn.divisor g K z : ℂ)))
          Complex.two_pi_I_ne_zero)
    _ = ∑ᶠ z, (MeromorphicOn.divisor g K z : ℂ) := hsupport_sum
