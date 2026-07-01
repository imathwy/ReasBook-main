import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

/-
This remark is `bridge/view`: its source-facing logarithmic-derivative consequences are expressed
using the core meromorphic owner `meromorphicOrderAt`, with normal-form input from
`meromorphicOrderAt_eq_int_iff` and the analytic simple-zero owner
`AnalyticAt.tendsto_mul_logDeriv_simple_zero`.
-/

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
variable {f : 𝕜 → 𝕜} {z₀ : 𝕜} {k : ℤ}

/-- Helper for Remark III.5-extra-6: punctured-neighborhood equality propagates to the
logarithmic derivative. -/
lemma logDeriv_congr_nhdsNE {f₁ f₂ : 𝕜 → 𝕜} (h : f₁ =ᶠ[𝓝[≠] z₀] f₂) :
    logDeriv f₁ =ᶠ[𝓝[≠] z₀] logDeriv f₂ := by
  -- Rewrite `logDeriv` as `deriv / value` and transport both pieces through the eventual equality.
  filter_upwards [h, h.nhdsNE_deriv] with z hz hderiv
  simp [logDeriv_apply, hz, hderiv]

/-- Helper for Remark III.5-extra-6: the logarithmic derivative of the normal form
`(z - z₀)^k * g(z)` splits into the principal part `k / (z - z₀)` and the logarithmic derivative
of the analytic unit `g`. -/
lemma logDeriv_zpow_id_sub_const_mul_analytic_eventuallyEq {g : 𝕜 → 𝕜}
    (hg : AnalyticAt 𝕜 g z₀) (hg0 : g z₀ ≠ 0) :
    logDeriv (fun z ↦ (z - z₀) ^ k * g z) =ᶠ[𝓝[≠] z₀] fun z ↦ (k : 𝕜) / (z - z₀) + logDeriv g z := by
  have hg_ne : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hg_an : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt 𝕜 g z :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  -- On the punctured neighborhood, both factors are nonzero and differentiable, so `logDeriv_mul`
  -- reduces the model computation to the power factor and the analytic remainder.
  filter_upwards [self_mem_nhdsWithin, hg_ne, hg_an] with z hz hgz hga
  have hz0 : z ≠ z₀ := by simpa using hz
  have hsub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
  have hsub_an : AnalyticAt 𝕜 (fun w : 𝕜 ↦ w - z₀) z := by
    simpa [sub_eq_add_neg] using (analyticAt_id.sub analyticAt_const : AnalyticAt 𝕜 (fun w : 𝕜 ↦ w - z₀) z)
  have hpow_diff : DifferentiableAt 𝕜 (fun w : 𝕜 ↦ (w - z₀) ^ k) z :=
    (hsub_an.zpow hsub_ne).differentiableAt
  have hsub_log : logDeriv (fun w : 𝕜 ↦ w - z₀) z = 1 / (z - z₀) := by
    simp [logDeriv_apply]
  have hpow :
      logDeriv (fun w : 𝕜 ↦ (w - z₀) ^ k) z = (k : 𝕜) / (z - z₀) := by
    -- The shift by `z₀` only changes the denominator of the standard `logDeriv_zpow` identity.
    calc
      logDeriv (fun w : 𝕜 ↦ (w - z₀) ^ k) z
          = (k : 𝕜) * logDeriv (fun w : 𝕜 ↦ w - z₀) z := by
              simpa using
                (logDeriv_fun_zpow (f := fun w : 𝕜 ↦ w - z₀) (x := z) hsub_an.differentiableAt k)
      _ = (k : 𝕜) * (1 / (z - z₀)) := by rw [hsub_log]
      _ = (k : 𝕜) / (z - z₀) := by simp [div_eq_mul_inv]
  have hpow_ne : (fun w : 𝕜 ↦ (w - z₀) ^ k) z ≠ 0 := by
    simpa using (zpow_ne_zero k hsub_ne)
  calc
    logDeriv (fun z ↦ (z - z₀) ^ k * g z) z
        = logDeriv (fun w : 𝕜 ↦ (w - z₀) ^ k) z + logDeriv g z := by
            rw [logDeriv_mul z hpow_ne hgz hpow_diff hga.differentiableAt]
    _ = (k : 𝕜) / (z - z₀) + logDeriv g z := by rw [hpow]

/-- Helper for Remark III.5-extra-6: multiplying an analytic germ by `z - z₀` forces it to tend
to `0` along the punctured neighborhood of `z₀`. -/
lemma tendsto_sub_mul_analyticAt_zero {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g z₀) :
    Tendsto (fun z ↦ (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
  have hsub : Tendsto (fun z : 𝕜 ↦ z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using
      ((continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : 𝕜 ↦ z₀) z₀)).continuousWithinAt.tendsto)
  -- The first factor tends to `0`, while the analytic factor stays bounded and tends to `g z₀`.
  simpa [sub_self] using hsub.mul (hg.continuousAt.continuousWithinAt.tendsto)

/-- Helper for Remark III.5-extra-6: the principal part `k / (z - z₀)` has order `-1` when
`k ≠ 0`. -/
lemma meromorphicOrderAt_principalPart_eq_neg_one (hk : k ≠ 0) :
    meromorphicOrderAt (fun z ↦ (k : 𝕜) / (z - z₀)) z₀ = (-1 : ℤ) := by
  -- Rewrite the principal part as a quotient of a nonzero constant by `z - z₀`.
  classical
  have hconst : meromorphicOrderAt (fun _ : 𝕜 ↦ (k : 𝕜)) z₀ = 0 := by
    simpa [Int.cast_ne_zero.mpr hk] using (meromorphicOrderAt_const_intCast (𝕜 := 𝕜) z₀ k)
  calc
    meromorphicOrderAt (fun z ↦ (k : 𝕜) / (z - z₀)) z₀
        = meromorphicOrderAt (fun _ : 𝕜 ↦ (k : 𝕜)) z₀ - meromorphicOrderAt (fun z ↦ z - z₀) z₀ := by
            simpa using
              (meromorphicOrderAt_div (f := fun _ : 𝕜 ↦ (k : 𝕜)) (g := fun z ↦ z - z₀)
                (x := z₀) (MeromorphicAt.const (k : 𝕜) z₀) (by fun_prop))
    _ = 0 - 1 := by rw [hconst, meromorphicOrderAt_id_sub_const]
    _ = (-1 : ℤ) := by norm_num

/-- Remark III.5-extra-6 (1): if a meromorphic function has finite order `k` at `z₀`, then its
logarithmic derivative is, on a punctured neighborhood of `z₀`, the principal part
`k / (z - z₀)` plus an analytic term. -/
theorem logDeriv_eventuallyEq_order_principalPart_add_analytic
    (hf : MeromorphicAt f z₀) (horder : meromorphicOrderAt f z₀ = k) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g z₀ ∧
      logDeriv f =ᶠ[𝓝[≠] z₀] fun z ↦ (k : 𝕜) / (z - z₀) + g z := by
  obtain ⟨g₀, hg₀, hg₀_ne, hf_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 horder
  refine ⟨logDeriv g₀, ?_, ?_⟩
  · -- The logarithmic derivative of the analytic unit is analytic because the denominator stays
    -- nonzero at `z₀`.
    simpa [logDeriv] using (hg₀.deriv.div hg₀ hg₀_ne)
  · -- Replace `f` by its meromorphic normal form and then compute the logarithmic derivative of
    -- that model expression.
    have hf_eq_mul :
        f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ k * g₀ z := by
      filter_upwards [hf_eq] with z hz
      simpa [smul_eq_mul] using hz
    exact (logDeriv_congr_nhdsNE hf_eq_mul).trans
      (logDeriv_zpow_id_sub_const_mul_analytic_eventuallyEq (k := k) hg₀ hg₀_ne)

/-- Remark III.5-extra-6 (2): after multiplication by `z - z₀`, the logarithmic derivative tends
to the meromorphic order `k`; this is the source-form residue statement. -/
theorem tendsto_sub_mul_logDeriv_eq_order
    (hf : MeromorphicAt f z₀) (horder : meromorphicOrderAt f z₀ = k) :
    Tendsto (fun z ↦ (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 (k : 𝕜)) := by
  obtain ⟨g, hg, hlog⟩ := logDeriv_eventuallyEq_order_principalPart_add_analytic hf horder
  have hmul :
      (fun z ↦ (z - z₀) * logDeriv f z) =ᶠ[𝓝[≠] z₀]
        fun z ↦ (z - z₀) * ((k : 𝕜) / (z - z₀) + g z) := by
    -- First substitute the principal-part decomposition from part (1).
    filter_upwards [hlog] with z hz
    simp [hz]
  have hrewrite :
      (fun z ↦ (z - z₀) * ((k : 𝕜) / (z - z₀) + g z)) =ᶠ[𝓝[≠] z₀]
        fun z ↦ (k : 𝕜) + (z - z₀) * g z := by
    -- On the punctured neighborhood, the singular term cancels with the prefactor `z - z₀`.
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ z₀ := by simpa using hz
    have hsub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
    calc
      (z - z₀) * ((k : 𝕜) / (z - z₀) + g z)
          = (z - z₀) * ((k : 𝕜) / (z - z₀)) + (z - z₀) * g z := by ring
      _ = (k : 𝕜) + (z - z₀) * g z := by
        calc
          (z - z₀) * ((k : 𝕜) / (z - z₀)) + (z - z₀) * g z
              = ((z - z₀) * ((z - z₀)⁻¹) * (k : 𝕜)) + (z - z₀) * g z := by
                  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ = (k : 𝕜) + (z - z₀) * g z := by simp [hsub_ne, mul_assoc]
  have hlimit :
      Tendsto (fun z ↦ (k : 𝕜) + (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 (k : 𝕜)) := by
    -- The regular part vanishes after multiplication by `z - z₀`.
    simpa using tendsto_const_nhds.add (tendsto_sub_mul_analyticAt_zero hg)
  exact (hlimit.congr' hrewrite.symm).congr' hmul.symm

/-- Remark III.5-extra-6 (3): if `z₀` is a zero or a pole of `f`, then the logarithmic derivative
has a simple pole there. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one_of_order_ne_zero
    (horder : meromorphicOrderAt f z₀ = k) (hk : k ≠ 0) :
    meromorphicOrderAt (logDeriv f) z₀ = (-1 : ℤ) := by
  have hf : MeromorphicAt f z₀ := by
    -- A nonzero order is finite, so `f` is meromorphic at `z₀`.
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    simpa [horder] using hk
  obtain ⟨g, hg, hlog⟩ := logDeriv_eventuallyEq_order_principalPart_add_analytic hf horder
  have hlt :
      meromorphicOrderAt (fun z ↦ (k : 𝕜) / (z - z₀)) z₀ < meromorphicOrderAt g z₀ := by
    -- The principal part has order `-1`, while the analytic remainder has nonnegative order.
    rw [meromorphicOrderAt_principalPart_eq_neg_one (z₀ := z₀) hk]
    have hneg : ((-1 : ℤ) : WithTop ℤ) < 0 := by
      exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
    exact lt_of_lt_of_le hneg hg.meromorphicOrderAt_nonneg
  -- The lower-order principal part controls the order of the sum.
  rw [meromorphicOrderAt_congr hlog]
  simpa using
    (meromorphicOrderAt_add_eq_left_of_lt (f₁ := fun z ↦ (k : 𝕜) / (z - z₀))
      (f₂ := g) (x := z₀) hg.meromorphicAt hlt).trans
      (meromorphicOrderAt_principalPart_eq_neg_one (z₀ := z₀) hk)

end
