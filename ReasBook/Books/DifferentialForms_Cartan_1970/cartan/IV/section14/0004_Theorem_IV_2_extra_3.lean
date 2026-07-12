import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Theorem IV.2-extra-3:
- part (1) is `source-facing`: it is the local several-variable vanishing statement whose natural
  owner is `AnalyticAt`, and its proof should use the canonical analytic/power-series API rather
  than a concrete `(ℂ × ℂ) → ℂ` model;
- part (3) is a `bridge/view`: neighborhood vanishing forces vanishing of all higher iterated
  derivatives, and the canonical owner is the locality of `iteratedFDeriv`;
- parts (2), (4), and (5) are already `core/canonical` facts upstream, so this file should reuse
  them directly instead of keeping parallel local wrappers.

The relevant owner declarations sampled before refinement were:
- `HasFPowerSeriesOnBall.factorial_smul`;
- `Filter.EventuallyEq.eq_of_nhds`;
- `Filter.EventuallyEq.iteratedFDeriv`;
- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`.
-/

open Filter
open scoped Topology

universe u v

section LocalVanishing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Theorem IV.2-extra-3 (1): for an analytic map on a normed vector space over a
characteristic-zero normed field, vanishing at `z₀` and vanishing of all higher iterated Fréchet
derivatives at `z₀` force vanishing on a
neighborhood of `z₀`. -/
theorem AnalyticAt.eventuallyEq_zero_of_zero_and_iteratedFDeriv_eq_zero
    {f : E → F} {z₀ : E} (hf : AnalyticAt 𝕜 f z₀) (hfz₀ : f z₀ = 0)
    (hiter : ∀ n : ℕ, iteratedFDeriv 𝕜 (n + 1) f z₀ = 0) :
    f =ᶠ[𝓝 z₀] 0 := by
  rcases hf with ⟨p, hp⟩
  rcases hp with ⟨r, hr⟩
  have hpAt : HasFPowerSeriesAt f p z₀ := ⟨r, hr⟩
  have hp0 : p 0 = 0 := by
    ext v
    simpa [hfz₀] using hpAt.coeff_zero v
  have hp_succ (n : ℕ) (y : E) : p (n + 1) (fun _ ↦ y) = 0 := by
    have hiter_apply : iteratedFDeriv 𝕜 (n + 1) f z₀ (fun _ ↦ y) = 0 := by
      rw [hiter n]
      simp
    have hdiag_nat : Nat.factorial (n + 1) • p (n + 1) (fun _ ↦ y) = 0 :=
      (hr.factorial_smul y (n + 1)).trans hiter_apply
    have hdiag : ((Nat.factorial (n + 1) : 𝕜)) • p (n + 1) (fun _ ↦ y) = 0 := by
      simpa [Nat.cast_smul_eq_nsmul 𝕜] using hdiag_nat
    exact (smul_eq_zero.mp hdiag).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  filter_upwards [hr.eventually_hasSum_sub] with z hz
  have hz0 : HasSum (fun n : ℕ ↦ p n (fun _ ↦ z - z₀)) 0 := by
    have hterms : (fun n : ℕ ↦ p n (fun _ ↦ z - z₀)) = fun _ : ℕ ↦ (0 : F) := by
      funext n
      cases n with
      | zero =>
          simp [hp0]
      | succ n =>
          exact hp_succ n (z - z₀)
    have hzero : HasSum (fun _ : ℕ ↦ (0 : F)) 0 := hasSum_zero
    exact hterms.symm ▸ hzero
  exact hz.unique hz0

end LocalVanishing

section EventuallyZero

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Theorem IV.2-extra-3 (3): neighborhood vanishing forces vanishing of every higher iterated
Fréchet derivative at the base point. The analyticity assumption is mathematically redundant here,
so the bridge is stated in the canonical locality form. -/
theorem iteratedFDeriv_eq_zero_of_eventuallyEq_zero {f : E → F} {z₀ : E}
    (hzero : f =ᶠ[𝓝 z₀] 0) (n : ℕ) :
    iteratedFDeriv 𝕜 (n + 1) f z₀ = 0 := by
  simpa using (hzero.iteratedFDeriv 𝕜 (n + 1)).eq_of_nhds

end EventuallyZero

/- Theorem IV.2-extra-3 (2) is the canonical neighborhood-filter fact
`Filter.EventuallyEq.eq_of_nhds`. -/
#check Filter.EventuallyEq.eq_of_nhds

/- Theorem IV.2-extra-3 (4) is exactly the canonical identity principle on a preconnected set; the
stronger `IsConnected` hypothesis from the previous local wrapper was redundant. -/
recall AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero

/- Theorem IV.2-extra-3 (5) is the open-set specialization of the generic bridge
`Set.EqOn.eventuallyEq_of_mem`. -/
#check Set.EqOn.eventuallyEq_of_mem
