import Mathlib

open Filter Set
open scoped Topology

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the analytic functions `logDeriv f` and `logDeriv g` agree on a sequence in `D`
-- converging to a point `a ∈ D`, so the identity theorem yields `D.EqOn (logDeriv f)
-- (logDeriv g)`. On the open preconnected domain `D`, mathlib's canonical bridge
-- `logDeriv_eqOn_iff` then identifies this with `f = c • g` on `D` for a nonzero constant `c`.
/-- Exercise 11: if two nowhere-vanishing analytic functions on an open preconnected domain have
equal logarithmic derivatives along a sequence converging to a point of the domain, then they
differ by a nonzero constant scalar factor on that domain. -/
theorem exists_const_eqOn_smul_of_log_deriv_eq_on_convergent_sequence
    {𝕜 : Type*} [RCLike 𝕜] {D : Set 𝕜} (hD_open : IsOpen D)
    (hD_preconnected : IsPreconnected D) {f g : 𝕜 → 𝕜} (hf : AnalyticOnNhd 𝕜 f D)
    (hg : AnalyticOnNhd 𝕜 g D) (hf_ne : ∀ z ∈ D, f z ≠ 0) (hg_ne : ∀ z ∈ D, g z ≠ 0)
    {u : ℕ → 𝕜} {a : 𝕜} (ha : a ∈ D) (hu_tendsto : Tendsto u atTop (𝓝 a))
    (hu_ne : ∀ n, u n ≠ a)
    (hlog : ∀ n, logDeriv f (u n) = logDeriv g (u n)) :
    ∃ c : 𝕜, c ≠ 0 ∧ EqOn f (c • g) D := by
  have hlogf : AnalyticOnNhd 𝕜 (logDeriv f) D := by
    simpa [logDeriv] using (hf.deriv_of_isOpen hD_open).div hf hf_ne
  have hlogg : AnalyticOnNhd 𝕜 (logDeriv g) D := by
    simpa [logDeriv] using (hg.deriv_of_isOpen hD_open).div hg hg_ne
  have hclosure : a ∈ closure ({z | logDeriv f z = logDeriv g z} \ {a}) :=
    mem_closure_of_tendsto hu_tendsto <| .of_forall fun n ↦ ⟨hlog n, hu_ne n⟩
  have hlog_eq : EqOn (logDeriv f) (logDeriv g) D :=
    hlogf.eqOn_of_preconnected_of_mem_closure hlogg hD_preconnected ha hclosure
  exact (logDeriv_eqOn_iff hf.differentiableOn hg.differentiableOn hD_open hD_preconnected
    hg_ne hf_ne).mp hlog_eq
