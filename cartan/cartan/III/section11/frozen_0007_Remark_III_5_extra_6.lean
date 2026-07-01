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

/-- Remark III.5-extra-6 (1): if a meromorphic function has finite order `k` at `z₀`, then its
logarithmic derivative is, on a punctured neighborhood of `z₀`, the principal part
`k / (z - z₀)` plus an analytic term. -/
theorem logDeriv_eventuallyEq_order_principalPart_add_analytic
    (hf : MeromorphicAt f z₀) (horder : meromorphicOrderAt f z₀ = k) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g z₀ ∧
      logDeriv f =ᶠ[𝓝[≠] z₀] fun z ↦ (k : 𝕜) / (z - z₀) + g z := sorry

/-- Remark III.5-extra-6 (2): after multiplication by `z - z₀`, the logarithmic derivative tends
to the meromorphic order `k`; this is the source-form residue statement. -/
theorem tendsto_sub_mul_logDeriv_eq_order
    (hf : MeromorphicAt f z₀) (horder : meromorphicOrderAt f z₀ = k) :
    Tendsto (fun z ↦ (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 (k : 𝕜)) := sorry

/-- Remark III.5-extra-6 (3): if `z₀` is a zero or a pole of `f`, then the logarithmic derivative
has a simple pole there. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one_of_order_ne_zero
    (horder : meromorphicOrderAt f z₀ = k) (hk : k ≠ 0) :
    meromorphicOrderAt (logDeriv f) z₀ = (-1 : ℤ) := sorry

end
