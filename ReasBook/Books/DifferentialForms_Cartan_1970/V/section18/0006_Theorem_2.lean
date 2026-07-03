import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- `lean_leansearch` was unavailable in this runner, so this source-facing sequence specialization
-- is stated directly as a thin bridge to the canonical mathlib owner
-- `TendstoLocallyUniformlyOn.deriv`.
/-- Theorem 2: if a sequence of holomorphic functions on `D` converges to a holomorphic limit
uniformly on compact subsets of `D`, then the sequence of derivatives converges uniformly on
compact subsets of `D` to the derivative of the limit. -/
theorem tendsto_locally_uniformly_on_compacts_deriv
    {D : Set ℂ} (hD : IsOpen D) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) atTop D :=
  hconv.deriv (Eventually.of_forall hF) hD
