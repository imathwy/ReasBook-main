import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- `lean_leansearch` was unavailable in this agent environment, so this source-facing sequence
-- specialization is stated directly as a thin bridge to the canonical mathlib owner
-- `TendstoLocallyUniformlyOn.differentiableOn`.
/-- Theorem 1: if a sequence of holomorphic functions on `D` converges uniformly on compact
subsets of `D`, then its limit is holomorphic on `D`. -/
theorem differentiableOn_of_tendsto_locally_uniformly_on_compacts
    {D : Set ℂ} (hD : IsOpen D) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop D) :
    DifferentiableOn ℂ f D :=
  hconv.differentiableOn (Eventually.of_forall hF) hD
