import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric
open scoped Topology

-- `lean_leansearch` was unavailable in this agent environment, so this item is stated directly
-- against the canonical local/uniform convergence API from mathlib.
/-- Proposition 1.1: on an open subset `D` of `ℂ`, a sequence of functions converges locally
uniformly exactly when it converges uniformly on every compact closed disc contained in `D`. -/
theorem tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_compact_discs
    {E : Type u} [UniformSpace E] {D : Set ℂ} (hD : IsOpen D) {F : ℕ → ℂ → E} {f : ℂ → E} :
    TendstoLocallyUniformlyOn F f Filter.atTop D ↔
      ∀ z r, 0 ≤ r → closedBall z r ⊆ D →
        TendstoUniformlyOn F f Filter.atTop (closedBall z r) := by
  constructor
  · intro h z r hr hzr
    exact
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp h (closedBall z r) hzr
        (isCompact_closedBall z r)
  · intro h u hu z hz
    obtain ⟨r, hr, hzr⟩ := nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz)
    refine
      ⟨closedBall z r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds z hr), ?_⟩
    exact (h z r hr.le hzr) u hu
