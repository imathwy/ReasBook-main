import DifferentialForms_Cartan_1970.V.section18.«0006_Theorem_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- This remark is a bridge/view corollary of the chapter owner
-- `tendsto_locally_uniformly_on_compacts_deriv`, which is itself the sequence-specialized bridge
-- to the canonical mathlib theorem `TendstoLocallyUniformlyOn.deriv`.
/-- Remark V.1-extra-5: as an alternative Cauchy-integral proof route to Theorem 2, if a sequence
of holomorphic functions on `D` converges locally uniformly to a holomorphic limit, then the
derivatives converge uniformly on each compact subset `K ⊆ D`. -/
theorem tendstoUniformlyOn_compact_deriv_of_tendstoLocallyUniformlyOn
    {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) D) (hconv : TendstoLocallyUniformlyOn F f atTop D) :
    TendstoUniformlyOn (deriv ∘ F) (deriv f) atTop K :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp
      (tendsto_locally_uniformly_on_compacts_deriv hD hF hconv) K hKD hK
