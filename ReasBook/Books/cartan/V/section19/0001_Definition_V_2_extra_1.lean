import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file is source-facing in the meromorphic-series / compacta-convergence
-- domain. The local project owner style for compacta predicates is the direct
-- `∀ K, IsCompact K → K ⊆ D → ...` layer, with `MeromorphicOn` and `AnalyticOnNhd` as the
-- canonical meromorphy / holomorphy owners and `NNReal` majorants for normal convergence.

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Definition V.2-extra-1 (1): a series of `E`-valued meromorphic functions on an open set `D`
converges uniformly on compact subsets of `D` if every compact `K ⊆ D` admits a tail whose terms
are analytic on `K` and form a uniformly convergent series there. -/
class MeromorphicSeriesUniformlyConvergentOnCompacta
    (f : ℕ → 𝕜 → E) (D : Set 𝕜) : Prop where
  isOpen_domain : IsOpen D
  meromorphic_terms (n : ℕ) : MeromorphicOn (f n) D
  on_compact {K : Set 𝕜} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ,
      (∀ n, AnalyticOnNhd 𝕜 (f (n + N)) K) ∧
      SummableUniformlyOn (fun n ↦ f (n + N)) K

/-- Definition V.2-extra-1 (2): a series of `E`-valued meromorphic functions on an open set `D`
converges normally on compact subsets of `D` if every compact `K ⊆ D` admits a tail whose terms
are analytic on `K` and are uniformly bounded there by a summable nonnegative real majorant. -/
class MeromorphicSeriesNormallyConvergentOnCompacta
    (f : ℕ → 𝕜 → E) (D : Set 𝕜) : Prop where
  isOpen_domain : IsOpen D
  meromorphic_terms (n : ℕ) : MeromorphicOn (f n) D
  on_compact {K : Set 𝕜} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ,
      (∀ n, AnalyticOnNhd 𝕜 (f (n + N)) K) ∧
      ∃ u : ℕ → NNReal,
        Summable (fun n ↦ (u n : ℝ)) ∧
        ∀ n z, z ∈ K → ‖f (n + N) z‖ ≤ (u n : ℝ)

namespace MeromorphicSeriesNormallyConvergentOnCompacta

/-- Compact-normal convergence on meromorphic tails implies compact-uniform convergence. -/
theorem uniformlyConvergentOnCompacta
    [CompleteSpace E] {f : ℕ → 𝕜 → E} {D : Set 𝕜}
    (h : MeromorphicSeriesNormallyConvergentOnCompacta f D) :
    MeromorphicSeriesUniformlyConvergentOnCompacta f D := by
  refine ⟨h.isOpen_domain, h.meromorphic_terms, ?_⟩
  intro K hK hKD
  rcases h.on_compact hK hKD with ⟨N, hanalytic, u, hu, hubound⟩
  refine ⟨N, hanalytic, ?_⟩
  exact (HasSumUniformlyOn.of_norm_le_summable hu fun n z hz ↦ hubound n z hz).summableUniformlyOn

end MeromorphicSeriesNormallyConvergentOnCompacta
