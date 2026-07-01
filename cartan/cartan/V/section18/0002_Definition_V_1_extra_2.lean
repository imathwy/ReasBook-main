import Mathlib

open Filter

-- Domain sampling: this file is source-facing in the function-series / uniform-convergence
-- domain. The relevant core owners are `HasSumUniformlyOn`, `SummableUniformlyOn`,
-- `SummableLocallyUniformlyOn`, and `tendstoUniformlyOn_tsum_nat`. The compact-majorant condition
-- below is the source-facing input on raw function families; the uniform and locally uniform
-- summability statements are derived API.

variable {D F : Type*} [TopologicalSpace D] [NormedAddCommGroup F]

/-- Definition V.1-extra-2 (1). A series of functions on `D` is normally convergent on compact
subsets of `s` if every compact `K ⊆ s` admits a convergent series of nonnegative constants
majorizing the norms of all terms on `K`. -/
def NormallyConvergentOnCompacta (f : ℕ → D → F) (s : Set D) : Prop :=
  ∀ ⦃K : Set D⦄, IsCompact K → K ⊆ s →
    ∃ u : ℕ → NNReal, Summable (fun n ↦ (u n : ℝ)) ∧ ∀ n x, x ∈ K → ‖f n x‖ ≤ (u n : ℝ)

/-- On each compact subset `K ⊆ s`, normal convergence supplies the canonical uniform-summability
owner for the underlying function series. -/
theorem NormallyConvergentOnCompacta.summableUniformlyOn
    [CompleteSpace F] {f : ℕ → D → F} {s K : Set D} (hf : NormallyConvergentOnCompacta f s)
    (hK : IsCompact K) (hKs : K ⊆ s) :
    SummableUniformlyOn f K := by
  rcases hf hK hKs with ⟨u, hu, hbound⟩
  exact (HasSumUniformlyOn.of_norm_le_summable hu fun n x hx ↦ hbound n x hx).summableUniformlyOn

/-- On a locally compact domain, normal convergence on compact subsets is exactly the local
majorant hypothesis needed for mathlib's canonical locally uniform summability owner. -/
theorem NormallyConvergentOnCompacta.summableLocallyUniformlyOn
    [CompleteSpace F] [LocallyCompactSpace D] {f : ℕ → D → F} {s : Set D}
    (hf : NormallyConvergentOnCompacta f s) (hs : IsOpen s) :
    SummableLocallyUniformlyOn f s := by
  exact SummableLocallyUniformlyOn_of_locally_bounded hs fun K hKs hK ↦ by
    rcases hf hK hKs with ⟨u, hu, hbound⟩
    exact ⟨fun n ↦ (u n : ℝ), hu, fun n x hx ↦ hbound n x hx⟩

/-- Definition V.1-extra-2 (2). On every compact subset `K ⊆ s`, the partial sums of a series
that is normally convergent on compact subsets converge uniformly to its infinite sum. -/
theorem tendstoUniformlyOn_partialSums_of_normally_convergent_on_compacts
    [CompleteSpace F] {f : ℕ → D → F} {s K : Set D} (hf : NormallyConvergentOnCompacta f s)
    (hK : IsCompact K) (hKs : K ⊆ s) :
    TendstoUniformlyOn (fun N x ↦ ∑ n ∈ Finset.range N, f n x) (fun x ↦ ∑' n, f n x) atTop K := by
  rcases hf hK hKs with ⟨u, hu, hbound⟩
  exact tendstoUniformlyOn_tsum_nat hu fun n x hx ↦ hbound n x hx
