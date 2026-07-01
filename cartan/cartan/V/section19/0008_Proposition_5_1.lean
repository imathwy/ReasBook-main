import Mathlib

namespace PeriodPair

open scoped Topology

/-- Proposition 5.1: on every compact subset of `ℂ` avoiding the lattice poles, the defining
Weierstrass series converges uniformly. -/
theorem hasSumUniformlyOn_weierstrassP_of_isCompact (L : PeriodPair) {K : Set ℂ}
    (hK : IsCompact K) (hKc : K ⊆ L.latticeᶜ) :
    HasSumUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - l) ^ 2 - 1 / l ^ 2)
      ℘[L]
      K :=
by
  have h :
      HasSumLocallyUniformlyOn
        (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - l) ^ 2 - 1 / l ^ 2)
        ℘[L]
        L.latticeᶜ :=
    L.hasSumLocallyUniformly_weierstrassP.hasSumLocallyUniformlyOn
  have h' := h.mono hKc
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h'
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp h'

end PeriodPair
