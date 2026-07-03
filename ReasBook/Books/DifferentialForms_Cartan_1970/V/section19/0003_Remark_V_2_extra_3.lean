import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

-- Semantic recall note: `lean_leansearch` was unavailable in this session; local repository and
-- mathlib order lemmas were used instead.

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Remark V.2-extra-3 (1): every pole of the sum `f` lies in the union of the pole sets of the
terms `fₙ`, provided each term is in meromorphic normal form and whenever all terms are analytic at
a point, the sum is analytic there as well. -/
theorem poles_subset_iUnion_poles_of_analyticAt
    {f : 𝕜 → E} {fₙ : ℕ → 𝕜 → E}
    (hnf : ∀ z₀ n, MeromorphicNFAt (fₙ n) z₀)
    (hanalytic : ∀ z₀, (∀ n, AnalyticAt 𝕜 (fₙ n) z₀) → AnalyticAt 𝕜 f z₀) :
    {z : 𝕜 | meromorphicOrderAt f z < 0} ⊆
      ⋃ n : ℕ, {z : 𝕜 | meromorphicOrderAt (fₙ n) z < 0} := by
  intro z hz
  by_contra hz_union
  have hterms : ∀ n, AnalyticAt 𝕜 (fₙ n) z := by
    intro n
    have hnonneg : 0 ≤ meromorphicOrderAt (fₙ n) z := by
      apply le_of_not_gt
      intro hn
      exact hz_union <| Set.mem_iUnion.mpr ⟨n, hn⟩
    exact ((hnf z n).meromorphicOrderAt_nonneg_iff_analyticAt).1 hnonneg
  exact (not_lt_of_ge (hanalytic z hterms).meromorphicOrderAt_nonneg) hz

/-- Remark V.2-extra-3 (2): more precisely, if `z₀` is a pole of order `k` of one term `fₙ n`,
and near `z₀` the full sum is that term plus an analytic remainder, then `z₀` is a pole of order
`k` of `f` as well. -/
theorem meromorphicOrderAt_eq_of_eventuallyEq_term_add_analytic
    {f : 𝕜 → E} {fₙ : ℕ → 𝕜 → E} {z₀ : 𝕜} {n : ℕ}
    (horder : meromorphicOrderAt (fₙ n) z₀ < 0)
    (hdecomp : ∃ g : 𝕜 → E, AnalyticAt 𝕜 g z₀ ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ fₙ n z + g z) :
    meromorphicOrderAt f z₀ = meromorphicOrderAt (fₙ n) z₀ := by
  rcases hdecomp with ⟨g, hg, hfg⟩
  rw [meromorphicOrderAt_congr hfg]
  simpa using
    (meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt
      (lt_of_lt_of_le horder hg.meromorphicOrderAt_nonneg) :
      meromorphicOrderAt (fₙ n + g) z₀ = meromorphicOrderAt (fₙ n) z₀)

/-- Remark V.2-extra-3 (3): if each term is in meromorphic normal form, the sum is analytic
whenever all terms are analytic, and each pole of a term admits the source-form decomposition of
the full sum into that term plus an analytic remainder, then the pole set of `f` is exactly the
union of the pole sets of the terms. -/
theorem poles_eq_iUnion_poles_of_analyticAt_and_local_decomposition
    {f : 𝕜 → E} {fₙ : ℕ → 𝕜 → E}
    (hnf : ∀ z₀ n, MeromorphicNFAt (fₙ n) z₀)
    (hanalytic : ∀ z₀, (∀ n, AnalyticAt 𝕜 (fₙ n) z₀) → AnalyticAt 𝕜 f z₀)
    (hdecomp : ∀ z₀ n, meromorphicOrderAt (fₙ n) z₀ < 0 →
      ∃ g : 𝕜 → E, AnalyticAt 𝕜 g z₀ ∧
        f =ᶠ[𝓝[≠] z₀] fun z ↦ fₙ n z + g z) :
    {z : 𝕜 | meromorphicOrderAt f z < 0} =
      ⋃ n : ℕ, {z : 𝕜 | meromorphicOrderAt (fₙ n) z < 0} := by
  ext z
  constructor
  · intro hz
    exact poles_subset_iUnion_poles_of_analyticAt hnf hanalytic hz
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
    have hn' : meromorphicOrderAt (fₙ n) z < 0 := by
      simpa using hn
    change meromorphicOrderAt f z < 0
    rw [meromorphicOrderAt_eq_of_eventuallyEq_term_add_analytic hn' (hdecomp z n hn')]
    exact hn'
