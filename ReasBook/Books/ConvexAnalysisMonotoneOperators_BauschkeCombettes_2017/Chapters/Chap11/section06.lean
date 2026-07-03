import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_11_6 (from Chap11) -/
universe u

namespace ERealFunction

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {H : Type u} [AddCommMonoid H] [SMul 𝕜 H]

/-- Proposition 11.6: the set of global minimizers of a quasiconvex `]-∞,+∞]`-valued function is
convex. -/
-- Proof sketch: identify `Argmin f` with the sublevel set at `sInf (Set.range f)` using the
-- owner theorem `argmin_eq_setOf_le_sInf_range`, then specialize `QuasiconvexOn` to that
-- threshold.
theorem convex_argmin_of_quasiconvexOn_univ
    {f : H → EReal} (hf_quasi : QuasiconvexOn 𝕜 Set.univ f) :
    Convex 𝕜 (Argmin f) := by
  simpa [argmin_eq_setOf_le_sInf_range] using hf_quasi (sInf (Set.range f))

end ERealFunction
