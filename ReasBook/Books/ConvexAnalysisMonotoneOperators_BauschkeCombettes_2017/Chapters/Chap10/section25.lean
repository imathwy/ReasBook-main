import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_25 (from Chap10) -/
open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 10.25: for a quasiconvex extended-real-valued function on a real Hilbert space,
weak sequential lower semicontinuity, sequential lower semicontinuity, lower semicontinuity, and
weak lower semicontinuity are equivalent. -/
-- Proof sketch: quasiconvexity is exactly convexity of every real lower level set by
-- `quasiconvexOn_univ_iff_convex_lowerLevelSet`, so this is the lower-level-set owner theorem
-- `lowerSemicontinuity_tfae_of_convex_lowerLevelSet`.
theorem quasiconvexOn_univ_lowerSemicontinuity_tfae {f : H → EReal}
    (hf : QuasiconvexOn ℝ Set.univ f) :
    List.TFAE
      [ (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto xₙ atTop (𝓝 x) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        LowerSemicontinuous f,
        WeaklyLowerSemicontinuous f ] :=
  lowerSemicontinuity_tfae_of_convex_lowerLevelSet
    ((quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ f).1 hf)

/-- A lower semicontinuous quasiconvex extended-real-valued function on a real Hilbert space is
weakly lower semicontinuous. -/
theorem weaklyLowerSemicontinuous_of_quasiconvexOn_univ {f : H → EReal}
    (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f) :
    WeaklyLowerSemicontinuous f :=
  (List.TFAE.out (quasiconvexOn_univ_lowerSemicontinuity_tfae hf_quasi) 2 3).1 hf_lsc

end ERealFunction
