import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this environment; local precedents used:
-- `Definition_4_21_extra_1.lean`, `Theorem_4_12.lean`, and mathlib's manifold derivative API.

noncomputable section

open scoped ContDiff Manifold

namespace Manifold

universe u𝕜 uE uE' uH uH' uM uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}

/-- Exercise 4.4 (1): if `f` is manifold differentiable at `p`, then the rank of `f` at `p`
is the finite dimension of the range of its manifold derivative there. -/
noncomputable def rankAt (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (f : M → N) (p : M) : ℕ :=
  Module.finrank 𝕜 ((mfderiv I J f p).range)

/-
The defining formula for `rankAt`.
-/
omit [FiniteDimensional 𝕜 E'] in
theorem rankAt_eq_finrank_range_mfderiv (f : M → N) (p : M) :
    rankAt I J f p = Module.finrank 𝕜 ((mfderiv I J f p).range) :=
  rfl

/-- Exercise 4.4 (2): `f` has constant rank `r` when it is manifold differentiable and its
pointwise manifold rank is equal to `r` at every point. -/
def HasConstantRank (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (f : M → N) (r : ℕ) : Prop :=
  MDifferentiable I J f ∧ ∀ p : M, rankAt I J f p = r

/-
The defining pointwise characterization of `HasConstantRank`.
-/
omit [FiniteDimensional 𝕜 E'] in
theorem hasConstantRank_iff_forall_rankAt_eq (f : M → N) (r : ℕ) :
    HasConstantRank I J f r ↔
      MDifferentiable I J f ∧ ∀ p : M, rankAt I J f p = r :=
  Iff.rfl

end

end Manifold
