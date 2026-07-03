import Mathlib
import StacksProject_2024.Chap15.Lemma_15_111_1
import StacksProject_2024.Chap15.Lemma_15_111_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

attribute [local instance] fixedPointsSubring_smulCommClass

/- Domain-style sampling for Lemma 15.111.8:
- primary domain: invariant-theoretic transitivity on prime ideals above a fixed prime of the
  fixed subring
- sampled owner declarations:
  `fixedPointsSubring_smulCommClass`,
  `FixedPoints.subring_isInvariant`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `Ideal.LiesOver`,
  `Algebra.IsInvariant.orbit_eq_primesOver`
- best owner abstraction: `Algebra.IsInvariant.exists_smul_of_under_eq`
- primitive data: the fixed-subring extension `RFix ↪ R` and primes `q`, `q'` lying over
  `p : Ideal RFix`
- derived API: transitivity of the `G`-action on primes of `R` above `p`

Layer triage:
- `source-facing`: the fixed-subring prime-transitivity statement
- `core/canonical`: `Algebra.IsInvariant.exists_smul_of_under_eq`
- `bridge/view`: the imported fixed-subring action bridge `fixedPointsSubring_smulCommClass`
  together with the imported owner instance `FixedPoints.subring_isInvariant`

The public theorem stays source-facing, while the proof is reduced to a direct specialization of
the canonical invariant-theory owner theorem. The `SMulCommClass` bridge is already owned upstream
by `Lemma_15_111_6`, and the `IsInvariant` bridge is already owned upstream by `Lemma_15_111_1`,
so this file should reuse both owner declarations directly rather than rebuilding either locally.
-/

/-- Lemma 15.111.8: if two prime ideals of `R` lie over the same prime ideal of the fixed subring
`R^G`, then one is obtained from the other by the action of an element of `G`. -/
-- Proof sketch: specialize `Algebra.IsInvariant.exists_smul_of_under_eq` to the inclusion
-- `FixedPoints.subring R G ↪ R`. The hypotheses that `q` and `q'` both lie over `p` identify
-- their pullbacks to the fixed subring, and the general transitivity theorem then produces
-- `σ : G` with `σ • q = q'`.
theorem exists_smul_eq_of_liesOver_fixedPoints
    (p : Ideal RFix) (q q' : Ideal R)
    [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] :
    ∃ σ : G, σ • q = q' := by
  simpa [eq_comm] using Algebra.IsInvariant.exists_smul_of_under_eq RFix R G q q'
    ((q.over_def p).symm.trans (q'.over_def p))

end
