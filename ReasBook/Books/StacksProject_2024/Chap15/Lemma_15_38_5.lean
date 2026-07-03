import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsRegularLocalRing A]

/- Domain-style sampling for Lemma 15.38.5:
- primary domain: local commutative algebra of regular local `k`-algebras and maximal-ideal-adic
  formal smoothness.
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing`,
  `Algebra.IsSeparableOver`.
- best owner abstraction: the public conclusion should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`. Completion invariance and the
  finite-variable power-series presentation are proof bridges, not extra public data.
- primitive data: the field `k`, the regular local `k`-algebra `A`, and the Stacks-separability
  hypothesis on `ResidueField A / k`.
- derived API: formal smoothness of the structural map for the `maximalIdeal A`-adic topology.

Source/core/bridge triage:
- `source-facing`: the textbook implication from regularity plus separable residue field to adic
  formal smoothness.
- `core/canonical`: `RingHom.formally_smooth_for_adic`.
- `bridge/view`: completion invariance and the complete-regular-local power-series presentation.
-/

-- Proof sketch: by Lemma `15.37.4`, formal smoothness for the `maximalIdeal A`-adic topology can
-- be checked after passing to the completion. Lemma `15.38.4` identifies the completed regular
-- local `k`-algebra with a finite-variable power series ring over `ResidueField A`, and
-- Lemma `10.138.3` together with Lemma `15.37.2` shows that this power series ring is formally
-- smooth over `k` for its maximal-ideal-adic topology.
/-- Lemma 15.38.5: if `(A, maximalIdeal A, ResidueField A)` is a regular local `k`-algebra and the
residue field extension `ResidueField A / k` is separable in the Stacks Project sense, then the
structure map `k → A`, formalized by `algebraMap k A`, is formally smooth for the
`maximalIdeal A`-adic topology. -/
theorem formallySmooth_for_maximalIdeal_adic_of_isRegularLocalRing_of_isSeparableOver
    [Algebra.IsSeparableOver k (ResidueField A)] :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := sorry

end
