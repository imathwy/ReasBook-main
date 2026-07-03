import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type w}
variable [CommRing A] [CommRing B] [Field K]
variable [Algebra A B] [Algebra A K] [IsFractionRing A K]
variable [IsIntegrallyClosed A] [Algebra.IsWeaklyEtale A B]

/- Domain-style sampling:
- primary domain: commutative algebra of normal domains, weakly étale base change, and integral
  closedness in tensor-product overrings of the fraction field;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi`;
- best owner abstraction: this theorem is `source-facing`, but its public statement should remain
  the canonical owner predicate `IsIntegrallyClosedIn B (B ⊗[A] K)`. The weak-dimension transfer,
  weakly étale base change, and flat-epimorphism integrally closedness results already have owner
  declarations upstream, so the cartesian square from Lemma `15.105.20` is only bridge data and
  should not be repackaged locally;
- primitive data: the normal domain `A`, its fraction field `K`, and the weakly étale owner
  `Algebra.IsWeaklyEtale A B`;
- derived API: the weak-dimension and epimorphism facts after tensor base change, and the final
  `IsIntegrallyClosedIn` conclusion.

Source/core/bridge triage:
- `source-facing`: `isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale`;
- `core/canonical`: `IsIntegrallyClosedIn`, `Algebra.IsWeaklyEtale`, `HasWeakDimensionLE`,
  `Algebra.IsEpi`;
- `bridge/view`: the cartesian-square witness from Lemma `15.105.20`, together with the tensor
  base-change bridge from Lemma `10.107.3` and the weakly étale base-change theorem
  `Algebra.IsWeaklyEtale.baseChange`.
-/

-- Proof sketch: choose the cartesian square `A → K`, `V → L` from Lemma `15.105.20`. Base change
-- the weakly étale map `A → B` along `A → V`; by `Algebra.IsWeaklyEtale.baseChange`, the map
-- `V → B ⊗[A] V` is weakly étale, so `hasWeakDimensionLE_of_isWeaklyEtale` upgrades the weak
-- dimension bound on `V` to one on `B ⊗[A] V`. The bottom map `B ⊗[A] V → B ⊗[A] L` remains a
-- flat, injective epimorphism after tensor base change, using the canonical epimorphism base
-- change theorem `algebra_isEpi_tensorProduct_of_isEpi`; then Lemma `15.105.21` gives
-- `IsIntegrallyClosedIn (B ⊗[A] V) (B ⊗[A] L)`. The original cartesian square is bridge data used
-- only to descend this owner statement to `IsIntegrallyClosedIn B (B ⊗[A] K)`.
/-- Lemma 15.105.22: if `A` is a normal domain with fraction field `K` and `A → B` is weakly
étale, then `B` is integrally closed in `B ⊗[A] K`. -/
theorem isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale :
    IsIntegrallyClosedIn B (B ⊗[A] K) := sorry

end
