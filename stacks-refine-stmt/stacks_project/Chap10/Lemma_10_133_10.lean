import Mathlib
import stacks_project.Chap10.Definition_10_133_1
import stacks_project.Chap10.Lemma_10_132_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open LinearMap

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: algebraic de Rham differentials on exterior powers of Kähler differentials;
* sampled owner API: `LinearMap.IsDifferentialOperatorOfOrder`, `deRhamDifferentialFamily`,
  `isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily`, and `KaehlerDifferential.D`;
* owner abstraction: the canonical recursive family `deRhamDifferentialFamily A B`;
* primitive data vs. derived API: the primitive object is the canonical de Rham differential
  family from Lemma `10.132.2`, while “the `p`th differential is first-order” is derived
  theorem-level API and should be stated directly for that owner rather than via a parallel pair of
  parameters `δ` and `hd`.
-/

variable (A B)

/-- Lemma 10.133.10: in the canonical relative de Rham complex of `B` over `A`, the universal
derivation and all positive-degree de Rham differentials are differential operators of order `1`.
-/
-- Proof sketch: for degree `0`, expand the scalar commutator of `δ 0` and use
-- `IsExteriorPowerDeRhamDifferential.degree_zero` to identify it with the universal derivation.
-- For higher degrees, evaluate the commutator of `δ (i + 1)` on basic forms and use the de Rham
-- rule encoded by `IsExteriorPowerDeRhamDifferential` to see that each commutator is `B`-linear,
-- hence order `0`.
theorem de_rham_differentials_are_order_one_differential_operators
    (p : ℕ) :
    (deRhamDifferentialFamily A B p).IsDifferentialOperatorOfOrder B 1 := sorry

end
