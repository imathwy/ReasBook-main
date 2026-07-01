import Mathlib
import stacks_project.Chap10.Lemma_10_52_13
import stacks_project.Chap15.Lemma_15_121_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open Module.End
open scoped TensorProduct

universe u v w

section

/- Domain triage:
- primary domain: finite-length determinants of module endomorphisms over local rings and their
  behavior under flat local base change;
- sampled owner API:
  `Ideal.Fiber`,
  `finite_length_iff_finite_length_base_change`,
  `Module.End.finiteLengthDeterminant`,
  `TensorProduct.isBaseChange`,
  `IsBaseChange.endHom`;
- `source-facing`: the closed-fiber determinant comparison of Lemma `15.121.3`;
- `core/canonical`: the closed fiber is owned by `Ideal.Fiber (maximalIdeal R) R'`, and the
  base-changed endomorphism is owned by `IsBaseChange.endHom`, specialized to the canonical
  tensor-product base-change map `TensorProduct.isBaseChange R M R'`;
- primitive data vs derived API: the primitive data are the local map `R → R'`, the endomorphism
  `φ : Module.End R M`, and the canonical closed-fiber finite-length hypothesis; the determinant
  comparison theorem and the finite-length base-change consequence are derived API.
-/

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')] [Module.Flat R R']
variable [AddCommGroup M] [Module R M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) R'

namespace Module.End

-- Proof sketch: choose a composition series for `M`, base change it along the flat local
-- homomorphism `R → R'`, and apply multiplicativity of `finiteLengthDeterminant` to reduce to the
-- case of a simple object. In the simple case, identify the base change with
-- `R' ⧸ maximalIdeal R • R'` tensored over `ResidueField R`, filter the closed fiber by successive
-- quotients `ResidueField R'`, and finish with compatibility of ordinary determinants under field
-- extension. The finite-length hypothesis on the canonical closed fiber supplies the needed
-- finite-length statement for `R' ⊗[R] M` via Lemma `10.52.13`.
/-- Lemma 15.121.3: let `R → R'` be a flat local homomorphism of local rings, and let
`ClosedFiber = (maximalIdeal R).Fiber R'` have finite length over itself. For a finite-length
`R`-module endomorphism `φ`, the image of `det_κ(φ)` raised to the closed-fiber length equals the
determinant of the base-changed endomorphism on `R' ⊗[R] M`, which is Lean's model for the
textbook module `M ⊗_R R'`. -/
theorem finiteLengthDeterminant_baseChange_pow_closedFiberLength
    (φ : Module.End R M) (hM : IsFiniteLength R M)
    (hClosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    (ResidueField.map (algebraMap R R') (φ.finiteLengthDeterminant hM)) ^
        (Module.length ClosedFiber ClosedFiber).toNat =
      finiteLengthDeterminant ((TensorProduct.isBaseChange R M R').endHom φ)
        ((finite_length_iff_finite_length_base_change hClosedFiber).1 hM) := sorry

end Module.End

end
