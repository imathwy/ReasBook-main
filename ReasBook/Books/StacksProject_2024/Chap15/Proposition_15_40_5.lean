import Mathlib
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Proposition 15.40.5:
- primary domain: local commutative algebra of Noetherian local ring maps and their closed fibers;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.Flat`;
- best owner abstraction: the special fiber is canonically owned by
  `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, while the tensor product presentation
  `ResidueField A ⊗[A] B` is only a bridge view;
- primitive data: the local map `A → B`, its flatness, the closed fiber `ClosedFiber`, and the
  adic ideal `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`;
- derived API: geometric regularity and adic formal smoothness of `ClosedFiber`.

Source/core/bridge triage:
- `source-facing`: the three-way equivalence in Proposition 15.40.5;
- `core/canonical`: `Ideal.Fiber`, `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`, and `RingHom.Flat`;
- `bridge/view`: the tensor-product presentation `ResidueField A ⊗[A] B` of `ClosedFiber`.
-/
-- Proof sketch: `(1) ↔ (2)` is Theorem `15.40.1` applied to the special fiber `κ(A) ⊗[A] B`.
-- The implication `(3) → (2)` combines flatness from Lemma `15.40.3` with base change of adic
-- formal smoothness along `A → κ(A)` from Lemma `15.37.8`. For `(2) → (3)`, pass to completions,
-- choose Cohen presentations as in Lemma `15.39.3`, identify the completed base change with `B`,
-- and then run the same derivation-splitting argument as in the proof of Theorem `15.40.1`.
/-- Proposition 15.40.5: for a local homomorphism `A → B` of Noetherian local rings with special
fiber `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, canonically presented by `κ(A) ⊗[A] B`,
the following are equivalent: `A → B` is flat and `ClosedFiber` is geometrically regular over
`κ(A)`; `A → B` is flat and `κ(A) → ClosedFiber` is formally smooth for the adic topology defined
by `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`; and `A → B` is
formally smooth for the `maximalIdeal B`-adic topology. -/
theorem flat_geometricallyRegularSpecialFiber_formallySmooth_tfae :
    List.TFAE [
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end
