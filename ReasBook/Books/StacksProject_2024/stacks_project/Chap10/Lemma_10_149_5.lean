import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra TensorProduct
open Algebra.Extension
open TensorProduct.AlgebraTensorModule

universe u v w x

namespace Algebra.Extension

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable (R) (P : Extension A B)

/- Domain-style sampling:
- primary domain: universal first-order thickenings, formal unramifiedness, and the
  Jacobi-Zariski/transitivity sequence for Kähler differentials over a tower `R → A → P.Ring → B`;
- sampled owner declarations:
  `Algebra.FormallyUnramified`,
  `Algebra.FormallyUnramified.iff_comp_injective`,
  `KaehlerDifferential.mapBaseChange`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`;
- best owner abstraction:
  part (1) is governed by the canonical owner predicate `FormallyUnramified A _`,
  while part (2) is governed by the owner map `KaehlerDifferential.mapBaseChange R A P.Ring`,
  further base changed along `P.Ring → B`;
- primitive data vs. derived API:
  the primitive data are the extension `P : Extension A B` and the universal first-order
  thickening hypothesis, while the tensor-reassociated comparison used below is only a thin
  auxiliary bridge/view of the owner `KaehlerDifferential.mapBaseChange`;
- source/core/bridge triage:
  `source-facing`: the formal-unramified consequence and the textbook isomorphism on the
    base-changed differential modules;
  `core/canonical`: `FormallyUnramified` and `KaehlerDifferential.mapBaseChange`;
  `bridge/view`: the tensor-order identification
    `B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`.

The previous local map definition rebuilt this bridge by hand with `rid`/`assoc`/`map`.
The canonical owner-level construction is the standard further base change of
`KaehlerDifferential.mapBaseChange` using `lTensor` and `cancelBaseChange`.
-/

/-- Lemma 10.149.5 (2), source-facing canonical map: after identifying the displayed textbook
comparison with the further base change of `KaehlerDifferential.mapBaseChange R A P.Ring` along
`P.Ring → B`, we obtain the canonical `B`-linear map
`B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`. -/
noncomputable def universalFirstOrderThickening_kaehlerBaseChangeLinearMap
    : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  lTensor B B (KaehlerDifferential.mapBaseChange R A P.Ring) ∘ₗ
    (cancelBaseChange A P.Ring B B Ω[A⁄R]).symm.toLinearMap

variable {R} {P}

-- Proof sketch: the universal lifting property gives uniqueness of lifts from `P.Ring` after
-- precomposing with `P.Ring → B`, so `Algebra.FormallyUnramified.iff_comp_injective` yields
-- `FormallyUnramified A P.Ring`.
/-- Lemma 10.149.5 (1): a universal first-order thickening `B'` of a formally unramified
`A`-algebra `B` is itself formally unramified over `A`. -/
theorem universalFirstOrderThickening_formallyUnramified
    (hP : P.IsUniversalFirstOrderThickening) [FormallyUnramified A B] :
    FormallyUnramified A P.Ring := sorry

variable (R) (P)

-- Proof sketch: use the canonical Jacobi-Zariski/transitivity maps for `R → A → P.Ring → B`.
-- The vanishing of `Ω[P.Ring⁄A]` from part (1) forces injectivity on the owner map
-- `KaehlerDifferential.mapBaseChange R A P.Ring`, and the displayed comparison is just its
-- further base change along `P.Ring → B`.
/-- Lemma 10.149.5 (2), companion owner-level statement: the canonical base-changed comparison map
on Kähler differentials attached to a universal first-order thickening is bijective. -/
theorem universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective
    (hP : P.IsUniversalFirstOrderThickening) [FormallyUnramified A B] :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P) := sorry

/-- Lemma 10.149.5 (2): in the library-facing tensor order, the canonical base-changed map
`B ⊗[A] Ω[A⁄R] → B ⊗[B'] Ω[B'⁄R]` attached to a universal first-order thickening `B'`
induces a `B`-linear isomorphism. -/
noncomputable def universalFirstOrderThickening_kaehlerBaseChange
    (hP : P.IsUniversalFirstOrderThickening) [FormallyUnramified A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  LinearEquiv.ofBijective
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P)
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective R P hP)

@[simp] theorem universalFirstOrderThickening_kaehlerBaseChange_toLinearMap
    (hP : P.IsUniversalFirstOrderThickening) [FormallyUnramified A B] :
    (universalFirstOrderThickening_kaehlerBaseChange R P hP).toLinearMap =
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P :=
  by
    ext x
    rfl

end Algebra.Extension
