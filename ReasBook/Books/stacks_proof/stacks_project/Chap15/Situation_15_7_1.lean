import stacks_proof.stacks_project.Chap15.Situation_15_6_1
import stacks_proof.stacks_project.Chap15.«15_6_3_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped TensorProduct

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

/-
Domain-style sampling for 15.7.1:
- primary domain: fibre-product base change for commutative rings and the induced categorical
  pullback of module categories;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `moduleCatBaseChangeSquare`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `CategoricalPullback`;
- best owner abstractions: the pullback data is owned by
  `SurjectiveRingPullbackSituation`, while the categorical module-theoretic square is owned by
  `moduleCatBaseChangeSquare`;
- primitive data: a surjective pullback situation together with a ring map `B' → D'`;
- derived API: the tensor-product rings `D`, `C'`, `C`, their canonical structure maps, the
  commutative tensor square, the specialized owner square in `CatCommSqOver`, and the induced
  pullback functor on module categories obtained from that owner.

Source/core/bridge triage:
- `source-facing`: `FiberProductBaseChangeSituation`;
- `core/canonical`: `SurjectiveRingPullbackSituation` and `moduleCatBaseChangeSquare`;
- `bridge/view`: the specialized owner square `toModuleCatBaseChangeSquare`, together with the
  induced functor to `CategoricalPullback`. -/

/-- Situation 15.7.1: a pullback square of commutative rings `B' → B`, `B' → A'`, `B → A`,
`A' → A` as in Situation 15.6.1, together with a ring map `B' → D'`, yielding the base-changed
rings `D = D' ⊗[B'] B`, `C' = D' ⊗[B'] A'`, and `C = D' ⊗[B'] A`. -/
@[stacks 08KK]
structure FiberProductBaseChangeSituation extends SurjectiveRingPullbackSituation B A A' where
  /-- The map `B' → D'` used for base change. -/
  bprimeToDp : toSurjectiveRingPullbackSituation.Bprime →+* Dp

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

instance instAlgebraBprimeDp (S : Situation) : Algebra S.Bprime Dp :=
  S.bprimeToDp.toAlgebra

instance instAlgebraBprimeB (S : Situation) : Algebra S.Bprime B :=
  S.bprimeToB.toAlgebra

instance instAlgebraBprimeAprime (S : Situation) : Algebra S.Bprime A' :=
  S.bprimeToAprime.toAlgebra

instance instAlgebraBprimeA (S : Situation) : Algebra S.Bprime A :=
  (S.fromAprime.comp S.bprimeToAprime).toAlgebra

-- Proof sketch: the algebra maps `B' → B → A` and `B' → A` agree by the commutativity field
-- `S.comm`, so the scalar-tower condition is exactly the commuting-square hypothesis.
/-- The maps `B' → B → A` form an algebra tower. -/
private theorem bprime_B_A_isScalarTower
    (S : Situation) :
    let _ : Algebra B A := S.toA.toAlgebra
    IsScalarTower S.Bprime B A := sorry

-- Proof sketch: the chosen algebra map `B' → A` is already the composite `B' → A' → A`, so the
-- scalar-tower compatibility follows from the base-change algebra structures.
/-- The maps `B' → A' → A` form an algebra tower. -/
private theorem bprime_Aprime_A_isScalarTower
    (S : Situation) :
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    IsScalarTower S.Bprime A' A := sorry

/-- The ring `D = D' ⊗[B'] B` attached to a fibre-product base-change situation. -/
abbrev D (S : Situation) :
    Type u :=
  Dp ⊗[S.Bprime] B

/-- The ring `C' = D' ⊗[B'] A'` attached to a fibre-product base-change situation. -/
abbrev CPrime (S : Situation) :
    Type u :=
  Dp ⊗[S.Bprime] A'

/-- The ring `C = D' ⊗[B'] A` attached to a fibre-product base-change situation. -/
abbrev C (S : Situation) :
    Type u :=
  Dp ⊗[S.Bprime] A

noncomputable instance instAlgebraD (S : Situation) : Algebra B S.D := by
  change Algebra B (Dp ⊗[S.Bprime] B)
  exact Algebra.TensorProduct.rightAlgebra

noncomputable instance instAlgebraCPrime (S : Situation) : Algebra A' S.CPrime := by
  change Algebra A' (Dp ⊗[S.Bprime] A')
  exact Algebra.TensorProduct.rightAlgebra

/-- The canonical ring map `D' → D = D' ⊗[B'] B`. -/
abbrev dprimeToD (S : Situation) :
    Dp →+* S.D :=
  (Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom

/-- The canonical ring map `D' → C' = D' ⊗[B'] A'`. -/
abbrev dprimeToCPrime (S : Situation) :
    Dp →+* S.CPrime :=
  (Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom

/-- The canonical ring map `B → D = D' ⊗[B'] B`. -/
abbrev bToD (S : Situation) :
    B →+* S.D :=
  (Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom

/-- The canonical ring map `A' → C' = D' ⊗[B'] A'`. -/
abbrev aprimeToCPrime (S : Situation) :
    A' →+* S.CPrime :=
  (Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom

/-- The canonical ring map `D = D' ⊗[B'] B → C = D' ⊗[B'] A` induced by `B → A`. -/
abbrev dToC (S : Situation) :
    S.D →+* S.C :=
  let _ : Algebra B A := S.toA.toAlgebra
  let _ : IsScalarTower S.Bprime B A := bprime_B_A_isScalarTower S
  (Algebra.TensorProduct.map (AlgHom.id S.Bprime Dp) (IsScalarTower.toAlgHom S.Bprime B A)).toRingHom

/-- The canonical ring map `C' = D' ⊗[B'] A' → C = D' ⊗[B'] A` induced by `A' → A`. -/
abbrev cprimeToC (S : Situation) :
    S.CPrime →+* S.C :=
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  let _ : IsScalarTower S.Bprime A' A := bprime_Aprime_A_isScalarTower S
  (Algebra.TensorProduct.map (AlgHom.id S.Bprime Dp) (IsScalarTower.toAlgHom S.Bprime A' A)).toRingHom

-- Proof sketch: both composites are the canonical map from `D'` into `D' ⊗[B'] A`; one route uses
-- the morphism induced from `B → A`, and the other uses the morphism induced from `A' → A`. The
-- two coincide because the original square over `A` is commutative.
/-- The tensor-product square `D' → D`, `D' → C'`, `D → C`, `C' → C` as a commutative square in
`CommRingCat`. -/
theorem tensorSquare
    (S : Situation) :
    CommSq
      (CommRingCat.ofHom S.dprimeToD)
      (CommRingCat.ofHom S.dprimeToCPrime)
      (CommRingCat.ofHom S.dToC)
      (CommRingCat.ofHom S.cprimeToC) := by
  refine CommSq.mk ?_
  sorry

/-- The underlying ring-hom equality of `S.tensorSquare`. -/
theorem tensor_square_commutes
    (S : Situation) :
    S.dToC.comp S.dprimeToD = S.cprimeToC.comp S.dprimeToCPrime := by
  simpa using congrArg CommRingCat.Hom.hom (S.tensorSquare.w)

/-- The canonical comparison map from `D'` to the pullback of
`D = D' ⊗[B'] B → C = D' ⊗[B'] A ← D' ⊗[B'] A' = C'` attached to the tensor square of `S`. -/
noncomputable def tensorPullbackComparison
    (S : Situation) :
    CommRingCat.of Dp ⟶ pullback (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) :=
  pullback.lift
    (CommRingCat.ofHom S.dprimeToD)
    (CommRingCat.ofHom S.dprimeToCPrime)
    (by simpa using S.tensorSquare.w)

/-- The specialized module-category base-change square attached to the tensor square of
`S`. -/
noncomputable abbrev toModuleCatBaseChangeSquare
    (S : Situation) :
    CatCommSqOver (ModuleCat.extendScalars S.dToC) (ModuleCat.extendScalars S.cprimeToC)
      (ModuleCat Dp) :=
  moduleCatBaseChangeSquare
    S.dToC
    S.cprimeToC
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/-- The categorical pullback `Mod_D ×_[Mod_C] Mod_{C'}` attached to the tensor square of a
fibre-product base-change situation. -/
abbrev relativeModuleCategory (S : Situation) :=
  CategoricalPullback (ModuleCat.extendScalars S.dToC) (ModuleCat.extendScalars S.cprimeToC)

/-- The canonical functor `Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}` attached to the tensor square of a
fibre-product base-change situation. -/
noncomputable abbrev relativeModuleFunctor (S : Situation) :
    ModuleCat Dp ⥤ S.relativeModuleCategory :=
  moduleCatBaseChangeToCategoricalPullback
    S.dToC
    S.cprimeToC
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

end FiberProductBaseChangeSituation

end
