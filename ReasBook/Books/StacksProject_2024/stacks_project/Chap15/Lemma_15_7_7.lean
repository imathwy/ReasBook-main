import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Situation_15_6_1
import StacksProject_2024.Chap15.Situation_15_7_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CommRingCat

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

-- Proof sketch: this is the descent statement for finite type in the fibre-product algebra
-- situation; the two directions are read off from base change along `B' → B` and `B' → A'` and
-- from the finite-generation construction in the textbook.
/-- Lemma 15.7.7 (1): the map `B' → D'` is of finite type if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are of finite type. -/
theorem baseChangeMap_finiteType_iff
    (S : Situation) :
    S.bprimeToDp.FiniteType ↔ S.bToD.FiniteType ∧ S.aprimeToCPrime.FiniteType := sorry

-- Proof sketch: the forward implication comes from base change preserving flatness, while the
-- reverse implication is the flatness part of the fibre-product descent argument for the tensor
-- square attached to `S`.
/-- Lemma 15.7.7 (2): the map `B' → D'` is flat if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are flat. -/
theorem baseChangeMap_flat_iff
    (S : Situation) :
    Module.Flat S.Bprime Dp ↔ Module.Flat B S.D ∧ Module.Flat A' S.CPrime := sorry

-- Proof sketch: combine the flatness equivalence from the previous clause with the finite-type
-- criterion and the finite-presentation descent statement already proved for fibre-product modules.
/-- Lemma 15.7.7 (3): the map `B' → D'` is flat and of finite presentation if and only if the two
base-changed maps `B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are flat and of finite
presentation. -/
theorem baseChangeMap_flat_finitePresentation_iff
    (S : Situation) :
    (S.bprimeToDp.Flat ∧ S.bprimeToDp.FinitePresentation) ↔
      (S.bToD.Flat ∧ S.bToD.FinitePresentation) ∧
        (S.aprimeToCPrime.Flat ∧ S.aprimeToCPrime.FinitePresentation) := sorry

-- Proof sketch: smoothness is equivalent to flatness plus finite presentation together with the
-- smoothness of fibres; the fibres of `B' → D'` identify with the corresponding fibres of the two
-- base changes exactly as in the textbook.
/-- Lemma 15.7.7 (4): the map `B' → D'` is smooth if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are smooth. -/
theorem baseChangeMap_smooth_iff
    (S : Situation) :
    S.bprimeToDp.Smooth ↔ S.bToD.Smooth ∧ S.aprimeToCPrime.Smooth := sorry

-- Proof sketch: an étale map is a smooth map with discrete fibres; after the fibre
-- identifications used in the smooth case, the étale criterion descends and ascends across the
-- fibre-product square.
/-- Lemma 15.7.7 (5): the map `B' → D'` is étale if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are étale. -/
theorem baseChangeMap_etale_iff
    (S : Situation) :
    S.bprimeToDp.Etale ↔ S.bToD.Etale ∧ S.aprimeToCPrime.Etale := sorry

-- Proof sketch: this is the flat descent identification of `D'` with the pullback of its two
-- scalar extensions along `B' → B` and `B' → A'`, now stated in `CommRingCat`.
/-- Lemma 15.7.7 (6): if `D'` is flat over `B'`, then the canonical map
`D' → (D' ⊗[B'] B) ×_{D' ⊗[B'] A} (D' ⊗[B'] A')`
is an isomorphism. -/
theorem tensorPullbackComparison_isIso_of_flat
    (S : Situation)
    [Module.Flat S.Bprime Dp] :
    IsIso S.tensorPullbackComparison := sorry

end FiberProductBaseChangeSituation

namespace SurjectiveRingPullbackSituation

local notation "Situation" => @SurjectiveRingPullbackSituation B A A' _ _ _

/-- The object property on `Under (B')` selecting flat `B'`-algebras. -/
abbrev flatAlgebraProperty
    (S : Situation) :
    ObjectProperty (Under S.Bprime) :=
  fun D' ↦ Module.Flat S.Bprime D'

/-- The full subcategory of flat algebras over the fibre-product ring `B' = B ×_A A'`. -/
abbrev FlatAlgebraCat
    (S : Situation) :=
  (flatAlgebraProperty S).FullSubcategory

/-- The category of systems `(D, C', \varphi)` consisting of a `B`-algebra, an `A'`-algebra, and
an isomorphism between their two base changes to `A`. -/
abbrev algebraSystemCategory
    (S : Situation) :=
  let _ : Algebra B A := S.toA.toAlgebra
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  CategoricalPullback
    (Under.pushout (CommRingCat.ofHom S.toA))
    (Under.pushout (CommRingCat.ofHom S.fromAprime))

/-- The first component of an algebra system carries its canonical `B`-algebra structure. -/
private noncomputable instance instAlgebraSystemFst
    (S : Situation) (X : algebraSystemCategory S) : Algebra B X.fst := by
  rcases X.fst with ⟨_, _, f⟩
  exact f.hom.toAlgebra

/-- The second component of an algebra system carries its canonical `A'`-algebra structure. -/
private noncomputable instance instAlgebraSystemSnd
    (S : Situation) (X : algebraSystemCategory S) : Algebra A' X.snd := by
  rcases X.snd with ⟨_, _, f⟩
  exact f.hom.toAlgebra

/-- The object property on algebra systems requiring flatness of the `B`-algebra component and of
the `A'`-algebra component. -/
abbrev flatAlgebraSystemProperty
    (S : Situation) :
    ObjectProperty (algebraSystemCategory S) :=
  fun X ↦
    Module.Flat B X.fst ∧ Module.Flat A' X.snd

/-- The full subcategory of algebra systems `(D, C', \varphi)` with `D` flat over `B` and `C'`
flat over `A'`. -/
abbrev FlatAlgebraSystemCat
    (S : Situation) :=
  (flatAlgebraSystemProperty S).FullSubcategory

/-- The comparison isomorphism between the two ways of pushing a `B'`-algebra forward to an
`A`-algebra through the pullback square `B' → B`, `B' → A'`, `B → A`, `A' → A`. -/
noncomputable def algebraBaseChangeComparison
    (S : Situation) :
    let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
    let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
    Under.pushout bprimeToB ⋙ Under.pushout (ofHom S.toA) ≅
      Under.pushout bprimeToAprime ⋙ Under.pushout (ofHom S.fromAprime) :=
  let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
  let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
  let hcomm : bprimeToB ≫ ofHom S.toA = bprimeToAprime ≫ ofHom S.fromAprime := by
    simpa using congrArg ofHom S.comm
  (Under.pushoutComp bprimeToB (ofHom S.toA)).symm ≪≫
    eqToIso (congrArg (fun f ↦ Under.pushout f) hcomm) ≪≫
    Under.pushoutComp bprimeToAprime (ofHom S.fromAprime)

/-- The categorical square of pushout functors from `B'`-algebras to `B`-algebras and
`A'`-algebras attached to the pullback square `B' = B ×_A A'`. -/
noncomputable def algebraBaseChangeSquare
    (S : Situation) :
    CategoricalPullback.CatCommSqOver
      (Under.pushout (ofHom S.toA))
      (Under.pushout (ofHom S.fromAprime))
      (Under S.Bprime) where
  fst := Under.pushout (ofHom S.bprimeToB)
  snd := Under.pushout (ofHom S.bprimeToAprime)
  iso := algebraBaseChangeComparison S

/-- The canonical functor sending a `B'`-algebra to the corresponding system
`(D, C', \varphi)` of its two pushouts to `B` and `A'` together with the induced isomorphism after
base change to `A`. -/
noncomputable def algebraBaseChangeFunctor
    (S : Situation) :
    Under S.Bprime ⥤ algebraSystemCategory S :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Under.pushout (ofHom S.toA))
    (Under.pushout (ofHom S.fromAprime))
    (Under S.Bprime)).obj
    (algebraBaseChangeSquare S)

-- Proof sketch: pushout of commutative rings is tensor product, and tensoring a flat `B'`-algebra
-- with `B` or `A'` preserves flatness over the new base ring. Hence the canonical base-change
-- system attached to a flat `B'`-algebra lies in the flat full subcategory.
/-- Base change from `B'`-algebras to algebra systems preserves flatness of the two components. -/
theorem algebraBaseChange_obj_mem_flatAlgebraSystemProperty
    (S : Situation)
    ⦃D' : Under S.Bprime⦄
    (hflat : flatAlgebraProperty S D') :
    flatAlgebraSystemProperty S ((algebraBaseChangeFunctor S).obj D') := sorry

/-- The canonical base-change functor on the full subcategory of flat `B'`-algebras. -/
noncomputable abbrev flatAlgebraBaseChangeFunctor
    (S : Situation) :
    FlatAlgebraCat S ⥤ FlatAlgebraSystemCat S :=
  (flatAlgebraSystemProperty S).lift
    ((flatAlgebraProperty S).ι ⋙ algebraBaseChangeFunctor S)
    (fun D' ↦ algebraBaseChange_obj_mem_flatAlgebraSystemProperty S D'.property)

-- Proof sketch: the canonical base-change construction sends a flat `B'`-algebra `D'` to the
-- system `(D' ⊗[B'] B, D' ⊗[B'] A', \varphi)`, while the previous clause identifies a flat
-- `B'`-algebra with the pullback of such a flat system. This gives the equivalence of categories
-- described in the textbook.
/-- Lemma 15.7.7 (7): the category of flat `B'`-algebras is equivalent to the category of systems
`(D, C', \varphi)` with `D` a flat `B`-algebra, `C'` a flat `A'`-algebra, and
`D ⊗[B] A ≅ A ⊗[A'] C'`. -/
theorem flatAlgebraBaseChangeFunctor_isEquivalence
    (S : Situation) :
    Functor.IsEquivalence (flatAlgebraBaseChangeFunctor S) := sorry

end SurjectiveRingPullbackSituation

end
