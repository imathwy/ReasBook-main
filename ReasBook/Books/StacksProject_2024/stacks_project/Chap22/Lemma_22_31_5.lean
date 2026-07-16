import StacksProject_2024.stacks_project.Chap22.Lemma_22_20_2
import StacksProject_2024.stacks_project.Chap22.Lemma_22_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open DifferentialGradedCategory

noncomputable section

universe u v w

section DerivedHom

open scoped DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable (QisB : MorphismProperty (K R DGModB)) [QisB.IsSaturatedMultiplicativeSystem]
variable (QisA : MorphismProperty (K R DGModA)) [QisA.IsSaturatedMultiplicativeSystem]
variable (homOverBFromN : DgFunctor R DGModB DGModA)
variable [(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]

local notation "homToDerived" => (homOverBFromN.mapK ⋙ QisA.Q)

-- Semantic recall hits: `Localization.lift`, `Functor.totalRightDerived`, and
-- `Functor.isRightDerivedFunctor_of_inverts`. Local Chapter 22 precedent represents the
-- internal-Hom functor attached to `N` by `homOverBFromN.mapK`.

omit [QisB.IsSaturatedMultiplicativeSystem] [QisA.IsSaturatedMultiplicativeSystem]
  [(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB] in
private theorem underivedHomLift_isRightDerivedFunctor
    (hHom_inverts : QisB.IsInvertedBy homToDerived) :
    (Localization.lift homToDerived hHom_inverts QisB.Q).IsRightDerivedFunctor
      (Localization.fac homToDerived hHom_inverts QisB.Q).inv
      QisB := by
  simpa using
    (Functor.isRightDerivedFunctor_of_inverts
      QisB
      (Localization.lift homToDerived hHom_inverts QisB.Q)
      (Localization.fac homToDerived hHom_inverts QisB.Q))

/-- Lemma 22.31.5 (1): if the represented internal-Hom functor attached to a differential
graded `(A, B)`-bimodule `N` sends quasi-isomorphisms in `K(Mod_(B,d))` to isomorphisms after
localizing the target, then the total right derived functor `RHom(N, -)` is naturally
isomorphic to the functor on `D(B,d)` obtained by descending the underived Hom functor
`Hom_{Mod^{dg}_{(B,d)}}(N, -)`. -/
@[stacks 0BYW]
noncomputable def derivedHom_iso_underivedHom_of_inverts_quasiIso
    (hHom_inverts :
      QisB.IsInvertedBy homToDerived) :
    RHom[QisB, QisA](homOverBFromN) ≅
      (Localization.lift homToDerived hHom_inverts QisB.Q : QisB.Localization ⥤
        QisA.Localization) :=
  let _ :
      (Localization.lift homToDerived hHom_inverts QisB.Q).IsRightDerivedFunctor
        (Localization.fac homToDerived hHom_inverts QisB.Q).inv
        QisB :=
    underivedHomLift_isRightDerivedFunctor QisB QisA homOverBFromN hHom_inverts
  (RHom[QisB, QisA](homOverBFromN)).rightDerivedUnique
    (Localization.lift homToDerived hHom_inverts QisB.Q)
    ((homOverBFromN.mapK ⋙ QisA.Q).totalRightDerivedUnit QisB.Q QisB)
    (Localization.fac homToDerived hHom_inverts QisB.Q).inv
    QisB

end DerivedHom

namespace CochainComplex

open ComplexShape
open DerivedCategory
open HomotopyCategory

attribute [local instance] HasDerivedCategory.standard

universe u'

variable {B : Type u'} [Ring B]

local notation "KQ" => HomotopyCategory.quotient (ModuleCat B) (up ℤ)

/-- Lemma 22.31.5 (2): the source hypothesis
`Hom_{D(B,d)}(N, N') = Hom_{K(Mod_(B,d))}(N, N')` holds for every target `N'` when `N` has
property `(P)` as a differential graded `B`-module. In the canonical cochain-complex model this
is the bijectivity of the localization map on morphisms out of `N`. -/
@[stacks 0BYW]
theorem homotopyToDerivedHom_bijective_of_hasPropertyP
    (N N' : CochainComplex (ModuleCat.{u', u'} B) ℤ) (hN : HasPropertyP N) :
    Function.Bijective
      (DerivedCategory.Qh.map : ((KQ).obj N ⟶ (KQ).obj N') → _) := by
  let _ : Fact (HasPropertyP N) := ⟨hN⟩
  simpa using
    IsKProjective.Qh_map_bijective N ((KQ).obj N')

end CochainComplex
