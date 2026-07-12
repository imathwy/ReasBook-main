import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap22.Lemma_22_31_2
import StacksProject_2024.Chap22.Lemma_22_33_2

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

noncomputable section

universe u v w

section

open scoped DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable (QisB : MorphismProperty (K R DGModB)) [QisB.IsSaturatedMultiplicativeSystem]
variable (QisA : MorphismProperty (K R DGModA)) [QisA.IsSaturatedMultiplicativeSystem]
variable [Preadditive QisB.Localization] [HasCoproducts QisB.Localization]

/-- Lemma 22.33.9 (1): let `T` be a compact object of `D(B, d)`, let `homFromT` be the chosen
DG internal-Hom functor whose derived functor models `RHom(T, -)`, and let `S` be a DG object
representing `RHom(T, B)` in `D(A, d)`. Then `S` admits a tensor-by-`S` DG functor whose left
derived functor evaluates at `B` to the represented object.

In the current Chapter `22` API, the compact object is recorded as
`T : D_c(QisB.Localization)`, the chosen model of `RHom(T, -)` is the right-derived functor
`RHom[QisB, QisA](homFromT)`, and the source-facing relation to `T` is expressed by a chosen
derived tensor functor `derivedTensorWithT`, a regular object `Aunit`, an adjunction
`derivedTensorWithT ⊣ RHom[QisB, QisA](homFromT)`, and an identification
`derivedTensorWithT.obj Aunit ≅ T.obj`. The representing-object hypothesis is the isomorphism
`QisA.Q.obj S ≅ (RHom[QisB, QisA](homFromT)).obj (QisB.Q.obj B)`. -/
@[stacks 0BZ0]
theorem exists_tensorWithRepresentingObject
    (T : D_c(QisB.Localization))
    (Aunit : QisA.Localization)
    (derivedTensorWithT : QisA.Localization ⥤ QisB.Localization)
    (B : K R DGModB) (S : K R DGModA)
    (homFromT : DgFunctor R DGModB DGModA)
    [(homFromT.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]
    (hAdj : derivedTensorWithT ⊣ RHom[QisB, QisA](homFromT))
    (hTensorUnit : derivedTensorWithT.obj Aunit ≅ T.obj)
    (hRep : QisA.Q.obj S ≅ (RHom[QisB, QisA](homFromT)).obj (QisB.Q.obj B)) :
    ∃ tensorWithS : DgFunctor R DGModB DGModA,
      ∃ hLeft : (tensorWithS.mapK ⋙ QisA.Q).HasLeftDerivedFunctor QisB,
        letI : (tensorWithS.mapK ⋙ QisA.Q).HasLeftDerivedFunctor QisB := hLeft
        ∃ evaluationIso :
            (LTensor[QisB, QisA](tensorWithS)).obj (QisB.Q.obj B) ⟶ QisA.Q.obj S,
          IsIso evaluationIso := by
  sorry

/-- Lemma 22.33.9 (2): under the same hypotheses, there is a functorial isomorphism
`- ⊗_B^L S ≅ RHom(T, -)`.

Here the current Chapter `22` canonical owners are used directly: the left-derived tensor functor
attached to the representing object is `LTensor[QisB, QisA](tensorWithS)`, while
`RHom[QisB, QisA](homFromT)` is tied to the compact object `T : D_c(QisB.Localization)` by the
chosen adjunction `derivedTensorWithT ⊣ RHom[QisB, QisA](homFromT)` and the unit-object
identification `derivedTensorWithT.obj Aunit ≅ T.obj`. -/
@[stacks 0BZ0]
theorem exists_functorial_derivedTensorWithRepresentingObjectIso
    (T : D_c(QisB.Localization))
    (Aunit : QisA.Localization)
    (derivedTensorWithT : QisA.Localization ⥤ QisB.Localization)
    (B : K R DGModB) (S : K R DGModA)
    (homFromT : DgFunctor R DGModB DGModA)
    [(homFromT.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]
    (hAdj : derivedTensorWithT ⊣ RHom[QisB, QisA](homFromT))
    (hTensorUnit : derivedTensorWithT.obj Aunit ≅ T.obj)
    (hRep : QisA.Q.obj S ≅ (RHom[QisB, QisA](homFromT)).obj (QisB.Q.obj B)) :
    ∃ tensorWithS : DgFunctor R DGModB DGModA,
      ∃ hLeft : (tensorWithS.mapK ⋙ QisA.Q).HasLeftDerivedFunctor QisB,
        letI : (tensorWithS.mapK ⋙ QisA.Q).HasLeftDerivedFunctor QisB := hLeft
        ∃ derivedIso : LTensor[QisB, QisA](tensorWithS) ⟶ RHom[QisB, QisA](homFromT),
          IsIso derivedIso := by
  sorry

end
