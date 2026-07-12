import StacksProject_2024.Chap22.Lemma_22_31_2
import StacksProject_2024.Chap22.Lemma_22_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u v w

section

open scoped DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {DGModA : Type v} {DGModB : Type w}
variable [DifferentialGradedCategory R DGModA] [DifferentialGradedCategory R DGModB]

variable (QisA : MorphismProperty (K R DGModA))
variable (QisB : MorphismProperty (K R DGModB))
variable [QisA.IsSaturatedMultiplicativeSystem]
variable [QisB.IsSaturatedMultiplicativeSystem]
variable (tensorWithN : DgFunctor R DGModA DGModB)
variable (homOverBFromN : DgFunctor R DGModB DGModA)
variable [(tensorWithN.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
variable [(homOverBFromN.mapK ⋙ QisA.Q).HasRightDerivedFunctor QisB]

local notation "derivedTensorWithN" => LTensor[QisA, QisB](tensorWithN)
local notation "derivedHomFromN" => RHom[QisB, QisA](homOverBFromN)

-- Semantic recall hits: `Adjunction.derived`, `Adjunction.isLeftAdjoint`,
-- `Adjunction.isRightAdjoint`, `Functor.totalLeftDerived`, and
-- `Functor.totalRightDerived`.

/-- Lemma 22.33.5: let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded
`R`-algebras, and let `N` be a differential graded `(A, B)`-bimodule. The derived tensor functor
`- ⊗_A^L N : D(A, d) ⥤ D(B, d)` from Lemma `22.33.2` is left adjoint to the
right-derived internal-Hom functor `RHom(N, -) : D(B, d) ⥤ D(A, d)` from Lemma `22.31.2`.

In the current checked Chapter 22 API the underived tensor and internal-Hom functors are represented
on homotopy categories by `tensorWithN.mapK` and `homOverBFromN.mapK`; the hypothesis `underivedAdj`
is the adjunction coming from Lemma `22.30.3`. The proof uses the canonical owner
`CategoryTheory.Adjunction.derived` only as a proof-local witness, while the public result stays
proposition-valued so the file does not export sorry-backed unit/counit data. -/
@[stacks 09LT]
theorem derivedTensorWithN_leftAdjoint_and_derivedHomFromN_rightAdjoint
    (underivedAdj :
      tensorWithN.mapK ⊣ homOverBFromN.mapK) :
    Functor.IsLeftAdjoint derivedTensorWithN ∧
      Functor.IsRightAdjoint derivedHomFromN := by
  letI :
      (derivedTensorWithN ⋙ derivedHomFromN).IsLeftDerivedFunctor
        ((QisA.Q.associator derivedTensorWithN derivedHomFromN).inv ≫
          Functor.whiskerRight
            ((tensorWithN.mapK ⋙ QisB.Q).totalLeftDerivedCounit QisA.Q QisA)
            derivedHomFromN)
        QisA := by
    sorry
  letI :
      (derivedHomFromN ⋙ derivedTensorWithN).IsRightDerivedFunctor
        (Functor.whiskerRight
            ((homOverBFromN.mapK ⋙ QisA.Q).totalRightDerivedUnit QisB.Q QisB)
            derivedTensorWithN ≫
          (QisB.Q.associator derivedHomFromN derivedTensorWithN).hom)
        QisB := by
    sorry
  refine ⟨?_, ?_⟩
  · exact
      (Adjunction.derived
        underivedAdj
        QisA
        QisB
        ((tensorWithN.mapK ⋙ QisB.Q).totalLeftDerivedCounit QisA.Q QisA)
        ((homOverBFromN.mapK ⋙ QisA.Q).totalRightDerivedUnit QisB.Q QisB)).isLeftAdjoint
  · exact
      (Adjunction.derived
        underivedAdj
        QisA
        QisB
        ((tensorWithN.mapK ⋙ QisB.Q).totalLeftDerivedCounit QisA.Q QisA)
        ((homOverBFromN.mapK ⋙ QisA.Q).totalRightDerivedUnit QisB.Q QisB)).isRightAdjoint

/-- Companion theorem: the derived tensor functor from Lemma `22.33.2` is a left adjoint once the
underived DG tensor/Hom adjunction is fixed. -/
theorem derivedTensorWithN_isLeftAdjoint
    (underivedAdj : tensorWithN.mapK ⊣ homOverBFromN.mapK) :
    Functor.IsLeftAdjoint derivedTensorWithN :=
  (derivedTensorWithN_leftAdjoint_and_derivedHomFromN_rightAdjoint
    QisA QisB tensorWithN homOverBFromN underivedAdj).1

/-- Companion theorem: the derived internal-Hom functor from Lemma `22.33.5` is a right adjoint
once the underived DG tensor/Hom adjunction is fixed. -/
theorem derivedHomFromN_isRightAdjoint
    (underivedAdj : tensorWithN.mapK ⊣ homOverBFromN.mapK) :
    Functor.IsRightAdjoint derivedHomFromN :=
  (derivedTensorWithN_leftAdjoint_and_derivedHomFromN_rightAdjoint
    QisA QisB tensorWithN homOverBFromN underivedAdj).2

end
