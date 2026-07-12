import StacksProject_2024.Chap22.Lemma_22_32_1
import StacksProject_2024.Chap22.Lemma_22_35_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped CategoryTheory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {DGModE : Type v} {ComplexdgO : Type w}
variable [DifferentialGradedCategory R DGModE]
variable [DifferentialGradedCategory R ComplexdgO]

variable [HasShift (K R DGModE) ℤ] [HasShift (K R ComplexdgO) ℤ]
variable [HasZeroObject (K R DGModE)] [HasZeroObject (K R ComplexdgO)]
variable [Preadditive (K R DGModE)] [Preadditive (K R ComplexdgO)]
variable [∀ n : ℤ, (shiftFunctor (K R DGModE) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R ComplexdgO) n).Additive]
variable [Pretriangulated (K R DGModE)] [Pretriangulated (K R ComplexdgO)]

variable (QisE : MorphismProperty (K R DGModE))
variable (QisO : MorphismProperty (K R ComplexdgO))
variable [QisE.IsSaturatedMultiplicativeSystem]
variable [QisO.IsSaturatedMultiplicativeSystem]
variable (tensorWithK : DgFunctor R DGModE ComplexdgO)
variable (homFromK : K R ComplexdgO ⥤ K R DGModE)
variable [(tensorWithK.mapK ⋙ QisO.Q).HasPointwiseLeftDerivedFunctor QisE]
variable [(homFromK ⋙ QisE.Q).HasRightDerivedFunctor QisO]

local notation "derivedTensorWithK" => LTensor[QisE, QisO](tensorWithK)
local notation "derivedHomFromK" => RHom[QisO.Q, QisO](homFromK ⋙ QisE.Q)

-- Semantic recall hits: `Adjunction.derived`, `Adjunction.isLeftAdjoint`,
-- `Adjunction.isRightAdjoint`, `Functor.totalLeftDerived`, and the Chapter `22`
-- owner `CategoryTheory.derivedHom`. The source-facing output stays the derived
-- tensor/Hom adjunction, but we keep the public API at the proposition level
-- because the concrete `Adjunction.derived` witness would otherwise export
-- sorry-backed unit/counit data as public non-Prop data.

omit [HasShift (K R DGModE) ℤ] [HasShift (K R ComplexdgO) ℤ]
  [HasZeroObject (K R DGModE)] [HasZeroObject (K R ComplexdgO)]
  [Preadditive (K R DGModE)] [Preadditive (K R ComplexdgO)]
  [∀ n : ℤ, (shiftFunctor (K R DGModE) n).Additive]
  [∀ n : ℤ, (shiftFunctor (K R ComplexdgO) n).Additive]
  [Pretriangulated (K R DGModE)] [Pretriangulated (K R ComplexdgO)]
  [QisO.IsSaturatedMultiplicativeSystem] in
/-- Lemma 22.35.5: for a ringed site and a complex `K^•` of `𝒪`-modules, the canonical derived
tensor functor `- ⊗_E^L K^• : D(E, d) ⥤ D(𝒪)` from Lemma `22.35.3` is a left adjoint to the
canonical right-derived internal-Hom functor `RHom(K^•, -) : D(𝒪) ⥤ D(E, d)` from
Lemma `22.32.1`.

In the current checked Chapter 22 API the underlying tensor and Hom constructions are represented
by the induced homotopy-category functors `tensorWithK.mapK` and `homFromK`; the hypothesis
`underivedAdj` is the DG tensor/Hom adjunction before localization. The proof uses the canonical
owner `CategoryTheory.Adjunction.derived` internally, but the public output stays proposition-valued
so the file does not export sorry-backed unit/counit data. -/
@[stacks 09LY]
theorem derivedTensorWithK_leftAdjoint_and_derivedHomFromK_rightAdjoint
    (underivedAdj : tensorWithK.mapK ⊣ homFromK) :
    Functor.IsLeftAdjoint derivedTensorWithK ∧
      Functor.IsRightAdjoint derivedHomFromK := by
  letI :
      (derivedTensorWithK ⋙ derivedHomFromK).IsLeftDerivedFunctor
        ((QisE.Q.associator derivedTensorWithK derivedHomFromK).inv ≫
          Functor.whiskerRight
            ((tensorWithK.mapK ⋙ QisO.Q).totalLeftDerivedCounit QisE.Q QisE)
            derivedHomFromK)
        QisE := by
    sorry
  letI :
      (derivedHomFromK ⋙ derivedTensorWithK).IsRightDerivedFunctor
        (Functor.whiskerRight
            (derivedHomUnit QisO.Q QisO
              (homFromK ⋙ QisE.Q : K R ComplexdgO ⥤ QisE.Localization))
            derivedTensorWithK ≫
          (QisO.Q.associator derivedHomFromK derivedTensorWithK).hom)
        QisO := by
    sorry
  let hAdj : derivedTensorWithK ⊣ derivedHomFromK :=
    Adjunction.derived
      underivedAdj
      QisE
      QisO
      ((tensorWithK.mapK ⋙ QisO.Q).totalLeftDerivedCounit QisE.Q QisE)
      (derivedHomUnit QisO.Q QisO
        (homFromK ⋙ QisE.Q : K R ComplexdgO ⥤ QisE.Localization))
  exact ⟨hAdj.isLeftAdjoint, hAdj.isRightAdjoint⟩

omit [HasShift (K R DGModE) ℤ] [HasShift (K R ComplexdgO) ℤ]
  [HasZeroObject (K R DGModE)] [HasZeroObject (K R ComplexdgO)]
  [Preadditive (K R DGModE)] [Preadditive (K R ComplexdgO)]
  [∀ n : ℤ, (shiftFunctor (K R DGModE) n).Additive]
  [∀ n : ℤ, (shiftFunctor (K R ComplexdgO) n).Additive]
  [Pretriangulated (K R DGModE)] [Pretriangulated (K R ComplexdgO)]
  [QisO.IsSaturatedMultiplicativeSystem] in
/-- Lemma `22.35.5`: the derived tensor functor from Lemma `22.35.3` is a left adjoint once the
underived DG tensor/Hom adjunction is fixed. -/
theorem derivedTensorWithK_isLeftAdjoint
    (underivedAdj : tensorWithK.mapK ⊣ homFromK) :
    Functor.IsLeftAdjoint derivedTensorWithK :=
  (derivedTensorWithK_leftAdjoint_and_derivedHomFromK_rightAdjoint
    QisE QisO tensorWithK homFromK underivedAdj).1

omit [HasShift (K R DGModE) ℤ] [HasShift (K R ComplexdgO) ℤ]
  [HasZeroObject (K R DGModE)] [HasZeroObject (K R ComplexdgO)]
  [Preadditive (K R DGModE)] [Preadditive (K R ComplexdgO)]
  [∀ n : ℤ, (shiftFunctor (K R DGModE) n).Additive]
  [∀ n : ℤ, (shiftFunctor (K R ComplexdgO) n).Additive]
  [Pretriangulated (K R DGModE)] [Pretriangulated (K R ComplexdgO)]
  [QisO.IsSaturatedMultiplicativeSystem] in
/-- Companion theorem: the right-derived internal-Hom functor from Lemma `22.35.5` is a right
adjoint once the underived DG tensor/Hom adjunction is fixed. -/
theorem derivedHomFromK_isRightAdjoint
    (underivedAdj : tensorWithK.mapK ⊣ homFromK) :
    Functor.IsRightAdjoint derivedHomFromK :=
  (derivedTensorWithK_leftAdjoint_and_derivedHomFromK_rightAdjoint
    QisE QisO tensorWithK homFromK underivedAdj).2

end
