import Mathlib
import StacksProject_2024.Chap12.Definition_12_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

noncomputable section

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Domain-style sampling: the primary domain is homological algebra for shifts of chain homology.
Relevant owner declarations in the surrounding ecosystem are:
- `ChainComplex.cochainComplexEquivalence`,
- `CategoryTheory.PullbackShift` together with `pullbackShiftIso`,
- `Functor.CommShift.commShiftIso`,
- `CochainComplex.ShiftSequence.shiftIso`,
- `CategoryTheory.Functor.ShiftSequence.shiftIso`.

Source/core/bridge triage:
- `core/canonical`: the Chapter 12 shift owner on `ChainComplex`, built in
  `Definition_12_14_1` from `PullbackShift`, together with the cochain owner
  `CochainComplex.ShiftSequence.shiftIso`;
- `bridge/view`: this file transports that owner to chain homology.

Primitive data:
- the chain/cochain equivalence viewed in the pullback-shift owner category;
- the comparison isomorphisms from pullbacked cochain homology to chain homology.

Derived API:
- the owner shift-sequence instance on `(homologyFunctor C (down ℤ) 0)`;
- the public comparison morphism `(homologyFunctor C (down ℤ) 0).shiftIso`.
-/
private abbrev cochainShiftPullback :=
  PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ)

private abbrev pullbackHomologyFunctor (i : ℤ) : cochainShiftPullback C ⥤ C :=
  homologyFunctor C (up ℤ) (-i)

private noncomputable instance : (pullbackHomologyFunctor C 0).ShiftSequence ℤ where
  sequence i := pullbackHomologyFunctor C i
  isoZero := Iso.refl _
  shiftIso k i i' hi' :=
    Functor.isoWhiskerRight
      (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) k (-k) (by simp))
      (homologyFunctor C (up ℤ) (-i)) ≪≫
    (show shiftFunctor (CochainComplex C ℤ) (-k : ℤ) ⋙ homologyFunctor C (up ℤ) (-i) ≅
        pullbackHomologyFunctor C i' from
      CochainComplex.ShiftSequence.shiftIso C (-k) (-i) (-i') (by omega))
  shiftIso_zero i := by
    sorry
  shiftIso_add k l i i' i'' hi' hi'' := by
    sorry

private def homologyFunctorFactorsApp (A : ChainComplex C ℤ) (i : ℤ) :
    (pullbackHomologyFunctor C i).obj ((ChainComplex.cochainComplexEquivalence C).functor.obj A) ≅
      (homologyFunctor C (down ℤ) i).obj A :=
  ((((ChainComplex.cochainComplexEquivalence C).functor.obj A).restrictionHomologyIso
      embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
      (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
        change -(i + 1) = -i - 1
        omega)
      (show embeddingDownIntUpInt.f i = -i by simp)
      (show embeddingDownIntUpInt.f (i - 1) = -i + 1 by
        change -(i - 1) = -i + 1
        omega)
      (show (up ℤ).prev (-i) = -i - 1 by simp)
      (show (up ℤ).next (-i) = -i + 1 by simp)).symm) ≪≫
    (homologyFunctor C (down ℤ) i).mapIso
      (((ChainComplex.cochainComplexEquivalence C).unitIso.app A).symm)

private def homologyFunctorFactors (i : ℤ) :
    chainToCochain C ⋙ pullbackHomologyFunctor C i ≅
      homologyFunctor C (down ℤ) i :=
  NatIso.ofComponents
    (fun A ↦ homologyFunctorFactorsApp C A i)
    (by
      intro A B f
      sorry)

noncomputable instance :
    (homologyFunctor C (down ℤ) 0).ShiftSequence ℤ where
  sequence i := homologyFunctor C (down ℤ) i
  isoZero := Iso.refl _
  shiftIso k i i' hi' :=
    Functor.isoWhiskerLeft (shiftFunctor (ChainComplex C ℤ) k) (homologyFunctorFactors C i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((chainToCochain C).commShiftIso k) (pullbackHomologyFunctor C i) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (chainToCochain C)
              ((pullbackHomologyFunctor C 0).shiftIso k i i' hi') ≪≫
              homologyFunctorFactors C i'
  shiftIso_zero i := by
    sorry
  shiftIso_add k l i i' i'' hi' hi'' := by
    sorry

end ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Definition 12.14.2: after transporting the cochain owner
`CochainComplex.ShiftSequence.shiftIso` through the Chapter 12 pullback-shift owner on
`ChainComplex`, the canonical functorial identification `H_{i + k}(A) ≅ H_i(A[k])` is expressed
by the generic owner morphism `(homologyFunctor C (down ℤ) 0).shiftIso`. Its source is the
degreewise equality `A_{i + k} = A[k]_i` from Definition `12.14.1`. -/
#check (homologyFunctor C (down ℤ) 0).shiftIso

variable (A : ChainComplex C ℤ) (k : ℤ)

/- Companion recall: the underlying shifted chain complex is the canonical shift object `A⟦k⟧`. -/
#check A⟦k⟧
