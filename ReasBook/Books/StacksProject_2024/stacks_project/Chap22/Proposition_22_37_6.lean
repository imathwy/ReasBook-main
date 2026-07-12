import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap22.Definition_22_3_1
import StacksProject_2024.Chap22.Lemma_22_28_4
import StacksProject_2024.Chap22.Lemma_22_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uDA uDB uN vDA vDB vN

-- The source-facing proposition is stated over abstract derived categories, but the DG-bimodule
-- witness itself uses the existing Chapter 22 owner `N : CochainComplex DGBimodAB ℤ` and the
-- transported property `(P)` owner `bimoduleEquivalence.HasPropertyP N` from Lemma `22.28.4`.

/-- The source-to-core bridge for Proposition 22.37.6: a realizing differential graded
`(A, B)`-bimodule `N` satisfies the remaining abstract hypotheses of Lemma `22.37.2`. The
source DG-algebra assumptions `A = H⁰(A)` and `B` K-flat stay on the source-facing proposition,
not in this bridge package. -/
def DGBimoduleRealizationCriterion
    (R : Type uR) [CommRing R]
    {DA : Type uDA} {DB : Type uDB}
    [Category.{vDA} DA] [Category.{vDB} DB]
    [HasZeroObject DA] [HasZeroObject DB]
    [Preadditive DA] [Preadditive DB]
    [Linear R DA] [Linear R DB]
    [HasCoproducts.{max uDB vDB} DB]
    [HasShift DA ℤ] [HasShift DB ℤ]
    [∀ n : ℤ, (shiftFunctor DA n).Additive]
    [∀ n : ℤ, (shiftFunctor DB n).Additive]
    [Pretriangulated DA] [Pretriangulated DB]
    (e : DA ≌ DB) (Aunit : DA)
    {DGBimodAB : Type uN} [Category.{vN} DGBimodAB] [HasZeroMorphisms DGBimodAB]
    (representedObject : CochainComplex DGBimodAB ℤ → DB)
    (derivedTensorWith : CochainComplex DGBimodAB ℤ → DA ⥤ DB)
    (derivedHomFrom : CochainComplex DGBimodAB ℤ → DB ⥤ DA)
    (N : CochainComplex DGBimodAB ℤ)
    (hCommShift : (derivedTensorWith N).CommShift ℤ)
    (hFunctorIso : e.functor ≅ derivedTensorWith N)
    (hObjectIso : representedObject N ≅ e.functor.obj Aunit) : Prop :=
  let _ : (derivedTensorWith N).CommShift ℤ := hCommShift
  (∀ X : DB,
    (∀ n : ℤ, ∀ f : representedObject N ⟶ (shiftFunctor DB n).obj X, f = 0) →
      IsZero X) ∧
    (∀ X : DB,
      IsZero ((derivedHomFrom N).obj X) →
        ∀ n : ℤ, ∀ f : representedObject N ⟶ (shiftFunctor DB n).obj X, f = 0) ∧
      (∀ k : ℤ,
        Function.Bijective
          (derivedTensorWithN_selfExtMap
            (derivedTensorWith N) Aunit (representedObject N)
            ((hFunctorIso.app Aunit).symm ≪≫ hObjectIso.symm) k))

/-- If a DG-bimodule `N` realizes `e.functor` by derived tensoring and satisfies the remaining
abstract hypotheses from Lemma 22.37.2, then the realizing derived tensor functor is an
equivalence. This is the bridge from the source-facing realization data in
Proposition 22.37.6 to the canonical equivalence criterion. -/
theorem derivedTensorBy_isEquivalence_of_dgBimoduleRealization
    (R : Type uR) [CommRing R]
    {DA : Type uDA} {DB : Type uDB}
    [Category.{vDA} DA] [Category.{vDB} DB]
    [HasZeroObject DA] [HasZeroObject DB]
    [Preadditive DA] [Preadditive DB]
    [Linear R DA] [Linear R DB]
    [HasCoproducts.{max uDB vDB} DB]
    [HasShift DA ℤ] [HasShift DB ℤ]
    [∀ n : ℤ, (shiftFunctor DA n).Additive]
    [∀ n : ℤ, (shiftFunctor DB n).Additive]
    [Pretriangulated DA] [Pretriangulated DB]
    {e : DA ≌ DB} {Aunit : DA}
    {DGBimodAB : Type uN} [Category.{vN} DGBimodAB] [HasZeroMorphisms DGBimodAB]
    {representedObject : CochainComplex DGBimodAB ℤ → DB}
    {derivedTensorWith : CochainComplex DGBimodAB ℤ → DA ⥤ DB}
    {derivedHomFrom : CochainComplex DGBimodAB ℤ → DB ⥤ DA}
    {N : CochainComplex DGBimodAB ℤ}
    (hCommShift : (derivedTensorWith N).CommShift ℤ)
    (hIsTriangulated : (derivedTensorWith N).IsTriangulated)
    (hCompact : IsCompactObject (representedObject N))
    (hAdjunction : (derivedTensorWith N) ⊣ (derivedHomFrom N))
    (hFunctorIso : e.functor ≅ derivedTensorWith N)
    (hObjectIso : representedObject N ≅ e.functor.obj Aunit)
    (hCriterion :
      DGBimoduleRealizationCriterion
        R e Aunit representedObject derivedTensorWith derivedHomFrom
        N hCommShift hFunctorIso hObjectIso) :
    (derivedTensorWith N).IsEquivalence :=
  by
    letI : (derivedTensorWith N).CommShift ℤ := hCommShift
    rcases hCriterion with
      ⟨hDetectsZero, hHomVanishesOfDerivedHomZero, hSelfExtBijective⟩
    letI : (derivedTensorWith N).IsTriangulated := hIsTriangulated
    letI : IsCompactObject (representedObject N) := hCompact
    exact
      derivedTensorWithN_isEquivalence_of_compact_detectsZero_selfExt
        (derivedTensorWith N) (derivedHomFrom N) Aunit (representedObject N)
        hAdjunction
        ((hFunctorIso.app Aunit).symm ≪≫ hObjectIso.symm)
        inferInstance hDetectsZero hHomVanishesOfDerivedHomZero hSelfExtBijective

/-- Proposition 22.37.6: let `R` be a ring, let `(A, d)` and `(B, d)` be differential
graded `R`-algebras, and let `F : D(A, d) ⥤ D(B, d)` be an `R`-linear equivalence of
triangulated categories. If `A = H^0(A)` and `B` is K-flat as a complex of `R`-modules, then
there exists a differential graded `(A, B)`-bimodule `N` with property `(P)` whose derived tensor
functor realizes `F`; the remaining displayed conditions are exactly the abstract
Lemma 22.37.2 hypotheses for this `N`, packaged as the named bridge
`DGBimoduleRealizationCriterion`. The current statement keeps the DG algebras `A` and `B`, the
category of differential graded `(A, B)`-bimodules, the existing transported property-`(P)` owner
`bimoduleEquivalence.HasPropertyP`, the represented object of `D(B, d)`, and bridge data for the
realizing derived tensor/internal-Hom functors. The K-flatness hypothesis uses the canonical
Chapter 15 owner on the underlying complex `B.toCochainComplex.IsKFlat`. The hypothesis
`A = H⁰(A)` is recorded by the vanishing of the other homology objects together with a chosen
comparison `A.toCochainComplex.homology 0 ≅ A.toCochainComplex.X 0`, so the degree-zero
identification remains concrete data rather than an existential placeholder. -/
@[stacks 09SA]
theorem exists_propertyP_dgBimodule_realizing_rLinearTriangulatedEquivalence
    {R : Type uR} [CommRing R]
    (A B : CochainDGAlgebra R)
    {DA : Type uDA} {DB : Type uDB}
    [Category.{vDA} DA] [Category.{vDB} DB]
    [HasZeroObject DA] [HasZeroObject DB]
    [Preadditive DA] [Preadditive DB]
    [Linear R DA] [Linear R DB]
    [HasCoproducts.{max uDB vDB} DB]
    [HasShift DA ℤ] [HasShift DB ℤ]
    [∀ n : ℤ, (shiftFunctor DA n).Additive]
    [∀ n : ℤ, (shiftFunctor DB n).Additive]
    [Pretriangulated DA] [Pretriangulated DB]
    (hA_homology_isZero :
      ∀ i : ℤ, i ≠ 0 → IsZero (A.toCochainComplex.homology i))
    (hA_h0 : A.toCochainComplex.homology 0 ≅ A.toCochainComplex.X 0)
    (hB_kFlat : B.toCochainComplex.IsKFlat)
    (e : DA ≌ DB)
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.functor.IsTriangulated] [e.inverse.IsTriangulated]
    [e.functor.Linear R] [e.inverse.Linear R]
    (Aunit : DA)
    {AopTensorB : Type uN} [Ring AopTensorB]
    (DGBimodAB : Type uN) [Category.{vN} DGBimodAB] [Abelian DGBimodAB]
    (bimoduleEquivalence : DGBimodAB ≌ ModuleCat.{uN, uN} AopTensorB)
    (representedObject : CochainComplex DGBimodAB ℤ → DB)
    (derivedTensorWith : CochainComplex DGBimodAB ℤ → DA ⥤ DB)
    (derivedHomFrom : CochainComplex DGBimodAB ℤ → DB ⥤ DA) :
    ∃ (N : CochainComplex DGBimodAB ℤ)
      (hCommShift : (derivedTensorWith N).CommShift ℤ)
      (hIsTriangulated : (derivedTensorWith N).IsTriangulated)
      (hCompact : IsCompactObject (representedObject N))
      (hAdjunction : (derivedTensorWith N) ⊣ (derivedHomFrom N))
      (hFunctorIso : e.functor ≅ derivedTensorWith N)
      (hObjectIso : representedObject N ≅ e.functor.obj Aunit),
      bimoduleEquivalence.HasPropertyP N ∧
        DGBimoduleRealizationCriterion
          R e Aunit representedObject derivedTensorWith derivedHomFrom
          N hCommShift hFunctorIso hObjectIso := sorry
