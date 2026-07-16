import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap13.Lemma_13_31_7
import stacks_proof.stacks_project.Chap13.Lemma_13_34_2
import stacks_proof.stacks_project.Chap13.Lemma_13_34_7
import stacks_proof.stacks_project.Chap19.Lemma_19_13_4

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A]
  [Category.{v₂} B] [Abelian B]

local instance additiveFunctorDerivedSource_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

local instance additiveFunctorDerivedTarget_hasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

theorem mapHomologicalComplexQ_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  -- Proof comment: Chapter 13 already supplies a pointwise quasi-isomorphism from any complex to
  -- some K-injective complex, and Lemma 13.31.7 globalizes that pointwise existence to a right
  -- derived functor.
  exact
    hasRightDerivedFunctor_of_kInjective_resolutions
      (F := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (fun K ↦ exists_quasiIso_to_kInjective (𝒜 := A) K)

attribute [local instance] mapHomologicalComplexQ_hasRightDerivedFunctor

noncomputable abbrev additiveFunctorTotalRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- Helper for Lemma 19.13.6: on a K-injective representative, the total right derived functor
is computed by applying `F` termwise before passing to the derived category. -/
private noncomputable def additiveFunctorTotalRightDerivedValueIso
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  let G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  have hCompute :
      G.ComputesRightDerivedAt
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) := by
    -- Proof comment: a K-injective complex already computes the right derived functor.
    simpa [G] using
      (kInjective_computesRightDerivedFunctorAt (F := G) I)
  have hUnit :
      IsIso
        ((G.totalRightDerivedUnit
            DerivedCategory.Q
            (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
    -- Proof comment: convert the pointwise computation statement into invertibility of the
    -- total right derived unit.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := G)
        (S := HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        (X := ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).1
        hCompute
  -- Proof comment: the desired computation isomorphism is the inverse of the unit component.
  exact
    (asIso
      (((G.totalRightDerivedUnit
          DerivedCategory.Q
          (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))).symm

/-- Helper for Lemma 19.13.6: the computation isomorphism for `RF` is natural in a chain map
between K-injective representatives. -/
private theorem additiveFunctorTotalRightDerivedValueIso_naturality
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    {I J : CochainComplex A ℤ} [I.IsKInjective] [J.IsKInjective]
    (f : I ⟶ J) :
    (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map f) ≫
        (additiveFunctorTotalRightDerivedValueIso (F := F) J).hom =
      (additiveFunctorTotalRightDerivedValueIso (F := F) I).hom ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
  let G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let η :
      G ⟶
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).Q ⋙
          additiveFunctorTotalRightDerived F :=
    G.totalRightDerivedUnit
      DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let eI :
      DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≅
        (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj I) :=
    asIso (η.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
  let eJ :
      DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ≅
        (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj J) :=
    asIso (η.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))
  have hη :
      DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫ eJ.hom =
        eI.hom ≫
          (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map f) := by
    -- Proof comment: this is the naturality square for the total right derived unit.
    simpa [η, G] using
      η.naturality (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))
  -- Proof comment: postcompose the unit naturality square by the inverse unit on the target.
  apply (cancel_mono eJ.hom).1
  calc
    ((additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map f) ≫
        (additiveFunctorTotalRightDerivedValueIso (F := F) J).hom) ≫
          eJ.hom =
      (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map f) := by
        simp [additiveFunctorTotalRightDerivedValueIso, eJ, Category.assoc]
    _ =
      (additiveFunctorTotalRightDerivedValueIso (F := F) I).hom ≫
        (eI.hom ≫ (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map f)) := by
        simp [additiveFunctorTotalRightDerivedValueIso, eI, Category.assoc]
    _ =
      (additiveFunctorTotalRightDerivedValueIso (F := F) I).hom ≫
        (DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
          eJ.hom) := by
        rw [hη]
    _ =
      ((additiveFunctorTotalRightDerivedValueIso (F := F) I).hom ≫
          DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))) ≫
        eJ.hom := by
        simp [Category.assoc]

/-- Helper for Lemma 19.13.6: `RF` carries the represented product of a countable family of
K-injective complexes to the product of the derived images of the stages. -/
private noncomputable def additiveFunctorTotalRightDerivedRepresentedProductIso
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (I : ℕ → CochainComplex A ℤ)
    [∀ n : ℕ, (I n).IsKInjective] :
    (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (∏ᶜ I)) ≅
      ∏ᶜ fun n ↦ (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)) := by
  let eValue :
      (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (∏ᶜ I)) ≅
        DerivedCategory.Q.obj
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ I))) :=
    additiveFunctorTotalRightDerivedValueIso (F := F) (∏ᶜ I)
  let eFunctor :
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ I)) ≅
        ∏ᶜ fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)) :=
    PreservesProduct.iso (F.mapHomologicalComplex (ComplexShape.up ℤ)) I
  let eTarget :
      DerivedCategory.Q.obj
          (∏ᶜ fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) ≅
        ∏ᶜ fun n ↦
          DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) := by
    letI :
        PreservesLimit
          (Discrete.functor fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
          DerivedCategory.Q :=
      derivedCategory_Q_preserves_product_of_ab4Star
        (C := B)
        (I := fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
    exact
      PreservesProduct.iso
        DerivedCategory.Q
        (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
  let eStages :
      ∏ᶜ fun n ↦
          DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) ≅
        ∏ᶜ fun n ↦
          (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)) :=
    lim.mapIso <|
      Discrete.natIso fun n : Discrete ℕ ↦
        (additiveFunctorTotalRightDerivedValueIso (F := F) (I n.as)).symm
  -- Proof comment: rewrite `RF` on the product representative, then rewrite the termwise image
  -- of the product and finally transport each stage through the K-injective computation isomorphisms.
  exact
    eValue ≪≫
      DerivedCategory.Q.mapIso eFunctor ≪≫
        eTarget ≪≫
          eStages

/-- Helper for Lemma 19.13.6: the represented-product comparison for `RF` has the expected
`n`-th product projection. -/
private theorem additiveFunctorTotalRightDerivedRepresentedProductIso_hom_comp_π
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (I : ℕ → CochainComplex A ℤ)
    [∀ n : ℕ, (I n).IsKInjective]
    (n : ℕ) :
    (additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I).hom ≫
        Pi.π
          (fun n ↦
            (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)))
          n =
      (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map (Pi.π I n)) := by
  let eValue :
      (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (∏ᶜ I)) ≅
        DerivedCategory.Q.obj
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ I))) :=
    additiveFunctorTotalRightDerivedValueIso (F := F) (∏ᶜ I)
  let eFunctor :
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ I)) ≅
        ∏ᶜ fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)) :=
    PreservesProduct.iso (F.mapHomologicalComplex (ComplexShape.up ℤ)) I
  let eTarget :
      DerivedCategory.Q.obj
          (∏ᶜ fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) ≅
        ∏ᶜ fun n ↦
          DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) := by
    letI :
        PreservesLimit
          (Discrete.functor fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
          DerivedCategory.Q :=
      derivedCategory_Q_preserves_product_of_ab4Star
        (C := B)
        (I := fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
    exact
      PreservesProduct.iso
        DerivedCategory.Q
        (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
  let eStages :
      ∏ᶜ fun n ↦
          DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) ≅
        ∏ᶜ fun n ↦
          (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)) :=
    lim.mapIso <|
      Discrete.natIso fun n : Discrete ℕ ↦
        (additiveFunctorTotalRightDerivedValueIso (F := F) (I n.as)).symm
  have heFunctor_π :
      eFunctor.hom ≫
          Pi.π
            (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
            n =
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π I n)) := by
    -- Proof comment: `eFunctor` is the standard product-comparison isomorphism for
    -- `F.mapHomologicalComplex`, so its `n`-th projection is the image of `Pi.π`.
    simpa [eFunctor, Limits.PreservesProduct.iso_hom, Category.assoc] using
      (piComparison_comp_π (F.mapHomologicalComplex (ComplexShape.up ℤ)) I n)
  have heTarget_π :
      eTarget.hom ≫
          Pi.π
            (fun n ↦
              DerivedCategory.Q.obj
                (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))))
            n =
        DerivedCategory.Q.map
          (Pi.π (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) n) := by
    -- Proof comment: the localization functor preserves the product of the termwise image family,
    -- so its product-comparison isomorphism has the usual projection formula.
    simpa [eTarget, Limits.PreservesProduct.iso_hom, Category.assoc] using
      (piComparison_comp_π
        DerivedCategory.Q
        (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)))
        n)
  -- Proof comment: rewrite the represented-product comparison to the chain-level product,
  -- read off the `n`-th projection there, and then cancel the stagewise K-injective computation
  -- isomorphism.
  apply (cancel_mono (additiveFunctorTotalRightDerivedValueIso (F := F) (I n)).hom).1
  calc
    ((additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I).hom ≫
        Pi.π
          (fun n ↦
            (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)))
          n) ≫
          (additiveFunctorTotalRightDerivedValueIso (F := F) (I n)).hom =
      (additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I).hom ≫
        (Pi.π
            (fun n ↦
              (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)))
            n ≫
          (additiveFunctorTotalRightDerivedValueIso (F := F) (I n)).hom) := by
        simp [Category.assoc]
    _ =
      eValue.hom ≫
        DerivedCategory.Q.map eFunctor.hom ≫
          eTarget.hom ≫
            Pi.π
              (fun n ↦
                DerivedCategory.Q.obj
                  (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))))
              n := by
        simp [additiveFunctorTotalRightDerivedRepresentedProductIso, eValue, eFunctor, eTarget,
          eStages, Category.assoc]
    _ =
      eValue.hom ≫
        DerivedCategory.Q.map eFunctor.hom ≫
          DerivedCategory.Q.map
            (Pi.π (fun n ↦ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n))) n) := by
        rw [heTarget_π]
        simp [Category.assoc]
    _ =
      eValue.hom ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π I n))) := by
        rw [← Functor.map_comp, heFunctor_π]
        simp [Category.assoc]
    _ =
      (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map (Pi.π I n)) ≫
        (additiveFunctorTotalRightDerivedValueIso (F := F) (I n)).hom := by
        simpa [eValue] using
          additiveFunctorTotalRightDerivedValueIso_naturality
            (F := F)
            (Pi.π I n)

section

variable {D : Type u₁} [Category.{v₁} D]

/-- Helper for Lemma 19.13.6: an isomorphism of sequential inverse systems induces the obvious
isomorphism between their product objects. -/
private noncomputable def towerProductIso
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    ∏ᶜ inverseSystemFamily Ksys ≅ ∏ᶜ inverseSystemFamily Lsys where
  hom := Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom
  inv := Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Lsys) n ≫ (e.app (op n)).inv
  hom_inv_id := by
    -- Proof comment: compare the candidate composite with each product projection on `Lsys`.
    apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  inv_hom_id := by
    -- Proof comment: compare the candidate composite with each product projection on `Ksys`.
    apply Pi.hom_ext
    intro n
    simp [Category.assoc]

/-- Helper for Lemma 19.13.6: the product comparison induced by a tower isomorphism has the
expected `n`-th projection. -/
private theorem towerProductIso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (towerProductIso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
  -- Proof comment: this is the defining projection formula for `Pi.lift`.
  simp [towerProductIso, Category.assoc]

section

variable [Preadditive D]

/-- Helper for Lemma 19.13.6: the product comparison from a tower isomorphism conjugates the
Milnor difference maps. -/
private theorem towerProductIso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (towerProductIso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (towerProductIso e).hom := by
  -- Proof comment: compare the two Milnor endomorphisms after projection to each stage.
  apply Pi.hom_ext
  intro n
  calc
    ((towerProductIso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (towerProductIso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (op (n + 1))).hom ≫ Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [towerProductIso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (towerProductIso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫ (e.app (op n)).hom) := by
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫
        Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      (derivedLimitDifferenceMap Ksys ≫ (towerProductIso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n := by
          rw [Category.assoc, ← towerProductIso_hom_comp_π, ← Category.assoc]

end

section

variable [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Helper for Lemma 19.13.6: a derived-limit witness transports across an isomorphism of towers
while keeping the limiting object fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem D} {K : D}
    (e : Ksys ≅ Lsys) (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    let eFamily :
        Discrete.functor (inverseSystemFamily Ksys) ≅
          Discrete.functor (inverseSystemFamily Lsys) :=
      Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    towerProductIso e
  let T : Triangle D :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle D :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Proof comment: rewrite the original Milnor triangle through the induced product
    -- isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (towerProductIso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang D := by
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ι ≫ p.hom, p.inv ≫ δ, hT'⟩

/-- Helper for Lemma 19.13.6: an additive triangulated functor preserving countable products
maps a chosen Milnor triangle to the Milnor triangle of the image tower. -/
private theorem isDerivedLimit_map_functor
    {E : Type u₂} [Category.{v₂} E]
    [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor E n)] [Pretriangulated E]
    (G : D ⥤ E) [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    {Ksys : SequentialInverseSystem D} {K : D}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ G) (G.obj K) := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let hQ : HasProduct (inverseSystemFamily (Ksys ⋙ G)) := by
    infer_instance
  letI : HasProduct (inverseSystemFamily (Ksys ⋙ G)) := hQ
  let eprod :
      G.obj (∏ᶜ inverseSystemFamily Ksys) ≅
        ∏ᶜ inverseSystemFamily (Ksys ⋙ G) :=
    PreservesProduct.iso G (inverseSystemFamily Ksys)
  have heprod_π (n : ℕ) :
      eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ G)) n =
        G.map (Pi.π (inverseSystemFamily Ksys) n) := by
    -- Proof comment: `eprod` is the preserved-product comparison, so its stage projections are
    -- the standard `piComparison_comp_π` maps.
    simpa [eprod, Limits.PreservesProduct.iso_hom, inverseSystemFamily, Category.assoc] using
      (piComparison_comp_π G (inverseSystemFamily Ksys) n)
  have heprod_difference :
      G.map (derivedLimitDifferenceMap Ksys) ≫ eprod.hom =
        eprod.hom ≫ derivedLimitDifferenceMap (Ksys ⋙ G) := by
    -- Proof comment: compare both product endomorphisms after each stage projection and rewrite
    -- by the explicit Milnor difference-map formula.
    apply Pi.hom_ext
    intro n
    calc
      (G.map (derivedLimitDifferenceMap Ksys) ≫ eprod.hom) ≫
          Pi.π (inverseSystemFamily (Ksys ⋙ G)) n =
        G.map (derivedLimitDifferenceMap Ksys) ≫
          G.map (Pi.π (inverseSystemFamily Ksys) n) := by
            rw [Category.assoc, heprod_π]
      _ = G.map (derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n) := by
            simp [Functor.map_comp]
      _ =
        G.map
          (Pi.π (inverseSystemFamily Ksys) n -
            Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.transitionMap (Nat.le_succ n)) := by
            rw [derivedLimitDifferenceMap_comp_π]
      _ =
        G.map (Pi.π (inverseSystemFamily Ksys) n) -
          G.map
            (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.transitionMap (Nat.le_succ n)) := by
            simp [Functor.map_sub]
      _ =
        G.map (Pi.π (inverseSystemFamily Ksys) n) -
          (G.map (Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
            (Ksys ⋙ G).transitionMap (Nat.le_succ n)) := by
            simp [Functor.map_comp, SequentialInverseSystem.transitionMap]
      _ =
        (eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ G)) n) -
          ((eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ G)) (n + 1)) ≫
            (Ksys ⋙ G).transitionMap (Nat.le_succ n)) := by
            rw [heprod_π, heprod_π]
      _ =
        eprod.hom ≫
          (Pi.π (inverseSystemFamily (Ksys ⋙ G)) n -
            Pi.π (inverseSystemFamily (Ksys ⋙ G)) (n + 1) ≫
              (Ksys ⋙ G).transitionMap (Nat.le_succ n)) := by
            rw [Preadditive.comp_sub]
            simp [Category.assoc]
      _ = eprod.hom ≫ derivedLimitDifferenceMap (Ksys ⋙ G) := by
            rw [derivedLimitDifferenceMap_comp_π]
  let Tmilnor : Triangle D :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Tmapped : Triangle E :=
    G.mapTriangle.obj Tmilnor
  let Ttransported : Triangle E :=
    Triangle.mk
      (G.map ι ≫ eprod.hom)
      (derivedLimitDifferenceMap (Ksys ⋙ G))
      (eprod.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K)
  have hIso : Tmapped ≅ Ttransported := by
    -- Proof comment: rewrite the mapped product vertex to the canonical product of the image
    -- tower and replace the middle morphism by the standard Milnor difference map.
    refine Triangle.isoMk _ _ (Iso.refl _) eprod eprod ?_ ?_ ?_
    · simp [Tmapped, Tmilnor, Ttransported]
    · simpa [Tmapped, Tmilnor, Ttransported, Category.assoc] using heprod_difference
    · simp [Tmapped, Tmilnor, Ttransported, Category.assoc]
  have hTtransported : Ttransported ∈ distTriang E := by
    -- Proof comment: triangulated exactness carries the Milnor triangle to a distinguished
    -- triangle, and the product rewrite preserves distinguishedness.
    exact isomorphic_distinguished _ (G.map_distinguished Tmilnor hδ) _ hIso.symm
  exact
    ⟨hQ, G.map ι ≫ eprod.hom,
      eprod.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K,
      hTtransported⟩

end

end

theorem additiveFunctor_totalRightDerived_preservesDerivedLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory A} {K : DerivedCategory A}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ additiveFunctorTotalRightDerived F)
      ((additiveFunctorTotalRightDerived F).obj K) := by
  -- Route correction: the remaining proof has to transport the Milnor triangle of `Ksys`
  -- through `RF`, using a functorial K-injective resolution to compare `RF(∏ K_n)` with the
  -- countable product of the `RF(K_n)`.
  -- Proof comment: the new represented-product bridge above reduces the remaining work to
  -- assembling a theorem-local `PreservesLimitsOfShape (Discrete ℕ)` instance for `RF` from
  -- functorial K-injective representatives of an arbitrary countable family in `D(A)`.
  classical
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  choose I hI s hs using fun n : ℕ ↦
    exists_quasiIso_to_kInjective
      (𝒜 := A)
      (DerivedCategory.Q.objPreimage (Ksys.obj (op n)))
  let eI : ∀ n : ℕ, DerivedCategory.Q.obj (I n) ≅ inverseSystemFamily Ksys n := fun n ↦
    -- Proof comment: the chosen K-injective model is quasi-isomorphic to the canonical preimage
    -- of the `n`-th stage, so it represents that stage in the derived category.
    (asIso (DerivedCategory.Q.map (s n))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (Ksys.obj (op n))
  letI : ∀ n : ℕ, (I n).IsKInjective := fun n ↦ hI n
  let hExplicit :
      IsLimit
        (Fan.mk
          (DerivedCategory.Q.obj (∏ᶜ I))
          (fun n ↦ DerivedCategory.Q.map (Pi.π I n) ≫ (eI n).hom)) :=
    termwise_product_represents_product (X := inverseSystemFamily Ksys) I eI
  let p : ∏ᶜ inverseSystemFamily Ksys ≅ DerivedCategory.Q.obj (∏ᶜ I) :=
    (limit.isLimit (Discrete.functor (inverseSystemFamily Ksys))).conePointUniqueUpToIso hExplicit
  let eStages :
      ∏ᶜ fun n ↦
          (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)) ≅
        ∏ᶜ inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F) :=
    lim.mapIso <|
      Discrete.natIso fun n : Discrete ℕ ↦
        (additiveFunctorTotalRightDerived F).mapIso (eI n.as)
  let eprod :
      (additiveFunctorTotalRightDerived F).obj (∏ᶜ inverseSystemFamily Ksys) ≅
        ∏ᶜ inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F) :=
    (additiveFunctorTotalRightDerived F).mapIso p ≪≫
      additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I ≪≫
        eStages
  have hp_comp_π (n : ℕ) :
      p.hom ≫ (DerivedCategory.Q.map (Pi.π I n) ≫ (eI n).hom) =
        Pi.π (inverseSystemFamily Ksys) n := by
    -- Proof comment: `p` is the unique comparison from the abstract product of `Ksys` to the
    -- explicit termwise-product model chosen from the K-injective representatives.
    simpa [p, inverseSystemFamily, Category.assoc] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (limit.isLimit (Discrete.functor (inverseSystemFamily Ksys)))
        hExplicit
        (Discrete.mk n)
  have heprod_π (n : ℕ) :
      eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n =
        (additiveFunctorTotalRightDerived F).map (Pi.π (inverseSystemFamily Ksys) n) := by
    -- Proof comment: expand the explicit product comparison for `RF`, then collapse the chosen
    -- K-injective product model back to the original product of `Ksys`.
    calc
      eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n =
        (additiveFunctorTotalRightDerived F).map p.hom ≫
          (additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I).hom ≫
            eStages.hom ≫
              Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n := by
          simp [eprod, Category.assoc]
      _ =
        (additiveFunctorTotalRightDerived F).map p.hom ≫
          (additiveFunctorTotalRightDerivedRepresentedProductIso (F := F) I).hom ≫
            Pi.π
              (fun n ↦
                (additiveFunctorTotalRightDerived F).obj (DerivedCategory.Q.obj (I n)))
              n ≫
              ((additiveFunctorTotalRightDerived F).mapIso (eI n)).hom := by
          simp [eStages, inverseSystemFamily, Category.assoc]
      _ =
        (additiveFunctorTotalRightDerived F).map p.hom ≫
          (additiveFunctorTotalRightDerived F).map (DerivedCategory.Q.map (Pi.π I n)) ≫
            ((additiveFunctorTotalRightDerived F).mapIso (eI n)).hom := by
          rw [additiveFunctorTotalRightDerivedRepresentedProductIso_hom_comp_π (F := F) I n]
      _ =
        (additiveFunctorTotalRightDerived F).map
          (p.hom ≫ DerivedCategory.Q.map (Pi.π I n)) ≫
            ((additiveFunctorTotalRightDerived F).mapIso (eI n)).hom := by
          simp [Functor.map_comp, Category.assoc]
      _ =
        (additiveFunctorTotalRightDerived F).map
          (p.hom ≫ DerivedCategory.Q.map (Pi.π I n) ≫ (eI n).hom) := by
          simp [Functor.map_comp, Category.assoc]
      _ =
        (additiveFunctorTotalRightDerived F).map (Pi.π (inverseSystemFamily Ksys) n) := by
          rw [hp_comp_π]
  have heprod_difference :
      (additiveFunctorTotalRightDerived F).map (derivedLimitDifferenceMap Ksys) ≫ eprod.hom =
        eprod.hom ≫ derivedLimitDifferenceMap (Ksys ⋙ additiveFunctorTotalRightDerived F) := by
    -- Proof comment: compare the mapped Milnor difference map and the target Milnor difference
    -- map after every stage projection, exactly as in the abstract preserved-product argument.
    apply Pi.hom_ext
    intro n
    calc
      ((additiveFunctorTotalRightDerived F).map (derivedLimitDifferenceMap Ksys) ≫ eprod.hom) ≫
          Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n =
        (additiveFunctorTotalRightDerived F).map (derivedLimitDifferenceMap Ksys) ≫
          (additiveFunctorTotalRightDerived F).map
            (Pi.π (inverseSystemFamily Ksys) n) := by
            rw [Category.assoc, heprod_π]
      _ =
        (additiveFunctorTotalRightDerived F).map
          (derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n) := by
            simp [Functor.map_comp]
      _ =
        (additiveFunctorTotalRightDerived F).map
          (Pi.π (inverseSystemFamily Ksys) n -
            Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.transitionMap (Nat.le_succ n)) := by
            rw [derivedLimitDifferenceMap_comp_π]
      _ =
        (additiveFunctorTotalRightDerived F).map (Pi.π (inverseSystemFamily Ksys) n) -
          (additiveFunctorTotalRightDerived F).map
            (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.transitionMap (Nat.le_succ n)) := by
            simp [Functor.map_sub]
      _ =
        (additiveFunctorTotalRightDerived F).map (Pi.π (inverseSystemFamily Ksys) n) -
          ((additiveFunctorTotalRightDerived F).map
              (Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
            (Ksys ⋙ additiveFunctorTotalRightDerived F).transitionMap (Nat.le_succ n)) := by
            simp [Functor.map_comp, SequentialInverseSystem.transitionMap]
      _ =
        (eprod.hom ≫ Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n) -
          ((eprod.hom ≫
              Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) (n + 1)) ≫
            (Ksys ⋙ additiveFunctorTotalRightDerived F).transitionMap (Nat.le_succ n)) := by
            rw [heprod_π, heprod_π]
      _ =
        eprod.hom ≫
          (Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) n -
            Pi.π (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) (n + 1) ≫
              (Ksys ⋙ additiveFunctorTotalRightDerived F).transitionMap (Nat.le_succ n)) := by
            rw [Preadditive.comp_sub]
            simp [Category.assoc]
      _ =
        eprod.hom ≫ derivedLimitDifferenceMap (Ksys ⋙ additiveFunctorTotalRightDerived F) := by
            rw [derivedLimitDifferenceMap_comp_π]
  let hQ : HasProduct (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) := by
    infer_instance
  letI : HasProduct (inverseSystemFamily (Ksys ⋙ additiveFunctorTotalRightDerived F)) := hQ
  let Tmilnor : Triangle (DerivedCategory A) :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Tmapped : Triangle (DerivedCategory B) :=
    (additiveFunctorTotalRightDerived F).mapTriangle.obj Tmilnor
  let Ttransported : Triangle (DerivedCategory B) :=
    Triangle.mk
      ((additiveFunctorTotalRightDerived F).map ι ≫ eprod.hom)
      (derivedLimitDifferenceMap (Ksys ⋙ additiveFunctorTotalRightDerived F))
      (eprod.inv ≫
        (additiveFunctorTotalRightDerived F).map δ ≫
          ((additiveFunctorTotalRightDerived F).commShiftIso (1 : ℤ)).hom.app K)
  have hIso : Tmapped ≅ Ttransported := by
    -- Proof comment: the mapped Milnor triangle is rewritten through the explicit product
    -- comparison `eprod` and the corresponding Milnor difference-map identity.
    refine Triangle.isoMk _ _ (Iso.refl _) eprod eprod ?_ ?_ ?_
    · simp [Tmapped, Tmilnor, Ttransported]
    · simpa [Tmapped, Tmilnor, Ttransported, Category.assoc] using heprod_difference
    · simp [Tmapped, Tmilnor, Ttransported, Category.assoc]
  have hTtransported : Ttransported ∈ distTriang (DerivedCategory B) := by
    -- Proof comment: triangulated exactness carries the Milnor triangle through `RF`, and the
    -- product rewrite preserves distinguishedness.
    exact isomorphic_distinguished _ ((additiveFunctorTotalRightDerived F).map_distinguished Tmilnor hδ) _ hIso.symm
  exact
    ⟨hQ,
      (additiveFunctorTotalRightDerived F).map ι ≫ eprod.hom,
      eprod.inv ≫
        (additiveFunctorTotalRightDerived F).map δ ≫
          ((additiveFunctorTotalRightDerived F).commShiftIso (1 : ℤ)).hom.app K,
      hTtransported⟩

end

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable [IsGrothendieckAbelian.{w} A]
variable [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]

local instance stagewiseDerivedInverseLimit_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

local notation "SeqA" => SequentialInverseSystem A
local notation "DA" => DerivedCategory A
local notation "DSeqA" => DerivedCategory SeqA
local notation "QisA" =>
  (HomologicalComplex.quasiIso SeqA (ComplexShape.up ℤ) :
    MorphismProperty (CochainComplex SeqA ℤ))

local instance sequentialInverseSystem_isGrothendieckAbelian :
    IsGrothendieckAbelian.{w} SeqA := ‹IsGrothendieckAbelian.{w} (SequentialInverseSystem A)›

local instance stagewiseDerivedInverseSystem_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} SeqA :=
  HasDerivedCategory.standard SeqA

private abbrev stageEvaluation (n : ℕ) :
    SeqA ⥤ A :=
  ((evaluation ℕᵒᵖ A).obj (op n) : SeqA ⥤ A)

local instance stageEvaluation_additive (n : ℕ) :
    (((evaluation ℕᵒᵖ A).obj (op n)) : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
  exact inferInstance

local instance stageEvaluation_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (((evaluation ℕᵒᵖ A).obj (op n)) : (ℕᵒᵖ ⥤ A) ⥤ A) := by
  exact inferInstance

local instance stageEvaluation_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (((evaluation ℕᵒᵖ A).obj (op n)) : (ℕᵒᵖ ⥤ A) ⥤ A) := by
  exact inferInstance

private abbrev stageDerivedEvaluation (n : ℕ) :
    DSeqA ⥤ DA :=
  (stageEvaluation n).mapDerivedCategory

local instance stageDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (stageDerivedEvaluation n).IsRightDerivedFunctor
      (((stageEvaluation n).mapDerivedCategoryFactors.inv) :
        (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ stageDerivedEvaluation n)
      QisA := by
  simpa [stageDerivedEvaluation] using
    (Functor.isRightDerivedFunctor_of_inverts
      QisA
      ((stageEvaluation n).mapDerivedCategory : DSeqA ⥤ DA)
      ((stageEvaluation n).mapDerivedCategoryFactors))

private abbrev stageEvaluationStep (n : ℕ) :
    (((evaluation ℕᵒᵖ A).obj (op (n + 1))) : SeqA ⥤ A) ⟶
      (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A) :=
  (((evaluation ℕᵒᵖ A).map ((homOfLE (Nat.le_succ n)).op)) :
    (((evaluation ℕᵒᵖ A).obj (op (n + 1))) : SeqA ⥤ A) ⟶
      (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A))

private abbrev stageDerivedEvaluationStep (n : ℕ) :
    ((stageEvaluation (n + 1)).mapDerivedCategory : DSeqA ⥤ DA) ⟶
      ((stageEvaluation n).mapDerivedCategory : DSeqA ⥤ DA) :=
  (Functor.rightDerivedNatTrans
    ((stageDerivedEvaluation (n + 1)) : DSeqA ⥤ DA)
    ((stageDerivedEvaluation n) : DSeqA ⥤ DA)
    (((stageEvaluation (n + 1)).mapDerivedCategoryFactors.inv) :
      (stageEvaluation (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ stageDerivedEvaluation (n + 1))
    (((stageEvaluation n).mapDerivedCategoryFactors.inv) :
      (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ stageDerivedEvaluation n)
    (show MorphismProperty (CochainComplex SeqA ℤ) from QisA)
    ((Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (stageEvaluationStep n) (ComplexShape.up ℤ))
      DerivedCategory.Q) :
      (stageEvaluation (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    ((stageEvaluation (n + 1)).mapDerivedCategory : DSeqA ⥤ DA) ⟶
      ((stageEvaluation n).mapDerivedCategory : DSeqA ⥤ DA))

private abbrev stagewiseDerivedInverseLimitObject (K : DSeqA) (n : ℕ) : DA :=
  (stageDerivedEvaluation n).obj K

private abbrev stagewiseDerivedInverseLimitTransition (K : DSeqA) (n : ℕ) :
    stagewiseDerivedInverseLimitObject K (n + 1) ⟶
      stagewiseDerivedInverseLimitObject K n :=
  (stageDerivedEvaluationStep n).app K

abbrev stagewiseDerivedInverseLimitTower (K : DSeqA) :
    SequentialInverseSystem DA :=
  @Functor.ofOpSequence DA _ (stagewiseDerivedInverseLimitObject K)
    (stagewiseDerivedInverseLimitTransition K)

/-- Helper for Lemma 19.13.6: an isomorphism in `D(SequentialInverseSystem A)` induces the
corresponding isomorphism between the stagewise derived inverse-limit towers. -/
private noncomputable def stagewiseDerivedInverseLimitTowerIso
    {K L : DSeqA} (e : K ≅ L) :
    stagewiseDerivedInverseLimitTower K ≅ stagewiseDerivedInverseLimitTower L := by
  let h :
      stagewiseDerivedInverseLimitTower K ⟶
        stagewiseDerivedInverseLimitTower L :=
    NatTrans.ofOpSequence
      (fun n ↦ ((stageDerivedEvaluation n).mapIso e).hom)
      (fun n ↦ by
        -- Proof comment: this is just the naturality of the derived stage-transition map.
        simpa [stagewiseDerivedInverseLimitTower] using
          ((stageDerivedEvaluationStep n).naturality e.hom).symm)
  exact
    NatIso.ofComponents
      (fun n ↦ (stageDerivedEvaluation (Opposite.unop n)).mapIso e)
      (fun {_ _} f ↦ by
        simpa using h.naturality f)

/-- Helper for Lemma 19.13.6: once the Milnor triangle is known for one limiting object, any
isomorphic target object is a derived limit of the same tower as well. -/
private theorem isDerivedLimit_of_isoTarget
    {Ksys : SequentialInverseSystem DA} {K L : DA}
    (e : K ≅ L) (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let T : Triangle DA :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DA :=
    Triangle.mk
      (e.inv ≫ ι)
      (derivedLimitDifferenceMap Ksys)
      (δ ≫ ((shiftFunctor DA (1 : ℤ)).mapIso e).hom)
  have hIso : T ≅ T' := by
    -- Proof comment: transport the Milnor triangle across the given isomorphism of limiting
    -- objects and the induced shifted isomorphism on the third vertex.
    refine Triangle.isoMk _ _ e (Iso.refl _) ((shiftFunctor DA (1 : ℤ)).mapIso e) ?_ ?_ ?_
    · simp [T, T']
    · simp [T, T']
    · simp [T, T', Category.assoc]
  refine ⟨hP, ?_⟩
  refine
    ⟨e.inv ≫ ι, δ ≫ ((shiftFunctor DA (1 : ℤ)).mapIso e).hom, ?_⟩
  -- Proof comment: distinguishedness is invariant under isomorphism of triangles.
  exact isomorphic_distinguished _ hδ _ hIso.symm

theorem derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : SeqA ⥤ A).Additive]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SeqA ⥤ A)]
    (K : DSeqA) :
    IsDerivedLimit
      (stagewiseDerivedInverseLimitTower K)
      ((additiveFunctorTotalRightDerived (lim : SeqA ⥤ A)).obj K) := by
  -- Route correction: the unresolved step is the concrete K-injective Milnor triangle for a
  -- resolved representative of `K`, followed by transport to the abstract stagewise tower.
  -- Proof comment: choose one K-injective representative of `K`, prove the Milnor triangle on
  -- that concrete representative, then transport first to the public stagewise tower and finally
  -- to the public value of `R lim`.
  obtain ⟨I, hI, s, hs⟩ :=
    exists_quasiIso_to_kInjective
      (𝒜 := SeqA)
      (DerivedCategory.Q.objPreimage K)
  letI : I.IsKInjective := hI
  let eK : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K
  let resolvedTower : SequentialInverseSystem DA :=
    @Functor.ofOpSequence DA _
      (fun n ↦
        DerivedCategory.Q.obj
          ((((stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
      (fun n ↦
        DerivedCategory.Q.map
          (((NatTrans.mapHomologicalComplex
              (stageEvaluationStep n)
              (ComplexShape.up ℤ)).app I)))
  have hResolvedToQObj :
      resolvedTower ≅ stagewiseDerivedInverseLimitTower (DerivedCategory.Q.obj I) := by
    let a : ∀ n : ℕ,
        ((stageDerivedEvaluation n).obj (DerivedCategory.Q.obj I)) ≅
          DerivedCategory.Q.obj
            ((((stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
      fun n ↦ ((stageEvaluation n).mapDerivedCategoryFactors.app I)
    let h :
        resolvedTower ⟶ stagewiseDerivedInverseLimitTower (DerivedCategory.Q.obj I) :=
      NatTrans.ofOpSequence
        (fun n ↦ (a n).symm.hom)
        (fun n ↦ by
          let τ :
              (((stageEvaluation (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
                ((stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ)) :=
            NatTrans.mapHomologicalComplex
              (stageEvaluationStep n)
              (ComplexShape.up ℤ)
          let δ :
              ((stageDerivedEvaluation (n + 1)) : DSeqA ⥤ DA) ⟶
                ((stageDerivedEvaluation n) : DSeqA ⥤ DA) :=
            stageDerivedEvaluationStep n
          have hstep :=
            Functor.rightDerivedNatTrans_app
              ((stageDerivedEvaluation (n + 1)) : DSeqA ⥤ DA)
              ((stageDerivedEvaluation n) : DSeqA ⥤ DA)
              (((stageEvaluation (n + 1)).mapDerivedCategoryFactors.inv) :
                (stageEvaluation (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                    DerivedCategory.Q ⟶
                  DerivedCategory.Q ⋙ stageDerivedEvaluation (n + 1))
              (((stageEvaluation n).mapDerivedCategoryFactors.inv) :
                (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                    DerivedCategory.Q ⟶
                  DerivedCategory.Q ⋙ stageDerivedEvaluation n)
              QisA
              (Functor.whiskerRight τ DerivedCategory.Q)
              I
          have hstep_inv :
              δ.app (DerivedCategory.Q.obj I) ≫ (a n).hom =
                (a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app I) := by
            -- Proof comment: this is the defining comparison square for the right-derived
            -- transition map, rewritten so the strict stagewise map appears on the right.
            have hstep_post_raw :
                ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj I)) ≫ (a n).hom =
                  (DerivedCategory.Q.map (τ.app I) ≫ (a n).inv) ≫ (a n).hom := by
              simpa [a, δ, Category.assoc] using
                congrArg (fun k ↦ k ≫ (a n).hom) hstep
            have hstep_post :
                (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj I) ≫ (a n).hom) =
                  DerivedCategory.Q.map (τ.app I) := by
              calc
                (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj I) ≫ (a n).hom) =
                    ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj I)) ≫ (a n).hom := by
                      simp [Category.assoc]
                _ =
                    (DerivedCategory.Q.map (τ.app I) ≫ (a n).inv) ≫ (a n).hom := hstep_post_raw
                _ = DerivedCategory.Q.map (τ.app I) := by
                    simp [Category.assoc]
            apply (cancel_epi (a (n + 1)).inv).1
            calc
              (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj I) ≫ (a n).hom) =
                  DerivedCategory.Q.map (τ.app I) := hstep_post
              _ =
                  (a (n + 1)).inv ≫ ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app I)) := by
                    simp
          -- Proof comment: invert the right-derived comparison square so the resolved strict
          -- tower maps to the public tower.
          calc
            DerivedCategory.Q.map (τ.app I) ≫ (a n).symm.hom =
                (a (n + 1)).symm.hom ≫ δ.app (DerivedCategory.Q.obj I) := by
                  calc
                    DerivedCategory.Q.map (τ.app I) ≫ (a n).symm.hom =
                        (a (n + 1)).symm.hom ≫
                          (a (n + 1)).hom ≫
                            DerivedCategory.Q.map (τ.app I) ≫
                              (a n).symm.hom := by
                                simp [Category.assoc]
                    _ =
                        (a (n + 1)).symm.hom ≫
                          (δ.app (DerivedCategory.Q.obj I) ≫ (a n).hom) ≫
                            (a n).symm.hom := by
                                simpa [Category.assoc] using
                                  congrArg
                                    (fun k ↦ (a (n + 1)).symm.hom ≫ k ≫ (a n).symm.hom)
                                    hstep_inv
                    _ = (a (n + 1)).symm.hom ≫ δ.app (DerivedCategory.Q.obj I) := by
                        simp [Category.assoc]
    refine NatIso.ofComponents
      (fun n ↦ (a (Opposite.unop n)).symm)
      (fun {_ _} f ↦ by
        simpa using h.naturality f)
  have hQObjToK :
      stagewiseDerivedInverseLimitTower (DerivedCategory.Q.obj I) ≅
        stagewiseDerivedInverseLimitTower K :=
    stagewiseDerivedInverseLimitTowerIso eK
  let eValue :
      DerivedCategory.Q.obj
          (((lim : SeqA ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
        (additiveFunctorTotalRightDerived (lim : SeqA ⥤ A)).obj K :=
    (additiveFunctorTotalRightDerivedValueIso
      (F := (lim : SeqA ⥤ A))
      I).symm ≪≫
      (additiveFunctorTotalRightDerived (lim : SeqA ⥤ A)).mapIso eK
  have hResolved :
      IsDerivedLimit
        resolvedTower
        (DerivedCategory.Q.obj
          (((lim : SeqA ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
    -- TODO: prove the concrete Milnor triangle for the chosen K-injective representative by
    -- showing the chain-level limit-to-product map is the kernel of the Milnor difference map,
    -- then package the induced short exact sequence through `DerivedCategory.triangleOfSES`.
    sorry
  exact
    isDerivedLimit_of_isoTarget eValue <|
      isDerivedLimit_of_tower_iso hQObjToK <|
        isDerivedLimit_of_tower_iso hResolvedToQObj hResolved

end

end CategoryTheory
