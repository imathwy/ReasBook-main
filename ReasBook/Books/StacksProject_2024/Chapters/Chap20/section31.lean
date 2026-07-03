import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_31_1 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

section

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DΓX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "RΓ" => moduleDerivedGlobalSections X

variable
    (leftDerivedPullback : DΓX ⥤ DModX)
variable
    (globalSectionsAdj : Adjunction leftDerivedPullback RΓ)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorΓ : DΓX ⥤ DΓX ⥤ DΓX)
variable (pullbackTensorIso :
  ∀ (A B : DΓX),
    leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

-- Proof sketch: the cohomology-class tensor `ξ ⊗ η` is the morphism obtained by functoriality of
-- the derived tensor product on `RΓ(X, K)` and `RΓ(X, L)`, precomposed with the chosen
-- identification of the source object with the tensor of the two shifted copies of the unit.
-- Its adjoint transpose is expressed directly in terms of the canonical lifts
-- `(globalSectionsAdj.homEquiv _ _).symm ξ` and `(globalSectionsAdj.homEquiv _ _).symm η`.
/-- Lemma 20.31.1: for derived global sections, composing the tensor of two cohomology-class
representatives with the canonical derived cup product has adjoint transpose equal to the tensor
of their canonical lifted representatives under `Lf^* ⊣ R\Gamma(X, -)`. This is the agreement with the
usual cup product construction described in the text. -/
theorem derivedGlobalSections_cupProduct_homEquiv
    {K L : DModX}
    {A₁ A₂ A₁₂ : DΓX}
    (tensorSourceIso : A₁₂ ≅ ((derivedTensorΓ.obj A₂).obj A₁))
    (ξ : A₁ ⟶ RΓ.obj K)
    (η : A₂ ⟶ RΓ.obj L) :
    ((globalSectionsAdj.homEquiv A₁₂ ((derivedTensorX.obj L).obj K)).symm)
        (tensorSourceIso.hom ≫
          (derivedTensorΓ.map η).app A₁ ≫
          (derivedTensorΓ.obj (RΓ.obj L)).map ξ ≫
          relativeDerivedCupProduct leftDerivedPullback RΓ globalSectionsAdj
            derivedTensorX derivedTensorΓ pullbackTensorIso K L) =
      leftDerivedPullback.map tensorSourceIso.hom ≫
        (pullbackTensorIso A₁ A₂).hom ≫
        (derivedTensorX.map ((globalSectionsAdj.homEquiv A₂ L).symm η)).app
          (leftDerivedPullback.obj A₁) ≫
        (derivedTensorX.obj L).map ((globalSectionsAdj.homEquiv A₁ K).symm ξ) := by
  rw [globalSectionsAdj.homEquiv_naturality_left_symm,
    globalSectionsAdj.homEquiv_naturality_left_symm,
    globalSectionsAdj.homEquiv_naturality_left_symm]
  simp [relativeDerivedCupProduct_homEquiv]

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_31_2 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable
    (leftDerivedPullback :
      DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤ DerivedCategory (RingedSpace.Modules X))
variable
    (globalSectionsAdj :
      Adjunction leftDerivedPullback (moduleDerivedGlobalSections X))
variable (derivedTensorX :
  DerivedCategory (RingedSpace.Modules X) ⥤
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (RingedSpace.Modules X))
variable (derivedTensorΓ :
  DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
    DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)))
variable (pullbackTensorIso :
  ∀ (A B : DerivedCategory (ModuleCat (globalSectionsRing X))),
    leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

/-- Remark 20.31.2: a representative `ξ : \Gamma(X,\mathcal O_X)[-i] \to R\Gamma(X,K)` defines
the associated left cup-product morphism
`R\Gamma(X,M)[-i] \to R\Gamma(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`. The source is
identified with `\Gamma(X,\mathcal O_X)[-i] \otimes_A^{\mathbf L} R\Gamma(X,M)` by the chosen
isomorphism `shiftTensorIso`. -/
noncomputable def derivedGlobalSections_leftCupBy
    {K M : DerivedCategory (RingedSpace.Modules X)}
    (i : ℤ)
    (shiftTensorIso :
      ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ≅
        ((derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
            (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X)))))
    (ξ :
      ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
        (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X))) ⟶
        (moduleDerivedGlobalSections X).obj K) :
    ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ⟶
      (moduleDerivedGlobalSections X).obj ((derivedTensorX.obj M).obj K) :=
  shiftTensorIso.hom ≫
    (derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).map ξ ≫
      relativeDerivedCupProduct leftDerivedPullback (moduleDerivedGlobalSections X)
        globalSectionsAdj
        derivedTensorX derivedTensorΓ pullbackTensorIso K M

-- Proof sketch: unfold `derivedGlobalSections_leftCupBy`. By definition it is the composite of
-- the chosen identification `RΓ(X,M)[-i] ≅ Γ(X,\mathcal O_X)[-i] ⊗^L_A RΓ(X,M)`, the tensor of
-- the representative `ξ` with the identity on `RΓ(X,M)`, and the global derived cup product.
/-- The left cup-product map is the composite of the shift-tensor identification, the tensor of
the representative `ξ`, and the global derived cup product. -/
theorem derivedGlobalSections_leftCupBy_def
    {K M : DerivedCategory (RingedSpace.Modules X)}
    (i : ℤ)
    (shiftTensorIso :
      ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ≅
        ((derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
            (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X)))))
    (ξ :
      ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
        (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X))) ⟶
        (moduleDerivedGlobalSections X).obj K) :
    derivedGlobalSections_leftCupBy derivedTensorX derivedTensorΓ i shiftTensorIso ξ =
      shiftTensorIso.hom ≫
        (derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).map ξ ≫
          relativeDerivedCupProduct leftDerivedPullback (moduleDerivedGlobalSections X)
            globalSectionsAdj
            derivedTensorX derivedTensorΓ pullbackTensorIso K M := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_3 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable
    (leftDerivedPullback : DModY ⥤ DModX)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (pullbackTensorIso :
      ∀ (A B : DModY),
        leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj
            (leftDerivedPullback.obj A)))

/-- The adjoint-side morphism whose transpose is the relative derived cup product. -/
private noncomputable abbrev relativeDerivedCupProductAdjoint
    (K M : DModX) :
    leftDerivedPullback.obj
        ((derivedTensorY.obj (rightDerivedPushforward.obj M)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorX.obj M).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj M)).hom ≫
    ((derivedTensorX.map (pullPushAdj.counit.app M)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorX.obj M).map (pullPushAdj.counit.app K))

variable {SourceComplex : Type v} {TargetComplex : Type w}

/-- The derived cup product `Rf_* K ⊗^{\mathbf L} Rf_* M ⟶ Rf_*(K ⊗^{\mathbf L} M)` attached to
the adjunction `leftDerivedPullback ⊣ rightDerivedPushforward` and the pullback-tensor
comparison. -/
noncomputable def relativeDerivedCupProduct
    (K M : DModX) :
    ((derivedTensorY.obj (rightDerivedPushforward.obj M)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorX.obj M).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductAdjoint leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso K M)

variable
    (sourceComplexToDerived : SourceComplex → DModX)
    (targetComplexToDerived : TargetComplex → DModY)
    (pushforwardComplex : SourceComplex → TargetComplex)
    (sourceTensorComplex : SourceComplex → SourceComplex → SourceComplex)
    (pushforwardTensorComplex : SourceComplex → SourceComplex → TargetComplex)
    (targetTensorCounit :
      ∀ (K M : SourceComplex),
        ((derivedTensorY.obj (targetComplexToDerived (pushforwardComplex M))).obj
          (targetComplexToDerived (pushforwardComplex K))) ⟶
            targetComplexToDerived (pushforwardTensorComplex K M))
    (pushforwardUnit :
      ∀ (K : SourceComplex),
        targetComplexToDerived (pushforwardComplex K) ⟶
          rightDerivedPushforward.obj (sourceComplexToDerived K))
    (naiveCupProduct :
      ∀ (K M : SourceComplex),
        targetComplexToDerived (pushforwardTensorComplex K M) ⟶
          targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)))
    (sourceTensorCounit :
      ∀ (K M : SourceComplex),
        ((derivedTensorX.obj (sourceComplexToDerived M)).obj
          (sourceComplexToDerived K)) ⟶
            sourceComplexToDerived (sourceTensorComplex K M))

-- Proof sketch: compare the two outer composites by transporting both across the adjunction
-- `leftDerivedPullback ⊣ rightDerivedPushforward`. Remark `20.28.7` identifies the clockwise
-- composite with the pullback-tensor comparison followed by the two counits, while Lemma `20.28.6`
-- replaces the derived pullback comparisons by the underived ones on chosen representatives. The
-- remaining rectangle is then exactly the functoriality square for the naive cup product and the
-- map from derived tensor products to total tensor complexes, so the two transposes agree.
/-- Lemma 20.31.3: the comparison from the tensor of the underived pushforwards to the derived
pushforward of the derived tensor product is compatible with the naive cup product on chosen
complex representatives. Equivalently, the square whose top edge is the tensor of the canonical
maps `f_* K^\bullet ⟶ Rf_* K^\bullet` and `f_* M^\bullet ⟶ Rf_* M^\bullet`, whose right edge is
the derived cup product followed by the map to `Rf_* \mathrm{Tot}(K^\bullet \otimes
M^\bullet)`, whose left edge is the passage to `\mathrm{Tot}(f_* K^\bullet \otimes f_* M^\bullet)`,
and whose bottom edge is the naive cup product followed by the canonical map to the derived
pushforward commutes. -/
theorem derivedPushforward_tensor_naiveCupProduct_square_commutes
    (K M : SourceComplex) :
    ((derivedTensorY.map (pushforwardUnit M)).app
        (targetComplexToDerived (pushforwardComplex K))) ≫
      ((derivedTensorY.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
        (pushforwardUnit K)) ≫
      relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso
        (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
      rightDerivedPushforward.map (sourceTensorCounit K M) =
    targetTensorCounit K M ≫
      naiveCupProduct K M ≫
      pushforwardUnit (sourceTensorComplex K M) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_4 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

variable (𝒰 : ι → Opens X.carrier)
variable
  (sourceComplexToDerived :
    CochainComplex.Plus (RingedSpace.Modules X) → DerivedCategory (RingedSpace.Modules X))
variable
  (derivedGlobalSections :
    DerivedCategory (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat)
variable
  (derivedTensorΓ :
    CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat ⥤
        CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat)
variable
  (sourceDerivedTensor :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        DerivedCategory (RingedSpace.Modules X))
variable
  (tensorComplex :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        CochainComplex.Plus (RingedSpace.Modules X))
variable
  (cechTensorTotalComplex :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        CochainComplex.Plus AddCommGrpCat)
variable
  (cechComparison :
    ∀ K : CochainComplex.Plus (RingedSpace.Modules X),
      (moduleCechDerivedFunctor X 𝒰).obj K ⟶
        derivedGlobalSections.obj (sourceComplexToDerived K))
variable
  (derivedCupProduct :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((derivedTensorΓ.obj
          (derivedGlobalSections.obj (sourceComplexToDerived M))).obj
        (derivedGlobalSections.obj (sourceComplexToDerived K))) ⟶
        derivedGlobalSections.obj (sourceDerivedTensor K M))
variable
  (sourceTensorCounit :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      sourceDerivedTensor K M ⟶ sourceComplexToDerived (tensorComplex K M))
variable
  (cechTensorCounit :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((derivedTensorΓ.obj ((moduleCechDerivedFunctor X 𝒰).obj M)).obj
        ((moduleCechDerivedFunctor X 𝒰).obj K)) ⟶
        (CategoryTheory.boundedBelowCochainComplexToDerivedBelow
          (𝟭 AddCommGrpCat)).obj (cechTensorTotalComplex K M))
variable
  (cechCupProduct :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((CategoryTheory.boundedBelowCochainComplexToDerivedBelow
          (𝟭 AddCommGrpCat)).obj (cechTensorTotalComplex K M)) ⟶
        (moduleCechDerivedFunctor X 𝒰).obj (tensorComplex K M))

-- Proof sketch: this is the morphism-to-a-point specialization of Lemma `20.31.3`. Replace the
-- two bounded-below complexes by flasque resolutions as in Lemma `20.30.2`, so that both the
-- Čech representatives and the derived global sections are computed by ordinary global sections.
-- The resulting diagram is then the Čech cup-product compatibility square, whose commutativity
-- reduces to Lemma `20.31.3` together with the comparison map of Lemma `20.25.1`.
/-- Lemma 20.31.4: for a ringed space `(X, \mathcal O_X)`, an open covering `\mathcal U`, and
bounded-below complexes `\mathcal K^\bullet` and `\mathcal M^\bullet`, the cup product on derived
global sections is compatible with the Čech cup product. Concretely, if `cechComparison` denotes
the comparison morphism of Lemma 20.25.1 from the total Čech complex to derived global sections,
then the square from
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal K^\bullet)) \otimes^{\mathbf L}
  Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal M^\bullet))`
to
`R\Gamma(X, \mathcal K^\bullet) \otimes^{\mathbf L} R\Gamma(X, \mathcal M^\bullet)`,
down to the Čech cup product and to
`R\Gamma(X, \mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal M^\bullet))`,
commutes in the target derived category. -/
theorem cech_tensor_derivedGlobalSections_square_commutes
    (K M : CochainComplex.Plus (RingedSpace.Modules X)) :
    ((derivedTensorΓ.map (cechComparison M)).app
        ((moduleCechDerivedFunctor X 𝒰).obj K)) ≫
      ((derivedTensorΓ.obj
          (derivedGlobalSections.obj (sourceComplexToDerived M))).map
        (cechComparison K)) ≫
      derivedCupProduct K M ≫
      derivedGlobalSections.map (sourceTensorCounit K M) =
    cechTensorCounit K M ≫
      cechCupProduct K M ≫
      cechComparison (tensorComplex K M) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_5 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (leftDerivedPullback : DModY ⥤ DModX)
variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (pullbackTensorIso :
  ∀ (A B : DModY),
    leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))
variable (tensorAssocX :
  ∀ (A B C : DModX),
    ((derivedTensorX.obj C).obj ((derivedTensorX.obj B).obj A)) ≅
      ((derivedTensorX.obj ((derivedTensorX.obj C).obj B)).obj A))
variable (tensorAssocY :
  ∀ (A B C : DModY),
    ((derivedTensorY.obj C).obj ((derivedTensorY.obj B).obj A)) ≅
      ((derivedTensorY.obj ((derivedTensorY.obj C).obj B)).obj A))

/-- The derived tensor product on `D(\mathcal O_X)` with explicit left and right factors. -/
private def tensorXObj
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX) (A B : DModX) : DModX :=
  (derivedTensorX.obj B).obj A

/-- The derived tensor product on `D(\mathcal O_Y)` with explicit left and right factors. -/
private def tensorYObj
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY) (A B : DModY) : DModY :=
  (derivedTensorY.obj B).obj A

/-- The common source object in the associativity square for the relative cup product. -/
private def relativeDerivedCupProductAssociativitySource
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (K L M : DModX) : DModY :=
  tensorYObj derivedTensorY
    (tensorYObj derivedTensorY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L))
    (rightDerivedPushforward.obj M)

/-- The common target object in the associativity square for the relative cup product. -/
private def relativeDerivedCupProductAssociativityTarget
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (K L M : DModX) : DModY :=
  rightDerivedPushforward.obj
    (tensorXObj derivedTensorX K (tensorXObj derivedTensorX L M))

/-- The top-then-right composite in the associativity square for the relative cup product. -/
private noncomputable def relativeDerivedCupProductAssociativityTop
    (K L M : DModX) :
    relativeDerivedCupProductAssociativitySource derivedTensorY rightDerivedPushforward K L M ⟶
      relativeDerivedCupProductAssociativityTarget derivedTensorX rightDerivedPushforward K L M :=
  (derivedTensorY.obj (rightDerivedPushforward.obj M)).map
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L) ≫
    relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso (tensorXObj derivedTensorX K L) M ≫
    rightDerivedPushforward.map (tensorAssocX K L M).hom

/-- The left-then-bottom composite in the associativity square for the relative cup product. -/
private noncomputable def relativeDerivedCupProductAssociativityBottom
    (K L M : DModX) :
    relativeDerivedCupProductAssociativitySource derivedTensorY rightDerivedPushforward K L M ⟶
      relativeDerivedCupProductAssociativityTarget derivedTensorX rightDerivedPushforward K L M :=
  (tensorAssocY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L)
      (rightDerivedPushforward.obj M)).hom ≫
    (derivedTensorY.map
        (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
          derivedTensorX derivedTensorY pullbackTensorIso L M)).app
      (rightDerivedPushforward.obj K) ≫
    relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso K (tensorXObj derivedTensorX L M)

-- Proof sketch: both routes become adjoint under `pullPushAdj` to the same morphism
-- `Lf^*((Rf_* K ⊗ Rf_* L) ⊗ Rf_* M) ⟶ K ⊗ (L ⊗ M)`, namely the one obtained from the pullback
-- tensor comparison, the associators, and the three counit maps. Applying injectivity of the
-- adjunction hom-equivalence yields equality of the two relative cup-product composites.
/-- Lemma 20.31.5: the relative cup product of Remark 20.28.7 is associative, i.e. after
inserting the chosen tensor associators, the two composites
`(Rf_* K \otimes^{\mathbf L} Rf_* L) \otimes^{\mathbf L} Rf_* M ⟶
Rf_*(K \otimes^{\mathbf L} (L \otimes^{\mathbf L} M))`
obtained by cupping first in the pair `(K,L)` or first in the pair `(L,M)` agree. -/
theorem relativeDerivedCupProduct_associative
    (K L M : DModX) :
    relativeDerivedCupProductAssociativityTop K L M =
      relativeDerivedCupProductAssociativityBottom K L M := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_6 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (leftDerivedPullback : DModY ⥤ DModX)
variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (pullbackTensorIso :
  ∀ (A B : DModY),
    leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))
variable (tensorCommX :
  ∀ (A B : DModX),
    ((derivedTensorX.obj B).obj A) ≅ ((derivedTensorX.obj A).obj B))
variable (tensorCommY :
  ∀ (A B : DModY),
    ((derivedTensorY.obj B).obj A) ≅ ((derivedTensorY.obj A).obj B))

-- Proof sketch: transpose both routes across the adjunction `Lf^* ⊣ Rf_*`. By the defining
-- formula for `relativeDerivedCupProduct`, each transpose is obtained from the pullback-tensor
-- comparison followed by the two counit maps. The braidings `ψ` on `D(\mathcal O_X)` and
-- `D(\mathcal O_Y)` are compatible with these tensor products, so after inserting
-- `tensorCommX` and `tensorCommY` the two transposes agree. Injectivity of the adjunction
-- hom-equivalence then gives the commutative square in `D(\mathcal O_Y)`.
/-- Lemma 20.31.6: the relative cup product of Remark 20.28.7 is commutative. Equivalently, if
`ψ` denotes the commutativity constraint on the chosen derived tensor products of
`D(\mathcal O_X)` and `D(\mathcal O_Y)`, then for all `K, L ∈ D(\mathcal O_X)` the square
comparing the relative cup product on `(K, L)` with the one on `(L, K)` is commutative in
`D(\mathcal O_Y)`. -/
theorem relativeDerivedCupProduct_commutative
    (K L : DModX) :
    CommSq
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L)
      (tensorCommY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L)).hom
      (rightDerivedPushforward.map (tensorCommX K L).hom)
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso L K) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_7 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

local notation "DModX" => DerivedCategory (Modules X)
local notation "DModY" => DerivedCategory (Modules Y)
local notation "DModZ" => DerivedCategory (Modules Z)

variable
    (leftDerivedPullback_f : DModY ⥤ DModX)
    (rightDerivedPushforward_f : DModX ⥤ DModY)
    (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (leftDerivedPullback_g : DModZ ⥤ DModY)
    (rightDerivedPushforward_g : DModY ⥤ DModZ)
    (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
    (leftDerivedPullback_comp : DModZ ⥤ DModX)
    (rightDerivedPushforward_comp : DModX ⥤ DModZ)
    (pullPushAdj_comp : leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp)
    (pushforwardCompIso :
      rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)

variable
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)

variable
    (pullbackTensorIso_f :
      ∀ (A B : DModY),
        leftDerivedPullback_f.obj ((derivedTensorY.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback_f.obj B)).obj
            (leftDerivedPullback_f.obj A)))

variable
    (pullbackTensorIso_g :
      ∀ (A B : DModZ),
        leftDerivedPullback_g.obj ((derivedTensorZ.obj B).obj A) ≅
          ((derivedTensorY.obj (leftDerivedPullback_g.obj B)).obj
            (leftDerivedPullback_g.obj A)))

variable
    (pullbackTensorIso_comp :
      ∀ (A B : DModZ),
        leftDerivedPullback_comp.obj ((derivedTensorZ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback_comp.obj B)).obj
            (leftDerivedPullback_comp.obj A)))

/-- The pullback-side morphism whose adjoint is the relative cup product for a chosen derived
pullback/pushforward adjunction. -/
private noncomputable abbrev relativeDerivedCupProductForAdjunctionAdjoint
    {A : Type u} [Category A] {B : Type u} [Category B]
    (leftDerivedPullback : B ⥤ A)
    (rightDerivedPushforward : A ⥤ B)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorA : A ⥤ A ⥤ A)
    (derivedTensorB : B ⥤ B ⥤ B)
    (pullbackTensorIso :
      ∀ (U V : B),
        leftDerivedPullback.obj ((derivedTensorB.obj V).obj U) ≅
          ((derivedTensorA.obj (leftDerivedPullback.obj V)).obj
            (leftDerivedPullback.obj U)))
    (K L : A) :
    leftDerivedPullback.obj
        ((derivedTensorB.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorA.obj L).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj L)).hom ≫
    ((derivedTensorA.map (pullPushAdj.counit.app L)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorA.obj L).map (pullPushAdj.counit.app K))

/-- The relative cup product attached to a chosen derived pullback/pushforward adjunction and
pullback-tensor comparison. -/
noncomputable def relativeDerivedCupProductForAdjunction
    {A : Type u} [Category A] {B : Type u} [Category B]
    (leftDerivedPullback : B ⥤ A)
    (rightDerivedPushforward : A ⥤ B)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorA : A ⥤ A ⥤ A)
    (derivedTensorB : B ⥤ B ⥤ B)
    (pullbackTensorIso :
      ∀ (U V : B),
        leftDerivedPullback.obj ((derivedTensorB.obj V).obj U) ≅
          ((derivedTensorA.obj (leftDerivedPullback.obj V)).obj
            (leftDerivedPullback.obj U)))
    (K L : A) :
    ((derivedTensorB.obj (rightDerivedPushforward.obj L)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorA.obj L).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductForAdjunctionAdjoint
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorA derivedTensorB pullbackTensorIso K L)

/-- The clockwise composite in the composition-compatibility square for relative cup products. -/
noncomputable abbrev iteratedRelativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorZ.obj (rightDerivedPushforward_comp.obj L)).obj
      (rightDerivedPushforward_comp.obj K)) ⟶
      rightDerivedPushforward_comp.obj ((derivedTensorX.obj L).obj K) :=
  ((derivedTensorZ.map
      (pushforwardCompIso.inv.app L)).app
      (rightDerivedPushforward_comp.obj K)) ≫
    ((derivedTensorZ.obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).map
      (pushforwardCompIso.inv.app K)) ≫
    relativeDerivedCupProductForAdjunction
      leftDerivedPullback_g rightDerivedPushforward_g pullPushAdj_g
      derivedTensorY derivedTensorZ pullbackTensorIso_g
      (rightDerivedPushforward_f.obj K) (rightDerivedPushforward_f.obj L) ≫
    rightDerivedPushforward_g.map
      (relativeDerivedCupProductForAdjunction
        leftDerivedPullback_f rightDerivedPushforward_f pullPushAdj_f
        derivedTensorX derivedTensorY pullbackTensorIso_f K L) ≫
    pushforwardCompIso.hom.app
      ((derivedTensorX.obj L).obj K)

/-- The relative cup product attached directly to the composite adjunction for `g ∘ f`. -/
private noncomputable abbrev compositeRelativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorZ.obj (rightDerivedPushforward_comp.obj L)).obj
      (rightDerivedPushforward_comp.obj K)) ⟶
      rightDerivedPushforward_comp.obj ((derivedTensorX.obj L).obj K) :=
  relativeDerivedCupProductForAdjunction
    leftDerivedPullback_comp rightDerivedPushforward_comp pullPushAdj_comp
    derivedTensorX derivedTensorZ pullbackTensorIso_comp K L

-- Proof sketch: transport both paths across the adjunction for `L(g \circ f)^* ⊣ R(g \circ f)_*`.
-- The direct path is adjoint to the pullback-tensor comparison for `g \circ f` followed by the
-- counit `L(g \circ f)^* R(g \circ f)_* ⟶ 𝟭`. For the iterated path, apply
-- the defining adjunction formulas for the two relative cup products; the compatibility of
-- counits under composition from Categories, Lemma `4.24.9`, identifies the resulting composite
-- of counits with the counit of the composite adjunction, so both transposes are the same map.
/-- Lemma 20.31.7: for composable morphisms of ringed spaces `f : (X, \mathcal O_X) \to
(Y, \mathcal O_Y)` and `g : (Y, \mathcal O_Y) \to (Z, \mathcal O_Z)`, the relative cup product
for `g \circ f` agrees with the composite obtained by first applying the relative cup product for
`g` to `Rf_* K` and `Rf_* L`, then applying `Rg_*` to the relative cup product for `f`, and
finally identifying `Rg_* Rf_*` with `R(g \circ f)_*`. Equivalently, the composition square of
relative cup products is commutative in `D(\mathcal O_Z)` for all `K, L` in `D(\mathcal O_X)`. -/
theorem relativeDerivedCupProduct_comp
    (K L : DModX) :
    compositeRelativeDerivedCupProduct K L =
      iteratedRelativeDerivedCupProduct K L := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_31_8 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules on a
ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X X' Y Y' : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModX'" => ModuleDerived X'
local notation "DModY" => ModuleDerived Y
local notation "DModY'" => ModuleDerived Y'

variable
  (Lf : DModY ⥤ DModX)
  (Lf' : DModY' ⥤ DModX')
  (Lg : DModY ⥤ DModY')
  (Lg' : DModX ⥤ DModX')
  (Rf : DModX ⥤ DModY)
  (Rf' : DModX' ⥤ DModY')

variable
  (tensorX : DModX ⥤ DModX ⥤ DModX)
  (tensorX' : DModX' ⥤ DModX' ⥤ DModX')
  (tensorY : DModY ⥤ DModY ⥤ DModY)
  (tensorY' : DModY' ⥤ DModY' ⥤ DModY')

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is a derived base-change map if, after
transposing across the adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported through the commutativity isomorphism
`L(g)^* \circ L(f')^* \cong L(f)^* \circ L(g')^*`. -/
def IsDerivedBaseChangeMap
    (K : DModX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
noncomputable def relativeDerivedCupProductAdjoint
    (pullbackTensorIso :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DModX) :
    Lf.obj ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      ((tensorX.obj L).obj K) :=
  (pullbackTensorIso (Rf.obj K) (Rf.obj L)).hom ≫
    ((tensorX.map (adj_f.counit.app L)).app (Lf.obj (Rf.obj K))) ≫
    ((tensorX.obj L).map (adj_f.counit.app K))

/-- The relative cup product attached to an adjunction `Lf^* ⊣ Rf_*` and a pullback-tensor
comparison for `Lf^*`. -/
noncomputable def relativeDerivedCupProduct
    (pullbackTensorIso :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DModX) :
    ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      Rf.obj ((tensorX.obj L).obj K) :=
  (adj_f.homEquiv
      ((tensorY.obj (Rf.obj L)).obj (Rf.obj K))
      ((tensorX.obj L).obj K))
    (relativeDerivedCupProductAdjoint
      Lf
      Rf
      tensorX
      tensorY
      adj_f
      pullbackTensorIso
      K
      L)

-- Proof sketch: transpose both routes across `adj_f'`. The three base-change hypotheses identify
-- the vertical maps with the pullback of the counits via `squareIso`, while the two cup-product
-- maps are, by definition, the transposes of the pullback-tensor comparisons followed by those
-- same counits. After rewriting the pullbacks of the tensor products with `pullbackTensorIso_g`
-- and `pullbackTensorIso_g'`, both transposes are the same morphism from
-- `Lf' Lg (Rf K \otimes^{\mathbf L} Rf L)` to `Lg' (K \otimes^{\mathbf L} L)`.
/-- Lemma 20.31.8: for a commutative square of ringed spaces, the relative cup product is
compatible with base change. Formally, given derived pullback and pushforward functors for the
four corners, adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, pullback-tensor comparison
isomorphisms for the horizontal and vertical maps, and base-change morphisms for `K`, `L`, and
`K \otimes_{\mathcal O_X}^{\mathbf L} L`, the resulting square comparing the relative cup product
for `f` with the relative cup product for `f'` commutes in `D(\mathcal O_{Y'})`. -/
theorem relativeDerivedCupProduct_baseChange_commutes
    (pullbackTensorIso_f :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ (A B : DModY'),
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ (A B : DModY),
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ (A B : DModX),
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (K L : DModX)
    (ηK : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (ηL : Lg.obj (Rf.obj L) ⟶ Rf'.obj (Lg'.obj L))
    (ηKL : Lg.obj (Rf.obj ((tensorX.obj L).obj K)) ⟶
      Rf'.obj (Lg'.obj ((tensorX.obj L).obj K)))
    (hηK : IsDerivedBaseChangeMap K ηK)
    (hηL : IsDerivedBaseChangeMap L ηL)
    (hηKL : IsDerivedBaseChangeMap ((tensorX.obj L).obj K) ηKL) :
    Lg.map
        (relativeDerivedCupProduct pullbackTensorIso_f K L) ≫
      ηKL ≫
      Rf'.map ((pullbackTensorIso_g' K L).hom) =
    ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom) ≫
      ((tensorY'.map ηL).app (Lg.obj (Rf.obj K))) ≫
      ((tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK) ≫
      relativeDerivedCupProduct pullbackTensorIso_f' (Lg'.obj K) (Lg'.obj L) := sorry

end

end AlgebraicGeometry.RingedSpace
