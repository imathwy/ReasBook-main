import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap20.Lemma_20_11_11
import StacksProject_2024.Chap20.«20_25_0_2»

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open DerivedCategory.TStructure
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/-- The underlying sheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditiveSheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))

/-- The underlying presheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditivePresheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ X.carrier.Presheaf AddCommGrpCat.{u} :=
  moduleUnderlyingAdditiveSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The global-sections functor on `\mathcal O_X`-modules, after forgetting the
`\Gamma(X, \mathcal O_X)`-module structure down to abelian groups. -/
abbrev moduleGlobalSectionsAdditiveFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  moduleUnderlyingAdditiveSheaf X ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules is additive. -/
instance moduleGlobalSectionsAdditiveFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsAdditiveFunctor X).Additive := sorry

/-- The functor sending an `\mathcal O_X`-module to the extended Čech complex of its underlying
additive presheaf. -/
abbrev moduleCechRowFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  moduleUnderlyingAdditivePresheaf X ⋙
    cechComplexFunctor 𝒰 ⋙
      (ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat.{u}

/-- The extended rowwise Čech functor preserves zero morphisms. -/
instance moduleCechRowFunctor_preservesZeroMorphisms
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (moduleCechRowFunctor X 𝒰).PreservesZeroMorphisms := sorry

/-- The rowwise Čech bicomplex associated to a cochain complex of `\mathcal O_X`-modules and an
indexed family of opens. -/
abbrev moduleCechDoubleComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{u}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (moduleCechRowFunctor X 𝒰).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total Čech complex functor on cochain complexes of `\mathcal O_X`-modules. -/
abbrev moduleTotalCechComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  moduleCechDoubleComplexFunctor X 𝒰 ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

-- Proof sketch: the Čech direction is supported in nonnegative degrees, and the input complex is
-- bounded below, so only finitely many summands contribute to sufficiently negative total degrees.
-- Hence the total complex remains bounded below.
/-- The total Čech complex of a bounded-below complex of `\mathcal O_X`-modules is again bounded
below. -/
theorem moduleTotalCechComplex_obj_mem (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    CochainComplex.plus AddCommGrpCat.{u}
      ((moduleTotalCechComplexFunctor X 𝒰).obj K.obj) := sorry

/-- The total Čech complex functor, restricted to bounded-below complexes. -/
abbrev moduleTotalCechComplexToPlus (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤ CochainComplex.Plus AddCommGrpCat.{u} :=
  ObjectProperty.lift
    (CochainComplex.plus AddCommGrpCat.{u})
    (CochainComplex.Plus.ι (RingedSpace.Modules X) ⋙ moduleTotalCechComplexFunctor X 𝒰)
    (moduleTotalCechComplex_obj_mem X 𝒰)

section DerivedComparison

variable (X)
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

/-- The bounded-below derived functor represented by total Čech complexes for the family `𝒰`. -/
abbrev moduleCechDerivedFunctor (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u} :=
  moduleTotalCechComplexToPlus X 𝒰 ⋙
    CategoryTheory.boundedBelowCochainComplexToDerivedBelow (𝟭 AddCommGrpCat.{u})

/-- The bounded-below derived global-sections functor on complexes of `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSectionsFunctor :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.boundedBelowCochainComplexToDerivedBelow
    (moduleGlobalSectionsAdditiveFunctor X)

-- Proof sketch: choose a bounded-below injective resolution of the input complex, form the
-- rowwise Čech double complex on that injective resolution, and compare both the total Čech
-- complex and the derived global-sections complex with the total complex of the double complex.
-- Injective sheaf modules are Čech-acyclic on an open cover, so the resulting comparison is a
-- quasi-isomorphism and is natural in the input complex.
/-- Lemma 20.25.1: for an open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space `X`,
there is a natural transformation from the total Čech complex functor on bounded-below complexes
of `\mathcal O_X`-modules to the bounded-below derived global-sections functor `RΓ(X,-)`. This
formalizes the canonical map
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet)) \to RΓ(X,\mathcal F^\bullet)`,
functorial in `\mathcal F^\bullet`. -/
theorem moduleCechDerivedFunctor_exists_natTrans_to_derivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      (moduleCechDerivedFunctor X 𝒰 :
        CochainComplex.Plus (RingedSpace.Modules X) ⥤
          CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u}) ⟶
        moduleDerivedGlobalSectionsFunctor X,
      True := sorry

/-- The `E_2^{p,q}` term in the Čech-to-hypercohomology spectral sequence attached to the open
cover `𝒰` and a bounded-below complex `K`. -/
abbrev moduleCechHypercohomologyPageTwoTerm
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex.Plus (RingedSpace.Modules X))
    (p : ℕ) (q : ℤ) :
    AddCommGrpCat.{u} :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((cechComplexFunctor 𝒰).obj
      ((moduleUnderlyingAdditivePresheaf X).obj (K.obj.homology q)))

/-- The hypercohomology object `H^n(X, K)` computed via bounded-below derived global sections. -/
abbrev moduleDerivedGlobalSectionsCohomology
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (n : ℤ) :
    AddCommGrpCat.{u} :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((moduleDerivedGlobalSectionsFunctor X).obj K))

/-- A packaged cohomological spectral sequence computing hypercohomology from the Čech complexes
of the cohomology sheaves of a bounded-below complex. -/
structure CechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex.Plus (RingedSpace.Modules X)) where
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{u} 0
  /-- The `E_2`-page identifies with Čech cohomology of the cohomology sheaves `\underline H^q`.
  -/
  pageTwoIso :
    ∀ p : ℕ, ∀ q : ℤ,
      (spectralSequence.page 2).X (Int.ofNat p, q) ≅
        moduleCechHypercohomologyPageTwoTerm X 𝒰 K p q
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat.{u}
  /-- The abutment identifies with hypercohomology computed by `RΓ(X, K)`. -/
  targetIso :
    ∀ n : ℤ,
      abutment n ≅ moduleDerivedGlobalSectionsCohomology X K n

-- Proof sketch: choose a Cartan-Eilenberg resolution of the bounded-below complex `K`, apply the
-- Čech construction rowwise to obtain a triple complex, reinterpret it as a double complex, and
-- then take the second spectral sequence. The `E₂`-page identifies with Čech cohomology of the
-- cohomology sheaves, and convergence follows from the boundedness of the Cartan-Eilenberg model.
/-- A bounded-below Čech-to-hypercohomology spectral sequence for an open cover of a ringed space.
-/
theorem exists_moduleCechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    Nonempty (CechToDerivedGlobalSectionsSpectralSequence X 𝒰 K) := sorry

end DerivedComparison

end AlgebraicGeometry.RingedSpace
