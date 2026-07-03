import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_40_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]

/-- The underlying sheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditiveSheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The forgetful functor from `\mathcal O_X`-modules to abelian sheaves preserves zero
morphisms. -/
instance moduleUnderlyingAdditiveSheaf_preservesZeroMorphisms (X : RingedSpace.{u}) :
    (moduleUnderlyingAdditiveSheaf X).PreservesZeroMorphisms :=
  show (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms from inferInstance

/-- The global-sections functor on `\mathcal O_X`-modules, after forgetting the
`\Gamma(X, \mathcal O_X)`-module structure down to abelian groups. -/
abbrev moduleGlobalSectionsAsAbelianFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  moduleGlobalSectionsFunctor X ⋙
    forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}

/-- The global-sections functor on `\mathcal O_X`-modules is additive after forgetting the
module structure. -/
instance moduleGlobalSectionsAsAbelianFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsAsAbelianFunctor X).Additive :=
  inferInstance

/-- Applying abelian global sections termwise to a complex of `\mathcal O_X`-modules, then
localizing to the derived category of abelian groups. -/
abbrev moduleGlobalSectionsAsAbelianToDerived (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleGlobalSectionsToDerived X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The total alternating Čech complex of a complex of `\mathcal O_X`-modules, formed after
forgetting to abelian sheaves on the underlying space. -/
abbrev moduleAlternatingCechTotalComplexFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (moduleUnderlyingAdditiveSheaf X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰

/-- The total alternating Čech complex of a complex of `\mathcal O_X`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleAlternatingCechToDerivedFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleAlternatingCechTotalComplexFunctor X 𝒰 ⋙ DerivedCategory.Q

/-- The abelian-valued derived global-sections functor `R\Gamma(X, -)` on `D(\mathcal O_X)`. -/
abbrev moduleDerivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The canonical comparison from the underived abelian global-sections complex to
`R\Gamma(X, -)` in `D(\operatorname{Ab})`. -/
abbrev moduleGlobalSectionsAsAbelianDerivedUnit (X : RingedSpace.{u}) :
    moduleGlobalSectionsAsAbelianToDerived X ⟶
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X :=
  Functor.whiskerRight
      ((moduleGlobalSectionsToDerived X).totalRightDerivedUnit
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)))
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (moduleDerivedGlobalSections X)
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)).hom

/-- The complex-level map of `20.40.0.1` for a complex of `\mathcal O_X`-modules, obtained after
forgetting to abelian sheaves on the underlying space. -/
abbrev moduleGlobalSectionsToAlternatingCechTotalMap (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    ((moduleGlobalSectionsAsAbelianFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K :=
  TopCat.Sheaf.globalSectionsToAlternatingCechTotalMap X.carrier 𝒰
    (((moduleUnderlyingAdditiveSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The canonical comparison from the localized underived abelian global-sections complex of `K`
to `R\Gamma(X, K)` in `D(\operatorname{Ab})`, rewritten so that its source is the localization of
the abelian global-sections complex itself. -/
abbrev moduleGlobalSectionsAsAbelianDerivedUnitApp (X : RingedSpace.{u})
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory.Q.obj (((moduleGlobalSectionsAsAbelianFunctor X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X).obj K :=
  ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv.app
      (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    (moduleGlobalSectionsAsAbelianDerivedUnit X).app K

-- Proof sketch: choose a functorial K-injective resolution of complexes of `\mathcal O_X`-
-- modules. Apply `20.40.0.1` to the chosen K-injective resolution, use the finite-cover
-- acyclicity of injective terms to see that this Čech map computes derived global sections, and
-- descend the resulting comparison along the quasi-isomorphism from the original complex to its
-- resolution. Naturality comes from functoriality of the chosen resolution, and compatibility says
-- that precomposing with the localized map of `20.40.0.1` recovers the canonical derived-unit map
-- for abelian global sections.
/-- Lemma 20.40.1: for a finite open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space
`(X,\mathcal O_X)`, there exists a functorial comparison from the total alternating Čech complex
of a complex of `\mathcal O_X`-modules to `R\Gamma(X,-)` in `D(\operatorname{Ab})`, and this
comparison is compatible with the canonical map of `20.40.0.1` from the underived global-sections
complex to the total alternating Čech complex. -/
theorem exists_moduleAlternatingCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X,
      ∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
        DerivedCategory.Q.map (moduleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K) ≫
            τ.app K =
          moduleGlobalSectionsAsAbelianDerivedUnitApp X K := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_40_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- A family `𝓑` of open subsets of a ringed space covers every open subset if each open `W` is
the supremum of a family of members of `𝓑`. -/
abbrev BasisCoversEveryOpen (X : RingedSpace.{u}) (𝓑 : Set (Opens X.carrier)) : Prop :=
  ∀ W : Opens X.carrier, ∃ κ : Type u, ∃ V : κ → Opens X.carrier,
    (∀ k, V k ∈ 𝓑) ∧ iSup V = W

-- Proof sketch: choose the compatible comparison `τ` from Lemma `20.40.1`. For bounded-below
-- truncations `τ_{\ge -n} F`, Lemma `20.23.6` identifies alternating and ordinary Čech total
-- complexes, and Lemma `20.25.2` computes `RΓ(X, τ_{\ge -n} F)` from the ordinary Čech complex
-- using the basiswise acyclicity of the terms. The cokernel and cohomology-sheaf vanishing
-- hypotheses let one pass to a truncation-limit injective resolution as in Lemma `20.38.1`; the
-- resulting inverse systems are eventually constant in each total degree because the alternating
-- Čech complex is finite. Applying the Milnor-type limit comparison then shows that `τ.app F` is
-- an isomorphism in `D(Ab)`.
/-- Lemma 20.40.2: for a finite open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space
`(X, \mathcal O_X)`, assume every open subset of `X` is covered by opens from `𝓑`, every finite
intersection `U_{i_0 \ldots i_p}` of members of `𝒰` lies in `𝓑`, and for every `U ∈ 𝓑` and
every `p > 0` the cohomology groups `H^p(U, \mathcal F^q)`,
`H^p(U, \operatorname{Coker}(\mathcal F^{q-1} \to \mathcal F^q))`, and
`H^p(U, H^q(\mathcal F^\bullet))` all vanish. Then there exists a comparison morphism of
Lemma `20.40.1` from the total alternating Čech complex of `\mathcal F^\bullet` to
`R\Gamma(X, \mathcal F^\bullet)` whose component at `\mathcal F^\bullet` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (𝓑 : Set (Opens X.carrier))
    (hcover : BasisCoversEveryOpen X 𝓑)
    (hinter :
      ∀ (p : ℕ) (σ : Fin (p + 1) → ι), (⨅ a, 𝒰 (σ a)) ∈ 𝓑)
    (hterm :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj (F.X q)).H' p U))
    (hcoker :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj
              (cokernel (F.d (q - 1) q))).H' p U))
    (hcohom :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj (F.homology q)).H' p U)) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X,
      (∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
        DerivedCategory.Q.map (moduleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K) ≫
            τ.app K =
          moduleGlobalSectionsAsAbelianDerivedUnitApp X K) ∧
        IsIso (τ.app F) := sorry

end AlgebraicGeometry.RingedSpace
