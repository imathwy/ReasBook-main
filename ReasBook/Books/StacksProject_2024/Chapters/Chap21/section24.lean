import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_24_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [hGroth : IsGrothendieckAbelian.{w} Mod]
variable [HasCountableProducts Mod]
variable [EnoughInjectives Mod]

/-- The object property of being injective in `\mathrm{Mod}(\mathcal O)`. -/
abbrev injectiveModuleProperty : CategoryTheory.ObjectProperty Mod :=
  fun M ↦ Injective M

/-- The forgetful functor from `\mathrm{Mod}(\mathcal O)` to abelian presheaves on
`(\mathcal C, J)`. -/
private abbrev ringedSiteUnderlyingAbelianPresheafFunctor :
    Mod ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
    sheafToPresheaf J AddCommGrpCat.{u}

/-- The derived forgetful functor from `D(\mathcal O)` to derived abelian presheaves on
`(\mathcal C, J)`. -/
private abbrev ringedSiteUnderlyingAbelianPresheafDerived :
    DerivedCategory Mod ⥤ DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) _ _ _ _
    (ringedSiteUnderlyingAbelianPresheafFunctor J 𝒪)
    inferInstance hGroth

/-- The presheaf `U ↦ H^q(U, K)` attached to a derived `\mathcal O`-module `K`. -/
private abbrev ringedSiteObjectwiseCohomologyPresheaf
    (K : DerivedCategory Mod) (q : ℤ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) q).obj
    ((ringedSiteUnderlyingAbelianPresheafDerived J 𝒪).obj K)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O`-modules on
the ringed site `(\mathcal C, \mathcal O)`, computed by viewing `\mathcal F` in degree `0`. -/
abbrev ringedSiteModuleCohomologyOverObject
    (U : C) (p : ℤ) (ℱ : Mod) :
    AddCommGrpCat.{u} :=
  (ringedSiteObjectwiseCohomologyPresheaf J 𝒪
    ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ) p).obj (op U)

/-- Uniform vanishing of `H^p(U, H^q(F^•))` on the basis objects `U ∈ B` for all `p > d` and
negative `q`. -/
abbrev uniformBasiswiseNegativeCohomologySheafVanishing
    (F : CochainComplex Mod ℤ) (B : Set C) (d : ℕ) : Prop :=
  ∀ ⦃U : C⦄, U ∈ B → ∀ p q : ℤ, (d : ℤ) < p → q < 0 →
    IsZero
      (ringedSiteModuleCohomologyOverObject J 𝒪 U p
        ((DerivedCategory.homologyFunctor Mod q).obj (Q.obj F)))

/-- The inverse limit of the chosen lower truncation resolution system, with the `HasLimit`
evidence made explicit. -/
abbrev lowerTruncationResolutionSystemLimit
    (F : CochainComplex Mod ℤ)
    (S : LowerTruncationResolutionSystem (injectiveModuleProperty J 𝒪) F)
    (hS : HasLimit S.diagram) :
    CochainComplex Mod ℤ :=
  @CategoryTheory.Limits.limit _ _ _ _ S.diagram hS

/-- The projection from the explicit inverse limit of the lower truncation resolution system to
its `n`th stage. -/
abbrev lowerTruncationResolutionSystemLimitProj
    (F : CochainComplex Mod ℤ)
    (S : LowerTruncationResolutionSystem (injectiveModuleProperty J 𝒪) F)
    (hS : HasLimit S.diagram) (n : ℕ) :
    lowerTruncationResolutionSystemLimit J 𝒪 F S hS ⟶ S.diagram.obj (Opposite.op n) :=
  @CategoryTheory.Limits.limit.π _ _ _ _ S.diagram hS (Opposite.op n)

/-- A morphism `γ : F^• ⟶ lim I_n^•` is a comparison with the chosen lower truncation resolution
system if its composites with the limit projections recover the stage comparison maps. -/
abbrev isLowerTruncationResolutionLimitComparison
    (F : CochainComplex Mod ℤ)
    (S : LowerTruncationResolutionSystem (injectiveModuleProperty J 𝒪) F)
    (hS : HasLimit S.diagram)
    (γ : F ⟶ lowerTruncationResolutionSystemLimit J 𝒪 F S hS) : Prop :=
  ∀ n : ℕ,
    γ ≫ lowerTruncationResolutionSystemLimitProj J 𝒪 F S hS n =
      F.πTruncGE (-(((n + 1 : ℕ)) : ℤ)) ≫ S.comparison.app (Opposite.op n)

-- Proof sketch: apply Lemma `13.34.6` to reduce the quasi-isomorphism of
-- any compatible comparison map `γ` from `F^•` to the inverse limit `lim I_n^•` to the statement
-- that the induced map in the derived category is an isomorphism. The latter is exactly the
-- uniform-basis vanishing criterion supplied by Lemma `21.23.10` for the negative cohomology
-- sheaves `H^q(F^•)`. Applied to the universal `limit.lift`, this yields the textbook map
-- `(21.24.0.1)`.
/-- Lemma 21.24.1: the assertion that if every object of the site admits a covering by members of
`B` and, for every `U ∈ B`, the higher cohomology groups `H^p(U, H^q(\mathcal F^\bullet))`
vanish for `p > d` and `q < 0`, then any comparison map
`\mathcal F^\bullet \to \varprojlim_n \mathcal I_n^\bullet` whose composites with the limit
projections recover the stage maps of the lower truncation resolution system is a quasi-isomorph-
ism; in particular, this applies to the canonical map `(21.24.0.1)`. -/
abbrev lowerTruncationResolutionLimit_comparison_quasiIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (F : CochainComplex Mod ℤ)
    (S : LowerTruncationResolutionSystem (injectiveModuleProperty J 𝒪) F)
    (hS : HasLimit S.diagram)
    (γ : F ⟶ lowerTruncationResolutionSystemLimit J 𝒪 F S hS)
    (B : Set C)
    (d : ℕ) :
    Prop :=
  isLowerTruncationResolutionLimitComparison J 𝒪 F S hS γ →
    (∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow, I.Y ∈ B) →
      uniformBasiswiseNegativeCohomologySheafVanishing J 𝒪 F B d →
        QuasiIso γ

end

-- Proof sketch: this theorem is a companion theorem-form handle for the criterion above.
/-- A companion theorem name for the comparison quasi-isomorphism criterion. -/
theorem lowerTruncationResolutionLimit_comparison_quasiIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing_apply :
    True := sorry

/-! ### Lemma_21_24_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe u v w z

/- Domain-style sampling for Lemma 21.24.2:
- primary domain: sequential inverse systems of cochain complexes of `\mathcal O_X`-modules on a
  ringed site, evaluated objectwise and then passed to cohomology sheaves;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`,
  `limit.post`;
- best owner abstraction: the tower itself is a `SequentialInverseSystem`, while the canonical
  map `H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet)` is the
  standard `limit.post` morphism for the composite with the cohomology-sheaf functor.

Source/core/bridge triage:
- `source-facing`: the final basiswise hypothesis theorem about the two cohomology-sheaf maps;
- `core/canonical`: `SequentialInverseSystem`, `.transitionMap`, `.IsMittagLeffler`, and
  `limit.post`;
- `bridge/view`: the objectwise degree/cohomology towers obtained from sections over `U`.

Primitive data are just the ringed site `X`, the tower `F`, the object `U`, and the degree `m`.
The transition maps, Mittag-Leffler conditions, and limit comparison morphism are derived API from
the owner abstractions above, so this file should reuse those owners directly rather than keep
parallel local copies.
-/

/-- The category of cochain complexes of `\mathcal O_X`-modules on the ringed site `X`. -/
abbrev ringedSiteComplex (X : RingedSite.{u, v}) :=
  CochainComplex (SheafOfModules X.structureSheaf) ℤ

/-- The sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over the fixed object `U`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The inverse system of complexes of abelian groups obtained by taking sections over `U`
termwise. -/
private abbrev ringedSiteObjectwiseComplexInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) :
    SequentialInverseSystem (CochainComplex AddCommGrpCat.{max u v} ℤ) :=
  F ⋙ (ringedSiteSectionsOverObjectFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The inverse system `n ↦ \mathcal F_n^m(U)` attached to a tower of complexes on a ringed site.
-/
abbrev ringedSiteObjectwiseDegreeInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) (m : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ringedSiteObjectwiseComplexInverseSystem X F U ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m

/-- The inverse system `n ↦ H^m(\mathcal F_n^\bullet(U))` attached to a tower of complexes on a
ringed site. -/
abbrev ringedSiteObjectwiseCohomologyInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) (m : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ringedSiteObjectwiseComplexInverseSystem X F U ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m

/-- The inverse system of degree-`m` cohomology sheaves of the tower
`(\mathcal F_n^\bullet)_n`. -/
abbrev ringedSiteCohomologySheafTower (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ) :=
  F ⋙ HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ) m ⋙
    SheafOfModules.toSheaf X.structureSheaf

/-- The canonical morphism
`H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet)` on
underlying abelian sheaves. -/
abbrev ringedSiteCohomologySheafLimitComparison
    (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ)
    [HasLimit F] [HasLimit (ringedSiteCohomologySheafTower X F m)] :
    (SheafOfModules.toSheaf X.structureSheaf).obj
        ((HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf)
          (ComplexShape.up ℤ) m).obj (limit F)) ⟶
      limit (ringedSiteCohomologySheafTower X F m) :=
  limit.post F
    (HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf)
      (ComplexShape.up ℤ) m ⋙ SheafOfModules.toSheaf X.structureSheaf)

-- Proof sketch: for each basis object `U ∈ B`, apply Lemma `15.87.3` to the tower of complexes
-- `\Gamma(U, \mathcal F_n^\bullet)` in degrees shifted by `m`; the hypotheses force the
-- comparison `H^m(\Gamma(U, \varprojlim_n \mathcal F_n^\bullet)) \to
-- \varprojlim_n H^m(\Gamma(U, \mathcal F_n^\bullet))` to be an isomorphism, and eventual
-- constancy identifies the latter with `H^m(\Gamma(U, \mathcal F_{n_0}^\bullet))`. Since every
-- object admits a cover by elements of `B`, the two resulting morphisms of abelian sheaves are
-- isomorphisms.
/-- Lemma 21.24.2: let `(\mathcal C, \mathcal O)` be a ringed site, let
`(\mathcal F_n^\bullet)_n` be an inverse system of complexes of `\mathcal O`-modules, and let
`m ∈ \mathbf Z`. If a subset `B` of objects covers the site, if for every `U ∈ B` the towers
`n ↦ \mathcal F_n^{m - 2}(U)`, `n ↦ \mathcal F_n^{m - 1}(U)`, and
`n ↦ H^{m - 1}(\mathcal F_n^\bullet(U))` have vanishing `R^1 \!\varprojlim`, and if the tower
`n ↦ H^m(\mathcal F_n^\bullet(U))` is constant from stage `n₀` on for every `U ∈ B`, then the
canonical maps
`H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet) ⟶
H^m(\mathcal F_{n₀}^\bullet)` are isomorphisms of underlying abelian sheaves. -/
theorem cohomologySheafLimitComparison_and_projection_isIso_of_basiswise_vanishing_r1lim
    (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ) (B : Set X) (n₀ : ℕ)
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [HasLimit F]
    [HasLimit (ringedSiteCohomologySheafTower X F m)]
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hdeg_m_sub_two : ∀ U : X, U ∈ B →
      IsMittagLeffler (ringedSiteObjectwiseDegreeInverseSystem X F U (m - 2)))
    (hdeg_m_sub_one : ∀ U : X, U ∈ B →
      IsMittagLeffler (ringedSiteObjectwiseDegreeInverseSystem X F U (m - 1)))
    (hcohom_m_sub_one : ∀ U : X, U ∈ B →
      IsMittagLeffler
        (ringedSiteObjectwiseCohomologyInverseSystem X F U (m - 1)))
    (heventually_constant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((ringedSiteObjectwiseCohomologyInverseSystem X F U m).transitionMap h))
    :
    IsIso (ringedSiteCohomologySheafLimitComparison X F m) ∧
      IsIso (limit.π (ringedSiteCohomologySheafTower X F m) (op n₀)) := sorry
