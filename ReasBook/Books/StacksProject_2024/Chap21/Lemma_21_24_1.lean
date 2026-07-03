import Mathlib
import StacksProject_2024.Chap13.Lemma_13_29_3
import StacksProject_2024.Chap18.Lemma_18_27_9
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

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
