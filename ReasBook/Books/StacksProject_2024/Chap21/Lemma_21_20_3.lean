import Mathlib
import StacksProject_2024.Chap18.Lemma_18_27_9
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

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

variable [hGroth : IsGrothendieckAbelian.{w} Mod]

/-- The additive functor from `\operatorname{Mod}(\mathcal O)` to abelian presheaves on
`(\mathcal C, J)` obtained by forgetting the module structure to the underlying abelian sheaf and
then forgetting the sheaf condition. -/
abbrev ringedSiteUnderlyingAbelianPresheafFunctor :
    Mod ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
    sheafToPresheaf J AddCommGrpCat.{u}

/-- The total right derived functor of the forgetful functor from `\operatorname{Mod}(\mathcal O)`
to abelian presheaves on `(\mathcal C, J)`. -/
abbrev ringedSiteUnderlyingAbelianPresheafDerived :
    DerivedCategory Mod ⥤ DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) _ _ _ _
    (ringedSiteUnderlyingAbelianPresheafFunctor J 𝒪)
    inferInstance hGroth

/-- The presheaf `U ↦ H^q(U, K)` for a derived `\mathcal O`-module `K`, realized as the
degree-`q` homology presheaf of the total right derived underlying-presheaf functor. -/
abbrev ringedSiteObjectwiseCohomologyPresheaf
    (K : DerivedCategory Mod) (q : ℤ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) q).obj
    ((ringedSiteUnderlyingAbelianPresheafDerived J 𝒪).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` of a derived
`\mathcal O`-module `K`. -/
abbrev ringedSiteCohomologySheaf
    (K : DerivedCategory Mod) (q : ℤ) :
    Sheaf J AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)).obj
    ((DerivedCategory.homologyFunctor Mod q).obj K)

/-- Lemma 21.20.3: for a ringed site `(\mathcal C, \mathcal O)` and an object `K` of
`D(\mathcal O)`, the sheaf associated to the presheaf `U ↦ H^q(U, K)` is the underlying abelian
sheaf of the degree-`q` cohomology sheaf `H^q(K)`. -/
abbrev ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (K : DerivedCategory Mod) (q : ℤ) : Prop :=
  IsIsomorphic
    (ringedSiteCohomologySheaf J 𝒪 K q)
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (ringedSiteObjectwiseCohomologyPresheaf J 𝒪 K q))

end

attribute [-instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [hGroth : IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]

local notation "StdDerivedMod" =>
  @DerivedCategory (ringedSiteModuleCategory J 𝒪) _ _
    (HasDerivedCategory.standard (ringedSiteModuleCategory J 𝒪))

-- Proof sketch: this is exactly the comparison proposition introduced above; the substantive proof
-- will identify the derived underlying-presheaf homology with the underlying sheaf homology after
-- sheafification.
/-- Canonical theorem wrapper for the ringed-site comparison between sheafified objectwise
cohomology and the cohomology sheaf. -/
theorem ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf_holds
    (K : StdDerivedMod) (q : ℤ) :
    ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf J 𝒪 K q :=
  sorry

end
