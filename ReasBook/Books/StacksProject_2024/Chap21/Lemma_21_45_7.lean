import Mathlib
import StacksProject_2024.Chap18.Definition_18_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- Restriction of `\mathcal O_X`-modules to the localized ringed site `X.localization U`. -/
private abbrev localizedRestrictionFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ LocalizedRingedSiteModuleCat X U :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- Restriction to a localized ringed site preserves zero morphisms. -/
instance localizedRestrictionFunctor_preservesZeroMorphisms
    (X : RingedSite.{u, v}) (U : X) :
    (localizedRestrictionFunctor X U).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_X`-modules to the localized ringed site
`X.localization U`. -/
private abbrev localizedRestrictionComplex (X : RingedSite.{u, v}) (U : X) :
    CochainComplex (RingedSiteModuleCat X) ℤ →
      CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ :=
  fun E ↦ ((localizedRestrictionFunctor X U).mapHomologicalComplex (up ℤ)).obj E

/-- A complex of `\mathcal O_U`-modules on a localized ringed site is strictly perfect when it is
bounded and each term is a retract of a finite free module. -/
private def localizedComplexIsStrictlyPerfect
    (X : RingedSite.{u, v}) {U : X}
    (E : CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty
        (Retract (E.X i)
          (SheafOfModules.free.{max u v} I : LocalizedRingedSiteModuleCat X U))

namespace DerivedCategory

/-- A derived `\mathcal O_X`-module is `m`-pseudo-coherent if it is represented by a complex whose
restriction to every localized site becomes, after some cover, cohomologically approximable by a
strictly perfect complex above degree `m` and surjectively in degree `m`. -/
def IsMPseudoCoherent
    (X : RingedSite.{u, v}) (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) : Prop :=
  ∃ E : CochainComplex (RingedSiteModuleCat X) ℤ,
    (∃ _ :
        K ≅
          ((DerivedCategory.Q :
              CochainComplex (RingedSiteModuleCat X) ℤ ⥤
                DerivedCategory (RingedSiteModuleCat X)).obj E),
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow,
        ∃ EI : CochainComplex (LocalizedRingedSiteModuleCat X I.Y) ℤ,
          ∃ α : EI ⟶ localizedRestrictionComplex X I.Y E,
            localizedComplexIsStrictlyPerfect X EI ∧
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m))

-- Proof sketch: this is a direct unfolding of the local strictly-perfect approximation condition
-- built into `IsMPseudoCoherent`.
/-- Unfolding `IsMPseudoCoherent` gives a representing complex whose localized restrictions admit
strictly perfect approximations after covers, with the specified cohomological control. -/
theorem isMPseudoCoherent_iff
    (X : RingedSite.{u, v}) (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    IsMPseudoCoherent X K m ↔
      ∃ E : CochainComplex (RingedSiteModuleCat X) ℤ,
        (∃ _ :
            K ≅
              ((DerivedCategory.Q :
                  CochainComplex (RingedSiteModuleCat X) ℤ ⥤
                    DerivedCategory (RingedSiteModuleCat X)).obj E),
          ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow,
            ∃ EI : CochainComplex (LocalizedRingedSiteModuleCat X I.Y) ℤ,
              ∃ α : EI ⟶ localizedRestrictionComplex X I.Y E,
                localizedComplexIsStrictlyPerfect X EI ∧
                (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                Epi (HomologicalComplex.homologyMap α m)) := sorry

end DerivedCategory

section

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X
local notation "DModX" => DerivedCategory ModX

variable [Abelian ModX]
variable [CategoryWithHomology ModX]

-- Proof sketch: fix an object `U` of the site and use `m`-pseudo-coherence to refine `U` by a
-- cover on which `K` is approximated by a strictly perfect complex inducing cohomology
-- isomorphisms above `m` and an epimorphism in degree `m`. The vanishing of `H^i(K)` for `i > m`
-- lets one trim the strictly perfect complex from the top degree downward, showing locally that
-- `H^m(K)` is a quotient of a finite free module and hence of finite type.
/-- Lemma 21.45.7 (1): if `K ∈ D(\mathcal O_X)` is `m`-pseudo-coherent and has no cohomology
above degree `m`, then `H^m(K)` is a finite type `\mathcal O_X`-module. -/
theorem top_cohomology_isFiniteType_of_isMPseudoCoherent
    (K : DModX) (m : ℤ)
    (hK : DerivedCategory.IsMPseudoCoherent X K m)
    (hvanish :
      ∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor ModX i).obj K)) :
    ((DerivedCategory.homologyFunctor ModX m).obj K).IsFiniteType := sorry

-- Proof sketch: again work locally on an arbitrary object and replace `K` by a strictly perfect
-- approximation controlling cohomology in degrees `> m` and degree `m`. The stronger vanishing
-- above `m + 1` lets one cut the approximation down so that locally it is concentrated in degrees
-- `≤ m + 1`, after which `H^{m+1}(K)` is identified with the cokernel of a morphism between
-- finite free modules, hence is finitely presented.
/-- Lemma 21.45.7 (2): if `K ∈ D(\mathcal O_X)` is `m`-pseudo-coherent and has no cohomology
above degree `m + 1`, then `H^{m + 1}(K)` is a finitely presented `\mathcal O_X`-module. -/
theorem next_cohomology_isFinitePresentation_of_isMPseudoCoherent
    (K : DModX) (m : ℤ)
    (hK : DerivedCategory.IsMPseudoCoherent X K m)
    (hvanish :
      ∀ i : ℤ, m + 1 < i →
        IsZero ((DerivedCategory.homologyFunctor ModX i).obj K)) :
    ((DerivedCategory.homologyFunctor ModX (m + 1)).obj K).IsFinitePresentation := sorry

end

end RingedSite
