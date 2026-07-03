import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap21.Lemma_21_20_5

open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

open RingedSite.Hom

namespace RingedSite

/-- The additive functor from `\mathcal O_X`-modules to abelian presheaves on the underlying site
of `X`, obtained by forgetting module structure to the underlying abelian sheaf and then
forgetting the sheaf condition. -/
private abbrev underlyingAbelianPresheafFunctor (X : RingedSite.{u, v}) :
    ModuleCat X ⥤ Xᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}

/-- The total right derived functor of the underlying-abelian-presheaf functor on a ringed site.
-/
private abbrev underlyingAbelianPresheafDerived (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    DerivedCategory (ModuleCat X) ⥤
      DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (underlyingAbelianPresheafFunctor X)

/-- The presheaf `U ↦ H^i(U, K)` on a ringed site `X`, realized as the degree-`i` homology
presheaf of the derived underlying-presheaf functor. -/
abbrev objectwiseCohomologyPresheaf (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (K : DerivedCategory (ModuleCat X)) (i : ℤ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) i).obj
    ((underlyingAbelianPresheafDerived X).obj K)

/-- The underlying abelian sheaf of the degree-`i` cohomology sheaf `H^i(K)` on a ringed site
`X`. -/
abbrev cohomologySheaf (X : RingedSite.{u, v})
    (K : DerivedCategory (ModuleCat X)) (i : ℤ) :
    Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf X.structureSheaf).obj
    ((DerivedCategory.homologyFunctor (ModuleCat X) i).obj K)

end RingedSite

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The presheaf on the target site sending `V` to the objectwise cohomology `H^i(u(V), K)` on
the source site, expressed by precomposition with the continuous functor underlying `f`. -/
abbrev sourceObjectwiseCohomologyPresheaf (f : RingedSite.Hom X Y)
    (K : ModuleDerived X) (i : ℤ) :
    Yᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  f.base.op ⋙ X.objectwiseCohomologyPresheaf K i

-- Proof sketch: for each object `V : Y`, Lemma `21.20.5 (2)` identifies `RΓ(u(V), K)` with
-- `RΓ(V, Rf_* K)` after restriction of scalars. Taking degree-`i` homology and forgetting the
-- module structure gives the required objectwise isomorphism of abelian presheaves.
/-- The source-side and pushforward-side objectwise cohomology presheaves are canonically
isomorphic. -/
theorem sourceObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      (sourceObjectwiseCohomologyPresheaf f K i)
      (Y.objectwiseCohomologyPresheaf ((modulePushforwardDerived f).obj K) i) := sorry

-- Proof sketch: first replace the presheaf `V ↦ H^i(u(V), K)` by the canonically isomorphic
-- presheaf `V ↦ H^i(V, Rf_* K)` using the previous theorem. Then identify the sheafification of
-- that presheaf with the cohomology sheaf `H^i(Rf_* K)` on the target ringed site via the
-- derived underlying-presheaf comparison.
/-- Lemma 21.20.6: for a morphism of ringed sites `f : X ⟶ Y` and `K : D(\mathcal O_X)`, the
sheaf associated to the presheaf `V ↦ H^i(u(V), K)` is the degree-`i` cohomology sheaf of
`Rf_* K`. Equivalently, it is the sheaf associated to `V ↦ H^i(V, Rf_* K)`. -/
theorem sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (sourceObjectwiseCohomologyPresheaf f K i))
      (Y.cohomologySheaf ((modulePushforwardDerived f).obj K) i) := sorry

end

end RingedSite.Hom
