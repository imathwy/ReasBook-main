import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap21.Lemma_21_19_1_core

open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.20.3:
- primary domain: objectwise derived cohomology presheaves and cohomology sheaves on a ringed
  site;
- sampled owner declarations:
  `SheafOfModules.toSheaf`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.additiveFunctorTotalRightDerived`,
  `RingedSite.Hom.underlyingAbelianSheafFunctor`;
- best owner abstraction: the source-facing owner `𝓗^q(K)` should live in the module
  category `ModuleCat X`, while forgetting to additive sheaves is only the
  canonical bridge `underlyingAbelianSheafFunctor X`;
- primitive data: a ringed site `X`, a derived object `K : ModuleDerived X`, and a degree
  `q : ℤ`;
- derived API: the source-facing owners `objectwiseCohomologyPresheaf`, `cohomologySheaf`,
  `cohomologyOverObject`, the underlying-abelian bridge
  `underlyingAbelianCohomologySheaf`, the notation in the `RingedSiteCohomology` scope, and the
  sheafification comparison theorem.

Source/core/bridge triage:
- `source-facing`: the presheaf `U ↦ H^q(U, K)` and the module-valued cohomology sheaf
  `𝓗^q(K)`;
- `core/canonical`: `DerivedCategory.homologyFunctor` on `ModuleCat X` and
  the forgetful functor `SheafOfModules.toSheaf X.structureSheaf`;
- `bridge/view`: the underlying additive sheaf of `𝓗^q(K)` and the additive presheaf
  obtained by derived sections.
-/

section

variable (X : RingedSite.{u, v})

/-- The forgetful functor from `𝒪_X`-modules to their underlying abelian sheaves. -/
abbrev underlyingAbelianSheafFunctor :
    ModuleCat X ⥤ Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf

/-- The forgetful functor from `𝒪_X`-modules to their underlying abelian presheaves. -/
abbrev underlyingAbelianPresheafFunctor :
    ModuleCat X ⥤ (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  underlyingAbelianSheafFunctor X ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}

/-- The forgetful functor to underlying abelian presheaves is exact. -/
theorem underlyingAbelianPresheafFunctor_exact :
    exactFunctor
      (ModuleCat X)
      (Xᵒᵖ ⥤ AddCommGrpCat.{max u v})
      (underlyingAbelianPresheafFunctor X) := by
  sorry

/-- The homotopy-to-derived functor induced by `underlyingAbelianPresheafFunctor X`. -/
abbrev underlyingAbelianPresheafToDerived :
    HomotopyCategory (ModuleCat X) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (underlyingAbelianPresheafFunctor X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}))

/-- The canonical existence statement for the right derived functor of
`underlyingAbelianPresheafFunctor X`. -/
instance underlyingAbelianPresheafToDerived_hasRightDerivedFunctor
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    Functor.HasRightDerivedFunctor (underlyingAbelianPresheafToDerived X) (ModuleQis X) := by
  sorry

/-- The canonical derived functor of the exact additive presheaf functor
`underlyingAbelianSheafFunctor X ⋙ sheafToPresheaf ...`. -/
noncomputable abbrev underlyingAbelianPresheafDerived :
    ModuleDerived X ⥤ DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  let F := underlyingAbelianPresheafFunctor X
  letI : F.Additive :=
    exactFunctor_le_additiveFunctor
      (ModuleCat X)
      (Xᵒᵖ ⥤ AddCommGrpCat.{max u v})
      F
      (underlyingAbelianPresheafFunctor_exact X)
  letI : Limits.PreservesFiniteLimits F :=
    (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact X) |>.1
  letI : Limits.PreservesFiniteColimits F :=
    (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact X) |>.2
  F.mapDerivedCategory

/-- The additive presheaf `U ↦ H^q(U, K)` attached to a derived `𝒪_X`-module. -/
abbrev objectwiseCohomologyPresheaf (K : ModuleDerived X) (q : ℤ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) q).obj
    ((underlyingAbelianPresheafDerived X).obj K)

/-- The degree-`q` cohomology sheaf `𝓗^q(K)` of a derived `𝒪_X`-module. -/
abbrev cohomologySheaf (K : ModuleDerived X) (q : ℤ) :
    ModuleCat X :=
  (DerivedCategory.homologyFunctor (ModuleCat X) q).obj K

/-- The morphism `𝓗^q(K) ⟶ 𝓗^q(L)` induced by a morphism `K ⟶ L` in `D(𝒪_X)`. -/
abbrev cohomologySheafMap
    (q : ℤ)
    {K L : ModuleDerived X} (f : K ⟶ L) :
    cohomologySheaf X K q ⟶ cohomologySheaf X L q :=
  (DerivedCategory.homologyFunctor (ModuleCat X) q).map f

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `𝓗^q(K)`. -/
abbrev underlyingAbelianCohomologySheaf (K : ModuleDerived X) (q : ℤ) :
    Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  (underlyingAbelianSheafFunctor X).obj (cohomologySheaf X K q)

/-- The degree-`q` cohomology group `H^q(U, K)` over a fixed object of a ringed site. -/
abbrev cohomologyOverObject (U : X) (K : ModuleDerived X) (q : ℤ) :
    AddCommGrpCat.{max u v} :=
  (objectwiseCohomologyPresheaf X K q).obj (op U)

end

end RingedSite.Hom

namespace RingedSiteCohomology

/- Textbook surface notation: `𝓗'[q](X, K)` denotes the presheaf `U ↦ H^q(U, K)`,
`𝓗[q](X, K)` denotes the module-valued cohomology sheaf `𝓗^q(K)`, and `H^q(U, K)` denotes the
value of `𝓗'[q](X, K)` at `U`. -/
@[inherit_doc RingedSite.Hom.objectwiseCohomologyPresheaf]
scoped[RingedSiteCohomology] notation3:max "𝓗'[" q:max "](" X ", " K ")" =>
  RingedSite.Hom.objectwiseCohomologyPresheaf X K q

@[inherit_doc RingedSite.Hom.cohomologySheaf]
scoped[RingedSiteCohomology] notation3:max "𝓗[" q:max "](" X ", " K ")" =>
  RingedSite.Hom.cohomologySheaf X K q

@[inherit_doc RingedSite.Hom.cohomologyOverObject]
scoped[RingedSiteCohomology] notation3:max "H^" q:max "(" U ", " K ")" =>
  RingedSite.Hom.cohomologyOverObject _ U K q

end RingedSiteCohomology

namespace RingedSite.Hom

open scoped RingedSiteCohomology

section

variable (X : RingedSite.{u, v})

variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]

-- Proof sketch: regard `K` through the exact derived forgetful functor
-- `underlyingAbelianPresheafDerived X`. Its degree-`q` homology presheaf is exactly
-- `𝓗'[q](X, K)`, while `underlyingAbelianCohomologySheaf X K q` is the underlying abelian sheaf
-- of the module-valued cohomology sheaf `𝓗[q](X, K)`.
/-- Lemma 21.20.3: for a ringed site `X`, an object `K : ModuleDerived X`, and an integer `q`,
the sheaf associated to the presheaf `U ↦ H^q(U, K)` is canonically isomorphic to the
underlying abelian sheaf of the degree-`q` cohomology sheaf `𝓗[q](X, K)`. -/
@[stacks 0BKV]
theorem objectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf
    (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf X.siteTopology AddCommGrpCat.{max u v}).obj
        (𝓗'[q](X, K)))
      (underlyingAbelianCohomologySheaf X K q) := by
  sorry

end

end RingedSite.Hom

attribute [-instance] HasDerivedCategory.standard
