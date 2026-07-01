import Mathlib
import stacks_project.Chap15.Lemma_15_87_10
import stacks_project.Chap21.Lemma_21_20_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.2:
- primary domain: derived global/objectwise sections on a ringed site and the Milnor short exact
  sequence for sequential derived limits in `D(\operatorname{Ab})`;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.moduleGlobalSectionsDerived`,
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction: the ambient module category and derived category are already owned by
  `RingedSite.Hom.ModuleCat` and `RingedSite.Hom.ModuleDerived`; the relevant derived functors are
  already owned by `moduleGlobalSectionsDerived` and `moduleSectionsAsAbelianDerived`; the Milnor
  short exact sequence is already owned by `derivedLimit_cohomology_shortExact`, whose left term
  is the canonical `firstDerivedLimit`, not a raw cokernel wrapper;
- primitive data: a ringed site `X`, optionally an object `U : X`, a sequential inverse system
  `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`, a chosen derived limit `K`, and a cohomological degree `m`;
- derived API: preservation of derived limits by the canonical derived sections functors, and the
  resulting Milnor short exact sequences on cohomology.

Source/core/bridge triage:
- `source-facing`: the four ringed-site statements below about `RΓ(\mathcal C,-)` and
  `RΓ(U,-)`;
- `core/canonical`: `ModuleCat`, `ModuleDerived`, `moduleGlobalSectionsDerived`,
  `moduleSectionsAsAbelianDerived`, and `derivedLimit_cohomology_shortExact`;
- `bridge/view`: this file, which specializes the canonical Chapter 15 and Chapter 19 owners to
  the ringed-site functors without introducing a parallel local wrapper API.
-/

section GlobalSections

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]

-- Proof sketch: specialize Lemma `19.13.6` to the canonical derived global-sections functor
-- `moduleGlobalSectionsDerived X`.
/-- Lemma 21.23.2 (1): for a ringed site `X`, the canonical derived global-sections functor
`R\Gamma(\mathcal C,-)` carries a derived limit of a sequential inverse system in
`D(\mathcal O_X)` to the derived limit of the stagewise derived global sections. -/
theorem ringedSiteDerivedGlobalSections_preservesDerivedLimit
    {Ksys : ℕᵒᵖ ⥤ ModuleDerived X} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ moduleGlobalSectionsDerived X)
      ((moduleGlobalSectionsDerived X).obj K) := sorry

-- Proof sketch: apply the Milnor short exact sequence of Lemma `15.87.10` to the inverse system
-- `Ksys ⋙ moduleGlobalSectionsDerived X` in `D(\operatorname{Ab})`.
/-- Lemma 21.23.2 (4): for a ringed site `X`, a sequential inverse system `(K_n)` in
`D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the global cohomology of
`K` fits into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(\mathcal C, K_n) \to H^m(\mathcal C, K) \to
\varprojlim H^m(\mathcal C, K_n) \to 0`. -/
theorem ringedSiteDerivedGlobalSections_cohomology_shortExact
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ moduleGlobalSectionsDerived X) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleGlobalSectionsDerived X).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleGlobalSectionsDerived X).obj K) ⟶
          limit
            ((Ksys ⋙ moduleGlobalSectionsDerived X) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end GlobalSections

section SectionsOverObject

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

-- Proof sketch: specialize Lemma `19.13.6` to the canonical derived sections functor
-- `moduleSectionsAsAbelianDerived X U`.
/-- Lemma 21.23.2 (2): for a ringed site `X` and an object `U : X`, the canonical derived sections
functor `R\Gamma(U,-)` carries a derived limit of a sequential inverse system in `D(\mathcal O_X)`
to the derived limit of the stagewise derived sections over `U`. -/
theorem ringedSiteDerivedSectionsOverObject_preservesDerivedLimit
    (U : X)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    {Ksys : ℕᵒᵖ ⥤ ModuleDerived X} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ moduleSectionsAsAbelianDerived X U)
      ((moduleSectionsAsAbelianDerived X U).obj K) := sorry

-- Proof sketch: apply the Milnor short exact sequence of Lemma `15.87.10` to the inverse system
-- `Ksys ⋙ moduleSectionsAsAbelianDerived X U` in `D(\operatorname{Ab})`.
/-- Lemma 21.23.2 (3): for a ringed site `X`, an object `U : X`, a sequential inverse system
`(K_n)` in `D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the
cohomology groups over `U` fit into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim H^m(U, K_n) \to 0`. -/
theorem ringedSiteDerivedSectionsOverObject_cohomology_shortExact
    (U : X)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleSectionsAsAbelianDerived X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleSectionsAsAbelianDerived X U).obj K) ⟶
          limit
            ((Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end SectionsOverObject
