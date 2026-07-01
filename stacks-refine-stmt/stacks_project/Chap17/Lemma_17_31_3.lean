import Mathlib
import stacks_project.Chap17.Definition_17_31_1
import stacks_project.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]
variable [Limits.HasBinaryCoproducts (Y.Sheaf CommRingCat.{u})]

/- Domain-style sampling for Lemma 17.31.3:
- primary domain: inverse-image compatibility for the naive cotangent complex of a morphism of
  sheaves of commutative rings on a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `CategoryTheory.Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing owner is the whole two-term complex
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site of `X`, not only its
  degree-`0` relative-differentials term;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₂`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: the named complex isomorphism `inverseImage_naiveCotangentIso` and its thin
  theorem-level `IsIsomorphic` companion between the actual inverse image of the opens-site
  specialization `naiveCotangent (J := Opens.grothendieckTopology X) O₁ (Under.mk φ)` and the
  pulled-back opens-site specialization, transported across `pullbackRingSheafIso f O₂`.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1} NL_{\mathcal O_2 / \mathcal O_1} = NL_{f^{-1}\mathcal O_2 / f^{-1}\mathcal O_1}`;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`, `pullbackRingSheafIso`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: this file should expose the inverse-image comparison by the actual complex
  isomorphism over the raw pulled-back `RingCat`-valued structure sheaf, with `IsIsomorphic`
  retained only as the thin theorem companion. -/

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)] in
/-- The inverse image of the naive cotangent complex is canonically isomorphic, as a cochain
complex, to the naive cotangent complex of the pulled-back morphism. -/
noncomputable def inverseImage_naiveCotangentIso
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).mapHomologicalComplex
      (up ℤ)).obj
      (naiveCotangent O₁ (Under.mk φ))) ≅
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent
          ((pullback CommRingCat.{u} f).obj O₁)
          (Under.mk ((pullback CommRingCat.{u} f).map φ)))) := by
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)] in
/-- The inverse image of the naive cotangent complex is canonically identified with the naive
cotangent complex of the pulled-back morphism. This is the theorem-level `IsIsomorphic` companion
to `inverseImage_naiveCotangentIso`. -/
theorem inverseImage_naiveCotangent_isIsomorphic
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent O₁ (Under.mk φ)))
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent
          ((pullback CommRingCat.{u} f).obj O₁)
          (Under.mk ((pullback CommRingCat.{u} f).map φ)))) := by
  exact ⟨inverseImage_naiveCotangentIso f φ⟩

end TopCat.Sheaf
