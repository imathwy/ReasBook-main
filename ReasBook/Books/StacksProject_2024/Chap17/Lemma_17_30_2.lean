import Mathlib
import StacksProject_2024.Chap17.Definition_17_30_1
import StacksProject_2024.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace ComplexShape
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.2:
- primary domain: inverse-image compatibility for relative de Rham complexes of sheaves of rings
  on a topological space;
- sampled owner declarations:
  `TopCat.Sheaf.deRhamComplex`,
  `Ω^•(φ)`,
  `TopCat.Sheaf.deRhamComplexTerm_eq_restrictScalars`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `HomologicalComplex.Hom.isoOfComponents`;
- best owner abstraction: the source-facing owner remains the relative de Rham complex `Ω^•(φ)`,
  with raw owner `TopCat.Sheaf.deRhamComplex φ`, and the
  inverse-image comparison should be exposed by an actual complex isomorphism between the inverse
  image of `Ω^•(φ)` and the pulled-back de Rham complex;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₁`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: the named complex isomorphism `inverseImage_deRhamComplexIso` and its
  theorem-level `IsIsomorphic` companion.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1}\Omega^\bullet_{O₂/O₁} = \Omega^\bullet_{f^{-1}O₂/f^{-1}O₁}`;
- `core/canonical`: `Ω^•(φ)`, `inverseImage_relativeDifferentialsIso`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: this file packages that identification as a complex isomorphism transported across
  `pullbackRingSheafIso f O₁`.

The bridge should therefore live at the complex-isomorphism layer, with `IsIsomorphic` retained
only as the thin theorem companion, and its public type should mention the actual source and target
complexes rather than file-local wrapper aliases. -/

/-- Lemma 17.30.2: the inverse image of the relative de Rham complex
`\Omega^\bullet_{O₂/O₁}` is canonically isomorphic, as a cochain complex, to the relative de Rham
complex of the pulled-back morphism
`f^{-1}\mathcal O_1 \to f^{-1}\mathcal O_2`, expressed over the raw pulled-back
`RingCat`-valued structure sheaf via `pullbackRingSheafIso f O₁`. -/
noncomputable def inverseImage_deRhamComplexIso
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
      (up ℕ)).obj
      Ω^•(φ)) ≅
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)) := by
  sorry

/-- The inverse image of the relative de Rham complex is canonically identified with the relative
de Rham complex of the pulled-back morphism. This is the theorem-level `IsIsomorphic` companion to
`inverseImage_deRhamComplexIso`. -/
theorem inverseImage_deRhamComplex_isIsomorphic
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•(φ))
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)) := by
  exact ⟨inverseImage_deRhamComplexIso f φ⟩

end TopCat.Sheaf
