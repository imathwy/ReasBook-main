import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_30_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace ComplexShape
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
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
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `TopCat.Sheaf.deRhamComplex_d_basicForm`,
  `HomologicalComplex.Hom.isoOfComponents`,
  `CategoryTheory.Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing owner remains the relative de Rham complex `Ω^•(φ)`,
  with raw owner `TopCat.Sheaf.deRhamComplex φ`; this file records only the theorem-level
  inverse-image identification, so the public entry should be the theorem-level complex
  `IsIsomorphic` statement rather than a parallel chosen `Iso` wrapper with no extra owner data;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₁`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: the theorem-level comparison `inverseImage_deRhamComplex_isIsomorphic`. 

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1}\Omega^\bullet_{O₂/O₁} = \Omega^\bullet_{f^{-1}O₂/f^{-1}O₁}`;
- `core/canonical`: `Ω^•(φ)`, `inverseImage_relativeDifferentialsIso`,
  and `deRhamComplex_d_basicForm`;
- `bridge/view`: this file records the resulting complex isomorphism after transport across
  `pullbackRingSheafIso f O₁`, with no extra chosen `Iso` declaration. -/

/- Lemma 17.30.2: the inverse image of the relative de Rham complex
`\Omega^\bullet_{O₂/O₁}` is canonically identified with the relative de Rham complex of the
pulled-back morphism. This theorem-level statement is the main public comparison, avoiding a
parallel chosen complex `Iso` wrapper. -/
/-- Helper for Lemma 17.30.2: the change-of-rings square built from `φ` and the inverse-image
functor for `f` commutes strictly on the underlying opens categories. -/
private theorem inverseImageRestrictScalarsSquare_hcomm
    (f : Y ⟶ X) :
    (Opens.map f) ⋙ 𝟭 (Opens X) = 𝟭 (Opens Y) ⋙ (Opens.map f) := rfl

/-- Helper for Lemma 17.30.2: the ring map `φ` recast as a same-site `RingCat`-valued structure
map over the identity functor on `Opens X`. -/
private abbrev ringSheafMapOverId
    (φ : O₁ ⟶ O₂) :
    ringSheaf O₂ ⟶
      ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj
        (ringSheaf O₁) :=
  ringSheafMap φ ≫
    (Functor.sheafPushforwardContinuousId RingCat.{u} (Opens.grothendieckTopology X)).inv.app
      (ringSheaf O₁)

/-- Helper for Lemma 17.30.2: after unfolding the de Rham complex, the degree-`n` term on the
source side is the inverse image of the degree-`n` form sheaf viewed as an `O₁`-module. -/
private theorem inverseImageDeRhamComplexSourceObj
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) (n : ℕ) :
    ((((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•(φ)).X n) =
      (SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).obj
        ((SheafOfModules.restrictScalars (ringSheafMap φ)).obj Ω^[n](φ)) := by
  -- Proof comment: `mapHomologicalComplex` acts degreewise, so only the object formula
  -- `deRhamComplex_obj` remains after unfolding.
  simpa [deRhamComplex_obj]

/-- Helper for Lemma 17.30.2: after unfolding the de Rham complex, the degree-`n` term on the
target side is the pulled-back degree-`n` form sheaf, transported to the raw inverse-image ring
sheaf of `O₁`. -/
private theorem inverseImageDeRhamComplexTargetObj
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) (n : ℕ) :
    ((((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)).X n) =
      (SheafOfModules.restrictScalars
        (pullbackRingSheafIso f O₁).inv).obj
        ((SheafOfModules.restrictScalars
          (ringSheafMap ((pullback CommRingCat.{u} f).map φ))).obj
          Ω^[n]((pullback CommRingCat.{u} f).map φ)) := by
  -- Proof comment: the target complex is also degreewise, so the same object formula exposes the
  -- remaining scalar-transport layer that must be compared componentwise.
  simpa [deRhamComplex_obj]

/-- Helper for Lemma 17.30.2: in degree `1`, the target complex component is the pulled-back
relative-differentials sheaf, expressed on the raw inverse-image `O₁`-module surface. -/
private theorem inverseImageDeRhamComplexTargetObj_one
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    ((((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)).X 1) =
      (SheafOfModules.restrictScalars
        (pullbackRingSheafIso f O₁).inv).obj
        ((SheafOfModules.restrictScalars
          (ringSheafMap ((pullback CommRingCat.{u} f).map φ))).obj
          Ω((pullback CommRingCat.{u} f).map φ)) := by
  -- Proof comment: specializing the degreewise target normalization to `n = 1` exposes the
  -- exact one-form component needed for the future componentwise comparison.
  simpa using inverseImageDeRhamComplexTargetObj (f := f) (φ := φ) 1

/-- Helper for Lemma 17.30.2: the inverse image of the relative de Rham complex is canonically
isomorphic to the de Rham complex of the pulled-back morphism. -/
theorem inverseImage_deRhamComplexIso
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•(φ)) ≅
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)) := by
  -- Route correction: the ringed-site owner theorem already packages the entire degreewise
  -- comparison and differential compatibility, so this file only needs its opens-site
  -- specialization.
  -- Proof comment: after rewriting the Chapter 17 ring-sheaf wrapper to the canonical ringed-site
  -- pullback comparison, the imported owner theorem matches the target complex isomorphism.
  simpa [pullbackRingSheafIso_eq_ringedSite_pullbackRingSheafIso] using
    (SheafOfModules.RingedSite.inverseImage_deRhamComplexIso
      (F := Opens.map f)
      (JC := Opens.grothendieckTopology X)
      (JD := Opens.grothendieckTopology Y)
      O₁ O₂ φ)

/-- Lemma 17.30.2: the inverse image of the relative de Rham complex
`\Omega^\bullet_{O₂/O₁}` is canonically identified with the relative de Rham complex of the
pulled-back morphism. This theorem-level statement is the main public comparison, avoiding a
parallel chosen complex `Iso` wrapper. -/
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
        Ω^•((pullback CommRingCat.{u} f).map φ)) :=
  by
  -- Proof comment: the source-facing theorem is the `IsIsomorphic` packaging of the explicit
  -- complex isomorphism constructed above.
  exact ⟨inverseImage_deRhamComplexIso f φ⟩

end TopCat.Sheaf
