import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Lemma_20_31_8
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Situation 20.45.3:
- primary domain: derived restriction of `𝒪_X`-module sheaves to open subspaces and
  gluing data indexed by a basis of opens;
- sampled canonical declarations:
  `moduleRestrictionToOpenDerived`,
  `moduleDerivedOnOpen`,
  `derivedRestrictionBetweenOpens`,
  `derivedRestrictionBetweenOpensCompIso`,
  `moduleRestrictionToOpenDerivedCompIso`,
  `CategoryTheory.CommSq`;
- best owner abstraction in this local closure: the ambient owner is the Chapter 20 alias
  `ModuleDerived X` for objects of `D(𝒪_X)`, while
  `Open_subspace_module_core` owns the open-subspace derived categories `D(𝒪_U)` and
  restriction from `X` to a chosen open `U`, together with the nested-open restriction bridge and
  its canonical comparison isomorphisms; this file should therefore keep only the source-facing
  gluing datum built from those owners, while the canonical topological owner for a basis of opens
  is `Opens.IsBasis`;
- primitive data: the local derived objects on basis opens and their transition isomorphisms;
- derived API: negative self-Ext vanishing, realization data for an ambient object
  `K : ModuleDerived X`, the realization predicate, and compatible
  isomorphisms between realizations, with basis hypotheses taken downstream through
  `Opens.IsBasis`.

Layer triage:
- `source-facing`: `OpenFamilyDerivedGluing` and its realization predicate on ambient derived
  objects;
- `core/canonical`: `ModuleDerived X`, `moduleRestrictionToOpenDerived`,
  `moduleDerivedOnOpen`, `derivedRestrictionBetweenOpens`,
  `moduleRestrictionToOpenDerivedCompIso`, `Opens.IsBasis`, and `CommSq`;
- `bridge/view`: none new here beyond the owner layer imported from
  `Open_subspace_module_core`.

This file therefore keeps only the source-facing gluing datum and its immediate companion notions,
while reusing the project owner API for open-subspace derived categories and restriction functors
instead of redeclaring parallel local copies or a parallel basis predicate.
-/

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

local notation "OpenX" => Opens X.carrier
local notation "DModX" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DRes≤[" h "]" => derivedRestrictionBetweenOpens X h
local notation "DResFromXComp[" h "]" => moduleRestrictionToOpenDerivedCompIso X h

/-- Situation 20.45.3: a family of local derived objects on the opens of `𝓑`, together with
restriction isomorphisms satisfying the cocycle condition on triple inclusions. -/
@[stacks 0D67]
structure OpenFamilyDerivedGluing
    (X : RingedSpace.{u}) (𝓑 : Set (Opens X.carrier)) where
  /-- The derived object attached to a basis open of `𝓑`. -/
  obj (U : Opens X.carrier) (hU : U ∈ 𝓑) : moduleDerivedOnOpen X U
  /-- The restriction isomorphism `K_U|_V ≅ K_V` for an inclusion `V ⊆ U` in the basis. -/
  ρ (U V : Opens X.carrier) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
      (derivedRestrictionBetweenOpens X hVU).obj (obj U hU) ≅ obj V hV
  /-- The restriction isomorphisms satisfy the cocycle condition on triple inclusions. -/
  ρ_comp (U V W : Opens X.carrier)
      (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hW : W ∈ 𝓑) (hWV : W ≤ V) (hVU : V ≤ U) :
      ((derivedRestrictionBetweenOpensCompIso X hWV hVU).app (obj U hU)) ≪≫
          ρ U W hU hW (hWV.trans hVU) =
        (derivedRestrictionBetweenOpens X hWV).mapIso (ρ U V hU hV hVU) ≪≫
          ρ V W hV hW hWV

namespace OpenFamilyDerivedGluing

/-- The local derived objects of a gluing system have vanishing negative self-Ext groups on the
basis opens. -/
abbrev NegativeSelfExtVanishing
    (glue : OpenFamilyDerivedGluing X 𝓑) : Prop :=
  ∀ (U : OpenX) (hU : U ∈ 𝓑) (i : ℤ), i < 0 →
    IsZero (AddCommGrpCat.of (Ext^i(glue.obj U hU, glue.obj U hU)))

/-- A family of basiswise restriction identifications from an ambient derived object to the local
objects of a gluing datum. -/
abbrev RealizationIso
    (glue : OpenFamilyDerivedGluing X 𝓑) (K : DModX) :=
  ∀ (U : OpenX) (hU : U ∈ 𝓑), (DRes[U]).obj K ≅ glue.obj U hU

/-- The restriction identifications of an ambient derived object recover the prescribed local
restriction isomorphisms on inclusions inside the basis. -/
def IsRealization
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (K : DModX) (iso : glue.RealizationIso K) : Prop :=
  ∀ (U V : OpenX) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U),
    CommSq (((DResFromXComp[hVU]).app K).inv)
      (iso V hV).hom ((DRes≤[hVU]).map (iso U hU).hom) (glue.ρ U V hU hV hVU).inv

/-- An ambient derived object realizes a local derived gluing datum if its restrictions to the
basis opens recover the prescribed local objects compatibly with the transition isomorphisms. -/
def Realizes
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (K : DModX) : Prop :=
  ∃ iso : glue.RealizationIso K, glue.IsRealization K iso

/-- A global realization is exactly a choice of basiswise restriction isomorphisms satisfying the
compatibility squares with the prescribed transition maps. -/
theorem realizes_iff_exists_isRealization
    (glue : OpenFamilyDerivedGluing X 𝓑) (K : DModX) :
    glue.Realizes K ↔ ∃ iso : glue.RealizationIso K, glue.IsRealization K iso :=
  Iff.rfl

/-- Unpack one compatibility square from a realization datum. -/
theorem IsRealization.commSq
    {glue : OpenFamilyDerivedGluing X 𝓑} {K : DModX}
    {iso : glue.RealizationIso K}
    (hiso : glue.IsRealization K iso)
    (U V : OpenX) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    CommSq (((DResFromXComp[hVU]).app K).inv)
      (iso V hV).hom ((DRes≤[hVU]).map (iso U hU).hom) (glue.ρ U V hU hV hVU).inv :=
  hiso U V hU hV hVU

/-- Equational form of a realization compatibility square. -/
theorem IsRealization.w
    {glue : OpenFamilyDerivedGluing X 𝓑} {K : DModX}
    {iso : glue.RealizationIso K}
    (hiso : glue.IsRealization K iso)
    (U V : OpenX) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    ((DResFromXComp[hVU]).app K).inv ≫ ((DRes≤[hVU]).map (iso U hU).hom) =
      (iso V hV).hom ≫ (glue.ρ U V hU hV hVU).inv :=
  (hiso.commSq U V hU hV hVU).w

/-- An isomorphism between two ambient realizations is compatible with the prescribed basis
identifications when its restriction to each basis open intertwines the local comparison
isomorphisms. -/
abbrev IsCompatibleIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    {K L : DModX}
    (isoK : glue.RealizationIso K)
    (isoL : glue.RealizationIso L)
    (e : K ≅ L) : Prop :=
  ∀ (U : OpenX) (hU : U ∈ 𝓑),
    CommSq ((DRes[U]).map e.hom) (isoK U hU).hom (isoL U hU).hom (𝟙 (glue.obj U hU))

/-- Unpack the restriction square expressing compatibility of an ambient isomorphism with the
chosen basiswise realization data. -/
theorem IsCompatibleIso.commSq
    {glue : OpenFamilyDerivedGluing X 𝓑}
    {K L : DModX}
    {isoK : glue.RealizationIso K}
    {isoL : glue.RealizationIso L}
    {e : K ≅ L}
    (he : glue.IsCompatibleIso isoK isoL e)
    (U : OpenX) (hU : U ∈ 𝓑) :
    CommSq ((DRes[U]).map e.hom) (isoK U hU).hom (isoL U hU).hom (𝟙 (glue.obj U hU)) :=
  he U hU

/-- Equational form of compatibility of an ambient isomorphism with the chosen basiswise
realization data. -/
theorem IsCompatibleIso.w
    {glue : OpenFamilyDerivedGluing X 𝓑}
    {K L : DModX}
    {isoK : glue.RealizationIso K}
    {isoL : glue.RealizationIso L}
    {e : K ≅ L}
    (he : glue.IsCompatibleIso isoK isoL e)
    (U : OpenX) (hU : U ∈ 𝓑) :
    (DRes[U]).map e.hom ≫ (isoL U hU).hom =
      (isoK U hU).hom := by
  simpa using (he.commSq U hU).w

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
